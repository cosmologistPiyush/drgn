// Copyright (c) Meta Platforms, Inc. and affiliates.
// SPDX-License-Identifier: LGPL-2.1-or-later

#include <stdlib.h>
#include <unistd.h>

#include "array.h"
#include "debug_info.h"
#include "elf_file.h"
#include "error.h"

struct drgn_error *read_elf_section(Elf_Scn *scn, Elf_Data **ret)
{
	GElf_Shdr shdr_mem, *shdr;
	shdr = gelf_getshdr(scn, &shdr_mem);
	if (!shdr)
		return drgn_error_libelf();
	if ((shdr->sh_flags & SHF_COMPRESSED) && elf_compress(scn, 0, 0) < 0)
		return drgn_error_libelf();
	Elf_Data *data = elf_rawdata(scn, NULL);
	if (!data)
		return drgn_error_libelf();
	*ret = data;
	return NULL;
}

static const char * const drgn_section_index_names[] = {
	[DRGN_SCN_DEBUG_INFO] = ".debug_info",
	[DRGN_SCN_DEBUG_TYPES] = ".debug_types",
	[DRGN_SCN_DEBUG_ABBREV] = ".debug_abbrev",
	[DRGN_SCN_DEBUG_STR] = ".debug_str",
	[DRGN_SCN_DEBUG_STR_OFFSETS] = ".debug_str_offsets",
	[DRGN_SCN_DEBUG_LINE] = ".debug_line",
	[DRGN_SCN_DEBUG_LINE_STR] = ".debug_line_str",
	[DRGN_SCN_DEBUG_ADDR] = ".debug_addr",
	[DRGN_SCN_DEBUG_FRAME] = ".debug_frame",
	[DRGN_SCN_EH_FRAME] = ".eh_frame",
	[DRGN_SCN_ORC_UNWIND_IP] = ".orc_unwind_ip",
	[DRGN_SCN_ORC_UNWIND] = ".orc_unwind",
	[DRGN_SCN_DEBUG_LOC] = ".debug_loc",
	[DRGN_SCN_DEBUG_LOCLISTS] = ".debug_loclists",
	[DRGN_SCN_TEXT] = ".text",
	[DRGN_SCN_GOT] = ".got",
	[DRGN_SCN_GNU_DEBUGLINK] = ".gnu_debuglink",
	[DRGN_SCN_GNU_DEBUGALTLINK] = ".gnu_debugaltlink",
};

struct drgn_error *drgn_elf_file_create(struct drgn_module *module,
					const char *path, int fd, char *image,
					Elf *elf, struct drgn_elf_file **ret)
{
	struct drgn_error *err;

	if (elf_kind(elf) != ELF_K_ELF)
		return drgn_error_create(DRGN_ERROR_OTHER, "not an ELF file");

	GElf_Ehdr ehdr_mem, *ehdr = gelf_getehdr(elf, &ehdr_mem);
	if (!ehdr)
		return drgn_error_libelf();

	struct drgn_elf_file *file = calloc(1, sizeof(*file));
	if (!file)
		return &drgn_enomem;

	if (ehdr->e_type == ET_EXEC ||
	    ehdr->e_type == ET_DYN ||
	    ehdr->e_type == ET_REL) {
		size_t shstrndx;
		if (elf_getshdrstrndx(elf, &shstrndx)) {
			err = drgn_error_libelf();
			goto err;
		}

		bool has_sections = false;
		bool has_alloc_section = false;
		Elf_Scn *scn = NULL;
		while ((scn = elf_nextscn(elf, scn))) {
			GElf_Shdr shdr_mem, *shdr;
			shdr = gelf_getshdr(scn, &shdr_mem);
			if (!shdr) {
				err = drgn_error_libelf();
				goto err;
			}

			has_sections = true;
			if (shdr->sh_type != SHT_NOBITS &&
			    shdr->sh_type != SHT_NOTE &&
			    (shdr->sh_flags & SHF_ALLOC))
				has_alloc_section = true;

			if (shdr->sh_type != SHT_PROGBITS)
				continue;
			const char *scnname =
				elf_strptr(elf, shstrndx, shdr->sh_name);
			if (!scnname) {
				err = drgn_error_libelf();
				goto err;
			}
			for (size_t i = 0; i < DRGN_SECTION_INDEX_NUM; i++) {
				if (!file->scns[i] &&
				    strcmp(scnname,
					   drgn_section_index_names[i]) == 0) {
					file->scns[i] = scn;
					break;
				}
			}
		}
		if (ehdr->e_type == ET_REL) {
			// We consider a relocatable file "loadable" if it has
			// any allocated sections.
			file->is_loadable = has_alloc_section;
		} else {
			// We consider executable and shared object files
			// loadable if they have any loadable segments, and
			// either no sections or at least one allocated section.
			bool has_loadable_segment = false;
			size_t phnum;
			if (elf_getphdrnum(elf, &phnum) != 0) {
				err = drgn_error_libelf();
				goto err;
			}
			for (size_t i = 0; i < phnum; i++) {
				GElf_Phdr phdr_mem, *phdr =
					gelf_getphdr(elf, i, &phdr_mem);
				if (!phdr) {
					err = drgn_error_libelf();
					goto err;
				}
				if (phdr->p_type == PT_LOAD) {
					has_loadable_segment = true;
					break;
				}
			}
			file->is_loadable =
				has_loadable_segment &&
				(!has_sections || has_alloc_section);
		}
	}

	file->module = module;
	file->path = strdup(path);
	if (!file->path) {
		err = &drgn_enomem;
		goto err;
	}
	file->image = image;
	file->fd = fd;
	file->elf = elf;
	drgn_platform_from_elf(ehdr, &file->platform);
	*ret = file;
	return NULL;

err:
	free(file);
	return err;
}

void drgn_elf_file_destroy(struct drgn_elf_file *file)
{
	if (file) {
		dwarf_end(file->dwarf);
		elf_end(file->elf);
		if (file->fd >= 0)
			close(file->fd);
		free(file->image);
		free(file->path);
		free(file);
	}
}

static void truncate_null_terminated_section(Elf_Data *data)
{
	if (data) {
		const char *buf = data->d_buf;
		const char *nul = memrchr(buf, '\0', data->d_size);
		if (nul)
			data->d_size = nul - buf + 1;
		else
			data->d_size = 0;
	}
}

struct drgn_error *drgn_elf_file_precache_sections(struct drgn_elf_file *file)
{
	struct drgn_error *err;

	for (size_t i = 0; i < DRGN_SECTION_INDEX_NUM_PRECACHE; i++) {
		if (file->scns[i]) {
			err = read_elf_section(file->scns[i],
					       &file->scn_data[i]);
			if (err)
				return err;
		}
	}

	/*
	 * Truncate any extraneous bytes so that we can assume that a pointer
	 * within .debug_{,line_}str is always null-terminated.
	 */
	truncate_null_terminated_section(file->scn_data[DRGN_SCN_DEBUG_STR]);
	truncate_null_terminated_section(file->scn_data[DRGN_SCN_DEBUG_LINE_STR]);

	// TODO: ugly place to put this
	struct drgn_elf_file *gnu_debugaltlink_file = file->module->gnu_debugaltlink_file;
	if (gnu_debugaltlink_file) {
		err = read_elf_section(gnu_debugaltlink_file->scns[DRGN_SCN_DEBUG_INFO],
				       &gnu_debugaltlink_file->scn_data[DRGN_SCN_DEBUG_INFO]);
		if (err)
			return err;
		err = read_elf_section(gnu_debugaltlink_file->scns[DRGN_SCN_DEBUG_STR],
				       &gnu_debugaltlink_file->scn_data[DRGN_SCN_DEBUG_STR]);
		if (err)
			return err;
		truncate_null_terminated_section(gnu_debugaltlink_file->scn_data[DRGN_SCN_DEBUG_STR]);
		file->alt_debug_info_data =
			gnu_debugaltlink_file->scn_data[DRGN_SCN_DEBUG_INFO];
		file->alt_debug_str_data =
			gnu_debugaltlink_file->scn_data[DRGN_SCN_DEBUG_STR];
	}
	return NULL;
}

struct drgn_error *
drgn_elf_file_cache_section(struct drgn_elf_file *file, enum drgn_section_index scn)
{
	if (file->scn_data[scn])
		return NULL;
	return read_elf_section(file->scns[scn], &file->scn_data[scn]);
}

struct drgn_error *
drgn_elf_file_section_error(struct drgn_elf_file *file, Elf_Scn *scn,
			    Elf_Data *data, const char *ptr,
			    const char *message)
{
	// If we don't know what section the pointer came from, try to find it
	// in the cached sections.
	if (!scn) {
		uintptr_t p = (uintptr_t)ptr;
		for (size_t i = 0; i < array_size(file->scn_data); i++) {
			if (!file->scn_data[i])
				continue;
			uintptr_t start = (uintptr_t)file->scn_data[i]->d_buf;
			uintptr_t end = start + file->scn_data[i]->d_size;
			if (start <= p) {
				// If the pointer matches the end of a section,
				// remember the section but try to find a better
				// match.
				if (p <= end) {
					scn = file->scns[i];
					data = file->scn_data[i];
				}
				// If the pointer lies inside of the section,
				// we're done.
				if (p < end)
					break;
			}
		}
	}
	const char *scnname = NULL;
	size_t shstrndx;
	GElf_Shdr shdr_mem, *shdr;
	if (!elf_getshdrstrndx(file->elf, &shstrndx) &&
	    (shdr = gelf_getshdr(scn, &shdr_mem)))
		scnname = elf_strptr(file->elf, shstrndx, shdr->sh_name);

	if (scnname && data) {
		return drgn_error_format(DRGN_ERROR_OTHER, "%s: %s+%#tx: %s",
					 file->path, scnname,
					 ptr - (const char *)data->d_buf,
					 message);
	} else if (scnname) {
		return drgn_error_format(DRGN_ERROR_OTHER, "%s: %s: %s",
					 file->path, scnname, message);
	} else {
		return drgn_error_format(DRGN_ERROR_OTHER, "%s: %s", file->path,
					 message);
	}
}

struct drgn_error *drgn_elf_file_section_buffer_error(struct binary_buffer *bb,
						      const char *ptr,
						      const char *message)
{
	struct drgn_elf_file_section_buffer *buffer =
		container_of(bb, struct drgn_elf_file_section_buffer, bb);
	return drgn_elf_file_section_error(buffer->file, buffer->scn,
					   buffer->data, ptr, message);
}
