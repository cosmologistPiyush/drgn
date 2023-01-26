// Copyright (c) Meta Platforms, Inc. and affiliates.
// SPDX-License-Identifier: LGPL-2.1-or-later

#include <assert.h>
#include <byteswap.h>
#include <dirent.h>
#include <elf.h>
#include <elfutils/libdw.h>
#include <elfutils/libdwelf.h>
#include <elfutils/version.h>
#include <errno.h>
#include <fcntl.h>
#include <gelf.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/sysmacros.h>
#include <sys/types.h>
#include <termios.h>
#include <unistd.h>
#include <wchar.h>

#include "array.h"
#include "crc32.h"
#include "debug_info.h"
#include "elf_file.h"
#include "error.h"
#include "hexlify.h"
#include "io.h"
#include "linux_kernel.h"
#include "log.h"
#include "program.h"
#include "serialize.h"
#include "util.h"

DEFINE_HASH_MAP_FUNCTIONS(drgn_module_section_address_map,
			  c_string_key_hash_pair, c_string_key_eq)

struct drgn_module_trying_gnu_debugaltlink {
	struct drgn_elf_file *debug_file;
	const char *debugaltlink_path;
	const void *build_id;
	size_t build_id_len;
	char *build_id_str;
	struct drgn_elf_file *found;
};

#if !_ELFUTILS_PREREQ(0, 175)
// If we don't have dwelf_elf_begin(), this is equivalent except that it doesn't
// handle compressed files.
static inline Elf *dwelf_elf_begin(int fd)
{
	return elf_begin(fd, ELF_C_READ_MMAP_PRIVATE, NULL);
}
#endif

#if WITH_DEBUGINFOD

#if _ELFUTILS_PREREQ(0, 179)
// debuginfod_set_user_data(), debuginfod_get_user_data(), and
// debuginfod_get_url() were added in elfutils 0.179.
// debuginfod_set_progressfn() has been there since the beginning, but it's only
// useful to us if we have those other functions.
#define DRGN_DEBUGINFOD_0_179_FUNCTIONS	\
	X(debuginfod_set_progressfn)	\
	X(debuginfod_set_user_data)	\
	X(debuginfod_get_user_data)	\
	X(debuginfod_get_url)
#else
#define DRGN_DEBUGINFOD_0_179_FUNCTIONS
#endif

#define DRGN_DEBUGINFOD_FUNCTIONS	\
	X(debuginfod_begin)		\
	X(debuginfod_end)		\
	X(debuginfod_find_debuginfo)	\
	X(debuginfod_find_executable)	\
	DRGN_DEBUGINFOD_0_179_FUNCTIONS

#if ENABLE_DLOPEN_DEBUGINFOD
#include <dlfcn.h>

#define X(name) static typeof(&name) drgn_##name;
DRGN_DEBUGINFOD_FUNCTIONS
#undef X

__attribute__((__constructor__))
static void drgn_dlopen_debuginfod(void)
{
	void *handle = dlopen(DEBUGINFOD_SONAME, RTLD_LAZY);
	if (handle) {
		#define X(name) drgn_##name = dlsym(handle, #name);
		DRGN_DEBUGINFOD_FUNCTIONS
		#undef X

		#define X(name) || !drgn_##name
		if (0 DRGN_DEBUGINFOD_FUNCTIONS) {
		#undef X
			#define X(name) drgn_##name = NULL;
			DRGN_DEBUGINFOD_FUNCTIONS
			#undef X
			dlclose(handle);
		}
	}
}

static inline bool drgn_have_debuginfod(void)
{
	return !!drgn_debuginfod_begin;
}

#else
// GCC and Clang optimize out the function pointer.
#define X(name) static const typeof(&name) drgn_##name = name;
DRGN_DEBUGINFOD_FUNCTIONS
#undef X

static inline bool drgn_have_debuginfod(void)
{
	return true;
}
#endif

#undef DRGN_DEBUGINFOD_FUNCTIONS
#undef DRGN_DEBUGINFOD_0_179_FUNCTIONS
#endif

static inline
struct drgn_module_key drgn_module_entry_key(struct drgn_module * const *entry)
{
	struct drgn_module_key key;
	key.kind = (*entry)->kind;
	SWITCH_ENUM(key.kind,
	case DRGN_MODULE_SHARED_LIBRARY:
		key.shared_library.name = (*entry)->name;
		key.shared_library.dynamic_address =
			(*entry)->shared_library.dynamic_address;
		break;
	case DRGN_MODULE_VDSO:
		key.vdso.name = (*entry)->name;
		key.vdso.dynamic_address = (*entry)->vdso.dynamic_address;
		break;
	case DRGN_MODULE_LINUX_KERNEL_LOADABLE:
		key.linux_kernel_loadable.name = (*entry)->name;
		key.linux_kernel_loadable.base_address =
			(*entry)->linux_kernel_loadable.base_address;
		break;
	case DRGN_MODULE_EXTRA:
		key.extra.name = (*entry)->name;
		key.extra.id = (*entry)->extra.id;
		break;
	case DRGN_MODULE_MAIN:
	)
	return key;
}

static inline struct hash_pair
drgn_module_key_hash_pair(const struct drgn_module_key *key)
{
	size_t hash = key->kind;
	SWITCH_ENUM(key->kind,
	case DRGN_MODULE_SHARED_LIBRARY:
		hash = hash_combine(hash,
				    hash_c_string(key->shared_library.name));
		hash = hash_combine(hash, key->shared_library.dynamic_address);
		break;
	case DRGN_MODULE_VDSO:
		hash = hash_combine(hash, hash_c_string(key->vdso.name));
		hash = hash_combine(hash, key->vdso.dynamic_address);
		break;
	case DRGN_MODULE_LINUX_KERNEL_LOADABLE:
		hash = hash_combine(hash,
				    hash_c_string(key->linux_kernel_loadable.name));
		hash = hash_combine(hash, key->linux_kernel_loadable.base_address);
		break;
	case DRGN_MODULE_EXTRA:
		hash = hash_combine(hash, hash_c_string(key->extra.name));
		hash = hash_combine(hash, key->extra.id);
		break;
	case DRGN_MODULE_MAIN:
	)
	return hash_pair_from_avalanching_hash(hash);
}

static inline bool drgn_module_key_eq(const struct drgn_module_key *a,
				      const struct drgn_module_key *b)
{
	if (a->kind != b->kind)
		return false;
	SWITCH_ENUM(a->kind,
	case DRGN_MODULE_SHARED_LIBRARY:
		return (strcmp(a->shared_library.name,
			       b->shared_library.name) == 0
			&& a->shared_library.dynamic_address
			== b->shared_library.dynamic_address);
		break;
	case DRGN_MODULE_VDSO:
		return (strcmp(a->vdso.name, b->vdso.name) == 0
			&& a->vdso.dynamic_address == b->vdso.dynamic_address);
		break;
	case DRGN_MODULE_LINUX_KERNEL_LOADABLE:
		return (strcmp(a->linux_kernel_loadable.name,
			       b->linux_kernel_loadable.name) == 0
			&& a->linux_kernel_loadable.base_address
			== b->linux_kernel_loadable.base_address);
		break;
	case DRGN_MODULE_EXTRA:
		return (strcmp(a->extra.name, b->extra.name) == 0
			&& a->extra.id == b->extra.id);
		break;
	case DRGN_MODULE_MAIN:
	)
}

DEFINE_HASH_TABLE_FUNCTIONS(drgn_module_table, drgn_module_entry_key,
			    drgn_module_key_hash_pair, drgn_module_key_eq)

static inline uint64_t drgn_module_address_key(const struct drgn_module *entry)
{
	return entry->start;
}

DEFINE_BINARY_SEARCH_TREE_FUNCTIONS(drgn_module_address_tree, node,
				    drgn_module_address_key,
				    binary_search_tree_scalar_cmp, splay)

static void drgn_module_free_section_addresses(struct drgn_module *module)
{
	for (struct drgn_module_section_address_map_iterator it =
	     drgn_module_section_address_map_first(&module->section_addresses);
	     it.entry;
	     it = drgn_module_section_address_map_next(it))
		free(it.entry->key);
}

LIBDRGN_PUBLIC
struct drgn_module *drgn_module_find(struct drgn_program *prog,
				     const struct drgn_module_key *key)
{
	if (key->kind == DRGN_MODULE_MAIN) {
		return prog->dbinfo->main_module;
	} else {
		struct drgn_module_table_iterator it =
			drgn_module_table_search(&prog->dbinfo->modules, key);
		return it.entry ? *it.entry : NULL;
	}
}

// TODO: not a big fan of this
static struct drgn_error *drgn_program_create_dbinfo(struct drgn_program *prog)
{
	struct drgn_error *err;
	if (prog->dbinfo)
		return NULL;
	struct drgn_debug_info *dbinfo;
	err = drgn_debug_info_create(prog, &dbinfo);
	if (err)
		return err;
	err = drgn_program_add_object_finder(prog, drgn_debug_info_find_object,
					     dbinfo);
	if (err) {
		drgn_debug_info_destroy(dbinfo);
		return err;
	}
	err = drgn_program_add_type_finder(prog, drgn_debug_info_find_type,
					   dbinfo);
	if (err) {
		drgn_object_index_remove_finder(&prog->oindex);
		drgn_debug_info_destroy(dbinfo);
		return err;
	}
	prog->dbinfo = dbinfo;
	return NULL;
}

struct drgn_error *drgn_module_find_or_create(struct drgn_program *prog,
					      const struct drgn_module_key *key,
					      const char *name,
					      struct drgn_module **ret,
					      bool *new_ret)
{
	struct drgn_error *err;

	err = drgn_program_create_dbinfo(prog);
	if (err)
		return err;

	struct hash_pair hp;
	if (key->kind == DRGN_MODULE_MAIN) {
		if (prog->dbinfo->main_module) {
			*ret = prog->dbinfo->main_module;
			if (new_ret)
				*new_ret = false;
			return NULL;
		}
	} else {
		hp = drgn_module_table_hash(key);
		struct drgn_module_table_iterator it =
			drgn_module_table_search_hashed(&prog->dbinfo->modules, key,
							hp);
		if (it.entry) {
			*ret = *it.entry;
			if (new_ret)
				*new_ret = false;
			return NULL;
		}
	}

	struct drgn_module *module = calloc(1, sizeof(*module));
	if (!module)
		return &drgn_enomem;
	module->start = module->end = UINT64_MAX;

	module->prog = prog;
	module->kind = key->kind;
	SWITCH_ENUM(key->kind,
	case DRGN_MODULE_MAIN:
		break;
	case DRGN_MODULE_SHARED_LIBRARY:
		module->shared_library.dynamic_address =
			key->shared_library.dynamic_address;
		break;
	case DRGN_MODULE_VDSO:
		module->vdso.dynamic_address = key->vdso.dynamic_address;
		break;
	case DRGN_MODULE_LINUX_KERNEL_LOADABLE:
		module->linux_kernel_loadable.base_address =
			key->linux_kernel_loadable.base_address;
		break;
	case DRGN_MODULE_EXTRA:
		module->extra.id = key->extra.id;
		break;
	)

	module->name = strdup(name);
	if (!module->name) {
		err = &drgn_enomem;
		goto err_module;
	}

	if (key->kind == DRGN_MODULE_MAIN) {
		prog->dbinfo->main_module = module;
	} else if (drgn_module_table_insert_searched(&prog->dbinfo->modules,
						     &module, hp, NULL) < 0) {
		err = &drgn_enomem;
		goto err_name;
	}

	drgn_module_section_address_map_init(&module->section_addresses);

	SWITCH_ENUM(module->kind,
	case DRGN_MODULE_MAIN:
		drgn_log_debug(prog, "created main module %s\n", module->name);
		break;
	case DRGN_MODULE_SHARED_LIBRARY:
		drgn_log_debug(prog,
			       "created shared library module %s@0x%" PRIx64 "\n",
			       module->name,
			       module->shared_library.dynamic_address);
		break;
	case DRGN_MODULE_VDSO:
		drgn_log_debug(prog,
			       "created vDSO module %s@0x%" PRIx64 "\n",
			       module->name, module->vdso.dynamic_address);
		break;
	case DRGN_MODULE_LINUX_KERNEL_LOADABLE:
		drgn_log_debug(prog,
			       "created Linux kernel loadable module %s@0x%" PRIx64 "\n",
			       module->name,
			       module->linux_kernel_loadable.base_address);
		break;
	case DRGN_MODULE_EXTRA:
		drgn_log_debug(prog,
			       "created extra module %s 0x%" PRIx64 "\n",
			       module->name, module->extra.id);
		break;
	)

	*ret = module;
	if (new_ret)
		*new_ret = true;
	return NULL;

err_name:
	free(module->name);
err_module:
	free(module);
	return err;
}

LIBDRGN_PUBLIC
struct drgn_error *drgn_module_find_or_create_main(struct drgn_program *prog,
						   const char *name,
						   struct drgn_module **ret,
						   bool *new_ret)
{
	struct drgn_module_key key = { .kind = DRGN_MODULE_MAIN };
	return drgn_module_find_or_create(prog, &key, name, ret, new_ret);
}

LIBDRGN_PUBLIC struct drgn_error *
drgn_module_find_or_create_shared_library(struct drgn_program *prog,
					  const char *name,
					  uint64_t dynamic_address,
					  struct drgn_module **ret,
					  bool *new_ret)
{
	const struct drgn_module_key key = {
		.kind = DRGN_MODULE_SHARED_LIBRARY,
		.shared_library.name = name,
		.shared_library.dynamic_address = dynamic_address,
	};
	return drgn_module_find_or_create(prog, &key, name, ret, new_ret);
}

LIBDRGN_PUBLIC
struct drgn_error *drgn_module_find_or_create_vdso(struct drgn_program *prog,
						   const char *name,
						   uint64_t dynamic_address,
						   struct drgn_module **ret,
						   bool *new_ret)
{
	const struct drgn_module_key key = {
		.kind = DRGN_MODULE_VDSO,
		.vdso.name = name,
		.vdso.dynamic_address = dynamic_address,
	};
	return drgn_module_find_or_create(prog, &key, name, ret, new_ret);
}

LIBDRGN_PUBLIC
struct drgn_error *drgn_module_find_or_create_extra(struct drgn_program *prog,
						    const char *name,
						    uint64_t id,
						    struct drgn_module **ret,
						    bool *new_ret)
{
	const struct drgn_module_key key = {
		.kind = DRGN_MODULE_EXTRA,
		.extra.name = name,
		.extra.id = id,
	};
	return drgn_module_find_or_create(prog, &key, name, ret, new_ret);
}

__attribute__((__unused__)) // TODO
static void drgn_module_destroy(struct drgn_module *module)
{
	drgn_module_free_section_addresses(module);
	drgn_module_section_address_map_deinit(&module->section_addresses);
	drgn_module_orc_info_deinit(module);
	drgn_module_dwarf_info_deinit(module);
	drgn_elf_file_destroy(module->gnu_debugaltlink_file);
	if (module->debug_file != module->loaded_file)
		drgn_elf_file_destroy(module->debug_file);
	drgn_elf_file_destroy(module->loaded_file);
	free(module->build_id_str);
	free(module->build_id);
	free(module->name);
	free(module);
}

LIBDRGN_PUBLIC void drgn_module_delete(struct drgn_module *module)
{
	// TODO
}

LIBDRGN_PUBLIC
struct drgn_program *drgn_module_program(const struct drgn_module *module)
{
	return module->prog;
}

LIBDRGN_PUBLIC
struct drgn_module_key drgn_module_key(const struct drgn_module *module)
{
	if (module->kind == DRGN_MODULE_MAIN) {
		struct drgn_module_key key;
		key.kind = DRGN_MODULE_MAIN;
		return key;
	}
	return drgn_module_entry_key((struct drgn_module * const *)&module);
}

LIBDRGN_PUBLIC
enum drgn_module_kind drgn_module_kind(const struct drgn_module *module)
{
	return module->kind;
}

LIBDRGN_PUBLIC const char *drgn_module_name(const struct drgn_module *module)
{
	return module->name;
}

LIBDRGN_PUBLIC bool drgn_module_address_range(const struct drgn_module *module,
					      uint64_t *start_ret,
					      uint64_t *end_ret)
{
	if (module->start == UINT64_MAX)
		return false;
	*start_ret = module->start;
	*end_ret = module->end;
	return true;
}

LIBDRGN_PUBLIC struct drgn_error *
drgn_module_set_address_range(struct drgn_module *module, uint64_t start,
			      uint64_t end)
{
	if (start >= end && start != 0) {
		return drgn_error_create(DRGN_ERROR_INVALID_ARGUMENT,
					 "invalid module address range");
	}
	// TODO: allow changing?
	if (module->start != UINT64_MAX) {
		return drgn_error_create(DRGN_ERROR_INVALID_ARGUMENT,
					 "module address range is already set");
	}
	module->start = start;
	module->end = end;
	if (start < end) {
		// TODO: check for overlap?
		drgn_module_address_tree_insert(&module->prog->dbinfo->modules_by_address,
						module, NULL);
	}
	return NULL;
}

LIBDRGN_PUBLIC
const char *drgn_module_build_id(const struct drgn_module *module,
				 const void **raw_ret, size_t *raw_len_ret)
{
	if (raw_ret)
		*raw_ret = module->build_id;
	if (raw_len_ret)
		*raw_len_ret = module->build_id_len;
	return module->build_id_str;
}

LIBDRGN_PUBLIC
struct drgn_error *drgn_module_set_build_id(struct drgn_module *module,
					    const void *build_id,
					    size_t build_id_len)
{
	if (build_id_len == 0) {
		return drgn_error_create(DRGN_ERROR_INVALID_ARGUMENT,
					 "build ID cannot be empty");
	}
	// TODO: allow changing? allow unsetting?
	if (module->build_id_len > 0) {
		return drgn_error_create(DRGN_ERROR_INVALID_ARGUMENT,
					 "build ID is already set");
	}
	module->build_id = memdup(build_id, build_id_len);
	if (!module->build_id)
		return &drgn_enomem;
	module->build_id_str = ahexlify(build_id, build_id_len);
	if (!module->build_id_str) {
		free(module->build_id);
		module->build_id = NULL;
		return &drgn_enomem;
	}
	module->build_id_len = build_id_len;
	return NULL;
}

LIBDRGN_PUBLIC
const char *drgn_module_loaded_file_path(const struct drgn_module *module)
{
	return module->loaded_file ? module->loaded_file->path : NULL;
}

LIBDRGN_PUBLIC
const char *drgn_module_debug_file_path(const struct drgn_module *module)
{
	return module->debug_file ? module->debug_file->path : NULL;
}

LIBDRGN_PUBLIC const char *
drgn_module_gnu_debugaltlink_file_path(const struct drgn_module *module)
{
	return module->gnu_debugaltlink_file ?
	       module->gnu_debugaltlink_file->path : NULL;
}

bool drgn_module_set_section_address(struct drgn_module *module, const char *name,
				     uint64_t address)
{
	struct hash_pair hp =
		drgn_module_section_address_map_hash((char **)&name);
	struct drgn_module_section_address_map_iterator it =
		drgn_module_section_address_map_search_hashed(&module->section_addresses,
							      (char **)&name,
							      hp);
	if (it.entry) {
		it.entry->value = address;
		return true;
	}
	struct drgn_module_section_address_map_entry entry = {
		.key = strdup(name),
		.value = address,
	};
	if (!entry.key)
		return false;
	if (drgn_module_section_address_map_insert_searched(&module->section_addresses,
							    &entry, hp,
							    NULL) < 0) {
		free(entry.key);
		return false;
	}
	return true;
}

bool drgn_module_try_files_done(struct drgn_module_try_files_state *state)
{
	return !state->want_loaded && !state->want_debug;
}

static void drgn_module_try_files_log(struct drgn_module *module,
				      struct drgn_module_try_files_state *state,
				      const char *how)
{
	if (module->trying_gnu_debugaltlink) {
		drgn_log_info(module->prog,
			      "%s gnu_debugaltlink file with build ID %s\n",
			      how,
			      module->trying_gnu_debugaltlink->build_id_str);
	} else {
		drgn_log_info(module->prog,
			      "%s %s%s%s file%s for module %s with %s%s\n", how,
			      state->want_loaded ? "loaded" : "",
			      state->want_loaded && state->want_debug
			      ? " and " : "",
			      state->want_debug ? "debug" : "",
			      state->want_loaded && state->want_debug
			      ? "s" : "",
			      module->name,
			      module->build_id_str
			      ? "build ID " : "no build ID",
			      module->build_id_str ? module->build_id_str : "");
	}
}

// Get the build ID to use for trying module files. This is the
// .gnu_debugaltlink build ID if we're currently trying to find the
// .gnu_debugaltlink file and the module build ID otherwise.
static const char *
drgn_module_try_files_build_id(const struct drgn_module *module,
			       const void **raw_ret, size_t *raw_len_ret)
{
	if (module->trying_gnu_debugaltlink) {
		if (raw_ret)
			*raw_ret = module->trying_gnu_debugaltlink->build_id;
		if (raw_len_ret)
			*raw_len_ret = module->trying_gnu_debugaltlink->build_id_len;
		return module->trying_gnu_debugaltlink->build_id_str;
	} else {
		return drgn_module_build_id(module, raw_ret, raw_len_ret);
	}
}

static struct drgn_error *
drgn_module_find_gnu_debugaltlink_file(struct drgn_module *module,
				       struct drgn_module_try_files_state *state,
				       struct drgn_elf_file *file,
				       struct drgn_elf_file **ret)
{
	struct drgn_error *err;
	struct drgn_program *prog = module->prog;

	*ret = NULL;

	Elf_Data *data;
	err = read_elf_section(file->scns[DRGN_SCN_GNU_DEBUGALTLINK], &data);
	if (err) {
		if (drgn_error_should_log(err)) {
			drgn_error_log_debug(prog, err, "%s: ", file->path);
			drgn_error_destroy(err);
			err = NULL;
		}
		return err;
	}

	const char *debugaltlink = data->d_buf;
	const char *nul = memchr(debugaltlink, 0, data->d_size);
	if (!nul || nul + 1 == debugaltlink + data->d_size) {
		drgn_log_notice(prog, "%s: couldn't parse .gnu_debugaltlink\n",
				file->path);
		return NULL;
	}

	struct drgn_module_trying_gnu_debugaltlink trying = {
		.debug_file = file,
		.debugaltlink_path = debugaltlink,
		.build_id = nul + 1,
		.build_id_len = debugaltlink + data->d_size - (nul + 1),
	};
	trying.build_id_str = ahexlify(trying.build_id, trying.build_id_len);
	if (!trying.build_id_str)
		return &drgn_enomem;
	drgn_log_debug(prog, "%s has gnu_debugaltlink %s build ID %s\n", file->path,
		       debugaltlink, trying.build_id_str);
	module->trying_gnu_debugaltlink = &trying;
	struct drgn_module_try_files_args args = {
		.want_loaded = false,
		.want_debug = true,
		.debug_directories = state->debug_directories, // TODO: don't do
							       // this if they
							       // were
							       // defaulted?
		.arg = state->arg,
		// TODO: Won't be called, but copy it for consistency?
		.need_gnu_debugaltlink_file = state->need_gnu_debugaltlink_file,
	};
	if (state->need_gnu_debugaltlink_file) {
		err = state->need_gnu_debugaltlink_file(module, &args,
							trying.debug_file->path,
							trying.debugaltlink_path,
							trying.build_id,
							trying.build_id_len,
							trying.build_id_str);
	} else {
		err = drgn_module_try_default_files(module, &args);
	}
	module->trying_gnu_debugaltlink = NULL;
	free(trying.build_id_str);
	if (err) {
		drgn_elf_file_destroy(trying.found);
		return err;
	}
	*ret = trying.found;
	return NULL;
}

// TODO: explain file ownership
static struct drgn_error *
drgn_module_maybe_use_elf_file(struct drgn_module *module,
			       struct drgn_module_try_files_state *state,
			       struct drgn_elf_file *file)
{
	struct drgn_error *err;
	struct drgn_program *prog = module->prog;

	// We shouldn't be here if we already have everything we need.
	assert(state->want_loaded || state->want_debug);
	const bool use_loaded = state->want_loaded && file->is_loadable;
	const bool has_dwarf = drgn_elf_file_has_dwarf(file);
	bool use_debug = state->want_debug && has_dwarf;
	if (!use_loaded && !use_debug) {
		if (file->is_loadable) {
			drgn_log_debug(prog,
				       "loadable, but don't want loaded file; ignoring\n");
		} else if (has_dwarf) {
			drgn_log_debug(prog,
				       "has debug info, but don't want debug info; ignoring\n");
		} else {
			drgn_log_debug(prog,
				       "not loadable and no debug info; ignoring\n");
		}
		err = NULL;
		goto unused;
	}

	// TODO:
	// - Copy section addresses
	// - Get bias
#if 0
	if ((prog->flags & DRGN_PROGRAM_IS_LINUX_KERNEL) &&
	    module->kind == DRGN_MODULE_MAIN) {
		if (use_loaded)
			module->loaded_file_bias = prog->vmcoreinfo.kaslr_offset;
		if (use_debug)
			module->debug_file_bias = prog->vmcoreinfo.kaslr_offset;
	}
#endif

	if (use_debug) {
		file->dwarf = dwarf_begin_elf(file->elf, DWARF_C_READ, NULL);
		if (!file->dwarf) {
			drgn_log_debug(prog, "%s: %s\n", file->path,
				       dwarf_errmsg(-1));
			use_debug = false;
		}
	}
	if (use_debug) {
		// If the file has .gnu_debugaltlink, find it before we use the
		// file. TODO
		if (module->trying_gnu_debugaltlink) {
			drgn_log_info(prog, "using gnu_debugaltlink file %s\n",
				      file->path);
			module->trying_gnu_debugaltlink->found = file;
			state->want_debug = false;
			return NULL;
		} else if (file->scns[DRGN_SCN_GNU_DEBUGALTLINK]) {
			struct drgn_elf_file *gnu_debugaltlink_file;
			err = drgn_module_find_gnu_debugaltlink_file(module,
								     state,
								     file,
								     &gnu_debugaltlink_file);
			if (err)
				goto unused;
			if (gnu_debugaltlink_file) {
				dwarf_setalt(file->dwarf,
					     gnu_debugaltlink_file->dwarf);
				module->gnu_debugaltlink_file =
					gnu_debugaltlink_file;
			} else {
				drgn_log_debug(prog,
					       "couldn't find gnu_debugaltlink file; ignoring debug info\n");
				use_debug = false;
				dwarf_end(file->dwarf);
				file->dwarf = NULL;
			}
		}
	}
	if (!use_loaded && !use_debug) {
		err = NULL;
		goto unused;
	}

	// TODO: set address range (UNLESS SOMEONE ALREADY DID)
	// TODO: set build ID (UNLESS SOMEONE ALREADY DID)
	// TODO: queue to be indexed
	if (use_loaded) {
		module->loaded_file = file;
		state->want_loaded = false;
	}
	if (use_debug) {
		module->debug_file = file;
		state->want_debug = false;
		module->pending_indexing_next =
			prog->dbinfo->modules_pending_indexing;
		if (prog->dbinfo->modules_pending_indexing) {
			prog->dbinfo->modules_pending_indexing->pending_indexing_prev
				= module;
		}
		prog->dbinfo->modules_pending_indexing = module;
	}
	if (use_loaded && use_debug) {
		drgn_log_info(prog, "using loadable file with debug info %s\n",
			      file->path);
	} else if (use_loaded) {
		drgn_log_info(prog, "using loadable file %s\n", file->path);
	} else if (use_debug) {
		drgn_log_info(prog, "using debug info file %s\n", file->path);
	}
	if (!prog->has_platform) {
		drgn_log_info(prog, "setting program platform from %s\n",
			      file->path);
		drgn_program_set_platform(prog, &file->platform);
	}
	return NULL;

unused:
	// TODO: explain
	if (file != module->loaded_file && file != module->debug_file)
		drgn_elf_file_destroy(file);
	return err;
}

struct drgn_error *
drgn_module_try_file_internal(struct drgn_module *module,
			      struct drgn_module_try_files_state *state,
			      const char *path, int fd, bool check_build_id,
			      const uint32_t *expected_crc)
{
	struct drgn_error *err;
	struct drgn_program *prog = module->prog;

	if (fd >= 0) {
		drgn_log_debug(prog, "trying %s with fd %d\n", path, fd);
	} else {
		fd = open(path, O_RDONLY);
		if (fd < 0) {
			drgn_log_debug(prog, "%s: %m\n", path);
			return NULL;
		}
		drgn_log_debug(prog, "trying %s\n", path);
	}

	Elf *elf = dwelf_elf_begin(fd);
	if (!elf) {
		drgn_log_debug(prog, "%s: %s\n", path, elf_errmsg(-1));
		err = NULL;
		goto out_fd;
	}
	if (elf_kind(elf) != ELF_K_ELF) {
		drgn_log_debug(prog, "%s: not an ELF file\n", path);
		err = NULL;
		goto out_elf;
	}

	if (check_build_id) { // TODO: what if no build ID?
		const void *build_id;
		size_t build_id_len;
		if (drgn_module_try_files_build_id(module, &build_id,
						   &build_id_len)) {
			const void *elf_build_id;
			ssize_t elf_build_id_len =
				dwelf_elf_gnu_build_id(elf, &elf_build_id);
			if (elf_build_id_len < 0) {
				drgn_log_debug(prog, "%s: %s\n", path,
					       elf_errmsg(-1));
				err = NULL;
				goto out_elf;
			}
			if (elf_build_id_len != build_id_len ||
			    memcmp(elf_build_id, build_id, build_id_len) != 0) {
				if (elf_build_id_len == 0) {
					drgn_log_debug(prog,
						       "file is missing build ID\n");
				} else {
					drgn_log_debug(prog,
						       "build ID does not match\n");
				}
				err = NULL;
				goto out_elf;
			}
			drgn_log_debug(prog, "build ID matches\n");
		}
	}
	if (expected_crc) {
		size_t size;
		const void *rawfile = elf_rawfile(elf, &size);
		if (!rawfile) {
			drgn_log_debug(prog, "%s: %s\n", path, elf_errmsg(-1));
			err = NULL;
			goto out_elf;
		}
		uint32_t crc = ~crc32_update(-1, rawfile, size);
		if (crc != *expected_crc) {
			drgn_log_debug(prog,
				       "CRC 0x%08" PRIx32 " does not match\n",
				       crc);
			err = NULL;
			goto out_elf;
		}
		drgn_log_debug(prog, "CRC matches\n");
	}

	struct drgn_elf_file *file;
	err = drgn_elf_file_create(module, path, fd, NULL, elf, &file);
	if (err) {
		if (drgn_error_should_log(err)) {
			drgn_error_log_debug(prog, err, NULL);
			drgn_error_destroy(err);
			err = NULL;
		}
		goto out_elf;
	}
	return drgn_module_maybe_use_elf_file(module, state, file);

out_elf:
	elf_end(elf);
out_fd:
	close(fd);
	return err;
}

// Arbitrary limit on the number of bytes we'll allocate and read from the
// program's memory at once when finding modules/debug info.
static const uint64_t MAX_MEMORY_READ_FOR_DEBUG_INFO = UINT64_C(1048576);

static struct drgn_error *
drgn_module_try_vdso_in_core(struct drgn_module *module,
			     struct drgn_module_try_files_state *state)
{
	struct drgn_error *err;
	struct drgn_program *prog = module->prog;

	// The Linux kernel has included the entire vDSO in core dumps since
	// Linux kernel commit f47aef55d9a1 ("[PATCH] i386 vDSO: use
	// VM_ALWAYSDUMP") (in v2.6.20). Try to read it from program memory.

	// The vDSO is always stripped.
	if (!state->want_loaded)
		return NULL;

	uint64_t start, end;
	if (!drgn_module_address_range(module, &start, &end)) {
		drgn_log_debug(prog,
			       "vDSO address range is not known; "
			       "can't read from program\n");
		return NULL;
	}
	if (start >= end) {
		drgn_log_debug(prog,
			       "vDSO address range is empty; "
			       "can't read from program\n");
		return NULL;
	}
	uint64_t size = end - start;
	if (size > MAX_MEMORY_READ_FOR_DEBUG_INFO) {
		drgn_log_debug(prog,
			       "vDSO is unreasonably large (%" PRIu64 " bytes); "
			       "not reading from program\n",
			       size);
		return NULL;
	}

	char *image = malloc(size);
	if (!image)
		return &drgn_enomem;
	err = drgn_program_read_memory(prog, image, start, size, false);
	if (err) {
		if (drgn_error_should_log(err)) {
			drgn_error_log_debug(prog, err, "couldn't read vDSO: ");
			drgn_error_destroy(err);
			err = NULL;
		}
		goto out_image;
	}

	Elf *elf = elf_memory(image, size);
	if (!elf) {
		drgn_log_debug(prog, "couldn't read vDSO: %s\n", elf_errmsg(-1));
		err = NULL;
		goto out_image;
	}
	struct drgn_elf_file *file;
	err = drgn_elf_file_create(module, "", -1, image, elf, &file);
	if (err) {
		if (drgn_error_should_log(err)) {
			drgn_error_log_debug(prog, err, NULL);
			drgn_error_destroy(err);
			err = NULL;
		}
		goto out_elf;
	}
	// image is owned by the drgn_elf_file now.

	drgn_log_debug(prog, "trying vDSO in core\n");
	return drgn_module_maybe_use_elf_file(module, state, file);

out_elf:
	elf_end(elf);
out_image:
	free(image);
	return err;
}

static struct drgn_error *
drgn_module_try_proc_files(struct drgn_module *module,
			   struct drgn_module_try_files_state *state,
			   bool *tried)
{
	struct drgn_error *err;
	struct drgn_program *prog = module->prog;

	*tried = false;

	int fd;
#define EXE_FORMAT "/proc/%ld/exe"
#define MAP_FILES_FORMAT "/proc/%ld/map_files"
	char link_path[max_iconst(sizeof(EXE_FORMAT), sizeof(MAP_FILES_FORMAT))
		       - sizeof("%ld")
		       + max_decimal_length(long)
		       + 1];
	if (module->kind == DRGN_MODULE_MAIN) {
		snprintf(link_path, sizeof(link_path), EXE_FORMAT,
			 (long)prog->pid);
#undef EXE_FORMAT
		fd = open(link_path, O_RDONLY);
		if (fd < 0) {
			drgn_log_debug(prog, "%s: %m\n", link_path);
			return NULL;
		}
		drgn_log_debug(prog, "found %s\n", link_path);
	} else if (module->kind == DRGN_MODULE_SHARED_LIBRARY) {
		snprintf(link_path, sizeof(link_path), MAP_FILES_FORMAT,
			 (long)prog->pid);
#undef MAP_FILES_FORMAT
		DIR *dir = opendir(link_path);
		if (!dir) {
			if (errno != ENOENT) {
				return drgn_error_create_os("opendir", errno,
							    link_path);
			}
			drgn_log_debug(prog, "%s: %m\n", link_path);
			return NULL;
		}
		// TODO: cache this
		struct dirent *ent;
		while ((errno = 0, ent = readdir(dir))) {
			uint64_t start, end;
			if (sscanf(ent->d_name, "%" PRIx64 "-%" PRIx64, &start,
				   &end) != 2)
				continue;
			if (start <= module->shared_library.dynamic_address &&
			    module->shared_library.dynamic_address < end)
				break;
		}
		if (!ent) {
			if (errno) {
				err = drgn_error_create_os("readdir", errno,
							   link_path);
			} else {
				drgn_log_debug(prog,
					       "didn't find entry in %s containing dynamic section 0x%" PRIx64 "\n",
					       link_path,
					       module->shared_library.dynamic_address);
				err = NULL;
			}
			closedir(dir);
			return err;
		}
		drgn_log_debug(prog,
			       "found %s/%s containing dynamic section 0x%" PRIx64 "\n",
			       link_path, ent->d_name,
			       module->shared_library.dynamic_address);
		// TODO: log when running as root would help?
		fd = openat(dirfd(dir), ent->d_name, O_RDONLY);
		if (fd < 0) {
			drgn_log_debug(prog, "%s/%s: %m\n", link_path,
				       ent->d_name);
		}
		closedir(dir);
		if (fd < 0)
			return NULL;
	} else {
		return NULL;
	}

#define FORMAT "/proc/self/fd/%d"
	char fd_path[sizeof(FORMAT)
		     - sizeof("%d")
		     + max_decimal_length(int)
		     + 1];
	snprintf(fd_path, sizeof(fd_path), FORMAT, fd);
#undef FORMAT
	char *real_path = malloc(PATH_MAX);
	if (!real_path) {
		err = &drgn_enomem;
		goto out_fd;
	}
	ssize_t r = readlink(fd_path, real_path, PATH_MAX);
	if (r >= PATH_MAX || (r < 0 && errno == ENAMETOOLONG)) {
		drgn_log_debug(prog, "real path is too long\n");
		free(real_path);
		real_path = NULL;
	} else if (r < 0) {
		err = drgn_error_create_os("readlink", errno, fd_path);
		goto out_real_path;
	}
	real_path[r] = '\0';
	*tried = true;
	err = drgn_module_try_file_internal(module, state,
					    real_path ? real_path : link_path,
					    fd, false, NULL);
	fd = -1;
out_real_path:
	free(real_path);
out_fd:
	if (fd >= 0)
		close(fd);
	return err;
}

// TODO: debuginfod cache?
static struct drgn_error *
drgn_module_try_files_by_build_id(struct drgn_module *module,
				  struct drgn_module_try_files_state *state)
{
	struct drgn_error *err;

	size_t build_id_len;
	const char *build_id_str =
		drgn_module_try_files_build_id(module, NULL, &build_id_len);
	// We need at least 2 bytes (4 hex characters) to build the paths.
	if (build_id_len < 2)
		return NULL;

	struct string_builder sb = STRING_BUILDER_INIT;
	for (size_t i = 0; state->debug_directories[i]; i++) {
		if (state->debug_directories[i][0] != '/')
			continue;
		char *path;
		if (!string_builder_appendf(&sb, "%s/.build-id/%c%c/%s.debug",
					    state->debug_directories[i],
					    build_id_str[0], build_id_str[1],
					    &build_id_str[2]) ||
		    !(path = string_builder_null_terminate(&sb))) {
			err = &drgn_enomem;
			goto out;
		}
		// We trust the build ID encoded in the path and don't check it
		// again.
		if (state->want_debug) {
			err = drgn_module_try_file_internal(module, state, path,
							    -1, false, NULL);
			if (err || drgn_module_try_files_done(state))
				goto out;
		}
		if (state->want_loaded) {
			// Remove the ".debug" extension.
			path[sb.len - sizeof(".debug") + 1] = '\0';
			err = drgn_module_try_file_internal(module, state, path,
							    -1, false, NULL);
			if (err || drgn_module_try_files_done(state))
				goto out;
		}
		sb.len = 0;
	}
	err = NULL;
out:
	free(sb.str);
	return err;
}

static struct drgn_error *
drgn_module_try_files_by_gnu_debuglink(struct drgn_module *module,
				       struct drgn_module_try_files_state *state)
{
	struct drgn_error *err;
	struct drgn_program *prog = module->prog;

	struct drgn_elf_file *file = module->loaded_file;
	if (!file || !file->scns[DRGN_SCN_GNU_DEBUGLINK])
		return NULL;
	Elf_Data *data;
	err = read_elf_section(file->scns[DRGN_SCN_GNU_DEBUGLINK], &data);
	if (err) {
		if (drgn_error_should_log(err)) {
			drgn_error_log_debug(prog, err,
					     "%s: couldn't read .gnu_debuglink: ",
					     file->path);
			drgn_error_destroy(err);
			err = NULL;
		}
		return err;
	}

	struct drgn_elf_file_section_buffer buffer;
	drgn_elf_file_section_buffer_init(&buffer, file,
					  file->scns[DRGN_SCN_GNU_DEBUGLINK],
					  data);
	const char *debuglink;
	size_t debuglink_len;
	uint32_t crc;
	if ((err = binary_buffer_next_string(&buffer.bb, &debuglink,
					     &debuglink_len)) ||
	    // Align up to 4-byte boundary.
	    (err = binary_buffer_skip(&buffer.bb, -(debuglink_len + 1) & 3)) ||
	    (err = binary_buffer_next_u32(&buffer.bb, &crc))) {
		if (drgn_error_should_log(err)) {
			drgn_error_log_debug(prog, err, "%s: ", file->path);
			drgn_error_destroy(err);
			err = NULL;
		}
		return err;
	}
	drgn_log_debug(prog, "%s has debuglink %s crc 0x%08" PRIx32 "\n",
		       file->path, debuglink, crc);

	struct string_builder sb = STRING_BUILDER_INIT;
	if (debuglink[0] == '/') {
		// debuglink is absolute. Try it directly.
		err = drgn_module_try_file_internal(module, state, debuglink,
						    -1, false, &crc);
		if (err || drgn_module_try_files_done(state))
			goto out;
	} else if (file->path[0] && debuglink[0]) {
		// debuglink is relative. Try it in the debug directories.
		const char *slash = strrchr(file->path, '/');
		size_t dirslash_len = slash ? slash - file->path + 1 : 0;
		for (size_t i = 0; state->debug_directories[i]; i++) {
			const char *debug_dir = state->debug_directories[i];
			// If debug_dir is empty, then try:
			// $(dirname $path)/$debuglink
			// If debug_dir is relative, then try:
			// $(dirname $path)/$debug_dir/$debuglink
			// If debug_dir is absolute, then try:
			// $debug_dir/$(dirname $path)/$debuglink
			if (debug_dir[0] == '/') {
				// TODO: should call realpath at some point?
				if (file->path[0] != '/')
					continue;
				if (!string_builder_append(&sb, debug_dir))
					goto enomem;
			}
			char *path;
			if (!string_builder_appendn(&sb, file->path,
						    dirslash_len) ||
			    (debug_dir[0] && debug_dir[0] != '/' &&
			     !string_builder_appendf(&sb, "%s/", debug_dir)) ||
			    !string_builder_appendn(&sb, debuglink,
						    debuglink_len) ||
			    !(path = string_builder_null_terminate(&sb)))
				goto enomem;
			err = drgn_module_try_file_internal(module, state, path,
							    -1, false, &crc);
			if (err || drgn_module_try_files_done(state))
				goto out;
			sb.len = 0;
		}
	}
	err = NULL;

out:
	free(sb.str);
	return err;

enomem:
	err = &drgn_enomem;
	goto out;
}

static struct drgn_error *
drgn_module_try_local_files_gnu_debugaltlink(struct drgn_module *module,
					     struct drgn_module_try_files_state *state)
{
	struct drgn_error *err;
	const struct drgn_module_trying_gnu_debugaltlink *trying =
		module->trying_gnu_debugaltlink;

	struct string_builder sb = STRING_BUILDER_INIT;
	const char *slash;
	if (trying->debugaltlink_path[0] == '/' ||
	    !(slash = strrchr(trying->debug_file->path, '/'))) {
		// debugaltlink is absolute, or the debug file doesn't have a
		// directory component and is therefore in the current working
		// directory. Try debugaltlink directly.
		err = drgn_module_try_file_internal(module, state,
						    trying->debugaltlink_path,
						    -1, true, NULL);
	} else {
		// Try $(dirname $path)/$debugaltlink.
		char *path;
		if (!string_builder_appendn(&sb, trying->debug_file->path,
					    slash + 1
					    - trying->debug_file->path) ||
		    !string_builder_append(&sb, trying->debugaltlink_path) ||
		    !(path = string_builder_null_terminate(&sb))) {
			err = &drgn_enomem;
			goto out;
		}
		err = drgn_module_try_file_internal(module, state, path, -1,
						    true, NULL);
	}
	if (err || drgn_module_try_files_done(state))
		goto out;

	// All of the Linux distributions that use gnu_debugaltlink that I'm
	// aware of (Debian, Fedora, SUSE, and their derivatives) put
	// gnu_debugaltlink files in a ".dwz" subdirectory under the debug
	// directory (e.g., "/usr/lib/debug/.dwz"). Try the path starting with
	// the ".dwz" directory under all of the configured debug directories.
	// This can help in a couple of cases:
	//
	// 1. When the gnu_debugaltlink path is absolute (which is the case on
	//    Debian and its derivatives as of Debian 12/Ubuntu 22.10) and the
	//    debug directory has been copied to a different path. See
	//    https://bugs.launchpad.net/ubuntu/+source/gdb/+bug/1818918.
	// 2. When the gnu_debugaltlink path is relative (which is the case on
	//    Fedora, SUSE, and their derivatives) and the debug file was found
	//    outside of the debug directory.
	const char *dwz = strstr(trying->debugaltlink_path, "/.dwz/");
	if (dwz) {
		for (size_t i = 0; state->debug_directories[i]; i++) {
			if (state->debug_directories[i][0] != '/')
				continue;
			// TODO: avoid retrying the same file?
#if 0
			if (strncmp(state->debug_directories[i],
				    trying->debugaltlink_path,
				    dwz - trying->debugaltlink_path) == 0)
				continue;
#endif
			sb.len = 0;
			char *path;
			if (!string_builder_append(&sb,
						   state->debug_directories[i]) ||
			    !string_builder_append(&sb, dwz) ||
			    !(path = string_builder_null_terminate(&sb))) {
				err = &drgn_enomem;
				goto out;
			}
			err = drgn_module_try_file_internal(module, state, path,
							    -1, true, NULL);
			if (err || drgn_module_try_files_done(state))
				goto out;
		}
	}
	err = NULL;
out:
	free(sb.str);
	return err;
}

static struct drgn_error *
drgn_module_try_local_files_internal(struct drgn_module *module,
				     struct drgn_module_try_files_state *state)
{
	struct drgn_error *err;
	struct drgn_program *prog = module->prog;

	drgn_module_try_files_log(module, state,
				  "checking standard paths for");

	if (module->trying_gnu_debugaltlink) {
		return drgn_module_try_local_files_gnu_debugaltlink(module,
								    state);
	}

	// If a previous attempt used a loadable file with debug info but didn't
	// want both, we might be able to reuse it.
	if (state->want_loaded && module->debug_file
	    && module->debug_file->is_loadable) {
		drgn_log_debug(prog,
			       "reusing loadable debug file %s as loaded file\n",
			       module->debug_file->path);
		err = drgn_module_maybe_use_elf_file(module, state,
						     module->debug_file);
		if (err || drgn_module_try_files_done(state))
			return err;
	}
	// ... and vice versa.
	if (state->want_debug && module->loaded_file
	    && drgn_elf_file_has_dwarf(module->loaded_file)) {
		drgn_log_debug(prog,
			       "reusing loaded file with debug info %s as debug file\n",
			       module->loaded_file->path);
		err = drgn_module_maybe_use_elf_file(module, state,
						     module->loaded_file);
		if (err || drgn_module_try_files_done(state))
			return err;
	}

	// First, try methods that are guaranteed to find the right file:
	// reading a vDSO from the core dump and opening a file via a magic
	// symlink in /proc.
	bool tried_proc_symlink = false;
	if (module->kind == DRGN_MODULE_VDSO) {
		err = drgn_module_try_vdso_in_core(module, state);
		if (err || drgn_module_try_files_done(state))
			return err;
	} else if ((module->prog->flags
		    & (DRGN_PROGRAM_IS_LINUX_KERNEL | DRGN_PROGRAM_IS_LIVE))
		   == DRGN_PROGRAM_IS_LIVE) {
		err = drgn_module_try_proc_files(module, state,
						 &tried_proc_symlink);
		if (err || drgn_module_try_files_done(state))
			return err;
	}

	// If we already have the build ID, try it now before wasting time with
	// the expected paths. If this is a Linux kernel loadable module, this
	// can save us from needing the depmod index. If not, it can still save
	// us from trying a file with the wrong build ID.
	const bool had_build_id = module->build_id_len > 0;
	if (had_build_id) {
		err = drgn_module_try_files_by_build_id(module, state);
		if (err || drgn_module_try_files_done(state))
			return err;
	}

	// Next, try opening things at their expected paths. If this is the
	// Linux kernel or a Linux kernel loadable module, try some well-known
	// paths.
	if (module->kind == DRGN_MODULE_MAIN &&
	    (module->prog->flags & DRGN_PROGRAM_IS_LINUX_KERNEL)) {
		err = drgn_module_try_vmlinux_files(module, state);
		if (err || drgn_module_try_files_done(state))
			return err;
	} else if (module->kind == DRGN_MODULE_LINUX_KERNEL_LOADABLE) {
		err = drgn_module_try_linux_kmod_files(module, state);
		if (err || drgn_module_try_files_done(state))
			return err;
	// Otherwise, if the module name looks like a path (i.e., it contains a
	// slash), try it. The vDSO is embedded in the kernel and isn't on disk,
	// so there's no point in trying it. Additionally, if we already tried a
	// /proc symlink, we already tried the file that the path is supposed to
	// refer to, so don't try again.
	} else if (module->kind != DRGN_MODULE_VDSO
		   && !tried_proc_symlink
		   && strchr(module->name, '/')) {
		err = drgn_module_try_file_internal(module, state, module->name,
						    -1, true, NULL);
		if (err || drgn_module_try_files_done(state))
			return err;
	}

	// If we didn't have the build ID before, we might have found the loaded
	// file and gotten a build ID from it. Try to find the debug file by
	// build ID now.
	if (!had_build_id) {
		err = drgn_module_try_files_by_build_id(module, state);
		if (err || drgn_module_try_files_done(state))
			return err;
	}

	// We might have a loaded file with a .gnu_debuglink. Try to find the
	// corresponding debug file.
	err = drgn_module_try_files_by_gnu_debuglink(module, state);
	if (err || drgn_module_try_files_done(state))
		return err;
	return NULL;
}

#ifdef WITH_DEBUGINFOD
#if _ELFUTILS_PREREQ(0, 179)
static int count_columns(const char *s, size_t n)
{
	int columns = 0;
	while (n > 0) {
		mbstate_t ps;
		memset(&ps, 0, sizeof(ps));
		do {
			wchar_t wc;
			size_t r = mbrtowc(&wc, s, n, &ps);
			if (r == (size_t)-1) // Invalid multibyte sequence.
				return -1;
			if (r == (size_t)-2) // Incomplete multibyte character.
				return -2;
			if (r == 0) // Null wide character.
				r = 1;

			int w = wcwidth(wc);
			if (w < 0) // Nonprintable wide character.
				return -3;
			s += r;
			n -= r;
			columns += w;
		} while (!mbsinit(&ps));
	}
	return columns;
}

static int truncate_columns(struct string_builder *sb, size_t start, size_t end,
			    int max_columns)
{
	int columns = 0;

	size_t truncate_len = start;
	int truncate_column = 0;
	mbstate_t truncate_ps;
	memset(&truncate_ps, 0, sizeof(truncate_ps));

	while (start < end) {
		mbstate_t ps;
		memset(&ps, 0, sizeof(ps));
		do {
			wchar_t wc;
			size_t r = mbrtowc(&wc, &sb->str[start], end - start,
					   &ps);
			if (r == (size_t)-1) // Invalid multibyte sequence.
				return -1;
			if (r == (size_t)-2) // Incomplete multibyte character.
				return -2;
			if (r == 0) // Null wide character.
				r = 1;

			int w = wcwidth(wc);
			if (w < 0) // Nonprintable wide character.
				return -3;

			if (w > max_columns - columns) {
				int dots = min(max_columns, 3);
				char reset[MB_LEN_MAX];
				size_t reset_len = 0;
				if (!mbsinit(&truncate_ps)) {
					reset_len = wcrtomb(reset, L'\0',
							    &truncate_ps) - 1;
				}
				size_t new_len = (truncate_len
						  + reset_len
						  + dots
						  + (sb->len - end));
				if (!string_builder_reserve(sb, new_len))
					return INT_MIN;
				memmove(&sb->str[truncate_len + reset_len + dots],
					&sb->str[end], sb->len - end);
				memset(&sb->str[truncate_len + reset_len], '.',
				       dots);
				memcpy(&sb->str[truncate_len], reset,
				       reset_len);
				sb->len = new_len;
				return truncate_column + dots;
			}

			start += r;
			columns += w;
			if (columns <= max_columns - 3) {
				truncate_len = start;
				truncate_column = columns;
				memcpy(&truncate_ps, &ps, sizeof(ps));
			}
		} while (!mbsinit(&ps));
	}
	return columns;
}

static void reset_shift_state(struct string_builder *sb, mbstate_t *ps)
{
	if (!mbsinit(ps))
		sb->len += wcrtomb(&sb->str[sb->len], L'\0', ps) - 1;
}

static bool write_unicode_progress_bar(struct string_builder *sb, int columns,
				       double ratio)
{
	size_t orig_len = sb->len;

	mbstate_t ps;
	memset(&ps, 0, sizeof(ps));

	// "Right one eighth block" character.
	size_t r = wcrtomb(&sb->str[sb->len], L'\u2595', &ps);
	if (r == (size_t)-1)
		return false;
	sb->len += r;

	// + 0.25 so that we round up if the piece would be at least 75% full.
	int eighths = columns * ratio * 8.0 + 0.25;
	int blocks = eighths / 8;
	int i;
	for (i = 0; i < blocks; i++) {
		// "Full block" character.
		r = wcrtomb(&sb->str[sb->len], L'\u2588', &ps);
		if (r == (size_t)-1)
			goto undo;
		sb->len += r;
	}
	// "Left one eighth block" through "left seven eighths block"
	// characters.
	static const wchar_t eighths_blocks[7] =
		L"\u258f\u258e\u258d\u258c\u258b\u258a\u2589";
	if (eighths % 8 != 0) {
		r = wcrtomb(&sb->str[sb->len], eighths_blocks[eighths % 8 - 1],
			    &ps);
		if (r == (size_t)-1)
			goto undo;
		sb->len += r;
		i++;
	}

	for (; i < columns; i++) {
		r = wcrtomb(&sb->str[sb->len], L' ', &ps);
		if (r == (size_t)-1)
			goto undo;
		sb->len += r;
	}

	// "Left one eighth block" character.
	r = wcrtomb(&sb->str[sb->len], L'\u258f', &ps);
	if (r == (size_t)-1)
		goto undo;
	sb->len += r;

	reset_shift_state(sb, &ps);
	return true;

undo:
	sb->len = orig_len;
	return false;
}

static void write_ascii_progress_bar(struct string_builder *sb, int columns,
				     double ratio)
{
	sb->str[sb->len++] = '[';
	// + 0.25 so that we round up if the block would be at least 75% full.
	int blocks = columns * ratio + 0.25;
	memset(&sb->str[sb->len], '#', blocks);
	sb->len += blocks;
	memset(&sb->str[sb->len], ' ', columns - blocks);
	sb->len += columns - blocks;
	sb->str[sb->len++] = ']';
}

static bool write_unicode_spinner(struct string_builder *sb, int pos)
{
	static const wchar_t spinner[] = {
		L'\u2596', // Quadrant lower left
		L'\u2598', // Quadrant upper left
		L'\u259d', // Quadrant upper right
		L'\u2597', // Quadrant lower right
	};
	mbstate_t ps;
	memset(&ps, 0, sizeof(ps));
	size_t r = wcrtomb(&sb->str[sb->len],
			   spinner[pos % array_size(spinner)], &ps);
	if (r == (size_t)-1)
		return false;
	sb->len += r;

	reset_shift_state(sb, &ps);
	return true;
}

static void write_ascii_spinner(struct string_builder *sb, int pos)
{
	static const char spinner[] = { '|', '/', '-', '\\' };
	sb->str[sb->len++] = spinner[pos % array_size(spinner)];
}

static void drgn_log_debuginfod_progress(struct drgn_program *prog, long a,
					 long b, int result)
{
	const bool done = b == 0;
	const bool error = result < 0;

	if (!prog->dbinfo->debuginfod_downloaded) {
		if (!error) {
			drgn_log_debug(prog, "found %s%s in debuginfod cache\n",
				       prog->dbinfo->debuginfod_current_name,
				       prog->dbinfo->debuginfod_current_type);
		} else if (result == -ENOSYS) {
			if (!prog->dbinfo->logged_no_debuginfod) {
				drgn_log_debug(prog,
					       "no debuginfod servers configured; "
					       "try setting DEBUGINFOD_URLS\n");
				prog->dbinfo->logged_no_debuginfod = true;
			}
		} else {
			errno = -result;
			drgn_log_debug(prog,
				       "couldn't download %s%s from debuginfod: %m\n",
				       prog->dbinfo->debuginfod_current_name,
				       prog->dbinfo->debuginfod_current_type);
		}
		return;
	}

	if (!drgn_should_log(prog, DRGN_LOG_LEVEL_NOTICE))
		return;

	struct winsize winsize;
	const bool tty = ioctl(prog->log_file
			       ? fileno(prog->log_file) : prog->log_fd,
			       TIOCGWINSZ, &winsize) == 0;

	// We only do the progress animation if we would have at least one
	// column for a progress bar. Using the calculation for bar_columns
	// below:
	//
	//    ws_col - (floor(ws_col / 2) - 10) - 2 - 4 >= 1
	// => ws_col - floor(ws_col / 2) >= 17
	// => ceil(ws_col / 2) >= 17
	// => ws_col >= 33
	bool animate = tty && winsize.ws_col >= 33;
	const bool orig_animate = animate;

	struct string_builder sb = STRING_BUILDER_INIT;

	if (animate && !string_builder_appendc(&sb, '\r'))
		goto out;

	int fill_columns = 0;
	int bar_columns = 0;
	if (animate) {
		if (done) {
			// We need to erase anything left in the line with
			// spaces.
			fill_columns = winsize.ws_col;
		} else if (b > 0) {
			// Use half of the line plus a bit so that it doesn't
			// get too short in small terminals for the name and
			// download size.
			fill_columns = winsize.ws_col / 2 + 10;
			// Use the rest for the progress bar.
			bar_columns = (winsize.ws_col - fill_columns
				       - 2 // Ends of progress bar
				       - 4 // " XX%"
				      );
		} else {
			// Use the whole line minus the spinner for the name and
			// download size.
			fill_columns = winsize.ws_col - 1;
		}
	}

	if (!string_builder_append(&sb,
				   done && !error
				   ? "Downloaded " : "Downloading ") ||
	    !string_builder_append(&sb,
				   prog->dbinfo->debuginfod_current_name) ||
	    !string_builder_append(&sb,
				   prog->dbinfo->debuginfod_current_type))
		goto out;

	size_t download_size_start = sb.len;
	if (error) {
		errno = -result;
		if (!string_builder_appendf(&sb, " failed: %m"))
			goto out;
	} else {
		intmax_t download_size;
		if (done) {
			struct stat st;
			if (fstat(result, &st) < 0) {
				drgn_log_notice(prog, "fstat: %m\n");
				goto out;
			}
			download_size = st.st_size;
		} else {
			download_size = a;
		}
		if (download_size < 2048) {
			if (!string_builder_appendf(&sb, " (%" PRIdMAX " B)",
						    download_size))
				goto out;
		} else {
			static const char prefixes[] = "KMGTPEZY";
			int i = 1;
			while (i <= sizeof(prefixes) - 1
			       && (download_size >> (10 * i)) >= 2048)
				i++;
			double unit = INTMAX_C(1) << (10 * i);
			if (!string_builder_appendf(&sb, " (%.1f %ciB)",
						    download_size / unit,
						    prefixes[i - 1]))
				goto out;
		}
	}

	if (animate) {
		int current_column;
		if (done) {
			// Start at byte 1 to skip the "\r".
			current_column = count_columns(&sb.str[1], sb.len - 1);
		} else {
			int download_size_len = sb.len - download_size_start;
			// Leave room for the download size and an extra space.
			int max_columns =
				max(fill_columns - download_size_len - 1, 0);
			// Start at byte 1 to skip the "\r".
			current_column = truncate_columns(&sb, 1,
							  download_size_start,
							  max_columns);
			if (current_column == INT_MIN)
				goto out; // Memory allocation failed.
			if (current_column >= 0)
				current_column += download_size_len;
		}
		if (current_column < 0) {
			// We either couldn't parse the string or the string
			// contained a nonprintable character. Give up on the
			// animation.
			animate = false;
		} else if (current_column < fill_columns) {
			if (!string_builder_reserve_for_append(&sb,
							       fill_columns
							       - current_column))
				goto out;
			memset(&sb.str[sb.len], ' ',
			       fill_columns - current_column);
			sb.len += fill_columns - current_column;
		}
	}

	// If we can't encode any of the following Unicode characters in the
	// current locale, we fall back to ASCII.
	if (!done && b > 0) {
		// Clamp the ratio in case we get bogus sizes.
		double ratio = a < b ? (double)a / (double)b : 1.0;
		if (animate) {
			// One multibyte character for each bar column, one for
			// each end, and one to reset the shift state.
			if (!string_builder_reserve_for_append(&sb,
							       (bar_columns + 3)
							       * MB_CUR_MAX))
				goto out;
			if (!write_unicode_progress_bar(&sb, bar_columns,
							ratio)) {
				write_ascii_progress_bar(&sb, bar_columns,
							 ratio);
			}
		}
		unsigned int percent = 100.0 * ratio;
		// We're not 100% done until we're called with done = true.
		if (percent > 99)
			percent = 99;
		if (!string_builder_appendf(&sb, " %*u%%", animate ? 2 : 0,
					    percent))
			goto out;
	} else if (!done && animate) {
		// One multibyte character for the spinner, one to reset the
		// shift state.
		if (!string_builder_reserve_for_append(&sb, 2 * MB_CUR_MAX))
			goto out;
		unsigned int pos = prog->dbinfo->debuginfod_spinner_position++;
		if (!write_unicode_spinner(&sb, pos))
			write_ascii_spinner(&sb, pos);
	}

	if ((done || !animate) && !string_builder_appendc(&sb, '\n'))
		goto out;

	// If we were originally animating but gave up, we need to skip the
	// "\r".
	const void *write_buf = sb.str + (orig_animate && !animate ? 1 : 0);
	size_t write_count = sb.len - (orig_animate && !animate ? 1 : 0);
	if (prog->log_file) {
		fwrite(write_buf, 1, write_count, prog->log_file);
		if (animate)
			fflush(prog->log_file);
	} else {
		write_all(prog->log_fd, write_buf, write_count);
	}
out:
	free(sb.str);
}

static int drgn_debuginfod_progressfn(debuginfod_client *client, long a, long b)
{
	struct drgn_program *prog = drgn_debuginfod_get_user_data(client);
	// TODO: it seems like some unresponsive cases are indistinguishable
	// from cleaning cache
	if (b == 0) {
		if (a == 1)
			drgn_log_debug(prog, "cleaning debuginfod cache\n");
		return 0;
	}
	if (a < 0)
		return 0;
	if (!prog->dbinfo->debuginfod_downloaded) {
		const char *url = drgn_debuginfod_get_url(client);
		if (url)
			drgn_log_debug(prog, "downloading from %s\n", url);
		prog->dbinfo->debuginfod_downloaded = true;
	}
	drgn_log_debuginfod_progress(prog, a, b, 0);
	return 0;
}
#endif // _ELFUTILS_PREREQ(0, 179)
#endif // WITH_DEBUGINFOD

struct drgn_error *
drgn_module_try_download_files_internal(struct drgn_module *module,
					struct drgn_module_try_files_state *state)
{
	struct drgn_error *err;

	// TODO: I don't like that this prints when it's cached
	drgn_module_try_files_log(module, state, "downloading");

	// TODO: what's up with ctrl-C?
#ifdef WITH_DEBUGINFOD
	struct drgn_program *prog = module->prog;
	if (!prog->dbinfo->debuginfod_client) {
		if (!drgn_have_debuginfod()) {
			if (!prog->dbinfo->logged_no_debuginfod) {
				drgn_log_debug(prog,
					       "debuginfod client library is not installed\n");
				prog->dbinfo->logged_no_debuginfod = true;
			}
			return NULL;
		}
		prog->dbinfo->debuginfod_client = drgn_debuginfod_begin();
		if (!prog->dbinfo->debuginfod_client) {
			return drgn_error_create(DRGN_ERROR_OTHER,
						 "couldn't create debuginfod client session");
		}
#if _ELFUTILS_PREREQ(0, 179)
		drgn_debuginfod_set_user_data(prog->dbinfo->debuginfod_client,
					      prog);
		drgn_debuginfod_set_progressfn(prog->dbinfo->debuginfod_client,
					       drgn_debuginfod_progressfn);
#endif
	}

	const void *build_id;
	size_t build_id_len;
	if (!drgn_module_try_files_build_id(module, &build_id, &build_id_len))
		return NULL;

#define try_debuginfod(which)							\
	do {									\
		prog->dbinfo->debuginfod_current_name = module->name;		\
		enum {								\
			executable_is_debug = 0,				\
			debuginfo_is_debug = 1,					\
		};								\
		if (module->trying_gnu_debugaltlink)				\
			prog->dbinfo->debuginfod_current_type = " alternate debug info";\
		else if (which##_is_debug)					\
			prog->dbinfo->debuginfod_current_type = " debug info";	\
		else								\
			prog->dbinfo->debuginfod_current_type = "";		\
		prog->dbinfo->debuginfod_downloaded = false;			\
		char *path;							\
		int fd = drgn_debuginfod_find_##which(prog->dbinfo->debuginfod_client,\
						      build_id, build_id_len,	\
						      &path);			\
		drgn_log_debuginfod_progress(prog, 0, 0, fd);			\
		if (fd >= 0) {							\
			err = drgn_module_try_file_internal(module, state,	\
							    path, fd, false,	\
							    NULL);		\
			free(path);						\
			if (err)						\
				return err;					\
		}								\
	} while (0)

	drgn_log_debug(prog, "trying debuginfod\n");
	if (state->want_debug)
		try_debuginfod(debuginfo);
	if (state->want_loaded)
		try_debuginfod(executable);
#undef try_debuginfod
#else
	if (!prog->dbinfo->logged_no_debuginfod) {
		drgn_log_debug(prog,
			       "drgn was built without debuginfod support\n");
		prog->dbinfo->logged_no_debuginfod = true;
	}
#endif
	return NULL;
}

static struct drgn_error *
drgn_module_try_default_files_internal(struct drgn_module *module,
				       struct drgn_module_try_files_state *state)
{
	struct drgn_error *err;
	err = drgn_module_try_local_files_internal(module, state);
	if (err || drgn_module_try_files_done(state))
		return err;
	return drgn_module_try_download_files_internal(module, state);
}

// TODO: export this?
static const char * const drgn_default_debug_directories[] = {
	"", ".debug", "/usr/lib/debug", NULL,
};

static bool drgn_module_needs_loaded_file(struct drgn_module *module)
{
	// TODO: explain why?
	SWITCH_ENUM(module->kind,
	case DRGN_MODULE_MAIN:
		return !(module->prog->flags & DRGN_PROGRAM_IS_LINUX_KERNEL);
	case DRGN_MODULE_SHARED_LIBRARY:
	case DRGN_MODULE_VDSO:
	case DRGN_MODULE_EXTRA:
		return true;
	case DRGN_MODULE_LINUX_KERNEL_LOADABLE:
		return false;
	)
}

static void
drgn_module_try_files_begin(struct drgn_module *module,
			    struct drgn_module_try_files_args *args,
			    struct drgn_module_try_files_state *state)
{
	*state = (struct drgn_module_try_files_state){
		.debug_directories =
			args->debug_directories
			? args->debug_directories
			: drgn_default_debug_directories,
		.arg = args->arg,
		.need_gnu_debugaltlink_file = args->need_gnu_debugaltlink_file,
	};

	if (module->trying_gnu_debugaltlink) {
		args->loaded_status = DRGN_MODULE_FILE_NOT_NEEDED;
		if (module->trying_gnu_debugaltlink->found) { // TODO
			args->debug_status = DRGN_MODULE_FILE_ALREADY_HAD;
		} else {
			args->debug_status = DRGN_MODULE_FILE_SUCCEEDED;
			state->want_debug = true;
			// TODO: logging
		}
		return;
	}

	if (module->loaded_file) {
		args->loaded_status = DRGN_MODULE_FILE_ALREADY_HAD;
	} else if (!drgn_module_needs_loaded_file(module)) {
		args->loaded_status = DRGN_MODULE_FILE_NOT_NEEDED;
	} else if (!args->want_loaded) {
		args->loaded_status = DRGN_MODULE_FILE_NOT_WANTED;
	} else {
		args->loaded_status = DRGN_MODULE_FILE_SUCCEEDED;
		state->want_loaded = true;
	}
	if (module->debug_file) {
		args->debug_status = DRGN_MODULE_FILE_ALREADY_HAD;
	} else if (!args->want_debug) {
		args->debug_status = DRGN_MODULE_FILE_NOT_WANTED;
	} else {
		args->debug_status = DRGN_MODULE_FILE_SUCCEEDED;
		state->want_debug = true;
	}
}

static void drgn_module_try_files_end(struct drgn_module_try_files_args *args,
				      struct drgn_module_try_files_state *state)
{
	if (state->want_loaded)
		args->loaded_status = DRGN_MODULE_FILE_FAILED;
	if (state->want_debug)
		args->debug_status = DRGN_MODULE_FILE_FAILED;
}

#define DRGN_MODULE_TRY_FILES_WRAPPER(name)					\
LIBDRGN_PUBLIC struct drgn_error *						\
drgn_module_try_##name##_files(struct drgn_module *module,			\
			       struct drgn_module_try_files_args *args)		\
{										\
	struct drgn_error *err;							\
	struct drgn_module_try_files_state state;				\
	drgn_module_try_files_begin(module, args, &state);			\
	if (!drgn_module_try_files_done(&state)) {				\
		err = drgn_module_try_##name##_files_internal(module, &state);	\
		if (err)							\
			return err;						\
	}									\
	drgn_module_try_files_end(args, &state);				\
	return NULL;								\
}
DRGN_MODULE_TRY_FILES_WRAPPER(default)
DRGN_MODULE_TRY_FILES_WRAPPER(local)
DRGN_MODULE_TRY_FILES_WRAPPER(download)
#undef DRGN_MODULE_TRY_FILES_WRAPPER

LIBDRGN_PUBLIC
struct drgn_error *drgn_module_try_file(struct drgn_module *module,
					const char *path, int fd, bool force,
					struct drgn_module_try_files_args *args)
{
	struct drgn_error *err;
	struct drgn_module_try_files_state state;
	drgn_module_try_files_begin(module, args, &state);
	if (!drgn_module_try_files_done(&state)) {
		drgn_module_try_files_log(module, &state,
					  "trying provided file as");
		err = drgn_module_try_file_internal(module, &state, path, fd,
						    !force, NULL);
		if (err)
			return err;
	}
	drgn_module_try_files_end(args, &state);
	return NULL;
}

#if 0
static struct drgn_error *
drgn_module_copy_section_addresses(struct drgn_module *module, Elf *elf)
{
	size_t shstrndx;
	if (elf_getshdrstrndx(elf, &shstrndx))
		return drgn_error_libelf();

	Elf_Scn *scn = NULL;
	while ((scn = elf_nextscn(elf, scn))) {
		GElf_Shdr *shdr, shdr_mem;
		shdr = gelf_getshdr(scn, &shdr_mem);
		if (!shdr)
			return drgn_error_libelf();

		char *scnname = elf_strptr(elf, shstrndx, shdr->sh_name);
		if (!scnname)
			return drgn_error_libelf();

		struct drgn_module_section_address_map_iterator it =
			drgn_module_section_address_map_search(&module->section_addresses,
							       &scnname);
		if (!it.entry)
			continue;

		shdr->sh_addr = it.entry->value;
		if (!gelf_update_shdr(scn, shdr))
			return drgn_error_libelf();
	}
	return NULL;
}

// Get the start address from the first loadable segment and the end address
// from the last loadable segment.
//
// The ELF specification states that loadable segments are sorted on p_vaddr.
// However, vmlinux on x86-64 has an out of order segment for .data..percpu, and
// Arm has a couple for .vector and .stubs. Thankfully, those are placed in the
// middle by the vmlinux linker script, so we can still rely on the first and
// last loadable segments.
static struct drgn_error *
drgn_module_get_address_range(struct drgn_module *module, Elf *elf,
			      uint64_t bias)
{
	size_t phnum;
	if (elf_getphdrnum(elf, &phnum) != 0)
		return drgn_error_libelf();

	uint64_t start = UINT64_MAX, end = 0;
	GElf_Phdr phdr_mem, *phdr;
	size_t i;
	for (i = 0; i < phnum; i++) {
		phdr = gelf_getphdr(elf, i, &phdr_mem);
		if (!phdr)
			return drgn_error_libelf();
		if (phdr->p_type != PT_LOAD)
			continue;
		uint64_t align = phdr->p_align ? phdr->p_align : 1;
		start = (phdr->p_vaddr & -align) + bias;
		break;
	}
	if (i >= phnum) {
		return drgn_error_create(DRGN_ERROR_OTHER,
					 "no loadable segments");
	}

	for (i = phnum - 1;; i--) {
		phdr = gelf_getphdr(elf, i, &phdr_mem);
		if (!phdr)
			return drgn_error_libelf();
		if (phdr->p_type != PT_LOAD)
			continue;
		end = (phdr->p_vaddr + phdr->p_memsz) + bias;
		if (start >= end) {
			return drgn_error_create(DRGN_ERROR_OTHER,
						 "empty address range");
		}
		module->start = start;
		module->end = end;
		return NULL;
	}
}

struct debugaltlink_report_arg {
	const char *debug_path;
	const char *debugaltlink;
	size_t debugaltlink_len;
};

static struct drgn_error *
debugaltlink_try_default_files(struct drgn_discovered_module *discovered,
			       void *_arg)
{
	struct debugaltlink_report_arg *arg = _arg;
	const char *slash;
	if (arg->debugaltlink[0] == '/' ||
	    !(slash = strrchr(arg->debug_path, '/'))) {
		// Either the debugaltlink is absolute or the debug file path
		// has no directory component (which means it's in the current
		// working directory). Try the debugaltlink directly.
		return drgn_module_try_file(discovered, CHECK_BUILD_ID, 0,
					    arg->debugaltlink, false, -1);
	} else {
		// Otherwise, try $(dirname $debug_path)/$debugaltlink
		size_t dirslash_len = slash + 1 - arg->debug_path;
		size_t bytes;
		if (__builtin_add_overflow(dirslash_len,
					   arg->debugaltlink_len + 1, &bytes))
			return &drgn_enomem;
		char *path = malloc(bytes);
		if (!path)
			return &drgn_enomem;
		memcpy(path, arg->debug_path, dirslash_len);
		memcpy(path + dirslash_len, arg->debugaltlink,
		       arg->debugaltlink_len + 1);
		return drgn_module_try_file(discovered, CHECK_BUILD_ID, 0, path,
					    true, -1);
	}
}

static struct drgn_error *
drgn_module_use_file(struct drgn_discovered_module *discovered,
		     struct drgn_elf_file *file, bool use_loadable,
		     bool use_debug)
{
	struct drgn_error *err;
	struct drgn_program *prog = discovered->prog;
	struct drgn_discover_modules_state *state = discovered->state;
	struct drgn_module *module = discovered->module;
	bool reset_address_range = false;

	if (!module->loadable_file && !module->debug_file) {
		GElf_Ehdr ehdr_mem, *ehdr = gelf_getehdr(file->elf, &ehdr_mem);
		if (!ehdr) {
			err = drgn_error_libelf();
			goto log_err;
		}
		drgn_platform_from_elf(ehdr, &module->platform);
	}

	if (!drgn_module_section_address_map_empty(&module->section_addresses)) {
		err = drgn_module_copy_section_addresses(module, file->elf);
		if (err)
			goto log_err;
	}

	uint64_t bias = 0;
	if (discovered->report_callbacks->get_bias) {
		err = discovered->report_callbacks->get_bias(file->elf,
							     discovered->report_callbacks_arg,
							     &bias);
		if (err)
			goto log_err;
	}

	if (module->start == UINT64_MAX && module->end == UINT64_MAX) {
		reset_address_range = true;
		err = drgn_module_get_address_range(module, file->elf, bias);
		if (err)
			goto log_err;
	}

	if (use_debug) {
		Dwarf *dwarf = dwarf_begin_elf(file->elf, DWARF_C_READ, NULL);
		if (!dwarf) {
			err = drgn_error_libdw();
			goto log_err;
		}

		// If the file has .gnu_debugaltlink, find it before we use the
		// file. Note that it doesn't make sense for a .gnu_debugaltlink
		// file to have a .gnu_debugaltlink.
		if (module->kind != DRGN_MODULE_COMMON_DEBUG &&
		    file->scns[DRGN_SCN_GNU_DEBUGALTLINK]) {
			struct drgn_module *altmodule;
			err = drgn_module_report_debugaltlink(state, file,
							      &altmodule);
			if (err || !altmodule) {
				// If err, then there was a fatal error. If
				// !altmodule, then something was wrong with
				// this file. Either way, throw the file away.
				dwarf_end(dwarf);
				goto discard;
			}
			if (altmodule->debug_file) {
				dwarf_setalt(dwarf,
					     altmodule->debug_file->dwarf);
			} else {
				drgn_log_debug(prog,
					       "couldn't find .gnu_debugaltlink file for %s; ignoring debug info\n",
					       file->path);
				dwarf_end(dwarf);
				use_debug = false;
			}
		}

		if (use_debug) {
			if (!drgn_module_vector_append(&state->new_debug_modules,
						       &module)) {
				err = &drgn_enomem;
				dwarf_end(dwarf);
				goto discard;
			}
			file->dwarf = dwarf;
			module->debug_file = file;
			module->debug_file_bias = bias;
			discovered->want_debug_file = false;
		}
	}
	if (use_loadable) {
		module->loadable_file = file;
		module->loadable_file_bias = bias;
		discovered->want_loadable_file = false;
	}

	if (use_loadable && use_debug) {
		drgn_log_info(prog, "using loadable file with debug info %s\n",
			      file->path);
	} else if (use_loadable) {
		drgn_log_info(prog, "using loadable file %s\n", file->path);
	} else if (use_debug) {
		drgn_log_info(prog, "using debug info file %s\n", file->path);
	} else {
		err = NULL;
		goto discard;
	}

	if (!discovered->want_loadable_file && !discovered->want_debug_file)
		return &drgn_found_module_files;
	return NULL;

log_err:
	if (drgn_error_should_log(err)) {
		drgn_error_log_debug(prog, err, "%s: ", file->path);
		drgn_error_destroy(err);
		err = NULL;
	}
discard:
	if (reset_address_range)
		module->start = module->end = UINT64_MAX;
	drgn_elf_file_destroy(file);
	return err;
}

static int should_apply_relocation_section(Elf *elf, size_t shstrndx,
					   const GElf_Shdr *shdr)
{
	if (shdr->sh_type != SHT_RELA && shdr->sh_type != SHT_REL)
		return 0;

	const char *scnname = elf_strptr(elf, shstrndx, shdr->sh_name);
	if (!scnname)
		return -1;
	if (shdr->sh_type == SHT_RELA) {
		if (!strstartswith(scnname, ".rela."))
			return 0;
		scnname += sizeof(".rela.") - 1;
	} else {
		if (!strstartswith(scnname, ".rel."))
			return 0;
		scnname += sizeof(".rel.") - 1;
	}
	return (strstartswith(scnname, "debug_") ||
		strstartswith(scnname, "orc_"));
}

static inline struct drgn_error *get_reloc_sym_value(const void *syms,
						     size_t num_syms,
						     const uint64_t *sh_addrs,
						     size_t shdrnum,
						     bool is_64_bit,
						     bool bswap,
						     uint32_t r_sym,
						     uint64_t *ret)
{
	if (r_sym >= num_syms) {
		return drgn_error_create(DRGN_ERROR_OTHER,
					 "invalid ELF relocation symbol");
	}
	uint16_t st_shndx;
	uint64_t st_value;
	if (is_64_bit) {
		const Elf64_Sym *sym = (Elf64_Sym *)syms + r_sym;
		memcpy(&st_shndx, &sym->st_shndx, sizeof(st_shndx));
		memcpy(&st_value, &sym->st_value, sizeof(st_value));
		if (bswap) {
			st_shndx = bswap_16(st_shndx);
			st_value = bswap_64(st_value);
		}
	} else {
		const Elf32_Sym *sym = (Elf32_Sym *)syms + r_sym;
		memcpy(&st_shndx, &sym->st_shndx, sizeof(st_shndx));
		uint32_t st_value32;
		memcpy(&st_value32, &sym->st_value, sizeof(st_value32));
		if (bswap) {
			st_shndx = bswap_16(st_shndx);
			st_value32 = bswap_32(st_value32);
		}
		st_value = st_value32;
	}
	if (st_shndx >= shdrnum) {
		return drgn_error_create(DRGN_ERROR_OTHER,
					 "invalid ELF symbol section index");
	}
	*ret = sh_addrs[st_shndx] + st_value;
	return NULL;
}

static struct drgn_error *
apply_elf_relas(const struct drgn_relocating_section *relocating,
		Elf_Data *reloc_data, Elf_Data *symtab_data,
		const uint64_t *sh_addrs, size_t shdrnum,
		const struct drgn_platform *platform)
{
	struct drgn_error *err;

	bool is_64_bit = drgn_platform_is_64_bit(platform);
	bool bswap = drgn_platform_bswap(platform);
	apply_elf_reloc_fn *apply_elf_reloc = platform->arch->apply_elf_reloc;

	const void *relocs = reloc_data->d_buf;
	size_t reloc_size = is_64_bit ? sizeof(Elf64_Rela) : sizeof(Elf32_Rela);
	size_t num_relocs = reloc_data->d_size / reloc_size;

	const void *syms = symtab_data->d_buf;
	size_t sym_size = is_64_bit ? sizeof(Elf64_Sym) : sizeof(Elf32_Sym);
	size_t num_syms = symtab_data->d_size / sym_size;

	for (size_t i = 0; i < num_relocs; i++) {
		uint64_t r_offset;
		uint32_t r_sym;
		uint32_t r_type;
		int64_t r_addend;
		if (is_64_bit) {
			const Elf64_Rela *rela = (Elf64_Rela *)relocs + i;
			uint64_t r_info;
			memcpy(&r_offset, &rela->r_offset, sizeof(r_offset));
			memcpy(&r_info, &rela->r_info, sizeof(r_info));
			memcpy(&r_addend, &rela->r_addend, sizeof(r_addend));
			if (bswap) {
				r_offset = bswap_64(r_offset);
				r_info = bswap_64(r_info);
				r_addend = bswap_64(r_addend);
			}
			r_sym = ELF64_R_SYM(r_info);
			r_type = ELF64_R_TYPE(r_info);
		} else {
			const Elf32_Rela *rela32 = (Elf32_Rela *)relocs + i;
			uint32_t r_offset32;
			uint32_t r_info32;
			int32_t r_addend32;
			memcpy(&r_offset32, &rela32->r_offset, sizeof(r_offset32));
			memcpy(&r_info32, &rela32->r_info, sizeof(r_info32));
			memcpy(&r_addend32, &rela32->r_addend, sizeof(r_addend32));
			if (bswap) {
				r_offset32 = bswap_32(r_offset32);
				r_info32 = bswap_32(r_info32);
				r_addend32 = bswap_32(r_addend32);
			}
			r_offset = r_offset32;
			r_sym = ELF32_R_SYM(r_info32);
			r_type = ELF32_R_TYPE(r_info32);
			r_addend = r_addend32;
		}
		uint64_t sym_value;
		err = get_reloc_sym_value(syms, num_syms, sh_addrs, shdrnum,
					  is_64_bit, bswap, r_sym, &sym_value);
		if (err)
			return err;

		err = apply_elf_reloc(relocating, r_offset, r_type, &r_addend,
				      sym_value);
		if (err)
			return err;
	}
	return NULL;
}

static struct drgn_error *
apply_elf_rels(const struct drgn_relocating_section *relocating,
	       Elf_Data *reloc_data, Elf_Data *symtab_data,
	       const uint64_t *sh_addrs, size_t shdrnum,
	       const struct drgn_platform *platform)
{
	struct drgn_error *err;

	bool is_64_bit = drgn_platform_is_64_bit(platform);
	bool bswap = drgn_platform_bswap(platform);
	apply_elf_reloc_fn *apply_elf_reloc = platform->arch->apply_elf_reloc;

	const void *relocs = reloc_data->d_buf;
	size_t reloc_size = is_64_bit ? sizeof(Elf64_Rel) : sizeof(Elf32_Rel);
	size_t num_relocs = reloc_data->d_size / reloc_size;

	const void *syms = symtab_data->d_buf;
	size_t sym_size = is_64_bit ? sizeof(Elf64_Sym) : sizeof(Elf32_Sym);
	size_t num_syms = symtab_data->d_size / sym_size;

	for (size_t i = 0; i < num_relocs; i++) {
		uint64_t r_offset;
		uint32_t r_sym;
		uint32_t r_type;
		if (is_64_bit) {
			const Elf64_Rel *rel = (Elf64_Rel *)relocs + i;
			uint64_t r_info;
			memcpy(&r_offset, &rel->r_offset, sizeof(r_offset));
			memcpy(&r_info, &rel->r_info, sizeof(r_info));
			if (bswap) {
				r_offset = bswap_64(r_offset);
				r_info = bswap_64(r_info);
			}
			r_sym = ELF64_R_SYM(r_info);
			r_type = ELF64_R_TYPE(r_info);
		} else {
			const Elf32_Rel *rel32 = (Elf32_Rel *)relocs + i;
			uint32_t r_offset32;
			uint32_t r_info32;
			memcpy(&r_offset32, &rel32->r_offset, sizeof(r_offset32));
			memcpy(&r_info32, &rel32->r_info, sizeof(r_info32));
			if (bswap) {
				r_offset32 = bswap_32(r_offset32);
				r_info32 = bswap_32(r_info32);
			}
			r_offset = r_offset32;
			r_sym = ELF32_R_SYM(r_info32);
			r_type = ELF32_R_TYPE(r_info32);
		}
		uint64_t sym_value;
		err = get_reloc_sym_value(syms, num_syms, sh_addrs, shdrnum,
					  is_64_bit, bswap, r_sym, &sym_value);
		if (err)
			return err;

		err = apply_elf_reloc(relocating, r_offset, r_type, NULL,
				      sym_value);
		if (err)
			return err;
	}
	return NULL;
}

/*
 * TODO: don't talk about libdwfl
 *
 * Before the debugging information in a relocatable ELF file (e.g., Linux
 * kernel module) can be used, it must have ELF relocations applied. This is
 * usually done by libdwfl. However, libdwfl is relatively slow at it. This is a
 * much faster implementation.
 */
static struct drgn_error *relocate_elf_file(Elf *elf)
{
	struct drgn_error *err;

	GElf_Ehdr ehdr_mem, *ehdr;
	ehdr = gelf_getehdr(elf, &ehdr_mem);
	if (!ehdr)
		return drgn_error_libelf();

	if (ehdr->e_type != ET_REL) {
		/* Not a relocatable file. */
		return NULL;
	}

	struct drgn_platform platform;
	drgn_platform_from_elf(ehdr, &platform);
	if (!platform.arch->apply_elf_reloc) {
		/* Unsupported; fall back to libdwfl. */
		return NULL;
	}

	size_t shdrnum;
	if (elf_getshdrnum(elf, &shdrnum))
		return drgn_error_libelf();
	uint64_t *sh_addrs = calloc(shdrnum, sizeof(sh_addrs[0]));
	if (!sh_addrs && shdrnum > 0)
		return &drgn_enomem;

	Elf_Scn *scn = NULL;
	while ((scn = elf_nextscn(elf, scn))) {
		GElf_Shdr *shdr, shdr_mem;
		shdr = gelf_getshdr(scn, &shdr_mem);
		if (!shdr) {
			err = drgn_error_libelf();
			goto out;
		}
		sh_addrs[elf_ndxscn(scn)] = shdr->sh_addr;
	}

	size_t shstrndx;
	if (elf_getshdrstrndx(elf, &shstrndx)) {
		err = drgn_error_libelf();
		goto out;
	}

	Elf_Scn *reloc_scn = NULL;
	while ((reloc_scn = elf_nextscn(elf, reloc_scn))) {
		GElf_Shdr *reloc_shdr, reloc_shdr_mem;
		reloc_shdr = gelf_getshdr(reloc_scn, &reloc_shdr_mem);
		if (!reloc_shdr) {
			err = drgn_error_libelf();
			goto out;
		}
		/* We don't support any architectures that use SHT_REL yet. */
		if (reloc_shdr->sh_type != SHT_RELA)
			continue;

		int r = should_apply_relocation_section(elf, shstrndx,
							reloc_shdr);
		if (r < 0) {
			err = drgn_error_libelf();
			goto out;
		}
		if (r) {
			Elf_Scn *scn = elf_getscn(elf, reloc_shdr->sh_info);
			if (!scn) {
				err = drgn_error_libelf();
				goto out;
			}
			GElf_Shdr *shdr, shdr_mem;
			shdr = gelf_getshdr(scn, &shdr_mem);
			if (!shdr) {
				err = drgn_error_libelf();
				goto out;
			}
			if (shdr->sh_type == SHT_NOBITS)
				continue;

			Elf_Scn *symtab_scn = elf_getscn(elf,
							 reloc_shdr->sh_link);
			if (!symtab_scn) {
				err = drgn_error_libelf();
				goto out;
			}
			shdr = gelf_getshdr(symtab_scn, &shdr_mem);
			if (!shdr) {
				err = drgn_error_libelf();
				goto out;
			}
			if (shdr->sh_type == SHT_NOBITS) {
				err = drgn_error_create(DRGN_ERROR_OTHER,
							"relocation symbol table has no data");
				goto out;
			}

			Elf_Data *data, *reloc_data, *symtab_data;
			if ((err = read_elf_section(scn, &data)) ||
			    (err = read_elf_section(reloc_scn, &reloc_data)) ||
			    (err = read_elf_section(symtab_scn, &symtab_data)))
				goto out;

			struct drgn_relocating_section relocating = {
				.buf = data->d_buf,
				.buf_size = data->d_size,
				.addr = sh_addrs[elf_ndxscn(scn)],
				.bswap = drgn_platform_bswap(&platform),
			};

			if (reloc_shdr->sh_type == SHT_RELA) {
				err = apply_elf_relas(&relocating, reloc_data,
						      symtab_data, sh_addrs,
						      shdrnum, &platform);
			} else {
				err = apply_elf_rels(&relocating, reloc_data,
						     symtab_data, sh_addrs,
						     shdrnum, &platform);
			}
			if (err)
				goto out;

			/*
			 * Mark the relocation section as empty so that libdwfl
			 * doesn't try to apply it again.
			 */
			reloc_shdr->sh_size = 0;
			if (!gelf_update_shdr(reloc_scn, reloc_shdr)) {
				err = drgn_error_libelf();
				goto out;
			}
			reloc_data->d_size = 0;
		}
	}
	err = NULL;
out:
	free(sh_addrs);
	return err;
}

static struct drgn_error *drgn_module_relocate(struct drgn_module *module)
{
	struct drgn_error *err;
	if (drgn_module_section_address_map_empty(&module->section_addresses))
		return NULL;
	if (module->debug_file && !module->debug_file_committed) {
		err = relocate_elf_file(module->debug_file->elf);
		if (err)
			return err;
	}
	if (module->loadable_file != module->debug_file &&
	    module->loadable_file && !module->loadable_file_committed) {
		err = relocate_elf_file(module->loadable_file->elf);
		if (err)
			return err;
	}
	return NULL;
}

static struct drgn_error *
drgn_module_precache_sections(struct drgn_module *module)
{
	struct drgn_error *err;
	if (module->debug_file && !module->debug_file_committed) {
		err = drgn_elf_file_precache_sections(module->debug_file);
		if (err)
			return err;
	}
	if (module->loadable_file != module->debug_file &&
	    module->loadable_file && !module->loadable_file_committed) {
		err = drgn_elf_file_precache_sections(module->loadable_file);
		if (err)
			return err;
	}
	return NULL;
}

static struct drgn_error *
drgn_debug_info_read_module(struct drgn_debug_info_load_state *load,
			    struct drgn_dwarf_index_state *index,
			    struct drgn_module *module)
{
	struct drgn_error *err;

	err = drgn_module_relocate(module);
	if (err)
		return err;
	err = drgn_module_precache_sections(module);
	if (err)
		return err;
	return drgn_dwarf_index_read_module(index, module);
}

static struct drgn_error *
drgn_debug_info_update_index(struct drgn_debug_info_load_state *load)
{
	struct drgn_dwarf_index_state index;
	if (!drgn_dwarf_index_state_init(&index, load->dbinfo))
		return &drgn_enomem;
	struct drgn_error *err = NULL;
	#pragma omp parallel for schedule(dynamic)
	for (size_t i = 0; i < load->new_debug_modules.size; i++) {
		if (err)
			continue;
		struct drgn_error *module_err =
			drgn_debug_info_read_module(load, &index,
						    load->new_debug_modules.data[i]);
		if (module_err) {
			#pragma omp critical(drgn_debug_info_update_index_error)
			if (err)
				drgn_error_destroy(module_err);
			else
				err = module_err;
		}
	}
	if (!err)
		err = drgn_dwarf_info_update_index(&index);
	drgn_dwarf_index_state_deinit(&index);
	return err;
}

struct drgn_error *
drgn_commit_discovered_modules(struct drgn_discover_modules_state *state)
{
	struct drgn_error *err;
	struct drgn_debug_info *dbinfo = state->dbinfo;

	if (state->new_debug_modules.size) {
		err = drgn_debug_info_update_index(state);
		if (err)
			return err;
		state->new_debug_modules.size = 0;
	}

	struct drgn_module_table_iterator it =
		drgn_module_table_first(&dbinfo->modules);
	while (it.entry) {
		struct drgn_module **modulep = it.entry;
		do {
			struct drgn_module *module = *modulep;

			if (module->state == DRGN_MODULE_STATE_NEW) {
				*modulep = module->next;
				drgn_module_destroy(module);
				continue;
			}

			if (module->debug_file)
				module->debug_file_committed = true;
			if (module->loadable_file)
				module->loadable_file_committed = true;
			// TODO: or only check start?
			if (!module->address_range_committed &&
			    (module->start != UINT64_MAX ||
			     module->end != UINT64_MAX)) {
				// TODO: check for overlap?
				drgn_module_address_tree_insert(&dbinfo->modules_by_address,
								module, NULL);
				module->address_range_committed = true;
			}
			if (module->reported) {
				module->reported = false;
				struct drgn_discovered_module discovered = {
					.module = module,
				};
				state->post_fn(&discovered, state->fn_arg);
			}
			// Update the state after calling post_fn so that new
			// modules are still considered new in post_fn.
			module->state = DRGN_MODULE_STATE_COMMITTED;
			modulep = &module->next;
		} while (*modulep);
		if (*it.entry) {
			it = drgn_module_table_next(it);
		} else {
			it = drgn_module_table_delete_iterator(&dbinfo->modules,
							       it);
		}
	}
	return NULL;
}

static void drgn_rollback_discovered_modules(struct drgn_debug_info *dbinfo)
{
	struct drgn_module_table_iterator it =
		drgn_module_table_first(&dbinfo->modules);
	while (it.entry) {
		struct drgn_module **modulep = it.entry;
		do {
			struct drgn_module *module = *modulep;
			module->reported = false;
			if (!module->debug_file_committed) {
				module->gnu_debugaltlink_module = NULL;
				if (module->debug_file != module->loadable_file)
					drgn_elf_file_destroy(module->debug_file);
				module->debug_file = NULL;
			}
			if (!module->loadable_file_committed) {
				drgn_elf_file_destroy(module->loadable_file);
				module->loadable_file = NULL;
			}
			if (module->state < DRGN_MODULE_STATE_COMMITTED) {
				*modulep = module->next;
				drgn_module_destroy(module);
			} else {
				if (!module->address_range_committed) {
					module->start = UINT64_MAX;
					module->end = UINT64_MAX;
				}
				modulep = &module->next;
			}
		} while (*modulep);
		if (*it.entry) {
			it = drgn_module_table_next(it);
		} else {
			it = drgn_module_table_delete_iterator(&dbinfo->modules,
							       it);
		}
	}
}
#endif

// TODO: stop using this one.
#define read_struct64(prog, ret, address, n, type32, visit_members) ({		\
	struct drgn_program *_prog = (prog);					\
	__auto_type _ret = (ret);						\
	size_t _n = (n);							\
	static_assert(sizeof(_ret[0]) >= sizeof(type32),			\
		      "64-bit type is smaller than 32-bit type");		\
	/* TODO: check if have platform? */					\
	bool _is_64_bit = drgn_platform_is_64_bit(&_prog->platform);		\
	bool _bswap = drgn_platform_bswap(&_prog->platform);			\
	struct drgn_error *_err =						\
		drgn_program_read_memory(_prog, _ret, (address),		\
					 _n * (_is_64_bit ?			\
					       sizeof(_ret[0]) :		\
					       sizeof(type32)),			\
					 false);				\
	if (!_err) {								\
		if (_is_64_bit && !_bswap) {					\
			/* It's already what we want. */			\
		} else if (_is_64_bit /* && _bswap */) {			\
			for (size_t i = 0; i < _n; i++) {			\
				__auto_type _dst = &_ret[i];			\
				visit_members(bswap_member_in_place,		\
					      ignore_member);			\
			}							\
		} else if (/* !_is_64_bit && */ !_bswap) {			\
			for (size_t i = _n; i-- > 0;) {				\
				typeof(_ret[0]) _tmp;				\
				__auto_type _dst = &_tmp;			\
				typeof(type32) *_src =				\
					(typeof(type32) *)_ret + i;		\
				visit_members(assign_member, memcpy_member);	\
				memcpy(&_ret[i], _dst, sizeof(_ret[i]));	\
			}							\
		} else /* if (!_is_64_bit && _bswap) */ {			\
			for (size_t i = _n; i-- > 0;) {				\
				typeof(_ret[0]) _tmp;				\
				__auto_type _dst = &_tmp;			\
				typeof(type32) *_src =				\
					(typeof(type32) *)_ret + i;		\
				visit_members(bswap_member, memcpy_member);	\
				memcpy(&_ret[i], _dst, sizeof(_ret[i]));	\
			}							\
		}								\
	}									\
	_err;									\
})

LIBDRGN_PUBLIC
void drgn_module_iterator_destroy(struct drgn_module_iterator *it)
{
	if (it) {
		if (it->destroy)
			it->destroy(it);
		else
			free(it);
	}
}

LIBDRGN_PUBLIC struct drgn_program *
drgn_module_iterator_program(const struct drgn_module_iterator *it)
{
	return it->prog;
}

LIBDRGN_PUBLIC
struct drgn_error *drgn_module_iterator_next(struct drgn_module_iterator *it,
					     struct drgn_module **ret)
{
	if (!it->next) {
		*ret = NULL;
		return NULL;
	}
	struct drgn_error *err = it->next(it, ret);
	if (err || !*ret)
		it->next = NULL;
	return err;
}

struct drgn_mapped_file {
	const char *path;
	// Mapped address range containing file offset 0. This is used to find
	// the file header.
	uint64_t offset0_vaddr, offset0_size;
};

static struct drgn_mapped_file *drgn_mapped_file_create(const char *path)
{
	struct drgn_mapped_file *file = calloc(1, sizeof(*file));
	if (file)
		file->path = path;
	return file;
}

static void drgn_mapped_file_destroy(struct drgn_mapped_file *file)
{
	free(file);
}

struct drgn_mapped_file_range {
	uint64_t start;
	uint64_t end;
	struct drgn_mapped_file *file;
};

DEFINE_VECTOR(drgn_mapped_file_range_vector, struct drgn_mapped_file_range)

struct drgn_mapped_file_ranges {
	struct drgn_mapped_file_range_vector vector;
	// Whether the ranges are already sorted by start address. This should
	// always be true for both /proc/$pid/maps and NT_FILE, but we check and
	// sort afterwards if not just in case.
	bool sorted;
};

#define DRGN_MAPPED_FILE_RANGES_INIT { VECTOR_INIT, true }

static void drgn_mapped_file_ranges_abort(struct drgn_mapped_file_ranges *ranges)
{
	drgn_mapped_file_range_vector_deinit(&ranges->vector);
}

static struct drgn_error *
drgn_add_mapped_file_range(struct drgn_mapped_file_ranges *ranges,
			   uint64_t start, uint64_t end, uint64_t file_offset,
			   struct drgn_mapped_file *file)
{
	assert(start < end);
	if (file_offset == 0 && file->offset0_size == 0) {
		file->offset0_vaddr = start;
		file->offset0_size = end - start;
	}
	if (ranges->vector.size > 0) {
		struct drgn_mapped_file_range *last =
			&ranges->vector.data[ranges->vector.size - 1];
		// If the last range is contiguous with this one and from the
		// same file, merge into that one. Note that for this vector, we
		// only care about what file a particular address came from, so
		// we don't care about the file offset here.
		if (file == last->file && start == last->end) {
			last->end = end;
			return NULL;
		}
		if (start < last->start)
			ranges->sorted = false;
	}
	struct drgn_mapped_file_range *entry =
		drgn_mapped_file_range_vector_append_entry(&ranges->vector);
	if (!entry)
		return &drgn_enomem;
	entry->start = start;
	entry->end = end;
	entry->file = file;
	return NULL;
}

enum {
	// Yield main module next.
	USERSPACE_LOADED_MODULE_ITERATOR_STATE_MAIN,
	// Yield vDSO module next.
	USERSPACE_LOADED_MODULE_ITERATOR_STATE_VDSO,
	// Get first link_map from r_debug next.
	USERSPACE_LOADED_MODULE_ITERATOR_STATE_R_DEBUG,
	// Yield module from link_map list next.
	USERSPACE_LOADED_MODULE_ITERATOR_STATE_LINK_MAP,
	// States after this are the same as
	// USERSPACE_LOADED_MODULE_ITERATOR_STATE_LINK_MAP but also count how
	// many link_map entries we've iterated.
};

// Arbitrary limit on the number iterations to make through the link_map list in
// order to avoid getting stuck in a cycle.
static const int MAX_LINK_MAP_LIST_ITERATIONS = 10000;

struct userspace_loaded_module_iterator {
	struct drgn_module_iterator it;
	int state;
	// TODO: use bit fields?
	bool read_main_phdrs;
	bool have_main_dyn;
	bool have_vdso_dyn;

	struct drgn_mapped_file_range *file_ranges;
	size_t num_file_ranges;

	uint64_t main_bias;
	uint64_t main_dyn_vaddr;
	uint64_t main_dyn_memsz;
	uint64_t vdso_dyn_vaddr;
	uint64_t link_map;

	// Temporary buffer for reading program headers.
	void *phdrs_buf;
	size_t phdrs_buf_capacity;

	// Temporary buffer for reading segment contents.
	void *segment_buf;
	size_t segment_buf_capacity;
};

static void
userspace_loaded_module_iterator_deinit(struct userspace_loaded_module_iterator *it)
{
	free(it->segment_buf);
	free(it->phdrs_buf);
	free(it->file_ranges);
}

static inline int drgn_mapped_file_range_compare(const void *_a, const void *_b)
{
	const struct drgn_mapped_file_range *a = _a;
	const struct drgn_mapped_file_range *b = _b;
	if (a->start < b->start)
		return -1;
	else if (a->start > b->start)
		return 1;
	else
		return 0;
}

static void
userspace_loaded_module_iterator_set_file_ranges(struct userspace_loaded_module_iterator *it,
						 struct drgn_mapped_file_ranges *ranges)
{
	// Don't bother shrinking to fit since this is short-lived.
	it->file_ranges = ranges->vector.data;
	it->num_file_ranges = ranges->vector.size;
	if (!ranges->sorted) {
		qsort(it->file_ranges, it->num_file_ranges,
		      sizeof(it->file_ranges[0]),
		      drgn_mapped_file_range_compare);
	}
}

static struct drgn_mapped_file *
find_mapped_file(struct userspace_loaded_module_iterator *it, uint64_t address)
{
	if (!it->num_file_ranges || address < it->file_ranges[0].start)
		return NULL;
	size_t lo = 0, hi = it->num_file_ranges, found = 0;
	while (lo < hi) {
		size_t mid = lo + (hi - lo) / 2;
		if (it->file_ranges[mid].start <= address) {
			found = mid;
			lo = mid + 1;
		} else {
			hi = mid;
		}
	}
	if (address >= it->file_ranges[found].end)
		return NULL;
	return it->file_ranges[found].file;
}

// Alignment of ELF notes is a mess. The [System V
// gABI](http://www.sco.com/developers/gabi/latest/ch5.pheader.html#note_section)
// says that the note header and descriptor should be aligned to 4 bytes for
// 32-bit files and 8 bytes for 64-bit files. However, on Linux, 4-byte
// alignment is used for both 32-bit and 64-bit files.
//
// The only exception as of 2022 is NT_GNU_PROPERTY_TYPE_0, which is defined to
// follow the gABI alignment. See ["PT_NOTE alignment, NT_GNU_PROPERTY_TYPE_0,
// glibc and
// gold"](https://public-inbox.org/libc-alpha/13a92cb0-a993-f684-9a96-e02e4afb1bef@redhat.com/).
// But, note that the 12-byte note header plus the 4-byte "GNU\0" name is a
// multiple of 8 bytes, and the NT_GNU_PROPERTY_TYPE_0 descriptor is defined to
// be a multiple of 4 bytes for 32-bit files and 8 bytes for 64-bit files. As a
// result, NT_GNU_PROPERTY_TYPE_0 is never actually padded, and 4-byte vs 8-byte
// alignment are equivalent for parsing purposes.
//
// According to the [gABI Linux
// Extensions](https://gitlab.com/x86-psABIs/Linux-ABI), consumers are now
// supposed to use the p_align of the PT_NOTE segment instead of assuming an
// alignment. However, the Linux kernel as of 6.0 generates core dumps with
// PT_NOTE segments with a p_align of 0 or 1 which are actually aligned to 4
// bytes. So, when parsing notes from an ELF file, we use 8-byte alignment if
// p_align is 8 and 4-byte alignment otherwise. binutils and elfutils appear to
// do the same.
//
// As of Linux 6.0, the vmlinux linker script can create a PT_NOTE segment with
// a p_align of 8 where the entries other than NT_GNU_PROPERTY_TYPE_0 are
// actually aligned to 4 bytes. This appears to be a bug; see ["[PATCH 2/2]
// Discard .note.gnu.property sections in generic
// NOTES"](https://lore.kernel.org/lkml/20200428132105.170886-2-hjl.tools@gmail.com/).
// We ignore this in the hopes that it will be fixed soon.
//
// Finally, there are cases where we don't know p_align. /sys/kernel/notes
// contains the contents of the vmlinux .notes section, which (ignoring the
// aforementioned bug) we can assume has 4-byte alignment.
// /sys/module/$module/notes/* contains a file for each note section. Since
// NT_GNU_PROPERTY_TYPE_0 can be parsed assuming 4-byte alignment, we can again
// assume 4-byte alignment. This will work as long as any future note types
// requiring 8-byte alignment also happen to have an 8-byte aligned header+name
// and descriptor (but hopefully no one ever adds an 8-byte aligned note again).
size_t parse_gnu_build_id_from_note(const void *note, size_t note_size,
				    unsigned int align, bool bswap,
				    const void **ret)
{
	const char *p = note;
	const char *end = p + note_size;
	// Elf64_Nhdr is the same as Elf32_Nhdr.
	Elf32_Nhdr nhdr;
	while (end - p >= sizeof(nhdr)) {
#define ALIGN_NOTE() do {							\
		size_t to_align = (size_t)-(p - (char *)note) & (align - 1);	\
		if (to_align > end - p)						\
			break;							\
		p += to_align;							\
} while (0)

		memcpy(&nhdr, p, sizeof(nhdr));
		if (bswap) {
			nhdr.n_namesz = bswap_32(nhdr.n_namesz);
			nhdr.n_descsz = bswap_32(nhdr.n_descsz);
			nhdr.n_type = bswap_32(nhdr.n_type);
		}
		p += sizeof(nhdr);

		if (nhdr.n_namesz > end - p)
			break;
		const char *name = p;
		p += nhdr.n_namesz;
		ALIGN_NOTE();

		if (nhdr.n_namesz == sizeof("GNU") &&
		    memcmp(name, "GNU", sizeof("GNU")) == 0 &&
		    nhdr.n_type == NT_GNU_BUILD_ID &&
		    nhdr.n_descsz > 0) {
			if (nhdr.n_descsz > end - p)
				break;
			*ret = p;
			return nhdr.n_descsz;
		}

		p += nhdr.n_descsz;
		ALIGN_NOTE();

#undef ALIGN_NOTE
	}
	*ret = NULL;
	return 0;
}

struct drgn_error *find_elf_note(Elf *elf, const char *name, uint32_t type,
				 const void **ret, size_t *size_ret)
{
	size_t phnum;
	if (elf_getphdrnum(elf, &phnum) != 0)
		return drgn_error_libelf();
	size_t name_size = strlen(name) + 1;
	for (size_t i = 0; i < phnum; i++) {
		GElf_Phdr phdr_mem, *phdr = gelf_getphdr(elf, i, &phdr_mem);
		if (!phdr)
			return drgn_error_libelf();
		if (phdr->p_type != PT_NOTE)
			continue;
		Elf_Data *data = elf_getdata_rawchunk(elf, phdr->p_offset,
						      phdr->p_filesz,
						      note_header_type(phdr->p_align));
		if (!data)
			return drgn_error_libelf();
		GElf_Nhdr nhdr;
		size_t offset = 0, name_offset, desc_offset;
		while (offset < data->d_size &&
		       (offset = gelf_getnote(data, offset, &nhdr,
					      &name_offset,
					      &desc_offset))) {
			const char *note_name = (char *)data->d_buf + name_offset;
			if (nhdr.n_namesz == name_size &&
			    memcmp(note_name, name, name_size) == 0 &&
			    nhdr.n_type == type) {
				*ret = (char *)data->d_buf + desc_offset;
				*size_ret = nhdr.n_descsz;
				return NULL;
			}
		}
	}
	*ret = NULL;
	*size_ret = 0;
	return NULL;
}

static struct drgn_error *
userspace_loaded_module_iterator_read_ehdr(struct userspace_loaded_module_iterator *it,
					   uint64_t address, GElf_Ehdr *ret)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;

	err = drgn_program_read_memory(prog, ret, address, sizeof(*ret), false);
	if (err && err->code == DRGN_ERROR_FAULT) {
		drgn_log_notice(prog,
				"couldn't read ELF header at 0x%" PRIx64 ": %s\n",
				err->address, err->message);
		drgn_error_destroy(err);
		return &drgn_not_found;
	} else if (err) {
		return err;
	}
	if (memcmp(ret->e_ident, ELFMAG, SELFMAG) != 0) {
		drgn_log_debug(prog, "invalid ELF header magic\n");
		return &drgn_not_found;
	}
	if (ret->e_ident[EI_CLASS] !=
	    (drgn_platform_is_64_bit(&prog->platform)
	     ? ELFCLASS64 : ELFCLASS32)) {
		drgn_log_debug(prog,
			       "ELF header class (%u) does not match program\n",
			       ret->e_ident[EI_CLASS]);
		return &drgn_not_found;
	}
	if (ret->e_ident[EI_DATA] !=
	    (drgn_platform_is_little_endian(&prog->platform)
	     ? ELFDATA2LSB : ELFDATA2MSB)) {
		drgn_log_debug(prog,
			       "ELF header data encoding (%u) does not match program\n",
			       ret->e_ident[EI_DATA]);
		return &drgn_not_found;
	}
#define visit_elf_ehdr_members(visit_scalar_member, visit_raw_member) do {	\
	visit_raw_member(e_ident);						\
	visit_scalar_member(e_type);						\
	visit_scalar_member(e_machine);						\
	visit_scalar_member(e_version);						\
	visit_scalar_member(e_entry);						\
	visit_scalar_member(e_phoff);						\
	visit_scalar_member(e_shoff);						\
	visit_scalar_member(e_flags);						\
	visit_scalar_member(e_ehsize);						\
	visit_scalar_member(e_phentsize);					\
	visit_scalar_member(e_phnum);						\
	visit_scalar_member(e_shentsize);					\
	visit_scalar_member(e_shnum);						\
	visit_scalar_member(e_shstrndx);					\
} while (0)
	to_struct64(ret, Elf32_Ehdr, visit_elf_ehdr_members,
		    drgn_platform_is_64_bit(&prog->platform),
		    drgn_platform_bswap(&prog->platform));
#undef visit_elf_ehdr_members
	if (ret->e_phentsize !=
	    (drgn_platform_is_64_bit(&prog->platform)
	     ? sizeof(Elf64_Phdr) : sizeof(Elf32_Phdr))) {
		drgn_log_debug(prog,
			       "ELF program header entry size (%u) does not match class\n",
			       ret->e_phentsize);
		return &drgn_not_found;
	}
	return NULL;
}

static struct drgn_error *
userspace_loaded_module_iterator_read_phdrs(struct userspace_loaded_module_iterator *it,
					    uint64_t address, uint16_t phnum)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;
	uint32_t phentsize =
		(drgn_platform_is_64_bit(&prog->platform)
		 ? sizeof(Elf64_Phdr) : sizeof(Elf32_Phdr));
	uint32_t phdrs_size = (uint32_t)phnum * phentsize;
	if (phdrs_size > MAX_MEMORY_READ_FOR_DEBUG_INFO) {
		drgn_log_debug(prog,
			       "program header table is unreasonably large (%" PRIu32 " bytes); ignoring\n",
			       phdrs_size);
		return &drgn_not_found;
	}
	if (!alloc_or_reuse(&it->phdrs_buf, &it->phdrs_buf_capacity,
			    phdrs_size))
		return &drgn_enomem;
	err = drgn_program_read_memory(prog, it->phdrs_buf, address, phdrs_size,
				       false);
	if (err && err->code == DRGN_ERROR_FAULT) {
		drgn_log_debug(prog,
			       "couldn't read program header table from at 0x%" PRIx64 ": %s\n",
			       err->address, err->message);
		drgn_error_destroy(err);
		return &drgn_not_found;
	}
	return err;
}

static void
userspace_loaded_module_iterator_phdr(struct userspace_loaded_module_iterator *it,
				      size_t i, GElf_Phdr *ret)
{
	struct drgn_program *prog = it->it.prog;
	size_t phentsize =
		(drgn_platform_is_64_bit(&prog->platform)
		 ? sizeof(Elf64_Phdr) : sizeof(Elf32_Phdr));
#define visit_phdr_members(visit_scalar_member, visit_raw_member) do {	\
	visit_scalar_member(p_type);					\
	visit_scalar_member(p_flags);					\
	visit_scalar_member(p_offset);					\
	visit_scalar_member(p_vaddr);					\
	visit_scalar_member(p_paddr);					\
	visit_scalar_member(p_filesz);					\
	visit_scalar_member(p_memsz);					\
	visit_scalar_member(p_align);					\
} while (0)
	copy_struct64(ret,
		      (char *)it->phdrs_buf + i * phentsize,
		      Elf32_Phdr, visit_phdr_members,
		      drgn_platform_is_64_bit(&prog->platform),
		      drgn_platform_bswap(&prog->platform));
#undef visit_phdr_members
}

static struct drgn_error *
userspace_loaded_module_iterator_read_dynamic(struct userspace_loaded_module_iterator *it,
					      uint64_t address, uint64_t size,
					      size_t *num_dyn_ret)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;

	if (size > MAX_MEMORY_READ_FOR_DEBUG_INFO) {
		drgn_log_debug(prog,
			       "dynamic section is unreasonably large (%" PRIu64 " bytes); ignoring\n",
			       size);
		return &drgn_not_found;
	}
	size_t dyn_size =
		(drgn_platform_is_64_bit(&prog->platform)
		 ? sizeof(Elf64_Dyn) : sizeof(Elf32_Dyn));
	uint64_t num_dyn = size / dyn_size;
	*num_dyn_ret = num_dyn;
	if (num_dyn == 0)
		return NULL;

	if (!alloc_or_reuse(&it->segment_buf, &it->segment_buf_capacity,
			    num_dyn * dyn_size))
		return &drgn_enomem;
	err = drgn_program_read_memory(prog, it->segment_buf, address,
				       num_dyn * dyn_size, false);
	if (err && err->code == DRGN_ERROR_FAULT) {
		drgn_log_debug(prog,
			       "couldn't read dynamic section at 0x%" PRIx64 ": %s",
			       err->address, err->message);
		drgn_error_destroy(err);
		return &drgn_not_found;
	}
	return err;
}

static void
userspace_loaded_module_iterator_dyn(struct userspace_loaded_module_iterator *it,
				     size_t i, GElf_Dyn *ret)
{
	struct drgn_program *prog = it->it.prog;
	size_t dyn_size =
		(drgn_platform_is_64_bit(&prog->platform)
		 ? sizeof(Elf64_Dyn) : sizeof(Elf32_Dyn));
#define visit_elf_dyn_members(visit_scalar_member, visit_raw_member) do {	\
	visit_scalar_member(d_tag);						\
	visit_scalar_member(d_un.d_val);					\
} while (0)
	copy_struct64(ret, (char *)it->segment_buf + i * dyn_size, Elf32_Dyn,
		      visit_elf_dyn_members,
		      drgn_platform_is_64_bit(&prog->platform),
		      drgn_platform_bswap(&prog->platform));
#undef visit_elf_dyn_members
}

static struct drgn_error *
userspace_loaded_module_iterator_read_main_phdrs(struct userspace_loaded_module_iterator *it)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;

	drgn_log_debug(prog, "reading program header table from AT_PHDR\n");

	err = userspace_loaded_module_iterator_read_phdrs(it,
							  prog->auxv.at_phdr,
							  prog->auxv.at_phnum);
	if (err == &drgn_not_found)
		return NULL;
	else if (err)
		return err;

	bool have_pt_phdr = false;
	for (uint16_t i = 0; i < prog->auxv.at_phnum; i++) {
		GElf_Phdr phdr;
		userspace_loaded_module_iterator_phdr(it, i, &phdr);
		if (phdr.p_type == PT_PHDR) {
			drgn_log_debug(prog,
				      "found PT_PHDR with p_vaddr 0x%" PRIx64 "\n",
				      phdr.p_vaddr);
			have_pt_phdr = true;
			it->main_bias = prog->auxv.at_phdr - phdr.p_vaddr;
		} else if (phdr.p_type == PT_DYNAMIC) {
			drgn_log_debug(prog,
				       "found PT_DYNAMIC with p_vaddr 0x%" PRIx64
				       " and p_memsz 0x%" PRIx64 "\n",
				       phdr.p_vaddr, phdr.p_memsz);
			it->have_main_dyn = true;
			it->main_dyn_vaddr = phdr.p_vaddr;
			it->main_dyn_memsz = phdr.p_memsz;
		}
	}
	if (have_pt_phdr) {
		drgn_log_debug(prog, "main bias is 0x%" PRIx64 "\n",
			       it->main_bias);
	} else {
		drgn_log_debug(prog,
			       "didn't find PT_PHDR program header; assuming main bias is 0\n");
	}
	if (it->have_main_dyn) {
		it->main_dyn_vaddr += it->main_bias;
		drgn_log_debug(prog,
			       "main dynamic section is at 0x%" PRIx64 "\n",
			       it->main_dyn_vaddr);
	} else {
		drgn_log_debug(prog,
			       "didn't find PT_DYNAMIC program header; probably statically linked\n");
	}
	it->read_main_phdrs = true;
	return NULL;
}

static struct drgn_error *
identify_module_from_phdrs(struct userspace_loaded_module_iterator *it,
			   struct drgn_module *module, size_t phnum,
			   uint64_t bias)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;

	uint64_t start = UINT64_MAX, end = 0;
	for (size_t i = 0; i < phnum; i++) {
		GElf_Phdr phdr;
		userspace_loaded_module_iterator_phdr(it, i, &phdr);
		// The ELF specification says that "loadable segment entries in
		// the program header table appear in ascending order, sorted on
		// the p_vaddr member." However, as of Linux kernel commit
		// 10b19249192a ("ELF: fix overflow in total mapping size
		// calculation") (in v5.18), the Linux kernel doesn't enforce
		// this, and it's easy for us not to assume.
		if (phdr.p_type == PT_LOAD) {
			uint64_t segment_start = phdr.p_vaddr + bias;
			uint64_t segment_end = segment_start + phdr.p_memsz;
			if (segment_start < segment_end) {
				if (segment_start < start)
					start = segment_start;
				if (segment_end > end)
					end = segment_end;
			}
		} else if (phdr.p_type == PT_NOTE
			   && module->build_id_len == 0) {
			uint64_t note_size = min(phdr.p_filesz, phdr.p_memsz);
			if (!note_size)
				continue;
			if (note_size > MAX_MEMORY_READ_FOR_DEBUG_INFO) {
				drgn_log_debug(prog,
					       "note is unreasonably large (%" PRIu64 " bytes); ignoring\n",
					       note_size);
				continue;
			}
			if (!alloc_or_reuse(&it->segment_buf,
					    &it->segment_buf_capacity,
					    note_size))
				return &drgn_enomem;
			err = drgn_program_read_memory(prog, it->segment_buf,
						       phdr.p_vaddr + bias,
						       note_size, false);
			if (err && err->code == DRGN_ERROR_FAULT) {
				drgn_log_debug(prog,
					       "couldn't read note at 0x%" PRIx64 ": %s"
					       "; ignoring\n",
					       err->address, err->message);
				drgn_error_destroy(err);
				continue;
			} else if (err) {
				return err;
			}
			const void *build_id;
			size_t build_id_len =
				parse_gnu_build_id_from_note(it->segment_buf,
							     note_size,
							     phdr.p_align == 8 ?
							     8 : 4,
							     drgn_platform_bswap(&prog->platform),
							     &build_id);
			if (build_id_len > 0) {
				err = drgn_module_set_build_id(module, build_id,
							       build_id_len);
				if (err)
					return err;
				drgn_log_debug(prog,
					       "found build ID %s in note at 0x%" PRIx64 "\n",
					       module->build_id_str,
					       phdr.p_vaddr + bias
					       + (build_id - it->segment_buf));
			}
		}
	}
	if (module->build_id_len == 0) {
		drgn_log_debug(prog,
			       "couldn't find build ID from mapped program headers\n");
	}
	if (start < end) {
		err = drgn_module_set_address_range(module, start, end);
		if (err)
			return err;
		drgn_log_debug(prog,
			       "got address range 0x%" PRIx64 "-0x%" PRIx64 " from mapped program headers\n",
			       start, end);
	} else {
		drgn_log_debug(prog,
			       "couldn't find address range from mapped program headers\n");
	}
	return NULL;
}

static struct drgn_error *
userspace_loaded_module_iterator_yield_main(struct userspace_loaded_module_iterator *it,
					    struct drgn_module **ret)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;

	struct drgn_mapped_file *file = find_mapped_file(it,
							 prog->auxv.at_phdr);
	if (!file) {
		drgn_log_debug(prog,
			       "couldn't find mapped file containing AT_PHDR\n");
	}

	bool new;
	err = drgn_module_find_or_create_main(prog, file ? file->path : "", ret,
					      &new);
	if (err || !new)
		return err;
	err = userspace_loaded_module_iterator_read_main_phdrs(it);
	if (err)
		goto delete_module;
	if (it->read_main_phdrs) {
		err = identify_module_from_phdrs(it, *ret, prog->auxv.at_phnum,
						 it->main_bias);
		if (err)
			goto delete_module;
	}
	return NULL;

delete_module:
	drgn_module_delete(*ret);
	return err;
}

static struct drgn_error *
userspace_loaded_module_iterator_yield_vdso(struct userspace_loaded_module_iterator *it,
					    struct drgn_module **ret)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;

	if (!prog->auxv.at_sysinfo_ehdr) {
		drgn_log_debug(prog, "no vDSO\n");
		goto not_found;
	}

	drgn_log_debug(prog, "reading vDSO ELF header from AT_SYSINFO_EHDR\n");
	GElf_Ehdr ehdr;
	err = userspace_loaded_module_iterator_read_ehdr(it,
							 prog->auxv.at_sysinfo_ehdr,
							 &ehdr);
	if (err == &drgn_not_found)
		goto not_found;
	else if (err)
		return err;

	drgn_log_info(prog,
		      "reading %" PRIu16 " program headers at 0x%" PRIx64 "\n",
		      ehdr.e_phnum, prog->auxv.at_sysinfo_ehdr + ehdr.e_phoff);

	// It is effectively part of the ABI that the vDSO program headers are
	// mapped at AT_SYSINFO_EHDR + e_phoff (see the Linux kernel's reference
	// vDSO parser: vdso_init_from_sysinfo_ehdr() in
	// tools/testing/selftests/vDSO/parse_vdso.c, glibc: setup_vdso() in
	// elf/setup-vdso.h, and musl: __vdsosym() in src/internal/vdso.c).
	err = userspace_loaded_module_iterator_read_phdrs(it,
							  prog->auxv.at_sysinfo_ehdr + ehdr.e_phoff,
							  ehdr.e_phnum);
	if (err == &drgn_not_found)
		goto not_found;
	else if (err)
		return err;

	// This is based on the reference vDSO parser.
	uint64_t bias = prog->auxv.at_sysinfo_ehdr;
	uint64_t dyn_vaddr = 0, dyn_memsz = 0;
	bool have_load = false;
	for (size_t i = 0; i < ehdr.e_phnum; i++) {
		GElf_Phdr phdr;
		userspace_loaded_module_iterator_phdr(it, i, &phdr);
		if (phdr.p_type == PT_LOAD && !have_load) {
			drgn_log_debug(prog,
				       "found PT_LOAD with p_offset 0x%" PRIx64
				       " and p_vaddr 0x%" PRIx64 "\n",
				       phdr.p_offset, phdr.p_vaddr);
			have_load = true;
			bias = prog->auxv.at_sysinfo_ehdr + phdr.p_offset - phdr.p_vaddr;
		} else if (phdr.p_type == PT_DYNAMIC) {
			drgn_log_debug(prog,
				       "found PT_DYNAMIC with p_offset 0x%" PRIx64
				       " and p_memsz 0x%" PRIx64 "\n",
				       phdr.p_offset, phdr.p_memsz);
			dyn_vaddr = prog->auxv.at_sysinfo_ehdr + phdr.p_offset;
			dyn_memsz = phdr.p_memsz;
		}
	}
	if (!have_load) {
		drgn_log_notice(prog,
				"didn't find PT_LOAD program header for vDSO; ignoring\n");
		goto not_found;
	}
	drgn_log_debug(prog, "vDSO bias is 0x%" PRIx64 "\n", bias);
	if (!dyn_vaddr) {
		drgn_log_notice(prog,
				"didn't find valid PT_DYNAMIC program header for vDSO; ignoring\n");
		goto not_found;
	}
	it->vdso_dyn_vaddr = dyn_vaddr;
	it->have_vdso_dyn = true;

	drgn_log_debug(prog, "reading vDSO dynamic section at 0x%" PRIx64 "\n",
		       dyn_vaddr);
	size_t num_dyn;
	err = userspace_loaded_module_iterator_read_dynamic(it, dyn_vaddr,
							    dyn_memsz,
							    &num_dyn);
	if (err == &drgn_not_found)
		goto not_found;
	else if (err)
		return err;

	uint64_t dt_strtab = 0, dt_soname = 0;
	for (size_t i = 0; i < num_dyn; i++) {
		GElf_Dyn dyn;
		userspace_loaded_module_iterator_dyn(it, i, &dyn);
		if (dyn.d_tag == DT_STRTAB) {
			dt_strtab = dyn.d_un.d_ptr;
			drgn_log_debug(prog, "found DT_STRTAB 0x%" PRIx64 "\n",
				       dt_strtab);
		} else if (dyn.d_tag == DT_SONAME) {
			dt_soname = dyn.d_un.d_val;
			drgn_log_debug(prog, "found DT_SONAME 0x%" PRIx64 "\n",
				       dt_soname);
		} else if (dyn.d_tag == DT_NULL) {
			break;
		}
	}
	if (!dt_strtab || !dt_soname) {
		drgn_log_notice(prog,
				"didn't find valid %s%s%s for vDSO; skipping\n",
				dt_strtab ? "" : "DT_STRTAB",
				dt_strtab || dt_soname ? "" : " or ",
				dt_soname ? "" : "DT_SONAME");
		goto not_found;
	}

	char *name;
	err = drgn_program_read_c_string(prog, dt_strtab + bias + dt_soname,
					 false, SIZE_MAX, &name);
	if (err && err->code == DRGN_ERROR_FAULT) {
		drgn_log_notice(prog,
				"couldn't read vDSO soname at 0x%" PRIx64 ": %s"
				"; skipping\n",
				err->address, err->message);
		drgn_error_destroy(err);
		goto not_found;
	} else if (err) {
		return err;
	}
	drgn_log_debug(prog, "read vDSO soname \"%s\"\n", name);

	bool new;
	err = drgn_module_find_or_create_vdso(prog, name, dyn_vaddr, ret, &new);
	free(name);
	if (err || !new)
		return err;

	err = identify_module_from_phdrs(it, *ret, ehdr.e_phnum, bias);
	if (err)
		drgn_module_delete(*ret);
	return err;

not_found:
	*ret = NULL;
	return NULL;
}

static struct drgn_error *
userspace_get_link_map(struct userspace_loaded_module_iterator *it)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;

	if (!it->read_main_phdrs) {
		err = userspace_loaded_module_iterator_read_main_phdrs(it);
		if (err)
			return err;
	}
	if (!it->have_main_dyn)
		return NULL;

	drgn_log_debug(prog, "reading main dynamic section\n");
	size_t num_dyn;
	err = userspace_loaded_module_iterator_read_dynamic(it,
							    it->main_dyn_vaddr,
							    it->main_dyn_memsz,
							    &num_dyn);
	if (err == &drgn_not_found) {
		drgn_log_notice(prog,
				"couldn't read main dynamic section"
				"; can't iterate shared libraries\n");
		return NULL;
	} else if (err) {
		return err;
	}

	GElf_Dyn dyn;
	size_t i;
	for (i = 0; i < num_dyn; i++) {
		userspace_loaded_module_iterator_dyn(it, i, &dyn);
		if (dyn.d_tag == DT_NULL) {
			i = num_dyn;
			break;
		}
		if (dyn.d_tag == DT_DEBUG) {
			drgn_log_debug(prog, "found DT_DEBUG 0x%" PRIx64 "\n",
				       dyn.d_un.d_ptr);
			break;
		}
	}
	if (i >= num_dyn) {
		drgn_log_notice(prog,
				"didn't find main DT_DEBUG entry"
				"; can't iterate shared libraries\n");
		return NULL;
	}

	struct drgn_r_debug {
		int32_t r_version;
		alignas(8) uint64_t r_map;
	} r_debug;
	struct drgn_r_debug32 {
		int32_t r_version;
		uint32_t r_map;
	};
#define visit_r_debug_members(visit_scalar_member, visit_raw_member) do {	\
	visit_scalar_member(r_version);						\
	visit_scalar_member(r_map);						\
} while (0)
	err = read_struct64(prog, &r_debug, dyn.d_un.d_ptr, 1,
			    struct drgn_r_debug32, visit_r_debug_members);
#undef visit_r_debug_members
	if (err && err->code == DRGN_ERROR_FAULT) {
		drgn_log_notice(prog,
				"couldn't read r_debug at 0x%" PRIx64 ": %s"
				"; can't iterate shared libraries\n",
				err->address, err->message);
		drgn_error_destroy(err);
		return NULL;
	} else if (err) {
		return err;
	}
	drgn_log_debug(prog,
		       "read r_debug = { .r_version = %" PRId32 ", .r_map = 0x%" PRIx64 " }\n",
		       r_debug.r_version, r_debug.r_map);

	if (r_debug.r_version < 1) {
		drgn_log_notice(prog,
				"invalid r_debug.r_version %" PRId32
				"; can't iterate shared libraries\n",
				r_debug.r_version);
		return NULL;
	}
	it->link_map = r_debug.r_map;
	return NULL;
}

static struct drgn_error *
identify_module_from_link_map(struct userspace_loaded_module_iterator *it,
			      struct drgn_module *module,
			      struct drgn_mapped_file *file, uint64_t l_addr)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;

	// Even if it is a 32-bit file, segments should be at least a page, so
	// we should be able to read the 64-bit size.
	if (file->offset0_size < sizeof(Elf64_Ehdr)) {
		drgn_log_debug(prog, "didn't find mapped ELF header\n");
		return NULL;
	}

	drgn_log_debug(prog, "reading ELF header at 0x%" PRIx64 "\n",
		       file->offset0_vaddr);
	GElf_Ehdr ehdr;
	err = userspace_loaded_module_iterator_read_ehdr(it,
							 file->offset0_vaddr,
							 &ehdr);
	if (err == &drgn_not_found)
		return NULL;
	else if (err)
		return err;

	drgn_log_debug(prog,
		       "reading %" PRIu16 " program headers from 0x%" PRIx64 "\n",
		       ehdr.e_phnum, file->offset0_vaddr + ehdr.e_phoff);
	// e_phnum and e_phentsize are uint16_t, so this can't overflow.
	uint32_t phdrs_size =
		(uint32_t)ehdr.e_phnum * (uint32_t)ehdr.e_phentsize;
	if (ehdr.e_phoff > file->offset0_size ||
	    phdrs_size > file->offset0_size - ehdr.e_phoff) {
		drgn_log_debug(prog,
			       "program header table is not mapped with ELF header\n");
		return NULL;
	}
	err = userspace_loaded_module_iterator_read_phdrs(it,
							  file->offset0_vaddr + ehdr.e_phoff,
							  ehdr.e_phnum);
	if (err == &drgn_not_found)
		return NULL;
	else if (err)
		return err;

	return identify_module_from_phdrs(it, module, ehdr.e_phnum, l_addr);
}

// This is the public definition of struct link_map from glibc's link.h:
//
// struct link_map
//   {
//     /* These first few members are part of the protocol with the debugger.
//        This is the same format used in SVR4.  */
//
//     ElfW(Addr) l_addr;          /* Difference between the address in the ELF
//                                    file and the addresses in memory.  */
//     char *l_name;               /* Absolute file name object was found in.  */
//     ElfW(Dyn) *l_ld;            /* Dynamic section of the shared object.  */
//     struct link_map *l_next, *l_prev; /* Chain of loaded objects.  */
//   };
//
// We don't need l_prev, so we exclude it from our definition.
struct drgn_link_map {
	uint64_t l_addr;
	uint64_t l_name;
	uint64_t l_ld;
	uint64_t l_next;
};
struct drgn_link_map32 {
	uint32_t l_addr;
	uint32_t l_name;
	uint32_t l_ld;
	uint32_t l_next;
};

static struct drgn_error *
userspace_next_link_map(struct userspace_loaded_module_iterator *it,
			struct drgn_link_map *ret, char **name_ret)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;

	if (!it->link_map)
		return &drgn_stop;

	if (it->state
	    >= USERSPACE_LOADED_MODULE_ITERATOR_STATE_LINK_MAP
	    + MAX_LINK_MAP_LIST_ITERATIONS) {
		drgn_log_notice(prog,
				"too many entries or cycle in link_map list; "
				"can't iterate remaining shared libraries\n");
		return &drgn_stop;
	}
	it->state++;

#define visit_link_map_members(visit_scalar_member, visit_raw_member) do {	\
	visit_scalar_member(l_addr);						\
	visit_scalar_member(l_name);						\
	visit_scalar_member(l_ld);						\
	visit_scalar_member(l_next);						\
} while (0)
	err = read_struct64(prog, ret, it->link_map, 1, struct drgn_link_map32,
			    visit_link_map_members);
#undef visit_link_map_members
	if (err && err->code == DRGN_ERROR_FAULT) {
		drgn_log_notice(prog,
				"couldn't read next link_map at 0x%" PRIx64 ": %s"
				"; can't iterate remaining shared libraries\n",
				err->address, err->message);
		drgn_error_destroy(err);
		return &drgn_stop;
	} else if (err) {
		return err;
	}

	it->link_map = ret->l_next;

	err = drgn_program_read_c_string(prog, ret->l_name, false, SIZE_MAX,
					 name_ret);
	if (err && err->code == DRGN_ERROR_FAULT)
		*name_ret = NULL;
	else if (err)
		return err;
	drgn_log_debug(prog,
		       "read link_map = { .l_addr = 0x%" PRIx64 ", .l_name = 0x%" PRIx64 "%s%s%s, .l_ld = 0x%" PRIx64 ", .l_next = 0x%" PRIx64 " }\n",
		       ret->l_addr, ret->l_name, *name_ret ? " = \"" : "",
		       *name_ret ? *name_ret : "", *name_ret ? "\"" : "",
		       ret->l_ld, ret->l_next);
	if (err) {
		drgn_log_debug(prog,
			       "couldn't read l_name at 0x%" PRIx64 ": %s"
			       "; skipping\n",
			       err->address, err->message);
		drgn_error_destroy(err);
	}
	return NULL;
}

static struct drgn_error *
yield_from_link_map(struct userspace_loaded_module_iterator *it,
		    struct drgn_module **ret)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->it.prog;

	struct drgn_link_map link_map;
	char *name;
	while (!(err = userspace_next_link_map(it, &link_map, &name))) {
		if (link_map.l_ld == it->main_dyn_vaddr ||
		    (it->have_vdso_dyn && link_map.l_ld == it->vdso_dyn_vaddr)) {
			free(name);
			drgn_log_debug(prog,
				       "l_ld matches %s dynamic section; skipping\n",
				       link_map.l_ld == it->main_dyn_vaddr
				       ? "main" : "vDSO");
			continue;
		}
		if (!name)
			continue;

		bool new;
		err = drgn_module_find_or_create_shared_library(prog, name,
								link_map.l_ld,
								ret, &new);
		if (err || !new)
			return err;

		struct drgn_mapped_file *file =
			find_mapped_file(it, link_map.l_ld);
		if (file) {
			err = identify_module_from_link_map(it, *ret, file,
							    link_map.l_addr);
			if (err) {
				drgn_module_delete(*ret);
				return err;
			}
		} else {
			drgn_log_debug(prog,
				       "couldn't find mapped file containing l_ld\n");
		}
		return NULL;
	}
	if (err == &drgn_stop) {
		*ret = NULL;
		return NULL;
	}
	return err;
}

static struct drgn_error *
userspace_loaded_module_iterator_next(struct drgn_module_iterator *_it,
				      struct drgn_module **ret)
{
	struct drgn_error *err;
	struct userspace_loaded_module_iterator *it =
		container_of(_it, struct userspace_loaded_module_iterator, it);
	switch (it->state) {
	case USERSPACE_LOADED_MODULE_ITERATOR_STATE_MAIN:
		err = drgn_program_cache_auxv(it->it.prog);
		if (err)
			return err;
		it->state = USERSPACE_LOADED_MODULE_ITERATOR_STATE_VDSO;
		return userspace_loaded_module_iterator_yield_main(it, ret);
	case USERSPACE_LOADED_MODULE_ITERATOR_STATE_VDSO:
		it->state = USERSPACE_LOADED_MODULE_ITERATOR_STATE_R_DEBUG;
		err = userspace_loaded_module_iterator_yield_vdso(it, ret);
		if (err || *ret)
			return err;
		// fallthrough
	case USERSPACE_LOADED_MODULE_ITERATOR_STATE_R_DEBUG:
		it->state = USERSPACE_LOADED_MODULE_ITERATOR_STATE_LINK_MAP;
		err = userspace_get_link_map(it);
		if (err)
			return err;
		// fallthrough
	default:
		return yield_from_link_map(it, ret);
	}
}

struct process_mapped_file_entry {
	dev_t dev;
	ino_t ino;
	struct drgn_mapped_file *file;
};

struct process_mapped_file_key {
	dev_t dev;
	ino_t ino;
	const char *path;
};

static struct process_mapped_file_key
process_mapped_file_entry_to_key(const struct process_mapped_file_entry *entry)
{
	return (struct process_mapped_file_key){
		.dev = entry->dev,
		.ino = entry->ino,
		.path = entry->file->path,
	};
}

static struct hash_pair
process_mapped_file_key_hash_pair(const struct process_mapped_file_key *key)
{
	size_t hash = hash_combine(key->dev, key->ino);
	hash = hash_combine(hash, hash_c_string(key->path));
	return hash_pair_from_avalanching_hash(hash);
}

static bool process_mapped_file_key_eq(const struct process_mapped_file_key *a,
				       const struct process_mapped_file_key *b)
{
	return (a->dev == b->dev
		&& a->ino == b->ino
		&& strcmp(a->path, b->path) == 0);
}

DEFINE_HASH_TABLE(process_mapped_files, struct process_mapped_file_entry,
		  process_mapped_file_entry_to_key,
		  process_mapped_file_key_hash_pair, process_mapped_file_key_eq)

struct process_loaded_module_iterator {
	struct userspace_loaded_module_iterator u;
	struct process_mapped_files files;
};

static struct drgn_error *
process_add_mapping(struct process_loaded_module_iterator *it,
		    const char *maps_path, const char *map_files_path,
		    int map_files_fd, bool *logged_readlink_eperm,
		    bool *logged_stat_eperm,
		    struct drgn_mapped_file_ranges *ranges, char *line,
		    size_t line_len)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->u.it.prog;

	uint64_t segment_start, segment_end, segment_file_offset;
	unsigned int dev_major, dev_minor;
	uint64_t ino;
	int map_name_len, path_index;
	if (sscanf(line,
		   "%" PRIx64 "-%" PRIx64 "%n %*s %" PRIx64 " %x:%x %" PRIu64 " %n",
		   &segment_start, &segment_end, &map_name_len,
		   &segment_file_offset, &dev_major, &dev_minor, &ino,
		   &path_index) != 6) {
		return drgn_error_format(DRGN_ERROR_OTHER, "couldn't parse %s",
					 maps_path);
	}
	// Skip anonymous mappings.
	if (ino == 0)
		return NULL;

	struct process_mapped_file_key key = {
		.dev = makedev(dev_major, dev_minor),
		.ino = ino,
		.path = line + path_index,
	};
	char *real_path = NULL;

	// /proc/$pid/maps has a couple of ambiguities that
	// /proc/$pid/map_files/<address> can help with:
	//
	// 1. Newlines in the file path from /proc/$pid/maps are escaped as
	//    \012. However, \ is not escaped, so it is ambiguous whether \012
	//    is a newline or appeared literally in the path. We can read the
	//    map_files link to get the unescaped path.
	// 2. The device number in /proc/$pid/maps is incorrect for some
	//    filesystems. Specifically, for Btrfs as of Linux 6.0, it refers to
	//    a filesystem-wide device number rather than the subvolume-specific
	//    device numbers returned by stat. We can stat the map_files link to
	//    get the correct device number.
	if (map_files_fd >= 0) {
		line[map_name_len] = '\0';

		// The escaped path must be at least as long as the original
		// path, so use that as the readlink buffer size.
		size_t bufsiz = line_len - path_index + 1;
		real_path = malloc(bufsiz);
		if (!real_path)
			return &drgn_enomem;
		// Before Linux kernel commit bdb4d100afe9 ("procfs: always
		// expose /proc/<pid>/map_files/ and make it readable") (in
		// v4.3), reading these links required CAP_SYS_ADMIN. Since that
		// commit, it only requires PTRACE_MODE_READ, which we must have
		// since we opened /proc/$pid/maps.
		//
		// If we can't read this link, we have to fall back to the
		// escaped path. Newlines and the literal sequence \012 are
		// unlikely to appear in a path, so it's not a big deal.
		ssize_t r = readlinkat(map_files_fd, line, real_path, bufsiz);
		if (r < 0) {
			if (errno == EPERM) {
				free(real_path);
				real_path = NULL;
				if (!*logged_readlink_eperm) {
					drgn_log_debug(prog,
						       "don't have permission to read symlinks in %s\n",
						       map_files_path);
				}
				*logged_readlink_eperm = true;
			} else if (errno == ENOENT) {
				// We raced with a change to the mapping.
				drgn_log_debug(prog, "mapping %s disappeared\n",
					       line);
				err = NULL;
				goto out_real_path;
			} else {
				err = drgn_error_format_os("readlink", errno,
							   "%s/%s",
							   map_files_path,
							   line);
				goto out_real_path;
			}
		} else if (r == bufsiz) {
			// We didn't allocate enough for the link contents. The
			// only way this is possible is if we raced with the
			// mapping being replaced by a different path.
			drgn_log_debug(prog,
				       "mapping %s path changed; skipping\n",
				       line);
			err = NULL;
			goto out_real_path;
		} else {
			real_path[r] = '\0';
			key.path = real_path;
		}

		// Following these links requires CAP_SYS_ADMIN. If we can't, we
		// have to fall back to using the device number from
		// /proc/$pid/maps. Mapping files with the same path and inode
		// number in different Btrfs subvolumes is unlikely, so this is
		// also not a big deal.
		struct stat st;
		if (fstatat(map_files_fd, line, &st, 0) < 0) {
			if (errno == EPERM) {
				if (!*logged_stat_eperm) {
					drgn_log_debug(prog,
						       "don't have permission to follow symlinks in %s\n",
						       map_files_path);
				}
				*logged_stat_eperm = true;
			} else if (errno == ENOENT) {
				// We raced with a change to the mapping.
				drgn_log_debug(prog, "mapping %s disappeared\n",
					       line);
				err = NULL;
				goto out_real_path;
			} else {
				err = drgn_error_format_os("stat", errno,
							   "%s/%s",
							   map_files_path,
							   line);
				goto out_real_path;
			}
		} else {
			key.dev = st.st_dev;
		}
	}

	struct hash_pair hp = process_mapped_files_hash(&key);
	struct process_mapped_files_iterator files_it =
		process_mapped_files_search_hashed(&it->files, &key,
						   hp);
	if (!files_it.entry) {
		if (!real_path) {
			real_path = strdup(key.path);
			if (!real_path)
				return &drgn_enomem;
		}
		struct drgn_mapped_file *file =
			drgn_mapped_file_create(real_path);
		if (!file) {
			err = &drgn_enomem;
			goto out_real_path;
		}
		struct process_mapped_file_entry entry = {
			.dev = key.dev,
			.ino = key.ino,
			.file = file,
		};
		if (process_mapped_files_insert_searched(&it->files, &entry, hp,
							 &files_it) < 0) {
			drgn_mapped_file_destroy(file);
			err = &drgn_enomem;
			goto out_real_path;
		}
		// real_path is owned by the iterator now.
		real_path = NULL;
	}
	err = drgn_add_mapped_file_range(ranges, segment_start, segment_end,
					 segment_file_offset,
					 files_it.entry->file);
out_real_path:
	free(real_path);
	return err;
}

static struct drgn_error *
process_get_mapped_files(struct process_loaded_module_iterator *it)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->u.it.prog;

#define FORMAT "/proc/%ld/maps"
	char maps_path[sizeof(FORMAT)
		       - sizeof("%ld")
		       + max_decimal_length(long)
		       + 1];
	snprintf(maps_path, sizeof(maps_path), FORMAT, (long)prog->pid);
#undef FORMAT
	FILE *maps_file = fopen(maps_path, "r");
	if (!maps_file)
		return drgn_error_create_os("fopen", errno, maps_path);
	drgn_log_debug(prog, "parsing %s\n", maps_path);

#define FORMAT "/proc/%ld/map_files"
	char map_files_path[sizeof(FORMAT)
		            - sizeof("%ld")
			    + max_decimal_length(long)
			    + 1];
	snprintf(map_files_path, sizeof(map_files_path), FORMAT,
		 (long)prog->pid);
#undef FORMAT
	// Since Linux kernel commit bdb4d100afe9 ("procfs: always expose
	// /proc/<pid>/map_files/ and make it readable") (in v4.3),
	// /proc/$pid/map_files always exists. Before that, it only exists if
	// CONFIG_CHECKPOINT_RESTORE is enabled.
	//
	// If it exists, we should always have permission to open it since we
	// were able to open /proc/$pid/maps.
	int map_files_fd = open(map_files_path, O_RDONLY | O_DIRECTORY);
	if (map_files_fd < 0) {
		if (errno != ENOENT) {
			err = drgn_error_create_os("open", errno,
						   map_files_path);
			goto out_maps_file;
		}
		drgn_log_info(prog, "%s: %m\n", map_files_path);
	}

	char *line = NULL;
	size_t n = 0;
	bool logged_readlink_eperm = false, logged_stat_eperm = false;
	struct drgn_mapped_file_ranges ranges = DRGN_MAPPED_FILE_RANGES_INIT;
	for (;;) {
		errno = 0;
		ssize_t len;
		if ((len = getline(&line, &n, maps_file)) == -1) {
			if (errno) {
				err = drgn_error_create_os("getline", errno,
							   maps_path);
			} else {
				err = NULL;
			}
			break;
		}
		// Remove the newline.
		if (len > 0 && line[len - 1] == '\n')
			line[--len] = '\0';

		drgn_log_debug(prog, "read %s\n", line);
		err = process_add_mapping(it, maps_path, map_files_path,
					  map_files_fd, &logged_readlink_eperm,
					  &logged_stat_eperm, &ranges, line,
					  len);
		if (err)
			break;
	}
	if (err) {
		drgn_mapped_file_ranges_abort(&ranges);
	} else {
		userspace_loaded_module_iterator_set_file_ranges(&it->u,
								 &ranges);
	}

	free(line);
	if (map_files_fd >= 0)
		close(map_files_fd);
out_maps_file:
	fclose(maps_file);
	return err;
}

static void
process_loaded_module_iterator_destroy(struct drgn_module_iterator *_it)
{
	struct process_loaded_module_iterator *it =
		container_of(_it, struct process_loaded_module_iterator, u.it);
	for (struct process_mapped_files_iterator files_it =
	     process_mapped_files_first(&it->files);
	     files_it.entry; files_it = process_mapped_files_next(files_it)) {
		free((char *)files_it.entry->file->path);
		drgn_mapped_file_destroy(files_it.entry->file);
	}
	process_mapped_files_deinit(&it->files);
	userspace_loaded_module_iterator_deinit(&it->u);
	free(it);
}

static struct drgn_error *
process_loaded_module_iterator_create(struct drgn_program *prog,
				      struct drgn_module_iterator **ret)
{
	struct drgn_error *err;
	struct process_loaded_module_iterator *it = calloc(1, sizeof(*it));
	if (!it)
		return &drgn_enomem;
	drgn_module_iterator_init(&it->u.it, prog,
				  process_loaded_module_iterator_destroy,
				  userspace_loaded_module_iterator_next);
	process_mapped_files_init(&it->files);
	err = process_get_mapped_files(it);
	if (err) {
		process_loaded_module_iterator_destroy(&it->u.it);
		return err;
	}
	*ret = &it->u.it;
	return NULL;

}

static const char *core_mapped_file_entry_to_key(struct drgn_mapped_file * const *entry)
{
	return (*entry)->path;
}

DEFINE_HASH_TABLE(core_mapped_files, struct drgn_mapped_file *,
		  core_mapped_file_entry_to_key, c_string_key_hash_pair,
		  c_string_key_eq)

struct core_loaded_module_iterator {
	struct userspace_loaded_module_iterator u;
	struct core_mapped_files files;
};

static struct drgn_error *parse_nt_file_error(struct binary_buffer *bb,
					      const char *pos,
					      const char *message)
{
	return drgn_error_create(DRGN_ERROR_OTHER, "couldn't parse NT_FILE");
}

static struct drgn_error *
core_get_mapped_files(struct core_loaded_module_iterator *it)
{
	struct drgn_error *err;
	struct drgn_program *prog = it->u.it.prog;

	const void *note;
	size_t note_size;
	err = find_elf_note(prog->core, "CORE", NT_FILE, &note, &note_size);
	if (err)
		return err;
	if (!note) {
		drgn_log_debug(prog, "core doesn't have NT_FILE note\n");
		return NULL;
	}

	drgn_log_debug(prog, "parsing NT_FILE\n");

	bool is_64_bit = drgn_platform_is_64_bit(&prog->platform);
	bool little_endian = drgn_platform_is_little_endian(&prog->platform);

	struct binary_buffer bb;
	binary_buffer_init(&bb, note, note_size, little_endian,
			   parse_nt_file_error);

	// fs/binfmt_elf.c in the Linux kernel source code documents the format
	// of NT_FILE as:
	//
	// long count     -- how many files are mapped
	// long page_size -- units for file_ofs
	// array of [COUNT] elements of
	//   long start
	//   long end
	//   long file_ofs
	// followed by COUNT filenames in ASCII: "FILE1" NUL "FILE2" NUL...
	struct nt_file_segment64 {
		uint64_t start;
		uint64_t end;
		uint64_t file_offset;
	};
	struct nt_file_segment32 {
		uint32_t start;
		uint32_t end;
		uint32_t file_offset;
	};
	uint64_t count, page_size;
	if (is_64_bit) {
		if ((err = binary_buffer_next_u64(&bb, &count)))
			return err;
		if (count > UINT64_MAX / sizeof(struct nt_file_segment64))
			return binary_buffer_error(&bb, "count is too large");
		if ((err = binary_buffer_next_u64(&bb, &page_size)) ||
		    (err = binary_buffer_skip(&bb,
					      count * sizeof(struct nt_file_segment64))))
			return err;
	} else {
		if ((err = binary_buffer_next_u32_into_u64(&bb, &count)))
			return err;
		if (count > UINT64_MAX / sizeof(struct nt_file_segment32))
			return binary_buffer_error(&bb, "count is too large");
		if ((err = binary_buffer_next_u32_into_u64(&bb, &page_size)) ||
		    (err = binary_buffer_skip(&bb,
					      count * sizeof(struct nt_file_segment32))))
			return err;
	}

	struct drgn_mapped_file_ranges ranges = DRGN_MAPPED_FILE_RANGES_INIT;
	for (uint64_t i = 0; i < count; i++) {
		struct nt_file_segment64 segment;
#define visit_nt_file_segment_members(visit_scalar_member, visit_raw_member) do {	\
	visit_scalar_member(start);							\
	visit_scalar_member(end);							\
	visit_scalar_member(file_offset);						\
} while (0)
		copy_struct64(&segment,
			      (char *)note
			      + (is_64_bit
				 ? 16 + i * sizeof(struct nt_file_segment64)
				 : 8 + i * sizeof(struct nt_file_segment32)),
			      struct nt_file_segment32,
			      visit_nt_file_segment_members, is_64_bit,
			      bb.bswap);
#undef visit_nt_file_segment_members
		segment.file_offset *= page_size;
		const char *path = bb.pos;
		if ((err = binary_buffer_skip_string(&bb)))
			goto err;
		drgn_log_debug(prog,
			       "found 0x%" PRIx64 "-0x%" PRIx64 " 0x%" PRIx64 " %s\n",
			       segment.start, segment.end, segment.file_offset,
			       path);
		if (segment.start >= segment.end)
			continue;

		struct hash_pair hp = core_mapped_files_hash(&path);
		struct core_mapped_files_iterator files_it =
			core_mapped_files_search_hashed(&it->files, &path, hp);
		struct drgn_mapped_file *file;
		if (files_it.entry) {
			file = *files_it.entry;
		} else {
			file = drgn_mapped_file_create(path);
			if (!file) {
				err = &drgn_enomem;
				goto err;
			}
			if (core_mapped_files_insert_searched(&it->files, &file,
							      hp, NULL) < 0) {
				drgn_mapped_file_destroy(file);
				err = &drgn_enomem;
				goto err;
			}
		}
		err = drgn_add_mapped_file_range(&ranges, segment.start,
						 segment.end,
						 segment.file_offset, file);
		if (err)
			goto err;
	}
	userspace_loaded_module_iterator_set_file_ranges(&it->u, &ranges);
	return NULL;

err:
	drgn_mapped_file_ranges_abort(&ranges);
	return err;
}

static void
core_loaded_module_iterator_destroy(struct drgn_module_iterator *_it)
{
	struct core_loaded_module_iterator *it =
		container_of(_it, struct core_loaded_module_iterator, u.it);
	for (struct core_mapped_files_iterator files_it =
	     core_mapped_files_first(&it->files);
	     files_it.entry;
	     files_it = core_mapped_files_next(files_it))
		drgn_mapped_file_destroy(*files_it.entry);
	core_mapped_files_deinit(&it->files);
	userspace_loaded_module_iterator_deinit(&it->u);
	free(it);
}

static struct drgn_error *
core_loaded_module_iterator_create(struct drgn_program *prog,
				   struct drgn_module_iterator **ret)
{
	struct drgn_error *err;
	struct core_loaded_module_iterator *it = calloc(1, sizeof(*it));
	if (!it)
		return &drgn_enomem;
	drgn_module_iterator_init(&it->u.it, prog,
				  core_loaded_module_iterator_destroy,
				  userspace_loaded_module_iterator_next);
	core_mapped_files_init(&it->files);
	err = core_get_mapped_files(it);
	if (err) {
		core_loaded_module_iterator_destroy(&it->u.it);
		return err;
	}
	*ret = &it->u.it;
	return NULL;
}

static struct drgn_error *
null_loaded_module_iterator_create(struct drgn_program *prog,
				   struct drgn_module_iterator **ret)
{
	struct drgn_module_iterator *it = calloc(1, sizeof(*it));
	if (!it)
		return &drgn_enomem;
	drgn_module_iterator_init(it, prog, NULL, NULL);
	*ret = it;
	return NULL;
}

LIBDRGN_PUBLIC struct drgn_error *
drgn_loaded_module_iterator_create(struct drgn_program *prog,
				   struct drgn_module_iterator **ret)
{
	struct drgn_error *err;
	err = drgn_program_create_dbinfo(prog);
	if (err)
		return err;
	if (prog->flags & DRGN_PROGRAM_IS_LINUX_KERNEL)
		return linux_kernel_loaded_module_iterator_create(prog, ret);
	else if (prog->flags & DRGN_PROGRAM_IS_LIVE)
		return process_loaded_module_iterator_create(prog, ret);
	else if (prog->core)
		return core_loaded_module_iterator_create(prog, ret);
	else
		return null_loaded_module_iterator_create(prog, ret);
}

struct load_debug_info_file {
	const char *path;
	Elf *elf;
	int fd;
};

DEFINE_VECTOR(load_debug_info_file_vector, struct load_debug_info_file)

struct load_debug_info_candidate {
	const void *build_id;
	size_t build_id_len;
	struct load_debug_info_file_vector files;
	bool matched;
};

static struct nstring
load_debug_info_candidate_key(const struct load_debug_info_candidate *candidate)
{
	return (struct nstring){ candidate->build_id, candidate->build_id_len };
}

DEFINE_HASH_TABLE(load_debug_info_candidate_table,
		  struct load_debug_info_candidate,
		  load_debug_info_candidate_key, nstring_hash_pair, nstring_eq);

struct load_debug_info_state {
	struct drgn_program *prog;
	struct load_debug_info_candidate_table candidates;
	// Number of entries in the candidates table that haven't matched any
	// modules.
	size_t unmatched_candidates;
	bool load_default;
	bool load_main;
};

static struct drgn_error *
load_debug_info_add_candidate(struct load_debug_info_state *state,
			      const char *path)
{
	struct drgn_error *err;
	struct drgn_program *prog = state->prog;

	struct load_debug_info_file file = {
		.path = path,
		.fd = open(path, O_RDONLY),
	};
	if (file.fd < 0) {
		drgn_log_warning(prog, "%s: %m; ignoring\n", path);
		return NULL;
	}
	file.elf = dwelf_elf_begin(file.fd);
	if (!file.elf) {
		drgn_log_warning(prog, "%s: %s; ignoring\n", path,
				 elf_errmsg(-1));
		err = NULL;
		goto err_fd;
	}
	if (elf_kind(file.elf) != ELF_K_ELF) {
		drgn_log_warning(prog, "%s: not an ELF file; ignoring\n", path);
		err = NULL;
		goto err_elf;
	}
	const void *build_id;
	ssize_t build_id_len = dwelf_elf_gnu_build_id(file.elf, &build_id);
	if (build_id_len <= 0) {
		if (build_id_len < 0) {
			drgn_log_warning(prog, "%s: %s; ignoring\n", path,
					 elf_errmsg(-1));
		} else {
			drgn_log_warning(prog, "%s: no build ID; ignoring\n",
					 path);
		}
		err = NULL;
		goto err_elf;
	}

	struct load_debug_info_candidate candidate = {
		.build_id = build_id,
		.build_id_len = build_id_len,
	};
	struct load_debug_info_candidate_table_iterator it;
	int r = load_debug_info_candidate_table_insert(&state->candidates,
						       &candidate, &it);
	if (r < 0) {
		err = &drgn_enomem;
		goto err_elf;
	}
	if (r > 0) {
		load_debug_info_file_vector_init(&it.entry->files);
		state->unmatched_candidates++;
	}
	if (!load_debug_info_file_vector_append(&it.entry->files, &file)) {
		err = &drgn_enomem;
		goto err_elf;
	}
	return NULL;

err_elf:
	elf_end(file.elf);
err_fd:
	close(file.fd);
	return err;
}

static void load_debug_info_state_deinit(struct load_debug_info_state *state)
{
	for (struct load_debug_info_candidate_table_iterator it =
	     load_debug_info_candidate_table_first(&state->candidates);
	     it.entry;
	     it = load_debug_info_candidate_table_next(it)) {
		for (size_t i = 0; i < it.entry->files.size; i++) {
			elf_end(it.entry->files.data[i].elf);
			close(it.entry->files.data[i].fd);
		}
		load_debug_info_file_vector_deinit(&it.entry->files);
	}
	load_debug_info_candidate_table_deinit(&state->candidates);
}

static struct drgn_error *
load_debug_info_try_files(struct drgn_module *module,
			  const void *build_id, size_t build_id_len,
			  struct drgn_module_try_files_args *args,
			  bool *missing_debug_info_error_ret)
{
	struct drgn_error *err;
	struct load_debug_info_state *state = args->arg;

	*missing_debug_info_error_ret = false;

	struct nstring key = { build_id, build_id_len };
	struct load_debug_info_candidate *candidate;
	if (build_id_len > 0 &&
	    (candidate =
	     load_debug_info_candidate_table_search(&state->candidates,
						    &key).entry)) {
		if (!candidate->matched) {
			state->unmatched_candidates--;
			candidate->matched = true;
		}
		for (size_t i = 0; i < candidate->files.size; i++) {
			struct load_debug_info_file *file =
				&candidate->files.data[i];
			// TODO: reopen fd through proc? provide Elf handle?
			err = drgn_module_try_file(module, file->path, -1,
						   false, args);
			if (err)
				return err;
			if (args->loaded_status != DRGN_MODULE_FILE_FAILED &&
			    args->debug_status != DRGN_MODULE_FILE_FAILED)
				return NULL;
		}
	}

	if (state->load_default
	    || (state->load_main
		&& drgn_module_kind(module) == DRGN_MODULE_MAIN)) {
		err = drgn_module_try_default_files(module, args);
		if (err)
			return err;
		if (args->loaded_status == DRGN_MODULE_FILE_FAILED ||
		    args->debug_status == DRGN_MODULE_FILE_FAILED)
			*missing_debug_info_error_ret = true;
	}
	return NULL;
}

struct drgn_error *
load_debug_info_need_gnu_debugaltlink_file(struct drgn_module *module,
					   struct drgn_module_try_files_args *args,
					   const char *debug_file_path,
					   const char *debugaltlink_path,
					   const void *build_id,
					   size_t build_id_len,
					   const char *build_id_str)
{
	bool unused;
	return load_debug_info_try_files(module, build_id, build_id_len, args,
					 &unused);
}

LIBDRGN_PUBLIC struct drgn_error *
drgn_program_load_debug_info(struct drgn_program *prog, const char **paths,
			     size_t n, bool load_default, bool load_main)
{
	struct drgn_error *err;

	elf_version(EV_CURRENT); // TODO: get rid of this and create the debug
				 // info earlier

	struct load_debug_info_state state = {
		.prog = prog,
		.candidates = HASH_TABLE_INIT,
		.load_default = load_default,
		.load_main = load_main,
	};
	for (size_t i = 0; i < n; i++) {
		err = load_debug_info_add_candidate(&state, paths[i]);
		if (err)
			goto out_state;
	}

	if (load_debug_info_candidate_table_empty(&state.candidates)
	    && !load_default && !load_main) {
		// We don't have any files to try, so don't create any modules.
		err = NULL;
		goto out_state;
	}

	struct drgn_module_iterator *it;
	err = drgn_loaded_module_iterator_create(prog, &it);
	if (err)
		goto out_state;
	struct drgn_module *module;
	struct string_builder missing_debug_info_error_message =
		STRING_BUILDER_INIT;
	while (!(err = drgn_module_iterator_next(it, &module)) && module) {
		struct drgn_module_try_files_args args = {
			.want_loaded = true,
			.want_debug = true,
			.arg = &state,
			.need_gnu_debugaltlink_file =
				load_debug_info_need_gnu_debugaltlink_file,
		};
		const void *build_id;
		size_t build_id_len;
		drgn_module_build_id(module, &build_id, &build_id_len);
		bool missing_debug_info_error;
		err = load_debug_info_try_files(module, build_id, build_id_len,
						&args,
						&missing_debug_info_error);
		if (err)
			goto out;
		if (missing_debug_info_error) {
			if (missing_debug_info_error_message.len == 0 &&
			    !string_builder_append(&missing_debug_info_error_message,
						   "could not get debugging information for:")) { // TODO: not accurate
				err = &drgn_enomem;
				goto out;
			}
			// TODO: bring back max errors?
			/* if (!string_builder_line_break(&missing_debug_info_error_message) || */
			if (!string_builder_appendc(&missing_debug_info_error_message, ' ') ||
			    !string_builder_append(&missing_debug_info_error_message,
						   drgn_module_name(module))) {
				err = &drgn_enomem;
				goto out;
			}
		}
		// If we are only trying files for the main module (i.e., if
		// we're not loading all default debug info and any provided
		// files were all for the main module), then we only want to
		// create the main module.
		if (drgn_module_kind(module) == DRGN_MODULE_MAIN
		    && !load_default && state.unmatched_candidates == 0) {
			err = NULL;
			break;
		}
	}
	if (err)
		goto out;

	if (state.unmatched_candidates != 0) {
		for (struct load_debug_info_candidate_table_iterator it =
		     load_debug_info_candidate_table_first(&state.candidates);
		     it.entry;
		     it = load_debug_info_candidate_table_next(it)) {
			for (size_t i = 0; i < it.entry->files.size; i++) {
				drgn_log_warning(prog,
						 "%s did not match any loaded modules; ignoring\n",
						 it.entry->files.data[i].path);
			}
		}
	}

out:
	if (!err && missing_debug_info_error_message.len > 0) {
		err = drgn_error_from_string_builder(DRGN_ERROR_MISSING_DEBUG_INFO,
						     &missing_debug_info_error_message);
	} else {
		free(missing_debug_info_error_message.str);
	}
	drgn_module_iterator_destroy(it);
out_state:
	load_debug_info_state_deinit(&state);
	return err;
}

struct drgn_module *drgn_module_by_address(struct drgn_debug_info *dbinfo,
					   uint64_t address)
{
	struct drgn_module_address_tree_iterator it =
		drgn_module_address_tree_search_le(&dbinfo->modules_by_address,
						   &address);
	if (!it.entry || address >= it.entry->end)
		return NULL;
	return it.entry;
}

struct drgn_error *drgn_debug_info_create(struct drgn_program *prog,
					  struct drgn_debug_info **ret)
{
	elf_version(EV_CURRENT);
	struct drgn_debug_info *dbinfo = calloc(1, sizeof(*dbinfo));
	if (!dbinfo)
		return &drgn_enomem;
	dbinfo->prog = prog;
	drgn_module_table_init(&dbinfo->modules);
	drgn_module_address_tree_init(&dbinfo->modules_by_address);
	drgn_dwarf_info_init(dbinfo);
	*ret = dbinfo;
	return NULL;
}

void drgn_debug_info_destroy(struct drgn_debug_info *dbinfo)
{
	if (!dbinfo)
		return;
	depmod_index_deinit(&dbinfo->modules_dep);
	drgn_dwarf_info_deinit(dbinfo);
	// TODO: free the actual modules
	drgn_module_table_deinit(&dbinfo->modules);
#ifdef WITH_DEBUGINFOD
	if (dbinfo->debuginfod_client)
		drgn_debuginfod_end(dbinfo->debuginfod_client);
#endif
	free(dbinfo);
}

struct drgn_error *
drgn_module_find_cfi(struct drgn_program *prog, struct drgn_module *module,
		     uint64_t pc, struct drgn_elf_file **file_ret,
		     struct drgn_cfi_row **row_ret, bool *interrupted_ret,
		     drgn_register_number *ret_addr_regno_ret)
{
	struct drgn_error *err;

	// If the file's platform doesn't match the program's, we can't use its
	// CFI.
	const bool can_use_loaded_file =
		(module->loaded_file &&
		 drgn_platforms_equal(&module->loaded_file->platform,
				      &prog->platform));
	const bool can_use_debug_file =
		(module->debug_file &&
		 drgn_platforms_equal(&module->debug_file->platform,
				      &prog->platform));

	if (prog->prefer_orc_unwinder) {
		if (can_use_debug_file) {
			*file_ret = module->debug_file;
			err = drgn_module_find_orc_cfi(module, pc, row_ret,
						       interrupted_ret,
						       ret_addr_regno_ret);
			if (err != &drgn_not_found)
				return err;
			err = drgn_module_find_dwarf_cfi(module, pc, row_ret,
							 interrupted_ret,
							 ret_addr_regno_ret);
			if (err != &drgn_not_found)
				return err;
		}
		if (can_use_loaded_file) {
			*file_ret = module->loaded_file;
			return drgn_module_find_eh_cfi(module, pc, row_ret,
						       interrupted_ret,
						       ret_addr_regno_ret);
		}
	} else {
		if (can_use_debug_file) {
			*file_ret = module->debug_file;
			err = drgn_module_find_dwarf_cfi(module, pc, row_ret,
							 interrupted_ret,
							 ret_addr_regno_ret);
			if (err != &drgn_not_found)
				return err;
		}
		if (can_use_loaded_file) {
			*file_ret = module->loaded_file;
			err = drgn_module_find_eh_cfi(module, pc, row_ret,
						      interrupted_ret,
						      ret_addr_regno_ret);
			if (err != &drgn_not_found)
				return err;
		}
		if (can_use_debug_file) {
			*file_ret = module->debug_file;
			return drgn_module_find_orc_cfi(module, pc, row_ret,
							interrupted_ret,
							ret_addr_regno_ret);
		}
	}
	return &drgn_not_found;
}
