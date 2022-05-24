// Copyright (c) Meta Platforms, Inc. and affiliates.
// SPDX-License-Identifier: LGPL-2.1-or-later

#include <stdarg.h>
#include <stdio.h>

#include "drgn.h"
#include "log.h"
#include "program.h"
#include "util.h"

LIBDRGN_PUBLIC struct drgn_error *
drgn_program_set_log_level(struct drgn_program *prog, int level)
{
	if (level < DRGN_LOG_LEVEL_EMERG ||
	    level > (DRGN_LOG_LEVEL_DEBUG + 1)) {
		return drgn_error_create(DRGN_ERROR_INVALID_ARGUMENT,
					 "invalid log level");
	}
	prog->log_level = level;
	return NULL;
}

LIBDRGN_PUBLIC int drgn_program_get_log_level(struct drgn_program *prog)
{
	return prog->log_level;
}

LIBDRGN_PUBLIC struct drgn_error *
drgn_program_set_log_fd(struct drgn_program *prog, int fd)
{
	prog->log_fd = fd;
	prog->log_file = NULL;
	return NULL;
}

LIBDRGN_PUBLIC struct drgn_error *
drgn_program_set_log_file(struct drgn_program *prog, FILE *file)
{
	prog->log_fd = -1;
	prog->log_file = file;
	return NULL;
}

bool drgn_should_log(struct drgn_program *prog, enum drgn_log_level log_level)
{
	return log_level < prog->log_level;
}

void drgn_error_log(enum drgn_log_level log_level, struct drgn_program *prog,
		    struct drgn_error *err, const char *format, ...)
{
	if (!drgn_should_log(prog, log_level))
		return;

	va_list ap;
	va_start(ap, format);

	if (prog->log_file) {
		if (format)
			vfprintf(prog->log_file, format, ap);
		if (err)
			drgn_error_fwrite(prog->log_file, err);
	} else if (prog->log_fd >= 0) {
		if (format)
			vdprintf(prog->log_fd, format, ap);
		if (err)
			drgn_error_dwrite(prog->log_fd, err);
	}

	va_end(ap);
}
