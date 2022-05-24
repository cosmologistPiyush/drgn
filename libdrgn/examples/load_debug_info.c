// Copyright (c) Meta Platforms, Inc. and affiliates.
// SPDX-License-Identifier: LGPL-2.1-or-later

#include <errno.h>
#include <getopt.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <time.h>
#include <unistd.h>

#include "drgn.h"

static inline struct timespec timespec_sub(struct timespec a, struct timespec b)
{
	if (a.tv_nsec < b.tv_nsec) {
		return (struct timespec){
			.tv_sec = a.tv_sec - 1 - b.tv_sec,
			.tv_nsec = a.tv_nsec + 1000000000L - b.tv_nsec,
		};
	} else {
		return (struct timespec){
			.tv_sec = a.tv_sec - b.tv_sec,
			.tv_nsec = a.tv_nsec - b.tv_nsec,
		};
	}
}

noreturn static void usage(bool error)
{
	fprintf(error ? stderr : stdout,
		"usage: load_debug_info [-k|-c CORE|-p PID] [PATH...]\n"
		"\n"
		"Example libdrgn program that loads default debug information\n"
		"\n"
		"Options:\n"
		"  -k, --kernel            debug the running kernel\n"
		"  -c PATH, --core PATH    debug the given core dump\n"
		"  -p PID, --pid PID       debug the running process with the given PID\n"
		"  -T, --time              print how long loading debug info took in seconds\n"
		"  -h, --help              display this help message and exit\n");
	exit(error ? EXIT_FAILURE : EXIT_SUCCESS);
}

static const char *module_kind_str(enum drgn_module_kind kind)
{
	switch (kind) {
	case DRGN_MODULE_MAIN:
		return "main";
	case DRGN_MODULE_SHARED_LIBRARY:
		return "shared library";
	case DRGN_MODULE_VDSO:
		return "vdso";
	case DRGN_MODULE_LINUX_KERNEL_LOADABLE:
		return "linux kernel loadable";
	case DRGN_MODULE_EXTRA:
		return "extra";
	}
	return "<unknown>";
}

static const char *
drgn_module_file_status_str(enum drgn_module_file_status status)
{
	switch (status) {
	case DRGN_MODULE_FILE_ALREADY_HAD:
		return "already had";
	case DRGN_MODULE_FILE_NOT_NEEDED:
		return "not needed";
	case DRGN_MODULE_FILE_NOT_WANTED:
		return "not wanted";
	case DRGN_MODULE_FILE_FAILED:
		return "failed";
	case DRGN_MODULE_FILE_SUCCEEDED:
		return "succeeded";
	}
	return "<unknown>";
}

int main(int argc, char **argv)
{
	setlocale(LC_ALL, "");

	struct option long_options[] = {
		{"kernel", no_argument, NULL, 'k'},
		{"core", required_argument, NULL, 'c'},
		{"pid", required_argument, NULL, 'p'},
		{"time", no_argument, NULL, 'T'},
		{"help", no_argument, NULL, 'h'},
		{},
	};
	bool kernel = false;
	const char *core = NULL;
	const char *pid = NULL;
	bool print_time = false;
	for (;;) {
		int c = getopt_long(argc, argv, "kc:p:Th", long_options, NULL);
		if (c == -1)
			break;
		switch (c) {
		case 'k':
			kernel = true;
			break;
		case 'c':
			core = optarg;
			break;
		case 'p':
			pid = optarg;
			break;
		case 'T':
			print_time = true;
			break;
		case 'h':
			usage(false);
		default:
			usage(true);
		}
	}
	if (kernel + !!core + !!pid > 1)
		usage(true);

	struct drgn_program *prog;
	struct drgn_error *err = drgn_program_create(NULL, &prog);
	if (err) {
		prog = NULL;
		goto out;
	}

	err = drgn_program_set_log_level(prog, 8);
	if (err)
		goto out;

	if (core)
		err = drgn_program_set_core_dump(prog, core);
	else if (pid)
		err = drgn_program_set_pid(prog, atoi(pid) ?: getpid());
	else if (kernel)
		err = drgn_program_set_kernel(prog);
	if (err)
		goto out;

	struct timespec start, end;
	if (print_time && clock_gettime(CLOCK_MONOTONIC, &start))
		abort();

	struct drgn_module_iterator *it;
	err = drgn_loaded_module_iterator_create(prog, &it);
	if (err)
		goto out;
	struct drgn_module *module;
	while (!(err = drgn_module_iterator_next(it, &module)) &&
	       module) {
		const char *build_id = drgn_module_build_id(module, NULL, NULL);
		if (0) {
		printf("discovered %s module %s with%s build ID %s\n",
		       module_kind_str(drgn_module_kind(module)),
		       drgn_module_name(module), build_id ? "" : "out",
		       build_id ?: "");
		}
		struct drgn_module_try_files_args args = {
			.want_loaded = true,
			.want_debug = true,
		};
		err = drgn_module_try_default_files(module, &args);
		if (err)
			break;
		if (0) {
		printf("  loaded: %s\n  debug: %s\n",
		       drgn_module_file_status_str(args.loaded_status),
		       drgn_module_file_status_str(args.debug_status));
		}
	}
	drgn_module_iterator_destroy(it);

	if ((!err || err->code == DRGN_ERROR_MISSING_DEBUG_INFO) && print_time) {
		if (clock_gettime(CLOCK_MONOTONIC, &end))
			abort();
		struct timespec diff = timespec_sub(end, start);
		printf("%lld.%09ld\n", (long long)diff.tv_sec, diff.tv_nsec);
	}

out:;
	int status;
	if (err) {
		if (err->code == DRGN_ERROR_MISSING_DEBUG_INFO)
			status = EXIT_SUCCESS;
		else
			status = EXIT_FAILURE;
		drgn_error_fwrite(stderr, err);
		drgn_error_destroy(err);
	} else {
		status = EXIT_SUCCESS;
	}
	drgn_program_destroy(prog);
	return status;
}
