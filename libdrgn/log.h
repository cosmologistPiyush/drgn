// Copyright (c) Meta Platforms, Inc. and affiliates.
// SPDX-License-Identifier: LGPL-2.1-or-later

/**
 * @file
 *
 * Logging.
 *
 * See @ref LoggingInternals.
 */

#ifndef DRGN_LOG_H
#define DRGN_LOG_H

/**
 * @ingroup Internals
 *
 * @defgroup LoggingInternals Logging
 *
 * Logging functions.
 *
 * @{
 */

struct drgn_error;
struct drgn_program;

/**
 * Log levels.
 *
 * @sa drgn_program_set_log_level()
 */
enum drgn_log_level {
	DRGN_LOG_LEVEL_EMERG = 0,
	DRGN_LOG_LEVEL_ALERT = 1,
	DRGN_LOG_LEVEL_CRIT = 2,
	DRGN_LOG_LEVEL_ERR = 3,
	DRGN_LOG_LEVEL_WARNING = 4,
	DRGN_LOG_LEVEL_NOTICE = 5,
	DRGN_LOG_LEVEL_INFO = 6,
	DRGN_LOG_LEVEL_DEBUG = 7,
};

/**
 * @{
 *
 * @name Logging Functions
 */

#ifdef DOXYGEN
/** Log a printf-style message at the given level. */
void drgn_log(enum drgn_log_level level, struct drgn_program *prog,
	      const char *format, ...);
#else
#define drgn_log(level, prog, ...) drgn_error_log(level, prog, NULL, __VA_ARGS__)
#endif
/** Log an emergency message. */
#define drgn_log_emerg(...) drgn_log(DRGN_LOG_LEVEL_EMERG, __VA_ARGS__)
/** Log an alert message. */
#define drgn_log_alert(...) drgn_log(DRGN_LOG_LEVEL_ALERT, __VA_ARGS__)
/** Log a critical message. */
#define drgn_log_crit(...) drgn_log(DRGN_LOG_LEVEL_CRIT, __VA_ARGS__)
/** Log an error message. */
#define drgn_log_err(...) drgn_log(DRGN_LOG_LEVEL_ERR, __VA_ARGS__)
/** Log a warning message. */
#define drgn_log_warning(...) drgn_log(DRGN_LOG_LEVEL_WARNING, __VA_ARGS__)
/** Log a notice message. */
#define drgn_log_notice(...) drgn_log(DRGN_LOG_LEVEL_NOTICE, __VA_ARGS__)
/** Log an informational message. */
#define drgn_log_info(...) drgn_log(DRGN_LOG_LEVEL_INFO, __VA_ARGS__)
/** Log a debug message. */
#define drgn_log_debug(...) drgn_log(DRGN_LOG_LEVEL_DEBUG, __VA_ARGS__)

/**
 * @}
 *
 * @{
 *
 * @name Error Logging Functions
 */

/**
 * Log a printf-style message followed by a @ref drgn_error and a newline at the
 * given level.
 */
__attribute__((__format__(__printf__, 4, 5)))
void drgn_error_log(enum drgn_log_level level, struct drgn_program *prog,
		    struct drgn_error *err, const char *format, ...);
/** Log an emergency message followed by a @ref drgn_error. */
#define drgn_error_log_emerg(...) drgn_error_log(DRGN_LOG_LEVEL_EMERG, __VA_ARGS__)
/** Log an alert message followed by a @ref drgn_error. */
#define drgn_error_log_alert(...) drgn_error_log(DRGN_LOG_LEVEL_ALERT, __VA_ARGS__)
/** Log a critical message followed by a @ref drgn_error. */
#define drgn_error_log_crit(...) drgn_error_log(DRGN_LOG_LEVEL_CRIT, __VA_ARGS__)
/** Log an error message followed by a @ref drgn_error. */
#define drgn_error_log_err(...) drgn_error_log(DRGN_LOG_LEVEL_ERR, __VA_ARGS__)
/** Log a warning message followed by a @ref drgn_error. */
#define drgn_error_log_warning(...) drgn_error_log(DRGN_LOG_LEVEL_WARNING, __VA_ARGS__)
/** Log a notice message followed by a @ref drgn_error. */
#define drgn_error_log_notice(...) drgn_error_log(DRGN_LOG_LEVEL_NOTICE, __VA_ARGS__)
/** Log an informational message followed by a @ref drgn_error. */
#define drgn_error_log_info(...) drgn_error_log(DRGN_LOG_LEVEL_INFO, __VA_ARGS__)
/** Log a debug message followed by a @ref drgn_error. */
#define drgn_error_log_debug(...) drgn_error_log(DRGN_LOG_LEVEL_DEBUG, __VA_ARGS__)

/**
 * @}
 * @}
 */

#endif /* DRGN_LOG_H */
