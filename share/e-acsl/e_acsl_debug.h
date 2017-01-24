/**************************************************************************/
/*                                                                        */
/*  This file is part of the Frama-C's E-ACSL plug-in.                    */
/*                                                                        */
/*  Copyright (C) 2012-2015                                               */
/*    CEA (Commissariat à l'énergie atomique et aux énergies              */
/*         alternatives)                                                  */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 2.1.                                              */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 2.1                 */
/*  for more details (enclosed in the file license/LGPLv2.1).             */
/*                                                                        */
/**************************************************************************/

/*! ***********************************************************************
 * \file   e_acsl_debug.h
 * \brief  Debug-level functions and macros
***************************************************************************/

/* Stringification macros {{{ */
#ifndef E_ACSL_STRINGIFICATION
#define E_ACSL_STRINGIFICATION
#  define STRINGIFY(x) #x
#  define TOSTRING(x) STRINGIFY(x)
#  define __AT__ __FILE__ ":" TOSTRING(__LINE__)
#endif
/* }}} */

/** Debugging support {{{
 * Enabled in the presence of the E_ACSL_DEBUG macro */
#ifdef E_ACSL_DEBUG

/* Default location of the E_ACSL log file */
#ifndef E_ACSL_DEBUG_LOG
#  define E_ACSL_DEBUG_LOG /tmp/e-acsl.log
#endif

/*! \brief Name of the debug log file */
static const char *dlog_name = TOSTRING(E_ACSL_DEBUG_LOG);

/*! \brief File descriptor associated with the debug log file */
static int dlog_fd = -1;

/*! \brief Output a message to a log file */
#define DLOG(...) dprintf(dlog_fd, __VA_ARGS__)

/*! \brief Debug-time assertion based on assert (see e_acsl.print.h) */
#define DASSERT(_e) assert(_e)

/*! \brief Debug-time assertion based on vassert (see e_acsl.print.h) */
#define DVASSERT(_expr, _fmt, ...) vassert(_expr, _fmt, __VA_ARGS__)

/*! \brief Initialize debug report file:
 *  - open file descriptor
 *  - add program arguments to the log */
static void initialize_report_file(int *argc, char ***argv) {
  // Redirect the log to stderr is just set to be defined or set to '-'
  if (!strcmp(dlog_name, "-") || !strcmp(dlog_name, "1")) {
    dlog_fd = 2;
  } else {
    dlog_fd = open(dlog_name, O_WRONLY | O_CREAT | O_TRUNC  |O_NONBLOCK
      | O_NOCTTY, S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH | S_IWOTH);
  }

  if (dlog_fd == -1)
    vabort("Cannot open file descriptor for %s\n", dlog_name);
  else {
    DLOG("<<< E-ACSL instrumented run >>>\n");
    DLOG("<<< Program arguments: ");
    if (argc && argv) {
      int i;
      for (i = 0; i < *argc; i++)
        DLOG("%s ", (*argv)[i]);
      DLOG(">>>\n");
    } else {
      DLOG("unknown >>>\n");
    }
  }
}

static int debug_stop_number = 0;
int getchar(void);

#define STOP { \
  DLOG(" << ==================== " "Debug Stop Point %d in '%s' at %s:%d" \
    " ==================== >> ", \
    ++debug_stop_number, __func__, __FILE__, __LINE__); \
    getchar(); \
}
#else
#  define initialize_report_file(...)
#  define DLOG(...)
#  define DASSERT(_e)
#  define DVASSERT(_expr, _fmt, ...)
#endif
// }}}
