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
 * \file  e_acsl_trace.h
 * \brief Interface for producing backtrace. Requires GLIBC.
***************************************************************************/

#ifndef E_ACSL_TRACE
#define E_ACSL_TRACE

#include "e_acsl_shexec.h"

# ifdef __GLIBC__
#  include <execinfo.h>
# endif

static void trace() {
# ifdef __GLIBC__
# ifdef __linux__
  int size = 24;
  void **bb = native_malloc(sizeof(void*)*size);
  backtrace(bb,size);

  char executable [PATH_MAX];
  sprintf(executable, "/proc/%d/exe", getpid());

  printf("/** Backtrace **************************/\n");
  int counter = 0;
  while (*bb) {
    char *addr = (char*)native_malloc(21);
    sprintf(addr,"%p", *bb);
    char *ar[] = { "addr2line", "-f", "-p", "-C", "-s", "-e",
      executable, addr, NULL};
    ipr_t *ipr = shexec(ar, NULL);
    char *prefix = (counter) ? " - " : "";
    if (ipr) {
      char *outs = (char*)ipr->stdouts;
      outs[strlen(outs)-1] = '\0';
      if (strlen(outs) && endswith(outs, "??:0") && endswith(outs, "??:?")) {
        printf("%s%s\n", prefix, outs);
      }
    }
    bb++;
    counter++;
  }
  printf("/***************************************/\n");
# endif /* __linux__ */
# endif /* __GLIBC__ */
}
#endif
