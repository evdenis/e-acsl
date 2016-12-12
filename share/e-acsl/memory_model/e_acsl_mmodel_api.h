/**************************************************************************/
/*                                                                        */
/*  This file is part of the Frama-C's E-ACSL plug-in.                    */
/*                                                                        */
/*  Copyright (C) 2012-2016                                               */
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

#ifndef E_ACSL_MMODEL_API
#define E_ACSL_MMODEL_API

#ifndef __KERNEL__
#include <stddef.h>
#include <stdbool.h>
#else
#include <linux/kernel.h>

#ifdef CONFIG_X86_64
# define E_ACSL_MACHDEP x86_64
#else
# define E_ACSL_MACHDEP x86_32
#endif
#endif /* __KERNEL__ */

#if E_ACSL_MACHDEP == x86_64
#define WORDBITS 64
#elif E_ACSL_MACHDEP == x86_32
#define WORDBITS 32
#elif E_ACSL_MACHDEP == ppc_32
#define WORDBITS 32
#elif E_ACSL_MACHDEP == x86_16
#define WORDBITS 16
#else
#define WORDBITS 32
#endif

/* Memory block allocated and may be deallocated */
struct _block {
  size_t ptr;	/* begin address */
  size_t size;	/* size in bytes */
/* Keep trace of initialized sub-blocks within a memory block */
  unsigned char * init_ptr; /* dynamic array of booleans */
  size_t init_cpt;
  _Bool is_litteral_string;
  _Bool is_out_of_bound;
  _Bool freeable;
};

/* print the information about a block */
void __print_block(struct _block * ptr );

/* erase information about initialization of a block */
void __clean_init(struct _block * ptr );

/* erase all information about a block */
void __clean_block(struct _block * ptr);

/* remove the block from the structure */
void  __remove_element(struct _block *);

/* add a block in the structure */
void  __add_element(struct _block *);

/* return the block B such as : begin addr of B == ptr
   we suppose that such a block exists, but we could return NULL if not */
struct _block * __get_exact(void *);

/* return the block B containing ptr, such as :
   begin addr of B <= ptr < (begin addr + size) of B
   or NULL if such a block does not exist */
struct _block * __get_cont(void *);

/* erase the content of the structure */
void __clean_struct(void);

/* print the content of the structure */
void  __debug_struct(void);

#endif
