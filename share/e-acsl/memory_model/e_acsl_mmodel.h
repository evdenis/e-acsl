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

#ifndef E_ACSL_MMODEL
#define E_ACSL_MMODEL

#ifndef __KERNEL__
#include <stddef.h>
typedef unsigned gfp_t;
#else
#include <linux/kernel.h>
#include <linux/slab.h>
#include <linux/types.h>
#endif

/* allocate size bytes and store the returned block
 * for further information, see kmalloc */
/*@ assigns \result \from size; */
void * __ekmalloc(size_t size, gfp_t f)
  __attribute__((FC_BUILTIN)) ;

/* kfree the block starting at ptr,
 * for further information, see kfree */
/*@ assigns *((char*)ptr) \from ptr; */
void __ekfree(void * ptr)
  __attribute__((FC_BUILTIN));

/*@ assigns \result \from ptr; */
int __freeable(void * ptr)
  __attribute__((FC_BUILTIN));

/* resize the block starting at ptr to fit its new size,
 * for further information, see krealloc */
/*@ assigns \result \from *(((char*)ptr)+(0..size-1)); */
void * __ekrealloc(void * ptr, size_t size, gfp_t f)
  __attribute__((FC_BUILTIN));

/* allocate memory for an array of nbr_block elements of size_block size,
 * this memory is set to zero, the returned block is stored,
 * for further information, see kcalloc */
/*@ assigns \result \from nbr_elt,size_elt; */
void * __ekcalloc(size_t nbr_elt, size_t size_elt, gfp_t t)
  __attribute__((FC_BUILTIN));

/* From outside the library, the following functions have no side effect */

/* put argc/argv in memory model */
/*@ assigns \nothing; */
void __init_args(int argc_ref, char **argv_ref)
	__attribute__((FC_BUILTIN));

/* store the block of size bytes starting at ptr */
/*@ assigns \result \from *(((char*)ptr)+(0..size-1)); */
void * __store_block(void * ptr, size_t size)
  __attribute__((FC_BUILTIN));

/* remove the block starting at ptr */
/*@ assigns \nothing; */
void __delete_block(void * ptr)
  __attribute__((FC_BUILTIN));

/* mark the size bytes of ptr as initialized */
/*@ assigns \nothing; */
void __initialize(void * ptr, size_t size)
  __attribute__((FC_BUILTIN));

/* mark all bytes of ptr as initialized */
/*@ assigns \nothing; */
void __full_init(void * ptr)
  __attribute__((FC_BUILTIN));

/* marks a block as litteral string */
/*@ assigns \nothing; */
void __literal_string(void * ptr)
  __attribute__((FC_BUILTIN));

/* ****************** */
/* E-ACSL annotations */
/* ****************** */

/* return whether the first size bytes of ptr are readable/writable */
/*@ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> \valid(((char *)ptr)+(0..size-1));
  @ assigns \result \from *(((char*)ptr)+(0..size-1)); */
int __valid(void * ptr, size_t size)
  __attribute__((FC_BUILTIN));

/* return whether the first size bytes of ptr are readable */
/*@ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> \valid_read(((char *)ptr)+(0..size-1));
  @ assigns \result \from *(((char*)ptr)+(0..size-1)); */
int __valid_read(void * ptr, size_t size)
  __attribute__((FC_BUILTIN));

/* return the base address of the block containing ptr */
/*@ ensures \result == \base_addr(ptr);
  @ assigns \result \from ptr; */
void * __base_addr(void * ptr)
  __attribute__((FC_BUILTIN));

/* return the length (in bytes) of the block containing ptr */
/*@ ensures \result == \block_length(ptr);
  @ assigns \result \from ptr; */
size_t __block_length(void * ptr)
  __attribute__((FC_BUILTIN));

/* return the offset of ptr within its block */
/*@ ensures \result == \offset(ptr);
  @ assigns \result \from ptr; */
int __offset(void * ptr)
  __attribute__((FC_BUILTIN));

/* return whether the size bytes of ptr are initialized */
/*@ ensures \result == 0 || \result == 1;
  @ ensures \result == 1 ==> \initialized(((char *)ptr)+(0..size-1));
  @ assigns \result \from *(((char*)ptr)+(0..size-1)); */
int __initialized(void * ptr, size_t size)
  __attribute__((FC_BUILTIN));

void __out_of_bound(void * ptr, _Bool flag)
  __attribute__((FC_BUILTIN));

/* print the content of the abstract structure */
void __e_acsl_memory_debug(void)
  __attribute__((FC_BUILTIN));

/*@ ghost int extern __e_acsl_internal_heap; */

/* erase the content of the abstract structure
 * have to be called at the end of the `main` */
/*@ assigns __e_acsl_internal_heap \from __e_acsl_internal_heap; */
void __e_acsl_memory_clean(void)
  __attribute__((FC_BUILTIN));

/* return the number of bytes dynamically allocated */
/*@ assigns \result \from __e_acsl_internal_heap; */
size_t __get_memory_size(void)
  __attribute__((FC_BUILTIN));

/* for predicates */
extern size_t __memory_size;

/*@ predicate diffSize{L1,L2}(integer i) =
  \at(__memory_size, L1) - \at(__memory_size, L2) == i;
*/

#endif
