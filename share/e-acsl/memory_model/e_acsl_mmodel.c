/**************************************************************************/
/*                                                                        */
/*  This file is part of the Frama-C's E-ACSL plug-in.                    */
/*                                                                        */
/*  Copyright (C) 2012-2016                                               */
/*    CEA (Commissariat � l'�nergie atomique et aux �nergies              */
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

#include <linux/kernel.h>
#include <linux/module.h>
#include <linux/types.h>
#include <linux/slab.h>
#include <linux/slab_def.h>
#include "e_acsl_mmodel_api.h"
#include "e_acsl_mmodel.h"

MODULE_LICENSE("GPL");

// E-ACSL warnings {{{
#define WARNING 0   // Output a warning message to stderr
#define ERROR   1   // Treat warnings as errors and abort execution
#define IGNORE  2   // Ignore warnings

#ifndef E_ACSL_WARNING
#define E_ACSL_WARNING WARNING
#endif

static int warning_level = E_ACSL_WARNING;

// Issue a warning to stderr or abort a program
// based on the current warning level
static void warning(const char* message) {
  if (warning_level != IGNORE) {
    pr_warn("%s\n", message);
    if (warning_level == ERROR)
      BUG();
  }
}

// Shortcut for issuing a warning and returning from a function
#define return_warning(_cond,_msg) \
  if(_cond) { \
    warning(_msg); \
    return; \
  }
// }}}

void* __e_acsl_mmodel_memset(void* dest, int val, size_t len) {
  unsigned char *ptr = (unsigned char*)dest;
  while (len-- > 0)
    *ptr++ = val;
  return dest;
}

size_t __memory_size = 0;
/*unsigned cpt_store_block = 0;*/

static const int nbr_bits_to_1[256] = {
  0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8
};

/*@ assigns \nothing;
  @ ensures \result == __memory_size;
  @*/
size_t __get_memory_size(void) {
  return __memory_size;
}

/*@ assigns \nothing;
  @ ensures size%8 == 0 ==> \result == size/8;
  @ ensures size%8 != 0 ==> \result == size/8+1;
  @*/
static size_t needed_bytes (size_t size) {
  return (size % 8) == 0 ? (size/8) : (size/8 + 1);
}

/* adds argc / argv to the memory model */
void __init_args(int argc, char **argv) {
  int i;

  __store_block(argv, (argc+1)*sizeof(char*));
  __full_init(argv);

  for (i = 0; i < argc; i++) {
    __store_block(argv[i], strlen(argv[i])+1);
    __full_init(argv[i]);
  }
}

/* store the block of size bytes starting at ptr, the new block is returned.
 * Warning: the return type is implicitly (struct _block*). */
void* __store_block(void* ptr, size_t size) {
  struct _block * tmp;
  BUG_ON(ptr == NULL);
  tmp = kmalloc(sizeof(struct _block), GFP_KERNEL);
  BUG_ON(tmp == NULL);
  tmp->ptr = (size_t)ptr;
  tmp->size = size;
  tmp->init_ptr = NULL;
  tmp->init_cpt = 0;
  tmp->is_litteral_string = false;
  tmp->is_out_of_bound = false;
  tmp->freeable = false;
  __add_element(tmp);
  /*cpt_store_block++;*/
  return tmp;
}

/* remove the block starting at ptr */
void __delete_block(void* ptr) {
  struct _block * tmp = __get_exact(ptr);
  BUG_ON(tmp == NULL);
  __clean_init(tmp);
  __remove_element(tmp);
  kfree(tmp);
}

/* allocate size bytes and store the returned block
 * for further information, see kmalloc */
void* __ekmalloc(size_t size, gfp_t t) {
  void * tmp;
  struct _block * new_block;
  if(size <= 0) return NULL;
  tmp = kmalloc(size, t);
  if(tmp == NULL) return NULL;
  new_block = __store_block(tmp, size);
  __memory_size += size;
  BUG_ON(new_block == NULL || (void*)new_block->ptr == NULL);
  new_block->freeable = true;
  return (void*)new_block->ptr;
}
EXPORT_SYMBOL_GPL(__ekmalloc);

void* __ekzalloc(size_t size, gfp_t t) {
  void * tmp;
  struct _block * new_block;
  if(size <= 0) return NULL;
  tmp = kzalloc(size, t);
  if(tmp == NULL) return NULL;
  new_block = __store_block(tmp, size);
  __memory_size += size;
  BUG_ON(new_block == NULL || (void*)new_block->ptr == NULL);
  new_block->freeable = true;
  return (void*)new_block->ptr;
}
EXPORT_SYMBOL_GPL(__ekzalloc);

void * __ekmem_cache_alloc(struct kmem_cache *s, gfp_t gfpflags) {
  void * tmp;
  struct _block * new_block;
  size_t size = s->object_size;
  tmp = kmem_cache_alloc(s, gfpflags);
  if(tmp == NULL) return NULL;
  new_block = __store_block(tmp, size);
  __memory_size += size;
  BUG_ON(new_block == NULL || (void*)new_block->ptr == NULL);
  new_block->freeable = true;
  return (void*)new_block->ptr;
}
EXPORT_SYMBOL_GPL(__ekmem_cache_alloc);

/* kfree the block starting at ptr,
 * for further information, see kfree */
void __ekfree(void* ptr) {
  struct _block * tmp;
  if(ptr == NULL) return;
  tmp = __get_exact(ptr);
  BUG_ON(tmp == NULL);
  kfree(ptr);
  __clean_init(tmp);
  __memory_size -= tmp->size;
  __remove_element(tmp);
  kfree(tmp);
}
EXPORT_SYMBOL_GPL(__ekfree);

void __ekzfree(void* ptr) {
  struct _block * tmp;
  if(ptr == NULL) return;
  tmp = __get_exact(ptr);
  BUG_ON(tmp == NULL);
  kzfree(ptr);
  __clean_init(tmp);
  __memory_size -= tmp->size;
  __remove_element(tmp);
  kfree(tmp);
}
EXPORT_SYMBOL_GPL(__ekzfree);

void __ekmem_cache_free(struct kmem_cache *cachep, void *objp) {
  struct _block * tmp;
  if(objp == NULL) return;
  tmp = __get_exact(objp);
  BUG_ON(tmp == NULL);
  kmem_cache_free(cachep, objp);
  __clean_init(tmp);
  __memory_size -= tmp->size;
  __remove_element(tmp);
  kfree(tmp);
}
EXPORT_SYMBOL_GPL(__ekmem_cache_free);

int __freeable(void* ptr) {
  struct _block * tmp;
  if(ptr == NULL) return false;
  tmp = __get_exact(ptr);
  if(tmp == NULL) return false;
  return tmp->freeable;
}

/* resize the block starting at ptr to fit its new size,
 * for further information, see krealloc */
void* __ekrealloc(void* ptr, size_t size, gfp_t t) {
  struct _block * tmp;
  void * new_ptr;
  if(ptr == NULL) return __ekmalloc(size, t);
  if(size == 0) {
    __ekfree(ptr);
    return NULL;
  }
  tmp = __get_exact(ptr);
  BUG_ON(tmp == NULL);
  new_ptr = krealloc((void*)tmp->ptr, size, t);
  if(new_ptr == NULL) return NULL;
  __memory_size -= tmp->size;
  tmp->ptr = (size_t)new_ptr;
  /* uninitialized, do nothing */
  if(tmp->init_cpt == 0) ;
  /* already fully initialized block */
  else if (tmp->init_cpt == tmp->size) {
    /* krealloc smaller block */
    if(size <= tmp->size)
      /* adjust new size, allocation not necessary */
      tmp->init_cpt = size;
    /* krealloc bigger larger block */
    else {
      int nb = needed_bytes(size);
      tmp->init_ptr = kmalloc(nb, t);
      __e_acsl_mmodel_memset(tmp->init_ptr, 0xFF, nb);
      if(size%8 != 0)
	tmp->init_ptr[size/8] <<= (8 - size%8);
    }
  }
  /* contains initialized and uninitialized parts */
  else {
    int nb = needed_bytes(size);
    int nb_old = needed_bytes(tmp->size);
    int i;
    tmp->init_ptr = krealloc(tmp->init_ptr, nb, t);
    for(i = nb_old; i < nb; i++)
      tmp->init_ptr[i] = 0;
    tmp->init_cpt = 0;
    for(i = 0; i < nb; i++)
      tmp->init_cpt += nbr_bits_to_1[tmp->init_ptr[i]];
    if(tmp->init_cpt == size || tmp->init_cpt == 0) {
      kfree(tmp->init_ptr);
      tmp->init_ptr = NULL;
    }
  }
  tmp->size = size;
  tmp->freeable = true;
  __memory_size += size;
  return (void*)tmp->ptr;
}
EXPORT_SYMBOL_GPL(__ekrealloc);

/* allocate memory for an array of nbr_block elements of size_block size,
 * this memory is set to zero, the returned block is stored,
 * for further information, see kcalloc */
void* __ekcalloc(size_t nbr_block, size_t size_block, gfp_t t) {
  void * tmp;
  struct _block * new_block;
  if(nbr_block * size_block <= 0) return NULL;
  tmp = kcalloc(nbr_block, size_block, t);
  if(tmp == NULL) return NULL;
  new_block = __store_block(tmp, nbr_block * size_block);
  __memory_size += nbr_block * size_block;
  BUG_ON(new_block == NULL || (void*)new_block->ptr == NULL);
  new_block->freeable = true;
  return (void*)new_block->ptr;
}
EXPORT_SYMBOL_GPL(__ekcalloc);

/* mark the size bytes of ptr as initialized */
void __initialize (void * ptr, size_t size) {
  struct _block * tmp;
  unsigned i;

  return_warning(ptr == NULL, "initialize");

  BUG_ON(size == 0);
  tmp = __get_cont(ptr);

  return_warning(tmp == NULL, "initialize");

  /* already fully initialized, do nothing */
  if(tmp->init_cpt == tmp->size) return;

  /* fully uninitialized */
  if(tmp->init_cpt == 0) {
    int nb = needed_bytes(tmp->size);
    tmp->init_ptr = kmalloc(nb, GFP_KERNEL);
    __e_acsl_mmodel_memset(tmp->init_ptr, 0, nb);
  }

  for(i = 0; i < size; i++) {
    int byte_offset = (size_t)ptr - tmp->ptr + i;
    int ind = byte_offset / 8;
    unsigned char mask_bit = 1U << (7 - (byte_offset % 8));
    if((tmp->init_ptr[ind] & mask_bit) == 0) tmp->init_cpt++;
    tmp->init_ptr[ind] |= mask_bit;
  }

  /* now fully initialized */
  if(tmp->init_cpt == tmp->size) {
    kfree(tmp->init_ptr);
    tmp->init_ptr = NULL;
  }
}

/* mark all bytes of ptr as initialized */
void __full_init (void * ptr) {
  struct _block * tmp;
  return_warning(ptr == NULL, "full_init");

  tmp = __get_exact(ptr);
  return_warning(tmp == NULL, "full_init");

  if (tmp->init_ptr != NULL) {
    kfree(tmp->init_ptr);
    tmp->init_ptr = NULL;
  }

  tmp->init_cpt = tmp->size;
}

/* mark a block as litteral string */
void __literal_string (void * ptr) {
  struct _block * tmp;
  return_warning(ptr == NULL, "literal_string");
  tmp = __get_exact(ptr);
  return_warning(tmp == NULL, "literal_string");
  tmp->is_litteral_string = true;
}

/* return whether the size bytes of ptr are initialized */
int __initialized (void * ptr, size_t size) {
  unsigned i;
  struct _block * tmp = __get_cont(ptr);
  BUG_ON(size == 0);
  if(tmp == NULL)
    return false;

  /* fully uninitialized */
  if(tmp->init_cpt == 0) return false;
  /* fully initialized */
  if(tmp->init_cpt == tmp->size) return true;

  for(i = 0; i < size; i++) {
    /* if one byte is uninitialized */
    int byte_offset = (size_t)ptr - tmp->ptr + i;
    int ind = byte_offset / 8;
    unsigned char mask_bit = 1U << (7 - (byte_offset % 8));
    if((tmp->init_ptr[ind] & mask_bit) == 0) return false;
  }
  return true;
}
EXPORT_SYMBOL_GPL(__initialized);

/* return the length (in bytes) of the block containing ptr */
size_t __block_length(void* ptr) {
  struct _block * tmp = __get_cont(ptr);
  BUG_ON(tmp == NULL);
  return tmp->size;
}

/* return whether the size bytes of ptr are readable/writable */
int __valid(void* ptr, size_t size) {
  struct _block * tmp;
  if(ptr == NULL)
    return false;
  //assert(size > 0);
  tmp = __get_cont(ptr);
  return (tmp == NULL) ?
    false : ( tmp->size - ( (size_t)ptr - tmp->ptr ) >= size
	      && !tmp->is_litteral_string && !tmp->is_out_of_bound);
}
EXPORT_SYMBOL_GPL(__valid);

/* return whether the size bytes of ptr are readable */
int __valid_read(void* ptr, size_t size) {
  struct _block * tmp;
  if(ptr == NULL)
    return false;
  //assert(size > 0);
  tmp = __get_cont(ptr);
  return (tmp == NULL) ?
    false : ( tmp->size - ( (size_t)ptr - tmp->ptr ) >= size
	      && !tmp->is_out_of_bound);
}
EXPORT_SYMBOL_GPL(__valid_read);

/* return the base address of the block containing ptr */
void* __base_addr(void* ptr) {
  struct _block * tmp = __get_cont(ptr);
  BUG_ON(tmp == NULL);
  return (void*)tmp->ptr;
}

/* return the offset of ptr within its block */
int __offset(void* ptr) {
  struct _block * tmp = __get_cont(ptr);
  BUG_ON(tmp == NULL);
  return ((size_t)ptr - tmp->ptr);
}

void __out_of_bound(void* ptr, _Bool flag) {
  struct _block * tmp = __get_cont(ptr);
  BUG_ON(tmp == NULL);
  tmp->is_out_of_bound = flag;
}

/*******************/
/* PRINT           */
/*******************/

/* print the information about a block */
void __print_block (struct _block * ptr) {
  if (ptr != NULL) {
    pr_info("%p; %zu Bytes; %slitteral; [init] : %li ",
      (char*)ptr->ptr, ptr->size,
      ptr->is_litteral_string ? "" : "not ", ptr->init_cpt);
    if(ptr->init_ptr != NULL) {
      unsigned i;
      for(i = 0; i < ptr->size; i++) {
        int ind = i / 8;
        int one_bit = (unsigned)1 << (8 - (i % 8) - 1);
        pr_info("%i", (ptr->init_ptr[ind] & one_bit) != 0);
      }
    }
    pr_info("\n");
  }
}

/********************/
/* CLEAN            */
/********************/

/* erase information about initialization of a block */
void __clean_init (struct _block * ptr) {
  if(ptr->init_ptr != NULL) {
    kfree(ptr->init_ptr);
    ptr->init_ptr = NULL;
  }
  ptr->init_cpt = 0;
}


/* erase all information about a block */
void __clean_block (struct _block * ptr) {
  if(ptr == NULL) return;
  __clean_init(ptr);
  kfree(ptr);
}


/* erase the content of the abstract structure */
void __e_acsl_memory_clean() {
  __clean_struct();
}

/**********************/
/* DEBUG              */
/**********************/

/* print the content of the abstract structure */
void __debug(void) {
  __debug_struct();
}
