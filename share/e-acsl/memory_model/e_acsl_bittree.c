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

#include <errno.h>
#include <unistd.h>
#include "stdlib.h"
#include "stdbool.h"
#include "math.h"
#include "e_acsl_mmodel_api.h"
#include "e_acsl_bittree.h"
#include "e_acsl_mmodel.h"
#include "../e_acsl_printf.h"

#if WORDBITS == 16

const size_t Tmasks[] = {
0x0,0x8000,0xc000,0xe000,0xf000,0xf800,0xfc00,0xfe00,0xff00,0xff80,0xffc0,
0xffe0,0xfff0,0xfff8,0xfffc,0xfffe,0xffff};

const int Teq[] = {0,-1,3,-3,6,-5,7,-7,12,-9,11,-11,14,-13,15,16,-16};
const int Tneq[] = {0,0,1,-2,2,-4,5,-6,4,-8,9,-10,10,-12,13,-14,-15};

#elif WORDBITS == 32

const size_t Tmasks[] = {
0x0,0x80000000,0xc0000000,0xe0000000,0xf0000000,0xf8000000,0xfc000000,
0xfe000000,0xff000000,0xff800000,0xffc00000,0xffe00000,0xfff00000,0xfff80000,
0xfffc0000,0xfffe0000,0xffff0000,0xffff8000,0xffffc000,0xffffe000,0xfffff000,
0xfffff800,0xfffffc00,0xfffffe00,0xffffff00,0xffffff80,0xffffffc0,0xffffffe0,
0xfffffff0,0xfffffff8,0xfffffffc,0xfffffffe,0xffffffff};

const int Teq[] =
  { 0,-1,3,-3,6,-5,7,-7,12,-9,11,-11,14,-13,15,-15,24,-17,19,-19,22,
    -21,23,-23,28,-25,27,-27,30,-29,31,32,-32 };

const int Tneq[] =
  { 0,0,1,-2,2,-4,5,-6,4,-8,9,-10,10,-12,13,-14,8,-16,17,-18,18,-20,21,-22,20,
    -24,25,-26,26,-28,29,-30,-31 };

#else /* WORDBITS == 64 */

const size_t Tmasks[] = {
0x0,0x8000000000000000,0xc000000000000000,0xe000000000000000,0xf000000000000000,
0xf800000000000000,0xfc00000000000000,0xfe00000000000000,0xff00000000000000,
0xff80000000000000,0xffc0000000000000,0xffe0000000000000,0xfff0000000000000,
0xfff8000000000000,0xfffc000000000000,0xfffe000000000000,0xffff000000000000,
0xffff800000000000,0xffffc00000000000,0xffffe00000000000,0xfffff00000000000,
0xfffff80000000000,0xfffffc0000000000,0xfffffe0000000000,0xffffff0000000000,
0xffffff8000000000,0xffffffc000000000,0xffffffe000000000,0xfffffff000000000,
0xfffffff800000000,0xfffffffc00000000,0xfffffffe00000000,0xffffffff00000000,
0xffffffff80000000,0xffffffffc0000000,0xffffffffe0000000,0xfffffffff0000000,
0xfffffffff8000000,0xfffffffffc000000,0xfffffffffe000000,0xffffffffff000000,
0xffffffffff800000,0xffffffffffc00000,0xffffffffffe00000,0xfffffffffff00000,
0xfffffffffff80000,0xfffffffffffc0000,0xfffffffffffe0000,0xffffffffffff0000,
0xffffffffffff8000,0xffffffffffffc000,0xffffffffffffe000,0xfffffffffffff000,
0xfffffffffffff800,0xfffffffffffffc00,0xfffffffffffffe00,0xffffffffffffff00,
0xffffffffffffff80,0xffffffffffffffc0,0xffffffffffffffe0,0xfffffffffffffff0,
0xfffffffffffffff8,0xfffffffffffffffc,0xfffffffffffffffe,0xffffffffffffffff};


const int Teq[] =
  { 0,-1,3,-3,6,-5,7,-7,12,-9,11,-11,14,-13,15,-15,24,-17,19,-19,22,-21,23,-23,
    28,-25,27,-27,30,-29,31,-31,48,-33,35,-35,38,-37,39,-39,44,-41,43,-43,46,
    -45,47,-47,56,-49,51,-51,54,-53,55,-55,60,-57,59,-59,62,-61,63,64,-64 };

const int Tneq[] =
  { 0,0,1,-2,2,-4,5,-6,4,-8,9,-10,10,-12,13,-14,8,-16,17,-18,18,-20,21,-22,20,
    -24,25,-26,26,-28,29,-30,16,-32,33,-34,34,-36,37,-38,36,-40,41,-42,42,-44,
    45,-46,40,-48,49,-50,50,-52,53,-54,52,-56,57,-58,58,-60,61,-62,-63 };

#endif

struct bittree {
  _Bool is_leaf;
  size_t addr,  mask;
  struct bittree * left, * right, * father;
  struct _block * leaf;
} * __root = NULL;

/*unsigned cpt_mask = 0;*/

/* common prefix of two addresses */
/*@ assigns \nothing;
  @ ensures \forall int i;
     0 <= i <= WORDBITS
     ==> (Tmasks[i] & a) == (Tmasks[i] & b)
     ==> \result >= Tmasks[i];
  @ ensures (a & \result) == (b & \result);
  @ ensures \exists int i; 0 <= i <= WORDBITS && \result == Tmasks[i];
  @*/
size_t mask(size_t a, size_t b) {
  size_t nxor = ~(a ^ b), ret;
  int i = WORDBITS/2; /* dichotomic search, starting in the middle */
  /*cpt_mask++;*/

  /* if the current mask matches we use transition from Teq, else from Tneq
     we stop as soon as i is negative, meaning that we found the mask
     a negative element i from Teq or Tneq means stop and return Tmasks[-i] */
  /*@ loop invariant -WORDBITS <= i <= WORDBITS;
    @ loop assigns i;
    @*/
  while(i > 0) {
    //@ assert 0 < i <= WORDBITS;
    //@ assert \valid(Tmasks+i);
    if (nxor >= Tmasks[i])
      //@ assert \valid(Teq+i);
      i = Teq[i];
    else
      //@ assert \valid(Tneq+i);
      i = Tneq[i];
  }

  //@ assert -WORDBITS <= i <= 0;
  ret = Tmasks[-i];
  assert ((a & ret) == (b & ret));
  return ret;
}


/* called from __remove_element */
/* the block we are looking for has to be in the tree */
/*@ requires \valid(ptr);
  @ requires \valid(__root);
  @ assigns \nothing;
  @ ensures \valid(\result);
  @ ensures \result->leaf == ptr;
  @*/
struct bittree * __get_leaf_from_block (struct _block * ptr) {
  struct bittree * curr = __root;
  assert(__root != NULL);
  assert(ptr != NULL);

  /*@ loop assigns curr;
    @*/
  while(!curr->is_leaf) {
    // the prefix is consistent
    assert((curr->addr & curr->mask) == (ptr->ptr & curr->mask));
    // two sons
    assert(curr->left != NULL && curr->right != NULL);
    // the prefix of one son is consistent
    if((curr->right->addr & curr->right->mask)
       == (ptr->ptr & curr->right->mask))
      curr = curr->right;
    else if((curr->left->addr & curr->left->mask)
	    == (ptr->ptr & curr->left->mask))
      curr = curr->left;
    else
      assert(0);
  }
  assert(curr->is_leaf);
  assert(curr->leaf == ptr);
  return curr;
}


/* remove the block from the structure */
/* the block we are looking for has to be in the tree */
/*@ requires \valid(ptr);
  @*/
void __remove_element (struct _block * ptr) {
  struct bittree * leaf_to_delete = __get_leaf_from_block (ptr);
  assert(leaf_to_delete->leaf == ptr);

  if(leaf_to_delete->father == NULL)
    // the leaf is the root
    __root = NULL;
  else {
    struct bittree * brother, * father;
    father = leaf_to_delete->father;
    brother = (leaf_to_delete == father->left) ? father->right : father->left;
    assert(brother != NULL);
    // copying all brother's fields into the father's
    father->is_leaf = brother->is_leaf;
    father->addr = brother->addr;
    father->mask = brother->mask;
    father->left = brother->left;
    father->right = brother->right;
    father->leaf = brother->leaf;
    if(!brother->is_leaf) {
      brother->left->father = father;
      brother->right->father = father;
    }
    free(brother);
    /* necessary ? -- begin */
    if(father->father != NULL) {
      father->father->mask = mask(father->father->left->addr
				  & father->father->left->mask,
				  father->father->right->addr
				  & father->father->right->mask);
    }
    /* necessary ? -- end */
  }
  free(leaf_to_delete);
}


/* called from __add_element */
/* the returned node will be the brother of the soon to be added node */
/*@ requires \valid(ptr);
  @ requires \valid(__root);
  @ assigns \nothing;
  @ ensures \valid(\result);
  @*/
struct bittree * __most_similar_node (struct _block * ptr) {
  struct bittree * curr = __root;
  size_t left_prefix, right_prefix;
  assert(ptr != NULL);
  assert(__root != NULL);

  while(1) {
    if(curr->is_leaf)
      return curr;
    assert(curr->left != NULL && curr->right != NULL);
    left_prefix = mask(curr->left->addr & curr->left->mask, ptr->ptr);
    right_prefix = mask(curr->right->addr & curr->right->mask, ptr->ptr);
    if(left_prefix > right_prefix)
      curr = curr->left;
    else if(right_prefix > left_prefix)
      curr = curr->right;
    else
      return curr;
  }
}



/* add a block in the structure */
/*@ requires \valid(ptr);
  @*/
void __add_element (struct _block * ptr) {
  struct bittree * new_leaf;
  assert(ptr != NULL);

  new_leaf = malloc(sizeof(struct bittree));
  assert(new_leaf != NULL);
  new_leaf->is_leaf = true;
  new_leaf->addr = ptr->ptr;
  new_leaf->mask = Tmasks[WORDBITS]; /* ~0ul */
  new_leaf->left = NULL;
  new_leaf->right = NULL;
  new_leaf->father = NULL;
  new_leaf->leaf = ptr;

  if(__root == NULL)
    __root = new_leaf;
  else {
    struct bittree * brother = __most_similar_node (ptr), * father, * aux;

    assert(brother != NULL);
    father = malloc(sizeof(struct bittree));
    assert(father != NULL);
    father->is_leaf = false;
    father->addr = brother->addr & new_leaf->addr;
    /*father->mask = mask(brother->addr & brother->mask, ptr->ptr);*/
    father->leaf = NULL;
    if(new_leaf->addr <= brother->addr) {
      father->left = new_leaf;
      father->right = brother;
    } else {
      father->left = brother;
      father->right = new_leaf;
    }
    new_leaf->father = father;

    if(brother == __root) {
      father->father = NULL;
      father->mask = mask(brother->addr & brother->mask, ptr->ptr);
      __root = father;
    }
    else {
      if (brother->father->left == brother)
	brother->father->left = father;
      else
	brother->father->right = father;
      father->father = brother->father;

      /* necessary ? -- begin */
      aux = father;
      aux->mask = mask(aux->left->addr & aux->left->mask,
		       aux->right->addr & aux->right->mask);
      /* necessary ? -- end */
    }
    brother->father = father;
    if(!brother->is_leaf)
      brother->mask = mask(brother->left->addr & brother->left->mask,
			   brother->right->addr & brother->right->mask);

    assert((father->left == brother && father->right == new_leaf)
	   || (father->left == new_leaf && father->right == brother));
  }
}


/* return the block B such as: begin addr of B == ptr if such a block exists,
   return NULL otherwise */
/*@ assigns \nothing;
  @ ensures \valid(\result);
  @ ensures \result == \null || \result->ptr == (size_t)ptr;
  @*/
struct _block * __get_exact (void * ptr) {
  struct bittree * tmp = __root;
  assert(__root != NULL);
  assert(ptr != NULL);

  /*@ loop assigns tmp;
    @*/
  while(!tmp->is_leaf) {
    // if the ptr we are looking for does not share the prefix of tmp
    if((tmp->addr & tmp->mask) != ((size_t)ptr & tmp->mask)) return NULL;
    // two sons
    assert(tmp->left != NULL && tmp->right != NULL);
    // the prefix of one son is consistent
    if((tmp->right->addr & tmp->right->mask)
       == ((size_t)ptr & tmp->right->mask))
      tmp = tmp->right;
    else if((tmp->left->addr & tmp->left->mask)
	    == ((size_t)ptr & tmp->left->mask))
      tmp = tmp->left;
    else return NULL;
  }

  if(tmp->leaf->ptr != (size_t)ptr) return NULL;
  return tmp->leaf;
}


/* return the block B containing ptr, such as :
   begin addr of B <= ptr < (begin addr + size) of B
   or NULL if such a block does not exist */
struct _block * __get_cont (void * ptr) {
  struct bittree * tmp = __root;
  if(__root == NULL || ptr == NULL) return NULL;

  struct bittree * t [WORDBITS];
  short ind = -1;

  while(1) {
    if(tmp->is_leaf) {
      /* tmp cannot contain ptr because its begin addr is higher */
      if(tmp->addr > (size_t)ptr) {
	if(ind == -1)
	  return NULL;
	else {
	  tmp = t[ind];
	  ind--;
	  continue;
	}
      }
      /* tmp->addr <= ptr, tmp may contain ptr
	 ptr is contained if tmp is large enough (begin addr + size) */
      else if((size_t)ptr < tmp->leaf->size + tmp->addr
              || (tmp->leaf->size == 0 && (size_t)ptr == tmp->leaf->ptr))
	return tmp->leaf;
      /* tmp->addr <= ptr, but tmp->addr is not large enough */
      else if (ind == -1)
	return NULL;
      else {
	tmp = t[ind];
	ind--;
	continue;
      }
    }

    assert(tmp->left != NULL && tmp->right != NULL);

    /* the right child has the highest address, so we test it first */
    if(((size_t)tmp->right->addr & tmp->right->mask)
       <= ((size_t)ptr & tmp->right->mask)) {
      ind++;
      t[ind] = tmp->left;
      tmp = tmp->right;
    }
    else if(((size_t)tmp->left->addr & tmp->left->mask)
	    <= ((size_t)ptr & tmp->left->mask))
      tmp = tmp->left;
    else {
      if(ind == -1)
	return NULL;
      else {
	tmp = t[ind];
	ind--;
      }
    }
  }
}

/*******************/
/* CLEAN           */
/*******************/

/* called from __clean_struct */
/* recursively erase the content of the structure */
void __clean_rec (struct bittree * ptr) {
  if(ptr == NULL) return;
  else if(ptr->is_leaf) {
    __clean_block(ptr->leaf);
    ptr->leaf = NULL;
  }
  else {
    __clean_rec(ptr->left);
    __clean_rec(ptr->right);
    ptr->left = ptr->right = NULL;
  }
  free(ptr);
}

/* erase the content of the structure */
void __clean_struct () {
  __clean_rec(__root);
  __root = NULL;
  /*printf("%i &\n", cpt_mask);*/
}

/*********************/
/* DEBUG             */
/*********************/

/* called from __debug_struct */
/* recursively print the content of the structure */
/*@ assigns \nothing;
  @*/
void __debug_rec (struct bittree * ptr, int depth) {
  int i;
  if(ptr == NULL)
    return;
  for(i = 0; i < depth; i++)
    printf("  ");
  if(ptr->is_leaf)
    __print_block(ptr->leaf);
  else {
    printf("%p -- %p\n", (void*)ptr->mask, (void*)ptr->addr);
    __debug_rec(ptr->left, depth+1);
    __debug_rec(ptr->right, depth+1);
  }
}

/* print the content of the structure */
/*@ assigns \nothing;
  @*/
void __debug_struct () {
  printf("------------DEBUG\n");
  __debug_rec(__root, 0);
  printf("-----------------\n");
}
