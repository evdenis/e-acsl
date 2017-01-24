/* run.config
   COMMENT: allocation and de-allocation of local variables
   STDOPT: +"-val-builtin malloc:Frama_C_alloc_size,free:Frama_C_free -no-val-malloc-returns-null"
*/

#include <stdlib.h>

extern void *malloc(size_t size);

struct list {
  int element;
  struct list * next;
};

struct list * add(struct list * l, int i) {
  struct list * new;
  new = malloc(sizeof(struct list));
  /*@ assert \valid(new); */
  new->element = i;
  new->next = l;
  return new;
}

int main() {
  struct list * l = NULL;
  l = add(l, 4);
  l = add(l, 7);
  return 0;
}
