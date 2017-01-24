/* run.config
   COMMENT: function contract involving \valid
   STDOPT: +"-val-builtin malloc:Frama_C_alloc_size -val-builtin free:Frama_C_free"
*/

#include <stdlib.h>

struct list {
  int element;
  struct list * next;
};

/*@
  @ behavior B1:
  @  assumes l == \null;
  @  ensures \result == l;
  @ behavior B2:
  @  assumes ! \valid(l);
  @  assumes ! \valid(l->next);
  @  ensures \result == l;
*/
struct list * f(struct list * l) {
  /* length = 0 */
  if(l == NULL) return l;
  /* length = 1 : already sorted */
  if(l->next == NULL) return l;

  return NULL;
}

int main() {
  f(NULL);
  return 0;
}
