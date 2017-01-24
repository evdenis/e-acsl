/* run.config
   COMMENT: \valid in presence of aliasing
   STDOPT: +"-val-builtin malloc:Frama_C_alloc_size,free:Frama_C_free -no-val-malloc-returns-null"
*/

#include "stdlib.h"

int main(void) {
  int *a, *b, n = 0;
  /*@ assert ! \valid(a) && ! \valid(b); */
  a = malloc(sizeof(int));
  *a = n;
  b = a;
  /*@ assert \valid(a) && \valid(b); */
  /*@ assert *b == n; */
  free(b);
  /*@ assert ! \valid(a) && ! \valid(b); */
  return 0;
}
