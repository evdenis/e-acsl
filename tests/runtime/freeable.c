/* run.config
   COMMENT: \freeable
   STDOPT: +"-val-builtin malloc:Frama_C_alloc_size -val-builtin free:Frama_C_free"
*/

#include <stdlib.h>

extern void *malloc(size_t p);
extern void free(void* p);

char array[1024];

int main(void) {
  int *p;
  /*@ assert ! \freeable(p); */
  /*@ assert ! \freeable((void*)0); */
  p = (int*)malloc(4*sizeof(int));
  /*@ assert ! \freeable(p+1); */
  /*@ assert \freeable(p); */
  free(p);
  /*@ assert ! \freeable(p); */

  // test cases for BTS #1830
  /*@ assert ! \freeable(array); */
  /*@ assert ! \freeable(&(array[5])); */
}
