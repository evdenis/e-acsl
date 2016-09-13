/* run.config
   COMMENT: \freeable
   STDOPT: +"-val-builtin __malloc:Frama_C_alloc_size -val-builtin __free:Frama_C_free"
   EXECNOW: LOG gen_freeable.c BIN gen_freeable.out @frama-c@ -machdep gcc_x86_64 -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/freeable.c -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_freeable.c > /dev/null && ./gcc_runtime.sh freeable
   EXECNOW: LOG gen_freeable2.c BIN gen_freeable2.out @frama-c@ -machdep gcc_x86_64 -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/freeable.c -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_freeable2.c > /dev/null && ./gcc_runtime.sh freeable2
*/

#include "stdlib.h"

extern void *malloc(size_t p);
extern void free(void* p);

int main(void) {
  int *p;
  /*@ assert ! \freeable(p); */
  /*@ assert ! \freeable((void*)0); */
  p = (int*)malloc(4*sizeof(int));
  /*@ assert ! \freeable(p+1); */
  /*@ assert \freeable(p); */
  free(p);
  /*@ assert ! \freeable(p); */
}
