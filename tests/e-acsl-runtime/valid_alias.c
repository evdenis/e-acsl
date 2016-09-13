/* run.config
   COMMENT: \valid in presence of aliasing
   STDOPT: #"-cpp-extra-args=\"-I`@frama-c@ -print-share-path`/libc\"" +"-val-builtin __malloc:Frama_C_alloc_size -val-builtin __free:Frama_C_free"
   EXECNOW: LOG gen_valid_alias.c BIN gen_valid_alias.out @frama-c@ -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/valid_alias.c -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_valid_alias.c > /dev/null && ./gcc_runtime.sh valid_alias
   EXECNOW: LOG gen_valid_alias2.c BIN gen_valid_alias2.out @frama-c@ -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/valid_alias.c -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_valid_alias2.c > /dev/null && ./gcc_runtime.sh valid_alias2
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
