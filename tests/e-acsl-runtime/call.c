/* run.config
   COMMENT: function call
   STDOPT: #"-cpp-extra-args=\"-I`@frama-c@ -print-share-path`/libc\"" +"-val-builtin __malloc:Frama_C_alloc_size -val-builtin __free:Frama_C_free"
   EXECNOW: LOG gen_call.c BIN gen_call.out @frama-c@ -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/call.c -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_call.c > /dev/null && ./gcc_runtime.sh call
   EXECNOW: LOG gen_call2.c BIN gen_call2.out @frama-c@ -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/call.c -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_call2.c > /dev/null && ./gcc_runtime.sh call2
*/

#include <stdlib.h>

extern void *malloc(unsigned int size);

/*@ ensures \valid(\result); */
int *f(int *x, int *y) {
  *y = 1;
  return x;
}

int main() {
  int x = 0, *p, *q = malloc(sizeof(int)), *r = malloc(sizeof(int));
  p = f(&x, q);
  q = f(&x, r);
  return 0;
}
