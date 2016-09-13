/* run.config
   COMMENT: ghost code
   STDOPT: #"-cpp-extra-args=\"-I`@frama-c@ -print-share-path`/libc\"" +"-val-builtin __malloc:Frama_C_alloc_size -val-builtin __free:Frama_C_free"
   EXECNOW: LOG gen_ghost.c BIN gen_ghost.out @frama-c@ -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/ghost.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_ghost.c > /dev/null && ./gcc_runtime.sh ghost
   EXECNOW: LOG gen_ghost2.c BIN gen_ghost2.out @frama-c@ -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/ghost.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_ghost2.c > /dev/null && ./gcc_runtime.sh ghost2
*/

/*@ ghost int G = 0; */
/*@ ghost int *P; */

// /*@ ghost int foo(int *x) { return *x + 1; } */

int main(void) {
  /*@ ghost P = &G; */ ;
  /*@ ghost int *q = P; */
  /*@ ghost (*P)++; */
  /*@ assert *q == G; */
  //  /*@ ghost G = foo(&G); */
  //  /*@ assert G == 2; */
}
