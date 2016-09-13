/* run.config
   COMMENT: initialization of globals (bts #1818)
   EXECNOW: LOG gen_init.c BIN gen_init.out @frama-c@ -machdep x86_64 -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/init.c -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_init.c > /dev/null && ./gcc_runtime.sh init
   EXECNOW: LOG gen_init2.c BIN gen_init2.out @frama-c@ -machdep x86_64 -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/init.c -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_init2.c > /dev/null && ./gcc_runtime.sh init2
*/

int a = 0, b;

int main(void) {
  int *p = &a, *q = &b;
  /*@assert \initialized(&b) ; */
  /*@assert \initialized(q) ; */
  /*@assert \initialized(p) ; */
}
