/* run.config
   COMMENT: assert \null == 0
   EXECNOW: LOG gen_null.c BIN gen_null.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/null.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_null.c > /dev/null && ./gcc_runtime.sh null
   EXECNOW: LOG gen_null2.c BIN gen_null2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/null.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_null2.c > /dev/null && ./gcc_runtime.sh null2
*/

int main(void) {
  /*@ assert \null == 0; */
  return 0;
}
