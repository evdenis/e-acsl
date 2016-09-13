/* run.config
   COMMENT: assert \false
   EXECNOW: LOG gen_false.c BIN gen_false.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/false.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_false.c > /dev/null && ./gcc_runtime.sh false
   EXECNOW: LOG gen_false2.c BIN gen_false2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/false.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_false2.c > /dev/null && ./gcc_runtime.sh false2
*/
int main(void) {
  int x = 0;
  if (x) /*@ assert \false; */ ;
  return 0;
}
