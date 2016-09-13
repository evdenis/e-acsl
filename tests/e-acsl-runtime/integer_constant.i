/* run.config
   COMMENT: integer constant + a stmt after the assertion
   EXECNOW: LOG gen_integer_constant.c BIN gen_integer_constant.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/integer_constant.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_integer_constant.c > /dev/null && ./gcc_runtime.sh integer_constant
   EXECNOW: LOG gen_integer_constant2.c BIN gen_integer_constant2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/integer_constant.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_integer_constant2.c > /dev/null && ./gcc_runtime.sh integer_constant2
*/
int main(void) {
  int x;
  /*@ assert 0 == 0; */ x = 0;
  x++; /* prevent GCC's warning */
  /*@ assert 0 != 1; */
  /*@ assert 1152921504606846975 == 0xfffffffffffffff; */

  /*@ assert 0xffffffffffffffffffffffffffffffff == 0xffffffffffffffffffffffffffffffff; */

  return 0;
}
