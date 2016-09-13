/* run.config
   COMMENT: non integer constants
   EXECNOW: LOG gen_other_constants.c BIN gen_other_constants.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/other_constants.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_other_constants.c > /dev/null && ./gcc_runtime.sh other_constants
   EXECNOW: LOG gen_other_constants2.c BIN gen_other_constants2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/other_constants.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_other_constants2.c > /dev/null && ./gcc_runtime.sh other_constants2
*/

enum bool { false, true };

int main(void) {
  // waiting for clarification of semantics of ACSL's literal strings
  //  /*@ assert "toto" != "titi"; */
  /*@ assert 'c' == 'c'; */
  /*@ assert false != true; */
  return 0;
}
