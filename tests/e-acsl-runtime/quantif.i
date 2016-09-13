/* run.config
   COMMENT: quantifiers
   EXECNOW: LOG gen_quantif.c BIN gen_quantif.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/quantif.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_quantif.c > /dev/null && ./gcc_runtime.sh quantif
   EXECNOW: LOG gen_quantif2.c BIN gen_quantif2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/quantif.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_quantif2.c > /dev/null && ./gcc_runtime.sh quantif2
*/

int main(void) {

  // simple universal quantifications

  /*@ assert \forall integer x; 0 <= x <= 1 ==> x == 0 || x == 1; */
  /*@ assert \forall integer x; 0 < x <= 1 ==> x == 1; */
  /*@ assert \forall integer x; 0 < x < 1 ==> \false; */
  /*@ assert \forall integer x; 0 <= x < 1 ==> x == 0; */

  /* // multiple universal quantifications */

  /*@ assert \forall integer x,y,z; 0 <= x < 2 && 0 <= y < 5 && 0 <= z <= y
    ==> x+z <= y+1; */

  // simple existential quantification

  /*@ assert \exists int x; 0 <= x < 10 && x == 5; */

  // mixed universal and existential quantifications

  /*@ assert \forall int x; 0 <= x < 10
    ==> x % 2 == 0 ==> \exists integer y; 0 <= y <= x/2 && x == 2 * y; */

  return 0;
}
