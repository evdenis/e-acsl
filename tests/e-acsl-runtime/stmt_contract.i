/* run.config
   COMMENT: stmt contract
   EXECNOW: LOG gen_stmt_contract.c BIN gen_stmt_contract.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/stmt_contract.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_stmt_contract.c > /dev/null && ./gcc_runtime.sh stmt_contract
   EXECNOW: LOG gen_stmt_contract2.c BIN gen_stmt_contract2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/stmt_contract.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_stmt_contract2.c > /dev/null && ./gcc_runtime.sh stmt_contract2
*/
int main(void) {
  int x = 0, y = 2;
  // one ensures
  /*@ ensures x == 1; */
  x = 1;
  // several ensures
  /*@ ensures x == 2;
    @ ensures y == 2; */
  x = 2;
  // one requires
  /*@ requires x == 2; */
  x = x + 1;
  // several requires
  /*@ requires x == 3;
    @ requires y == 2; */
  x = x + y;
  // several behaviors
  /*@ behavior b1: 
    @   requires x == 5;
    @   ensures x == 3; 
    @ behavior b2:
    @   requires x == 3+y;
    @   requires y == 2;
    @   ensures x == y+1; */
  x = 3;
  // mix requires and assumes
  /*@ behavior b1:
    @   assumes x == 1;
    @   requires x == 0; 
    @ behavior b2:
    @   assumes x == 3;
    @   assumes y == 2;
    @   requires x == 3;
    @   requires x + y == 5; */
  x = x + y;

  /*@ requires x == 5; */
  /*@ requires y == 2; */
  x = x + y;

  /*@ requires x == 7; 
    @ ensures x == 7; */
  return 0;
}
