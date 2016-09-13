/* run.config
   COMMENT: pointers and pointer arithmetic
   EXECNOW: LOG gen_ptr.c BIN gen_ptr.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/ptr.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_ptr.c > /dev/null && ./gcc_runtime.sh ptr
   EXECNOW: LOG gen_ptr2.c BIN gen_ptr2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/ptr.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_ptr2.c > /dev/null && ./gcc_runtime.sh ptr2
*/

int main(void) {

  int x = 1;
  int t[3] = { 2, 3, 4 };
  int *p = &x;

  /*@ assert *p == 1; */
  /*@ assert *t == 2; */
  /*@ assert *(t+2) == 4; */
  /*@ assert *(t+2*sizeof(int)/sizeof((int)0x0)) == 4; */

  for(int i = 0; i < 2; i++) {
    /*@ assert (*(t+i) == i+2); */ ;
    /*@ assert (*(t+(2-i)) == 4-i); */ ;
    /*@ assert (*(t+2-i) == 4-i); */ ;
    ;
  }

  p = t+2;
  t[2] = 5;
  /*@ assert *p == 5; */

  return 0;
}
