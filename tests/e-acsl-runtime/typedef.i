/* run.config
   COMMENT: typedef (from a Bernard's bug report)
   EXECNOW: LOG gen_typedef.c BIN gen_typedef.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/typedef.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_typedef.c > /dev/null && ./gcc_runtime.sh typedef
   EXECNOW: LOG gen_typedef2.c BIN gen_typedef2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/typedef.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_typedef2.c > /dev/null && ./gcc_runtime.sh typedef2
*/

typedef unsigned char uint8;

int main(void) {
  uint8 x = 0;
  /*@ assert x == 0; */ ;
  return 0;
}
