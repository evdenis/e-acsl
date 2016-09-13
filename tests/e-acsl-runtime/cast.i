/* run.config
   COMMENT: cast
   STDOPT: #"-no-warn-signed-downcast" #"-no-warn-unsigned-downcast"
   EXECNOW: LOG gen_cast.c BIN gen_cast.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/cast.i -e-acsl -no-warn-signed-downcast -no-warn-unsigned-downcast -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_cast.c > /dev/null && ./gcc_runtime.sh cast
   EXECNOW: LOG gen_cast2.c BIN gen_cast2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/cast.i -e-acsl-gmp-only -no-warn-signed-downcast -no-warn-unsigned-downcast -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_cast2.c > /dev/null && ./gcc_runtime.sh cast2
*/

int main(void) {
  long x = 0;
  int y = 0;

  /*@ assert (int)x == y; */ ;
  /*@ assert x == (long)y; */ ;

  /*@ assert y == (int)0; */ ; // cast from integer to int
  /*@ assert (unsigned int) y == (unsigned int)0; */ ; /* cast from integer
  						          to unsigned int */

  /*@ assert y != (int)0xfffffffffffffff; */ ; // cast from integer to int
  /*@ assert (unsigned int) y != (unsigned int)0xfffffffffffffff; */ ; 
  /* cast from integer to unsigned int */

  return 0;
}
