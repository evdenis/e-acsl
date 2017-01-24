/* run.config
   COMMENT: cast
   STDOPT: #"-no-warn-signed-downcast" #"-no-warn-unsigned-downcast"
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
