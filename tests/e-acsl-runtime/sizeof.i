/* run.config
   COMMENT: sizeof
   EXECNOW: LOG gen_sizeof.c BIN gen_sizeof.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/sizeof.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_sizeof.c > /dev/null && ./gcc_runtime.sh sizeof
   EXECNOW: LOG gen_sizeof2.c BIN gen_sizeof2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/sizeof.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_sizeof2.c > /dev/null && ./gcc_runtime.sh sizeof2
*/

int main(void) {
  int x = 0;
  x++; /* prevent GCC's warning */
  /*@ assert sizeof(int) == sizeof(x); */ ;
  return 0;
}
