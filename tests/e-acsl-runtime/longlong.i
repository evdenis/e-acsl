/* run.config
   COMMENT: upgrading longlong to GMP
   STDOPT: +"-val-ignore-recursive-calls"
   EXECNOW: LOG gen_longlong.c BIN gen_longlong.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/longlong.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_longlong.c > /dev/null && ./gcc_runtime.sh longlong
   EXECNOW: LOG gen_longlong2.c BIN gen_longlong2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/longlong.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_longlong2.c > /dev/null && ./gcc_runtime.sh longlong2
*/

unsigned long long my_pow(unsigned int x, unsigned int n) {
  int tmp;
  if (n <= 1) return 1;
  tmp = my_pow(x, n / 2);
  tmp *= tmp;
  if (n % 2 == 0) return tmp;
  return x * tmp;
}

int main(void) {
  unsigned long long x = my_pow(2, 63);
  /*@ assert (2 * x + 1) % 2 == 1; */
  return 0;
}
