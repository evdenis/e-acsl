/* run.config
   COMMENT: alias
   EXECNOW: LOG gen_alias.c BIN gen_alias.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/alias.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_alias.c > /dev/null && ./gcc_runtime.sh alias
   EXECNOW: LOG gen_alias2.c BIN gen_alias2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/alias.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_alias2.c > /dev/null && ./gcc_runtime.sh alias2
*/

void f(int* dest, int val)
{
  int *ptr = dest;
  *ptr = val;
}

int main() {
  int i;
  f(&i, 255);
  /*@ assert \initialized(&i); */
  return 0;
}
