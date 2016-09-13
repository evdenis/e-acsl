/* run.config
   COMMENT: addrOf
   EXECNOW: LOG gen_addrOf.c BIN gen_addrOf.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/addrOf.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_addrOf.c > /dev/null && ./gcc_runtime.sh addrOf
   EXECNOW: LOG gen_addrOf2.c BIN gen_addrOf2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/addrOf.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_addrOf2.c > /dev/null && ./gcc_runtime.sh addrOf2
*/

void f(){
  int m, *u, *p;
  u = &m;
  p = u;
  m = 123;
  //@ assert \initialized(p);
}

int main(void) {
  int x = 0;
  f();
  /*@ assert &x == &x; */ ;
  return 0;
}
