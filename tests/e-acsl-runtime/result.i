/* run.config
   COMMENT: \result
   EXECNOW: LOG gen_result.c BIN gen_result.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/result.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_result.c > /dev/null && ./gcc_runtime.sh result
   EXECNOW: LOG gen_result2.c BIN gen_result2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/result.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_result2.c > /dev/null && ./gcc_runtime.sh result2 -Wno-unused-but-set-variable
*/

/*@ ensures \result == (int)(x - x); */
int f(int x) { 
  x = 0; 
  return x; }

int Y = 1;

// does not work since it is converted into \result == \old(x) and, 
// in this particular case, the pre-state and the post-state are the same and 
// it does not work yet (related to issue in at.i).
// /*@ ensures \result == x; */ 
/*@ ensures \result == Y; */
int g(int x) { 
  return x; 
}

/*@ ensures \result == 0; */
int h() { return 0; }

int main(void) {
  f(1);
  g(Y);
  h();
  return 0;
}
