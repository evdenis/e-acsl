/* run.config
   COMMENT: labeled stmt and gotos
   EXECNOW: LOG gen_labeled_stmt.c BIN gen_labeled_stmt.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/labeled_stmt.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_labeled_stmt.c > /dev/null && ./gcc_runtime.sh labeled_stmt
   EXECNOW: LOG gen_labeled_stmt2.c BIN gen_labeled_stmt2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/labeled_stmt.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_labeled_stmt2.c > /dev/null && ./gcc_runtime.sh labeled_stmt2
*/

int X = 0;

/*@ ensures X == 3; */
int main(void) {
  goto L1;
 L1: /*@ assert X == 0; */ X = 1;
  goto L2;
 L2: /*@ requires X == 1; ensures X == 2; */ X = 2;
  if (X) { X = 3; return 0; }
  return 0;
}
