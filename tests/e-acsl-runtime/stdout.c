/* run.config
   COMMENT: __fc_stdout et __fc_fopen
   STDOPT: #"-pp-annot"
   EXECNOW: LOG gen_stdout.c BIN gen_stdout.out @frama-c@ -machdep x86_64 -pp-annot -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/stdout.c -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_stdout.c > /dev/null && ./gcc_runtime.sh stdout
   EXECNOW: LOG gen_stdout2.c BIN gen_stdout2.out @frama-c@ -machdep x86_64 -pp-annot -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/stdout.c -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_stdout2.c > /dev/null && ./gcc_runtime.sh stdout2
*/

#include<stdio.h>

int main(){
  FILE *f = stdout;
  FILE *f2 = fopen("/tmp/foo","wb");
  //@ assert f == stdout;
}
