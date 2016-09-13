/* run.config
   COMMENT: the contents of argv should be valid
   EXECNOW: LOG gen_mainargs.c BIN gen_mainargs.out @frama-c@ -machdep x86_64 -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/mainargs.c -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_mainargs.c > /dev/null && ./gcc_test.sh e-acsl-runtime mainargs "" bar baz
   EXECNOW: LOG gen_mainargs2.c BIN gen_mainargs2.out @frama-c@ -machdep x86_64 -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/mainargs.c -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_mainargs2.c > /dev/null && ./gcc_test.sh e-acsl-runtime mainargs2 "" bar baz
*/

#include <string.h>

int main(int argc, char **argv) {
  int i;

  /*@ assert \valid(&argc) ; */
  /*@ assert \valid(&argv) ; */
  /*@ assert \forall int k; 0 <= k && k < argc ==> \valid(argv + k) ; */
  /*@ assert \block_length(argv) == (argc+1)*sizeof(char*) ; */

  /*@ assert argv[argc] == \null ; */
  /*@ assert ! \valid(argv[argc]) ; */
  for (i = 0; i < argc; i++) {
    int len = strlen(argv[i]);
    /*@ assert \valid(argv[i]) ; */
    /*@ assert \forall int k; 0 <= k && k <= len ==> \valid(&argv[i][k]) ; */
  }
}
