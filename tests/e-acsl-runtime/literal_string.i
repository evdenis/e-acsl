/* run.config
   COMMENT: literal string
   EXECNOW: LOG gen_literal_string.c BIN gen_literal_string.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/literal_string.i -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_literal_string.c > /dev/null && ./gcc_runtime.sh literal_string
   EXECNOW: LOG gen_literal_string2.c BIN gen_literal_string2.out @frama-c@ -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/literal_string.i -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_literal_string2.c > /dev/null && ./gcc_runtime.sh literal_string2
*/

int main(void);

char *T = "bar";
int G = 0;

void f(void) {
  /*@ assert T[G] == 'b'; */ ;
  G++;
}

char *S = "foo";
char *S2 = "foo2";
int IDX = 1;
int G2 = 2;

int main(void) {
  char *SS = "ss";
  /*@ assert S[G2] == 'o'; */
  /*@ assert \initialized(S); */
  /*@ assert \valid_read(S2); */
  /*@ assert ! \valid(SS); */
  f();
  return 0;
}

char *U = "baz";
