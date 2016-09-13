/* run.config
   COMMENT: Compound initializers
   EXECNOW: LOG gen_compound_initializers.c  BIN gen_compound_initializers.out  @frama-c@ -machdep x86_64 -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/compound_initializers.c -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_compound_initializers.c > /dev/null && ./gcc_runtime.sh compound_initializers
   EXECNOW: LOG gen_compound_initializers2.c BIN gen_compound_initializers2.out @frama-c@ -machdep x86_64 -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/compound_initializers.c -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_compound_initializers2.c > /dev/null && ./gcc_runtime.sh compound_initializers2
*/



int _F;

char *_A[2] = { "XX", "YY" };
char *_B = "ZZ";
char *_C;
int _D[] = { 44, 88 };
int _E = 44;
int _F = 9;;

struct ST {
    char *str;
    int num;
};

struct ST _G[] = {
    {
        .str = "First",
        .num = 99
    },
    {
        .str = "Second",
        .num = 147
    }
};

int main(int argc, char **argv) {
    /*@ assert \valid(_A); */
    /*@ assert \valid_read(_A[0]); */
    /*@ assert \valid_read(_A[1]); */
    /*@ assert \valid_read(_B); */
    /*@ assert \valid(&_C); */
    /*@ assert \valid(_D); */
    /*@ assert \valid(&_E); */
    /*@ assert \valid(&_F); */
    /*@ assert _E == 44; */
    /*@ assert \valid(&_G); */
    /*@ assert _G[0].num == 99; */
    return 0;
}
