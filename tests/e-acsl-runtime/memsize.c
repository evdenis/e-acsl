/* run.config
   COMMENT: Checking heap memory size
   EXECNOW: LOG gen_memsize.c  BIN gen_memsize.out  @frama-c@ -machdep=gcc_x86_$(getconf LONG_BIT) -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/memsize.c -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_memsize.c > /dev/null && ./gcc_runtime.sh memsize
   EXECNOW: LOG gen_memsize2.c BIN gen_memsize2.out @frama-c@ -machdep=gcc_x86_$(getconf LONG_BIT) -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/memsize.c -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_memsize2.c > /dev/null && ./gcc_runtime.sh memsize2
*/

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>

# ifndef UINTPTR_MAX
# if __WORDSIZE == 64
#  define UINTPTR_MAX (18446744073709551615UL)
# else
#  define UINTPTR_MAX (4294967295U)
# endif
# endif

extern size_t __memory_size;

int main(int argc, char **argv) {
    // Allocation increases
    char *a = malloc(7);
    /*@assert (__memory_size == 7);  */
    char *b = malloc(14);
    /*@assert (__memory_size == 21);  */

    // Allocation decreases
    free(a);
    /*@assert (__memory_size == 14);  */

    // Make sure that free with NULL behaves and does not affect allocation
    a = NULL;
    free(a);
    /*@assert (__memory_size == 14);  */

    // Realloc decreases allocation
    b = realloc(b, 9);
    /*@assert (__memory_size == 9);  */

    // Realloc increases allocation
    b = realloc(b, 18);
    /*@assert (__memory_size == 18);  */

    // Realloc with 0 is equivalent to free
    b = realloc(b, 0);
    b = NULL;
    /*@assert (__memory_size == 0);  */

    // realloc with 0 is equivalent to malloc
    b = realloc(b, 8);
    /*@assert (__memory_size == 8);  */

    // Abandon b and behave like malloc again
    b = realloc(NULL, 8);
    /*@assert (__memory_size == 16);  */

    // Make realloc fail by supplying a huge number
    b = realloc(NULL, UINTPTR_MAX);
    /*@assert (__memory_size == 16);  */
    /*@assert (b == NULL);  */

    // Same as test for calloc ...
    b = calloc(UINTPTR_MAX,UINTPTR_MAX);
    /*@assert (__memory_size == 16);  */
    /*@assert (b == NULL);  */

    // ... and for malloc
    b = malloc(UINTPTR_MAX);
    /*@assert (__memory_size == 16);  */
    /*@assert (b == NULL);  */
    return 0;
}
