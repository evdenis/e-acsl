/* run.config
   COMMENT: function call + initialized
   STDOPT: #"-cpp-extra-args=\"-I`@frama-c@ -print-share-path`/libc\"" +"-val-builtin __malloc:Frama_C_alloc_size -val-builtin __free:Frama_C_free"
   EXECNOW: LOG gen_vector.c BIN gen_vector.out @frama-c@ -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/vector.c -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_vector.c > /dev/null && ./gcc_runtime.sh vector
   EXECNOW: LOG gen_vector2.c BIN gen_vector2.out @frama-c@ -cpp-extra-args="-I`@frama-c@ -print-share-path`/libc" -e-acsl-share ./share/e-acsl ./tests/e-acsl-runtime/vector.c -e-acsl-gmp-only -e-acsl -then-on e-acsl -print -ocode ./tests/e-acsl-runtime/result/gen_vector2.c > /dev/null && ./gcc_runtime.sh vector2
*/

#include<stdlib.h>

int LAST;

int* new_inversed(int len, int *v) {
  int i, *p;
  // @ assert \valid(v) && \offset(v)+len*sizeof(int) <= \block_length(v);
  p = malloc(sizeof(int)*len);
  for(i=0; i<len; i++)
    p[i] = v[len-i-1];
  return p;
}

int main(void) {
  int x = 3;
  int v1[3]= { 1, 2, x }, *v2;
  // @ assert \valid(&v1[2]);
  LAST = v1[2]; 
  //@ assert \initialized(v1+2);
  v2 = new_inversed(3, v1);
  LAST = v2[2]; 
  //@ assert \initialized(v2+2);
  //@ assert LAST == 1;
  free(v2);
  return 0;
}
