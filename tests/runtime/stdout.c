/* run.config
   COMMENT: __fc_stdout et __fc_fopen
*/

#include<stdio.h>

int main(){
  FILE *f = stdout;
  FILE *f2 = fopen("/tmp/foo","wb");
  //@ assert f == stdout;
}
