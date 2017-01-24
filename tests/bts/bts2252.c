/* run.config
   COMMENT: bts #2252, failures due to typing of offsets
*/

int *p;
int main(void) {
  int i = -1;
  int t[10];
  /*@ assert ! \valid_read(t+i); */
  p = t;
  /*@ assert ! \valid_read(p+i); */
  return 0;
}
