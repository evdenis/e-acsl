/* Generated by Frama-C */
typedef unsigned char uint8;
int main(void)
{
  int __retres;
  uint8 x;
  x = (unsigned char)0;
  /*@ assert x ≡ 0; */
  __e_acsl_assert(x == 0,(char *)"Assertion",(char *)"main",(char *)"x == 0",
                  9);
  __retres = 0;
  return __retres;
}

