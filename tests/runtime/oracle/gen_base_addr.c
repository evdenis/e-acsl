/* Generated by Frama-C */
int A[4] = {1, 2, 3, 4};
int *PA;
void __e_acsl_globals_init(void)
{
  __e_acsl_store_block((void *)(& PA),8UL);
  __e_acsl_full_init((void *)(& PA));
  __e_acsl_store_block((void *)(A),16UL);
  __e_acsl_full_init((void *)(& A));
  return;
}

int main(void)
{
  int __retres;
  int a[4];
  int *pa;
  long l;
  char *pl;
  short *pi;
  char *p;
  char *pd;
  long *q;
  long *qd;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __e_acsl_globals_init();
  __e_acsl_store_block((void *)(& qd),8UL);
  __e_acsl_store_block((void *)(& q),8UL);
  __e_acsl_store_block((void *)(& pd),8UL);
  __e_acsl_store_block((void *)(& p),8UL);
  __e_acsl_store_block((void *)(& pi),8UL);
  __e_acsl_store_block((void *)(& pl),8UL);
  __e_acsl_store_block((void *)(& l),8UL);
  __e_acsl_store_block((void *)(& pa),8UL);
  __e_acsl_store_block((void *)(a),16UL);
  PA = (int *)(& A);
  /*@ assert \base_addr((int *)A) ≡ \base_addr(PA); */
  {
    void *__gen_e_acsl_base_addr;
    void *__gen_e_acsl_base_addr_2;
    __gen_e_acsl_base_addr = __e_acsl_base_addr((void *)(A));
    __gen_e_acsl_base_addr_2 = __e_acsl_base_addr((void *)PA);
    __e_acsl_assert(__gen_e_acsl_base_addr == __gen_e_acsl_base_addr_2,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr((int *)A) == \\base_addr(PA)",13);
  }
  /*@ assert \base_addr(&A[3]) ≡ \base_addr(PA); */
  {
    void *__gen_e_acsl_base_addr_3;
    void *__gen_e_acsl_base_addr_4;
    __gen_e_acsl_base_addr_3 = __e_acsl_base_addr((void *)(& A[3L]));
    __gen_e_acsl_base_addr_4 = __e_acsl_base_addr((void *)PA);
    __e_acsl_assert(__gen_e_acsl_base_addr_3 == __gen_e_acsl_base_addr_4,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(&A[3]) == \\base_addr(PA)",14);
  }
  PA ++;
  /*@ assert \base_addr(PA) ≡ \base_addr((int *)A); */
  {
    void *__gen_e_acsl_base_addr_5;
    void *__gen_e_acsl_base_addr_6;
    __gen_e_acsl_base_addr_5 = __e_acsl_base_addr((void *)PA);
    __gen_e_acsl_base_addr_6 = __e_acsl_base_addr((void *)(A));
    __e_acsl_assert(__gen_e_acsl_base_addr_5 == __gen_e_acsl_base_addr_6,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(PA) == \\base_addr((int *)A)",16);
  }
  /*@ assert \base_addr(PA + 2) ≡ \base_addr(&A[3]); */
  {
    void *__gen_e_acsl_base_addr_7;
    void *__gen_e_acsl_base_addr_8;
    __gen_e_acsl_base_addr_7 = __e_acsl_base_addr((void *)(PA + 2L));
    __gen_e_acsl_base_addr_8 = __e_acsl_base_addr((void *)(& A[3L]));
    __e_acsl_assert(__gen_e_acsl_base_addr_7 == __gen_e_acsl_base_addr_8,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(PA + 2) == \\base_addr(&A[3])",17);
  }
  __e_acsl_initialize((void *)(a),sizeof(int));
  a[0] = 1;
  __e_acsl_initialize((void *)(& a[1]),sizeof(int));
  a[1] = 2;
  __e_acsl_initialize((void *)(& a[2]),sizeof(int));
  a[2] = 3;
  __e_acsl_initialize((void *)(& a[3]),sizeof(int));
  a[3] = 4;
  __e_acsl_full_init((void *)(& pa));
  pa = (int *)(& a);
  /*@ assert \base_addr((int *)a) ≡ \base_addr(pa); */
  {
    void *__gen_e_acsl_base_addr_9;
    void *__gen_e_acsl_base_addr_10;
    __gen_e_acsl_base_addr_9 = __e_acsl_base_addr((void *)(a));
    __gen_e_acsl_base_addr_10 = __e_acsl_base_addr((void *)pa);
    __e_acsl_assert(__gen_e_acsl_base_addr_9 == __gen_e_acsl_base_addr_10,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr((int *)a) == \\base_addr(pa)",24);
  }
  /*@ assert \base_addr(&a[3]) ≡ \base_addr(pa); */
  {
    void *__gen_e_acsl_base_addr_11;
    void *__gen_e_acsl_base_addr_12;
    __gen_e_acsl_base_addr_11 = __e_acsl_base_addr((void *)(& a[3L]));
    __gen_e_acsl_base_addr_12 = __e_acsl_base_addr((void *)pa);
    __e_acsl_assert(__gen_e_acsl_base_addr_11 == __gen_e_acsl_base_addr_12,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(&a[3]) == \\base_addr(pa)",25);
  }
  __e_acsl_full_init((void *)(& pa));
  pa ++;
  /*@ assert \base_addr(pa) ≡ \base_addr((int *)a); */
  {
    void *__gen_e_acsl_base_addr_13;
    void *__gen_e_acsl_base_addr_14;
    __gen_e_acsl_base_addr_13 = __e_acsl_base_addr((void *)pa);
    __gen_e_acsl_base_addr_14 = __e_acsl_base_addr((void *)(a));
    __e_acsl_assert(__gen_e_acsl_base_addr_13 == __gen_e_acsl_base_addr_14,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(pa) == \\base_addr((int *)a)",27);
  }
  /*@ assert \base_addr(pa + 2) ≡ \base_addr((int *)a); */
  {
    void *__gen_e_acsl_base_addr_15;
    void *__gen_e_acsl_base_addr_16;
    __gen_e_acsl_base_addr_15 = __e_acsl_base_addr((void *)(pa + 2L));
    __gen_e_acsl_base_addr_16 = __e_acsl_base_addr((void *)(a));
    __e_acsl_assert(__gen_e_acsl_base_addr_15 == __gen_e_acsl_base_addr_16,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(pa + 2) == \\base_addr((int *)a)",
                    28);
  }
  __e_acsl_full_init((void *)(& l));
  l = (long)4;
  __e_acsl_full_init((void *)(& pl));
  pl = (char *)(& l);
  /*@ assert \base_addr(&l) ≡ \base_addr(pl); */
  {
    void *__gen_e_acsl_base_addr_17;
    void *__gen_e_acsl_base_addr_18;
    __gen_e_acsl_base_addr_17 = __e_acsl_base_addr((void *)(& l));
    __gen_e_acsl_base_addr_18 = __e_acsl_base_addr((void *)pl);
    __e_acsl_assert(__gen_e_acsl_base_addr_17 == __gen_e_acsl_base_addr_18,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(&l) == \\base_addr(pl)",33);
  }
  /*@ assert \base_addr(pl + 2) ≡ \base_addr(&l); */
  {
    void *__gen_e_acsl_base_addr_19;
    void *__gen_e_acsl_base_addr_20;
    __gen_e_acsl_base_addr_19 = __e_acsl_base_addr((void *)(pl + 2L));
    __gen_e_acsl_base_addr_20 = __e_acsl_base_addr((void *)(& l));
    __e_acsl_assert(__gen_e_acsl_base_addr_19 == __gen_e_acsl_base_addr_20,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(pl + 2) == \\base_addr(&l)",34);
  }
  __e_acsl_full_init((void *)(& pi));
  pi = (short *)(& l);
  __e_acsl_full_init((void *)(& pi));
  pi ++;
  __e_acsl_full_init((void *)(& pl));
  pl ++;
  /*@ assert \base_addr(pi) ≡ \base_addr(pl); */
  {
    void *__gen_e_acsl_base_addr_21;
    void *__gen_e_acsl_base_addr_22;
    __gen_e_acsl_base_addr_21 = __e_acsl_base_addr((void *)pi);
    __gen_e_acsl_base_addr_22 = __e_acsl_base_addr((void *)pl);
    __e_acsl_assert(__gen_e_acsl_base_addr_21 == __gen_e_acsl_base_addr_22,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(pi) == \\base_addr(pl)",38);
  }
  /*@ assert \base_addr(pl) ≡ \base_addr(&l); */
  {
    void *__gen_e_acsl_base_addr_23;
    void *__gen_e_acsl_base_addr_24;
    __gen_e_acsl_base_addr_23 = __e_acsl_base_addr((void *)pl);
    __gen_e_acsl_base_addr_24 = __e_acsl_base_addr((void *)(& l));
    __e_acsl_assert(__gen_e_acsl_base_addr_23 == __gen_e_acsl_base_addr_24,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(pl) == \\base_addr(&l)",39);
  }
  __e_acsl_full_init((void *)(& p));
  p = (char *)malloc((unsigned long)12);
  __e_acsl_full_init((void *)(& pd));
  pd = p;
  /*@ assert \base_addr(p) ≡ \base_addr(pd); */
  {
    void *__gen_e_acsl_base_addr_25;
    void *__gen_e_acsl_base_addr_26;
    __gen_e_acsl_base_addr_25 = __e_acsl_base_addr((void *)p);
    __gen_e_acsl_base_addr_26 = __e_acsl_base_addr((void *)pd);
    __e_acsl_assert(__gen_e_acsl_base_addr_25 == __gen_e_acsl_base_addr_26,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(p) == \\base_addr(pd)",44);
  }
  /*@ assert \base_addr(p + 1) ≡ \base_addr(pd + 5); */
  {
    void *__gen_e_acsl_base_addr_27;
    void *__gen_e_acsl_base_addr_28;
    __gen_e_acsl_base_addr_27 = __e_acsl_base_addr((void *)(p + 1L));
    __gen_e_acsl_base_addr_28 = __e_acsl_base_addr((void *)(pd + 5L));
    __e_acsl_assert(__gen_e_acsl_base_addr_27 == __gen_e_acsl_base_addr_28,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(p + 1) == \\base_addr(pd + 5)",45);
  }
  /*@ assert \base_addr(p + 11) ≡ \base_addr(pd + 1); */
  {
    void *__gen_e_acsl_base_addr_29;
    void *__gen_e_acsl_base_addr_30;
    __gen_e_acsl_base_addr_29 = __e_acsl_base_addr((void *)(p + 11L));
    __gen_e_acsl_base_addr_30 = __e_acsl_base_addr((void *)(pd + 1L));
    __e_acsl_assert(__gen_e_acsl_base_addr_29 == __gen_e_acsl_base_addr_30,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(p + 11) == \\base_addr(pd + 1)",46);
  }
  __e_acsl_full_init((void *)(& p));
  p += 5;
  /*@ assert \base_addr(p + 5) ≡ \base_addr(pd); */
  {
    void *__gen_e_acsl_base_addr_31;
    void *__gen_e_acsl_base_addr_32;
    __gen_e_acsl_base_addr_31 = __e_acsl_base_addr((void *)(p + 5L));
    __gen_e_acsl_base_addr_32 = __e_acsl_base_addr((void *)pd);
    __e_acsl_assert(__gen_e_acsl_base_addr_31 == __gen_e_acsl_base_addr_32,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(p + 5) == \\base_addr(pd)",48);
  }
  /*@ assert \base_addr(p - 5) ≡ \base_addr(pd); */
  {
    void *__gen_e_acsl_base_addr_33;
    void *__gen_e_acsl_base_addr_34;
    __gen_e_acsl_base_addr_33 = __e_acsl_base_addr((void *)(p - 5L));
    __gen_e_acsl_base_addr_34 = __e_acsl_base_addr((void *)pd);
    __e_acsl_assert(__gen_e_acsl_base_addr_33 == __gen_e_acsl_base_addr_34,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(p - 5) == \\base_addr(pd)",49);
  }
  __e_acsl_full_init((void *)(& q));
  q = (long *)malloc((unsigned long)30 * sizeof(long));
  __e_acsl_full_init((void *)(& qd));
  qd = q;
  /*@ assert \base_addr(q) ≡ \base_addr(qd); */
  {
    void *__gen_e_acsl_base_addr_35;
    void *__gen_e_acsl_base_addr_36;
    __gen_e_acsl_base_addr_35 = __e_acsl_base_addr((void *)q);
    __gen_e_acsl_base_addr_36 = __e_acsl_base_addr((void *)qd);
    __e_acsl_assert(__gen_e_acsl_base_addr_35 == __gen_e_acsl_base_addr_36,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(q) == \\base_addr(qd)",55);
  }
  __e_acsl_full_init((void *)(& q));
  q ++;
  /*@ assert \base_addr(q) ≡ \base_addr(qd); */
  {
    void *__gen_e_acsl_base_addr_37;
    void *__gen_e_acsl_base_addr_38;
    __gen_e_acsl_base_addr_37 = __e_acsl_base_addr((void *)q);
    __gen_e_acsl_base_addr_38 = __e_acsl_base_addr((void *)qd);
    __e_acsl_assert(__gen_e_acsl_base_addr_37 == __gen_e_acsl_base_addr_38,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(q) == \\base_addr(qd)",57);
  }
  __e_acsl_full_init((void *)(& q));
  q += 2;
  /*@ assert \base_addr(q) ≡ \base_addr(qd); */
  {
    void *__gen_e_acsl_base_addr_39;
    void *__gen_e_acsl_base_addr_40;
    __gen_e_acsl_base_addr_39 = __e_acsl_base_addr((void *)q);
    __gen_e_acsl_base_addr_40 = __e_acsl_base_addr((void *)qd);
    __e_acsl_assert(__gen_e_acsl_base_addr_39 == __gen_e_acsl_base_addr_40,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(q) == \\base_addr(qd)",59);
  }
  __e_acsl_full_init((void *)(& q));
  q += 4;
  /*@ assert \base_addr(q) ≡ \base_addr(qd); */
  {
    void *__gen_e_acsl_base_addr_41;
    void *__gen_e_acsl_base_addr_42;
    __gen_e_acsl_base_addr_41 = __e_acsl_base_addr((void *)q);
    __gen_e_acsl_base_addr_42 = __e_acsl_base_addr((void *)qd);
    __e_acsl_assert(__gen_e_acsl_base_addr_41 == __gen_e_acsl_base_addr_42,
                    (char *)"Assertion",(char *)"main",
                    (char *)"\\base_addr(q) == \\base_addr(qd)",61);
  }
  __retres = 0;
  __e_acsl_delete_block((void *)(& PA));
  __e_acsl_delete_block((void *)(A));
  __e_acsl_delete_block((void *)(& qd));
  __e_acsl_delete_block((void *)(& q));
  __e_acsl_delete_block((void *)(& pd));
  __e_acsl_delete_block((void *)(& p));
  __e_acsl_delete_block((void *)(& pi));
  __e_acsl_delete_block((void *)(& pl));
  __e_acsl_delete_block((void *)(& l));
  __e_acsl_delete_block((void *)(& pa));
  __e_acsl_delete_block((void *)(a));
  __e_acsl_memory_clean();
  return __retres;
}


