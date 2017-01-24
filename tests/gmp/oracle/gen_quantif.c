/* Generated by Frama-C */
int main(void)
{
  int __retres;
  /*@ assert ∀ ℤ x; 0 ≤ x ≤ 1 ⇒ x ≡ 0 ∨ x ≡ 1; */
  {
    int __gen_e_acsl_forall;
    int __gen_e_acsl_x;
    __gen_e_acsl_forall = 1;
    __gen_e_acsl_x = 0;
    while (1) {
      if (__gen_e_acsl_x <= 1) ; else break;
      {
        int __gen_e_acsl_or;
        if (__gen_e_acsl_x == 0) __gen_e_acsl_or = 1;
        else __gen_e_acsl_or = __gen_e_acsl_x == 1;
        if (__gen_e_acsl_or) ;
        else {
          __gen_e_acsl_forall = 0;
          goto e_acsl_end_loop1;
        }
      }
      __gen_e_acsl_x ++;
    }
    e_acsl_end_loop1: ;
    __e_acsl_assert(__gen_e_acsl_forall,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall integer x; 0 <= x <= 1 ==> x == 0 || x == 1",
                    9);
  }
  /*@ assert ∀ ℤ x; 0 < x ≤ 1 ⇒ x ≡ 1; */
  {
    int __gen_e_acsl_forall_2;
    int __gen_e_acsl_x_2;
    __gen_e_acsl_forall_2 = 1;
    __gen_e_acsl_x_2 = 0 + 1;
    while (1) {
      if (__gen_e_acsl_x_2 <= 1) ; else break;
      if (__gen_e_acsl_x_2 == 1) ;
      else {
        __gen_e_acsl_forall_2 = 0;
        goto e_acsl_end_loop2;
      }
      __gen_e_acsl_x_2 ++;
    }
    e_acsl_end_loop2: ;
    __e_acsl_assert(__gen_e_acsl_forall_2,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall integer x; 0 < x <= 1 ==> x == 1",10);
  }
  /*@ assert ∀ ℤ x; 0 < x < 1 ⇒ \false; */
  {
    int __gen_e_acsl_forall_3;
    int __gen_e_acsl_x_3;
    __gen_e_acsl_forall_3 = 1;
    __gen_e_acsl_x_3 = 0 + 1;
    while (1) {
      if (__gen_e_acsl_x_3 < 1) ; else break;
      if (0) ;
      else {
        __gen_e_acsl_forall_3 = 0;
        goto e_acsl_end_loop3;
      }
      __gen_e_acsl_x_3 ++;
    }
    e_acsl_end_loop3: ;
    __e_acsl_assert(__gen_e_acsl_forall_3,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall integer x; 0 < x < 1 ==> \\false",11);
  }
  /*@ assert ∀ ℤ x; 0 ≤ x < 1 ⇒ x ≡ 0; */
  {
    int __gen_e_acsl_forall_4;
    int __gen_e_acsl_x_4;
    __gen_e_acsl_forall_4 = 1;
    __gen_e_acsl_x_4 = 0;
    while (1) {
      if (__gen_e_acsl_x_4 < 1) ; else break;
      if (__gen_e_acsl_x_4 == 0) ;
      else {
        __gen_e_acsl_forall_4 = 0;
        goto e_acsl_end_loop4;
      }
      __gen_e_acsl_x_4 ++;
    }
    e_acsl_end_loop4: ;
    __e_acsl_assert(__gen_e_acsl_forall_4,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall integer x; 0 <= x < 1 ==> x == 0",12);
  }
  /*@ assert
      ∀ ℤ x, ℤ y, ℤ z;
        0 ≤ x < 2 ∧ 0 ≤ y < 5 ∧ 0 ≤ z ≤ y ⇒ x + z ≤ y + 1;
  */
  {
    int __gen_e_acsl_forall_5;
    int __gen_e_acsl_x_5;
    int __gen_e_acsl_y;
    int __gen_e_acsl_z;
    __gen_e_acsl_forall_5 = 1;
    __gen_e_acsl_x_5 = 0;
    while (1) {
      if (__gen_e_acsl_x_5 < 2) ; else break;
      __gen_e_acsl_y = 0;
      while (1) {
        if (__gen_e_acsl_y < 5) ; else break;
        __gen_e_acsl_z = 0;
        while (1) {
          if (__gen_e_acsl_z <= __gen_e_acsl_y) ; else break;
          if (__gen_e_acsl_x_5 + __gen_e_acsl_z <= __gen_e_acsl_y + 1) 
            ;
          else {
            __gen_e_acsl_forall_5 = 0;
            goto e_acsl_end_loop5;
          }
          __gen_e_acsl_z ++;
        }
        __gen_e_acsl_y ++;
      }
      __gen_e_acsl_x_5 ++;
    }
    e_acsl_end_loop5: ;
    __e_acsl_assert(__gen_e_acsl_forall_5,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall integer x, integer y, integer z;\n  0 <= x < 2 && 0 <= y < 5 && 0 <= z <= y ==> x + z <= y + 1",
                    16);
  }
  /*@ assert ∃ int x; 0 ≤ x < 10 ∧ x ≡ 5; */
  {
    int __gen_e_acsl_exists;
    int __gen_e_acsl_x_6;
    __gen_e_acsl_exists = 0;
    __gen_e_acsl_x_6 = 0;
    while (1) {
      if (__gen_e_acsl_x_6 < 10) ; else break;
      if (! (__gen_e_acsl_x_6 == 5)) ;
      else {
        __gen_e_acsl_exists = 1;
        goto e_acsl_end_loop6;
      }
      __gen_e_acsl_x_6 ++;
    }
    e_acsl_end_loop6: ;
    __e_acsl_assert(__gen_e_acsl_exists,(char *)"Assertion",(char *)"main",
                    (char *)"\\exists int x; 0 <= x < 10 && x == 5",21);
  }
  /*@ assert
      ∀ int x;
        0 ≤ x < 10 ⇒
        x % 2 ≡ 0 ⇒ (∃ ℤ y; 0 ≤ y ≤ x / 2 ∧ x ≡ 2 * y);
  */
  {
    int __gen_e_acsl_forall_6;
    int __gen_e_acsl_x_7;
    __gen_e_acsl_forall_6 = 1;
    __gen_e_acsl_x_7 = 0;
    while (1) {
      if (__gen_e_acsl_x_7 < 10) ; else break;
      {
        int __gen_e_acsl_implies;
        if (! (__gen_e_acsl_x_7 % 2 == 0)) __gen_e_acsl_implies = 1;
        else {
          int __gen_e_acsl_exists_2;
          int __gen_e_acsl_y_2;
          __gen_e_acsl_exists_2 = 0;
          __gen_e_acsl_y_2 = 0;
          while (1) {
            if (__gen_e_acsl_y_2 <= __gen_e_acsl_x_7 / 2) ; else break;
            if (! (__gen_e_acsl_x_7 == 2 * __gen_e_acsl_y_2)) ;
            else {
              __gen_e_acsl_exists_2 = 1;
              goto e_acsl_end_loop7;
            }
            __gen_e_acsl_y_2 ++;
          }
          e_acsl_end_loop7: ;
          __gen_e_acsl_implies = __gen_e_acsl_exists_2;
        }
        if (__gen_e_acsl_implies) ;
        else {
          __gen_e_acsl_forall_6 = 0;
          goto e_acsl_end_loop8;
        }
      }
      __gen_e_acsl_x_7 ++;
    }
    e_acsl_end_loop8: ;
    __e_acsl_assert(__gen_e_acsl_forall_6,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall int x;\n  0 <= x < 10 ==>\n  x % 2 == 0 ==> (\\exists integer y; 0 <= y <= x / 2 && x == 2 * y)",
                    25);
  }
  __retres = 0;
  return __retres;
}

