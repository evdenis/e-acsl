/* Generated by Frama-C */
int main(void)
{
  int __retres;
  /*@ assert ∀ ℤ x; 0 ≤ x ≤ 1 ⇒ x ≡ 0 ∨ x ≡ 1; */
  {
    int __gen_e_acsl_forall;
    __e_acsl_mpz_t __gen_e_acsl_x;
    __gen_e_acsl_forall = 1;
    __gmpz_init(__gen_e_acsl_x);
    {
      __e_acsl_mpz_t __gen_e_acsl__3;
      __gmpz_init_set_si(__gen_e_acsl__3,0L);
      __gmpz_set(__gen_e_acsl_x,
                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__3));
      __gmpz_clear(__gen_e_acsl__3);
    }
    while (1) {
      {
        __e_acsl_mpz_t __gen_e_acsl__4;
        int __gen_e_acsl_le;
        __gmpz_init_set_si(__gen_e_acsl__4,1L);
        __gen_e_acsl_le = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x),
                                     (__e_acsl_mpz_struct const *)(__gen_e_acsl__4));
        if (__gen_e_acsl_le <= 0) ; else break;
        __gmpz_clear(__gen_e_acsl__4);
      }
      {
        __e_acsl_mpz_t __gen_e_acsl_;
        int __gen_e_acsl_eq;
        int __gen_e_acsl_or;
        __gmpz_init_set_si(__gen_e_acsl_,0L);
        __gen_e_acsl_eq = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x),
                                     (__e_acsl_mpz_struct const *)(__gen_e_acsl_));
        if (__gen_e_acsl_eq == 0) __gen_e_acsl_or = 1;
        else {
          __e_acsl_mpz_t __gen_e_acsl__2;
          int __gen_e_acsl_eq_2;
          __gmpz_init_set_si(__gen_e_acsl__2,1L);
          __gen_e_acsl_eq_2 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x),
                                         (__e_acsl_mpz_struct const *)(__gen_e_acsl__2));
          __gen_e_acsl_or = __gen_e_acsl_eq_2 == 0;
          __gmpz_clear(__gen_e_acsl__2);
        }
        __gmpz_clear(__gen_e_acsl_);
        if (__gen_e_acsl_or) ;
        else {
          __gen_e_acsl_forall = 0;
          goto e_acsl_end_loop1;
        }
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__5;
        __e_acsl_mpz_t __gen_e_acsl_add;
        __gmpz_init_set_si(__gen_e_acsl__5,1L);
        __gmpz_init(__gen_e_acsl_add);
        __gmpz_add(__gen_e_acsl_add,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_x),
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__5));
        __gmpz_set(__gen_e_acsl_x,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_add));
        __gmpz_clear(__gen_e_acsl__5);
        __gmpz_clear(__gen_e_acsl_add);
      }
    }
    e_acsl_end_loop1: ;
    __e_acsl_assert(__gen_e_acsl_forall,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall integer x; 0 <= x <= 1 ==> x == 0 || x == 1",
                    9);
    __gmpz_clear(__gen_e_acsl_x);
  }
  /*@ assert ∀ ℤ x; 0 < x ≤ 1 ⇒ x ≡ 1; */
  {
    int __gen_e_acsl_forall_2;
    __e_acsl_mpz_t __gen_e_acsl_x_2;
    __gen_e_acsl_forall_2 = 1;
    __gmpz_init(__gen_e_acsl_x_2);
    {
      __e_acsl_mpz_t __gen_e_acsl__7;
      __e_acsl_mpz_t __gen_e_acsl__8;
      __e_acsl_mpz_t __gen_e_acsl_add_2;
      __gmpz_init_set_si(__gen_e_acsl__7,0L);
      __gmpz_init_set_si(__gen_e_acsl__8,1L);
      __gmpz_init(__gen_e_acsl_add_2);
      __gmpz_add(__gen_e_acsl_add_2,
                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__7),
                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__8));
      __gmpz_set(__gen_e_acsl_x_2,
                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_2));
      __gmpz_clear(__gen_e_acsl__7);
      __gmpz_clear(__gen_e_acsl__8);
      __gmpz_clear(__gen_e_acsl_add_2);
    }
    while (1) {
      {
        __e_acsl_mpz_t __gen_e_acsl__9;
        int __gen_e_acsl_le_2;
        __gmpz_init_set_si(__gen_e_acsl__9,1L);
        __gen_e_acsl_le_2 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x_2),
                                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__9));
        if (__gen_e_acsl_le_2 <= 0) ; else break;
        __gmpz_clear(__gen_e_acsl__9);
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__6;
        int __gen_e_acsl_eq_3;
        __gmpz_init_set_si(__gen_e_acsl__6,1L);
        __gen_e_acsl_eq_3 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x_2),
                                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__6));
        __gmpz_clear(__gen_e_acsl__6);
        if (__gen_e_acsl_eq_3 == 0) ;
        else {
          __gen_e_acsl_forall_2 = 0;
          goto e_acsl_end_loop2;
        }
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__10;
        __e_acsl_mpz_t __gen_e_acsl_add_3;
        __gmpz_init_set_si(__gen_e_acsl__10,1L);
        __gmpz_init(__gen_e_acsl_add_3);
        __gmpz_add(__gen_e_acsl_add_3,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_2),
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__10));
        __gmpz_set(__gen_e_acsl_x_2,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_3));
        __gmpz_clear(__gen_e_acsl__10);
        __gmpz_clear(__gen_e_acsl_add_3);
      }
    }
    e_acsl_end_loop2: ;
    __e_acsl_assert(__gen_e_acsl_forall_2,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall integer x; 0 < x <= 1 ==> x == 1",10);
    __gmpz_clear(__gen_e_acsl_x_2);
  }
  /*@ assert ∀ ℤ x; 0 < x < 1 ⇒ \false; */
  {
    int __gen_e_acsl_forall_3;
    __e_acsl_mpz_t __gen_e_acsl_x_3;
    __gen_e_acsl_forall_3 = 1;
    __gmpz_init(__gen_e_acsl_x_3);
    {
      __e_acsl_mpz_t __gen_e_acsl__11;
      __e_acsl_mpz_t __gen_e_acsl__12;
      __e_acsl_mpz_t __gen_e_acsl_add_4;
      __gmpz_init_set_si(__gen_e_acsl__11,0L);
      __gmpz_init_set_si(__gen_e_acsl__12,1L);
      __gmpz_init(__gen_e_acsl_add_4);
      __gmpz_add(__gen_e_acsl_add_4,
                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__11),
                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__12));
      __gmpz_set(__gen_e_acsl_x_3,
                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_4));
      __gmpz_clear(__gen_e_acsl__11);
      __gmpz_clear(__gen_e_acsl__12);
      __gmpz_clear(__gen_e_acsl_add_4);
    }
    while (1) {
      {
        __e_acsl_mpz_t __gen_e_acsl__13;
        int __gen_e_acsl_lt;
        __gmpz_init_set_si(__gen_e_acsl__13,1L);
        __gen_e_acsl_lt = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x_3),
                                     (__e_acsl_mpz_struct const *)(__gen_e_acsl__13));
        if (__gen_e_acsl_lt < 0) ; else break;
        __gmpz_clear(__gen_e_acsl__13);
      }
      if (0) ;
      else {
        __gen_e_acsl_forall_3 = 0;
        goto e_acsl_end_loop3;
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__14;
        __e_acsl_mpz_t __gen_e_acsl_add_5;
        __gmpz_init_set_si(__gen_e_acsl__14,1L);
        __gmpz_init(__gen_e_acsl_add_5);
        __gmpz_add(__gen_e_acsl_add_5,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_3),
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__14));
        __gmpz_set(__gen_e_acsl_x_3,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_5));
        __gmpz_clear(__gen_e_acsl__14);
        __gmpz_clear(__gen_e_acsl_add_5);
      }
    }
    e_acsl_end_loop3: ;
    __e_acsl_assert(__gen_e_acsl_forall_3,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall integer x; 0 < x < 1 ==> \\false",11);
    __gmpz_clear(__gen_e_acsl_x_3);
  }
  /*@ assert ∀ ℤ x; 0 ≤ x < 1 ⇒ x ≡ 0; */
  {
    int __gen_e_acsl_forall_4;
    __e_acsl_mpz_t __gen_e_acsl_x_4;
    __gen_e_acsl_forall_4 = 1;
    __gmpz_init(__gen_e_acsl_x_4);
    {
      __e_acsl_mpz_t __gen_e_acsl__16;
      __gmpz_init_set_si(__gen_e_acsl__16,0L);
      __gmpz_set(__gen_e_acsl_x_4,
                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__16));
      __gmpz_clear(__gen_e_acsl__16);
    }
    while (1) {
      {
        __e_acsl_mpz_t __gen_e_acsl__17;
        int __gen_e_acsl_lt_2;
        __gmpz_init_set_si(__gen_e_acsl__17,1L);
        __gen_e_acsl_lt_2 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x_4),
                                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__17));
        if (__gen_e_acsl_lt_2 < 0) ; else break;
        __gmpz_clear(__gen_e_acsl__17);
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__15;
        int __gen_e_acsl_eq_4;
        __gmpz_init_set_si(__gen_e_acsl__15,0L);
        __gen_e_acsl_eq_4 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x_4),
                                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__15));
        __gmpz_clear(__gen_e_acsl__15);
        if (__gen_e_acsl_eq_4 == 0) ;
        else {
          __gen_e_acsl_forall_4 = 0;
          goto e_acsl_end_loop4;
        }
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__18;
        __e_acsl_mpz_t __gen_e_acsl_add_6;
        __gmpz_init_set_si(__gen_e_acsl__18,1L);
        __gmpz_init(__gen_e_acsl_add_6);
        __gmpz_add(__gen_e_acsl_add_6,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_4),
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__18));
        __gmpz_set(__gen_e_acsl_x_4,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_6));
        __gmpz_clear(__gen_e_acsl__18);
        __gmpz_clear(__gen_e_acsl_add_6);
      }
    }
    e_acsl_end_loop4: ;
    __e_acsl_assert(__gen_e_acsl_forall_4,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall integer x; 0 <= x < 1 ==> x == 0",12);
    __gmpz_clear(__gen_e_acsl_x_4);
  }
  /*@ assert
      ∀ ℤ x, ℤ y, ℤ z;
        0 ≤ x < 2 ∧ 0 ≤ y < 5 ∧ 0 ≤ z ≤ y ⇒ x + z ≤ y + 1;
  */
  {
    int __gen_e_acsl_forall_5;
    __e_acsl_mpz_t __gen_e_acsl_x_5;
    __e_acsl_mpz_t __gen_e_acsl_y;
    __e_acsl_mpz_t __gen_e_acsl_z;
    __gen_e_acsl_forall_5 = 1;
    __gmpz_init(__gen_e_acsl_x_5);
    __gmpz_init(__gen_e_acsl_y);
    __gmpz_init(__gen_e_acsl_z);
    {
      __e_acsl_mpz_t __gen_e_acsl__25;
      __gmpz_init_set_si(__gen_e_acsl__25,0L);
      __gmpz_set(__gen_e_acsl_x_5,
                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__25));
      __gmpz_clear(__gen_e_acsl__25);
    }
    while (1) {
      {
        __e_acsl_mpz_t __gen_e_acsl__26;
        int __gen_e_acsl_lt_4;
        __gmpz_init_set_si(__gen_e_acsl__26,2L);
        __gen_e_acsl_lt_4 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x_5),
                                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__26));
        if (__gen_e_acsl_lt_4 < 0) ; else break;
        __gmpz_clear(__gen_e_acsl__26);
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__22;
        __gmpz_init_set_si(__gen_e_acsl__22,0L);
        __gmpz_set(__gen_e_acsl_y,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__22));
        __gmpz_clear(__gen_e_acsl__22);
      }
      while (1) {
        {
          __e_acsl_mpz_t __gen_e_acsl__23;
          int __gen_e_acsl_lt_3;
          __gmpz_init_set_si(__gen_e_acsl__23,5L);
          __gen_e_acsl_lt_3 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_y),
                                         (__e_acsl_mpz_struct const *)(__gen_e_acsl__23));
          if (__gen_e_acsl_lt_3 < 0) ; else break;
          __gmpz_clear(__gen_e_acsl__23);
        }
        {
          __e_acsl_mpz_t __gen_e_acsl__20;
          __gmpz_init_set_si(__gen_e_acsl__20,0L);
          __gmpz_set(__gen_e_acsl_z,
                     (__e_acsl_mpz_struct const *)(__gen_e_acsl__20));
          __gmpz_clear(__gen_e_acsl__20);
        }
        while (1) {
          {
            int __gen_e_acsl_le_4;
            __gen_e_acsl_le_4 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_z),
                                           (__e_acsl_mpz_struct const *)(__gen_e_acsl_y));
            if (__gen_e_acsl_le_4 <= 0) ; else break;
          }
          {
            __e_acsl_mpz_t __gen_e_acsl_add_7;
            __e_acsl_mpz_t __gen_e_acsl__19;
            __e_acsl_mpz_t __gen_e_acsl_add_8;
            int __gen_e_acsl_le_3;
            __gmpz_init(__gen_e_acsl_add_7);
            __gmpz_add(__gen_e_acsl_add_7,
                       (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_5),
                       (__e_acsl_mpz_struct const *)(__gen_e_acsl_z));
            __gmpz_init_set_si(__gen_e_acsl__19,1L);
            __gmpz_init(__gen_e_acsl_add_8);
            __gmpz_add(__gen_e_acsl_add_8,
                       (__e_acsl_mpz_struct const *)(__gen_e_acsl_y),
                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__19));
            __gen_e_acsl_le_3 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_add_7),
                                           (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_8));
            __gmpz_clear(__gen_e_acsl_add_7);
            __gmpz_clear(__gen_e_acsl__19);
            __gmpz_clear(__gen_e_acsl_add_8);
            if (__gen_e_acsl_le_3 <= 0) ;
            else {
              __gen_e_acsl_forall_5 = 0;
              goto e_acsl_end_loop5;
            }
          }
          {
            __e_acsl_mpz_t __gen_e_acsl__21;
            __e_acsl_mpz_t __gen_e_acsl_add_9;
            __gmpz_init_set_si(__gen_e_acsl__21,1L);
            __gmpz_init(__gen_e_acsl_add_9);
            __gmpz_add(__gen_e_acsl_add_9,
                       (__e_acsl_mpz_struct const *)(__gen_e_acsl_z),
                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__21));
            __gmpz_set(__gen_e_acsl_z,
                       (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_9));
            __gmpz_clear(__gen_e_acsl__21);
            __gmpz_clear(__gen_e_acsl_add_9);
          }
        }
        {
          __e_acsl_mpz_t __gen_e_acsl__24;
          __e_acsl_mpz_t __gen_e_acsl_add_10;
          __gmpz_init_set_si(__gen_e_acsl__24,1L);
          __gmpz_init(__gen_e_acsl_add_10);
          __gmpz_add(__gen_e_acsl_add_10,
                     (__e_acsl_mpz_struct const *)(__gen_e_acsl_y),
                     (__e_acsl_mpz_struct const *)(__gen_e_acsl__24));
          __gmpz_set(__gen_e_acsl_y,
                     (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_10));
          __gmpz_clear(__gen_e_acsl__24);
          __gmpz_clear(__gen_e_acsl_add_10);
        }
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__27;
        __e_acsl_mpz_t __gen_e_acsl_add_11;
        __gmpz_init_set_si(__gen_e_acsl__27,1L);
        __gmpz_init(__gen_e_acsl_add_11);
        __gmpz_add(__gen_e_acsl_add_11,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_5),
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__27));
        __gmpz_set(__gen_e_acsl_x_5,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_11));
        __gmpz_clear(__gen_e_acsl__27);
        __gmpz_clear(__gen_e_acsl_add_11);
      }
    }
    e_acsl_end_loop5: ;
    __e_acsl_assert(__gen_e_acsl_forall_5,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall integer x, integer y, integer z;\n  0 <= x < 2 && 0 <= y < 5 && 0 <= z <= y ==> x + z <= y + 1",
                    16);
    __gmpz_clear(__gen_e_acsl_x_5);
    __gmpz_clear(__gen_e_acsl_y);
    __gmpz_clear(__gen_e_acsl_z);
  }
  /*@ assert ∃ int x; 0 ≤ x < 10 ∧ x ≡ 5; */
  {
    int __gen_e_acsl_exists;
    __e_acsl_mpz_t __gen_e_acsl_x_6;
    __gen_e_acsl_exists = 0;
    __gmpz_init(__gen_e_acsl_x_6);
    __gmpz_set_si(__gen_e_acsl_x_6,0L);
    while (1) {
      {
        __e_acsl_mpz_t __gen_e_acsl__29;
        int __gen_e_acsl_lt_5;
        __gmpz_init_set_si(__gen_e_acsl__29,10L);
        __gen_e_acsl_lt_5 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x_6),
                                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__29));
        if (__gen_e_acsl_lt_5 < 0) ; else break;
        __gmpz_clear(__gen_e_acsl__29);
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__28;
        int __gen_e_acsl_eq_5;
        __gmpz_init_set_si(__gen_e_acsl__28,5L);
        __gen_e_acsl_eq_5 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x_6),
                                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__28));
        __gmpz_clear(__gen_e_acsl__28);
        if (! (__gen_e_acsl_eq_5 == 0)) ;
        else {
          __gen_e_acsl_exists = 1;
          goto e_acsl_end_loop6;
        }
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__30;
        __e_acsl_mpz_t __gen_e_acsl_add_12;
        __gmpz_init_set_si(__gen_e_acsl__30,1L);
        __gmpz_init(__gen_e_acsl_add_12);
        __gmpz_add(__gen_e_acsl_add_12,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_6),
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__30));
        __gmpz_set(__gen_e_acsl_x_6,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_12));
        __gmpz_clear(__gen_e_acsl__30);
        __gmpz_clear(__gen_e_acsl_add_12);
      }
    }
    e_acsl_end_loop6: ;
    __e_acsl_assert(__gen_e_acsl_exists,(char *)"Assertion",(char *)"main",
                    (char *)"\\exists int x; 0 <= x < 10 && x == 5",21);
    __gmpz_clear(__gen_e_acsl_x_6);
  }
  /*@ assert
      ∀ int x;
        0 ≤ x < 10 ⇒
        x % 2 ≡ 0 ⇒ (∃ ℤ y; 0 ≤ y ≤ x / 2 ∧ x ≡ 2 * y);
  */
  {
    int __gen_e_acsl_forall_6;
    __e_acsl_mpz_t __gen_e_acsl_x_7;
    __gen_e_acsl_forall_6 = 1;
    __gmpz_init(__gen_e_acsl_x_7);
    __gmpz_set_si(__gen_e_acsl_x_7,0L);
    while (1) {
      {
        __e_acsl_mpz_t __gen_e_acsl__38;
        int __gen_e_acsl_lt_6;
        __gmpz_init_set_si(__gen_e_acsl__38,10L);
        __gen_e_acsl_lt_6 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x_7),
                                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__38));
        if (__gen_e_acsl_lt_6 < 0) ; else break;
        __gmpz_clear(__gen_e_acsl__38);
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__31;
        __e_acsl_mpz_t __gen_e_acsl__32;
        int __gen_e_acsl_mod_guard;
        __e_acsl_mpz_t __gen_e_acsl_mod;
        int __gen_e_acsl_eq_6;
        int __gen_e_acsl_implies;
        __gmpz_init_set_si(__gen_e_acsl__31,2L);
        __gmpz_init_set_si(__gen_e_acsl__32,0L);
        __gen_e_acsl_mod_guard = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl__31),
                                            (__e_acsl_mpz_struct const *)(__gen_e_acsl__32));
        __gmpz_init(__gen_e_acsl_mod);
        /*@ assert E_ACSL: 2 ≢ 0; */
        __e_acsl_assert(! (__gen_e_acsl_mod_guard == 0),(char *)"Assertion",
                        (char *)"main",(char *)"2 == 0",26);
        __gmpz_tdiv_r(__gen_e_acsl_mod,
                      (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_7),
                      (__e_acsl_mpz_struct const *)(__gen_e_acsl__31));
        __gen_e_acsl_eq_6 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_mod),
                                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__32));
        if (! (__gen_e_acsl_eq_6 == 0)) __gen_e_acsl_implies = 1;
        else {
          int __gen_e_acsl_exists_2;
          __e_acsl_mpz_t __gen_e_acsl_y_2;
          __gen_e_acsl_exists_2 = 0;
          __gmpz_init(__gen_e_acsl_y_2);
          {
            __e_acsl_mpz_t __gen_e_acsl__34;
            __gmpz_init_set_si(__gen_e_acsl__34,0L);
            __gmpz_set(__gen_e_acsl_y_2,
                       (__e_acsl_mpz_struct const *)(__gen_e_acsl__34));
            __gmpz_clear(__gen_e_acsl__34);
          }
          while (1) {
            {
              __e_acsl_mpz_t __gen_e_acsl__35;
              __e_acsl_mpz_t __gen_e_acsl__36;
              int __gen_e_acsl_div_guard;
              __e_acsl_mpz_t __gen_e_acsl_div;
              int __gen_e_acsl_le_5;
              __gmpz_init_set_si(__gen_e_acsl__35,2L);
              __gmpz_init_set_si(__gen_e_acsl__36,0L);
              __gen_e_acsl_div_guard = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl__35),
                                                  (__e_acsl_mpz_struct const *)(__gen_e_acsl__36));
              __gmpz_init(__gen_e_acsl_div);
              /*@ assert E_ACSL: 2 ≢ 0; */
              __e_acsl_assert(! (__gen_e_acsl_div_guard == 0),
                              (char *)"Assertion",(char *)"main",
                              (char *)"2 == 0",26);
              __gmpz_tdiv_q(__gen_e_acsl_div,
                            (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_7),
                            (__e_acsl_mpz_struct const *)(__gen_e_acsl__35));
              __gen_e_acsl_le_5 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_y_2),
                                             (__e_acsl_mpz_struct const *)(__gen_e_acsl_div));
              if (__gen_e_acsl_le_5 <= 0) ; else break;
              __gmpz_clear(__gen_e_acsl__35);
              __gmpz_clear(__gen_e_acsl__36);
              __gmpz_clear(__gen_e_acsl_div);
            }
            {
              __e_acsl_mpz_t __gen_e_acsl__33;
              __e_acsl_mpz_t __gen_e_acsl_mul;
              int __gen_e_acsl_eq_7;
              __gmpz_init_set_si(__gen_e_acsl__33,2L);
              __gmpz_init(__gen_e_acsl_mul);
              __gmpz_mul(__gen_e_acsl_mul,
                         (__e_acsl_mpz_struct const *)(__gen_e_acsl__33),
                         (__e_acsl_mpz_struct const *)(__gen_e_acsl_y_2));
              __gen_e_acsl_eq_7 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x_7),
                                             (__e_acsl_mpz_struct const *)(__gen_e_acsl_mul));
              __gmpz_clear(__gen_e_acsl__33);
              __gmpz_clear(__gen_e_acsl_mul);
              if (! (__gen_e_acsl_eq_7 == 0)) ;
              else {
                __gen_e_acsl_exists_2 = 1;
                goto e_acsl_end_loop7;
              }
            }
            {
              __e_acsl_mpz_t __gen_e_acsl__37;
              __e_acsl_mpz_t __gen_e_acsl_add_13;
              __gmpz_init_set_si(__gen_e_acsl__37,1L);
              __gmpz_init(__gen_e_acsl_add_13);
              __gmpz_add(__gen_e_acsl_add_13,
                         (__e_acsl_mpz_struct const *)(__gen_e_acsl_y_2),
                         (__e_acsl_mpz_struct const *)(__gen_e_acsl__37));
              __gmpz_set(__gen_e_acsl_y_2,
                         (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_13));
              __gmpz_clear(__gen_e_acsl__37);
              __gmpz_clear(__gen_e_acsl_add_13);
            }
          }
          e_acsl_end_loop7: ;
          __gen_e_acsl_implies = __gen_e_acsl_exists_2;
          __gmpz_clear(__gen_e_acsl_y_2);
        }
        __gmpz_clear(__gen_e_acsl__31);
        __gmpz_clear(__gen_e_acsl__32);
        __gmpz_clear(__gen_e_acsl_mod);
        if (__gen_e_acsl_implies) ;
        else {
          __gen_e_acsl_forall_6 = 0;
          goto e_acsl_end_loop8;
        }
      }
      {
        __e_acsl_mpz_t __gen_e_acsl__39;
        __e_acsl_mpz_t __gen_e_acsl_add_14;
        __gmpz_init_set_si(__gen_e_acsl__39,1L);
        __gmpz_init(__gen_e_acsl_add_14);
        __gmpz_add(__gen_e_acsl_add_14,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_7),
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__39));
        __gmpz_set(__gen_e_acsl_x_7,
                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_14));
        __gmpz_clear(__gen_e_acsl__39);
        __gmpz_clear(__gen_e_acsl_add_14);
      }
    }
    e_acsl_end_loop8: ;
    __e_acsl_assert(__gen_e_acsl_forall_6,(char *)"Assertion",(char *)"main",
                    (char *)"\\forall int x;\n  0 <= x < 10 ==>\n  x % 2 == 0 ==> (\\exists integer y; 0 <= y <= x / 2 && x == 2 * y)",
                    25);
    __gmpz_clear(__gen_e_acsl_x_7);
  }
  __retres = 0;
  return __retres;
}

