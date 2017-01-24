/* Generated by Frama-C */
int A[10];
/*@ requires ∀ ℤ i; 0 ≤ i < 9 ⇒ A[i] ≤ A[i + 1];
    
    behavior exists:
      assumes ∃ ℤ j; 0 ≤ j < 10 ∧ A[j] ≡ elt;
      ensures \result ≡ 1;
    
    behavior not_exists:
      assumes ∀ ℤ j; 0 ≤ j < 10 ⇒ A[j] ≢ elt;
      ensures \result ≡ 0;
 */
int __gen_e_acsl_search(int elt);

/*@ requires ∀ ℤ i; 0 ≤ i < 9 ⇒ A[i] ≤ A[i + 1];
    
    behavior exists:
      assumes ∃ ℤ j; 0 ≤ j < 10 ∧ A[j] ≡ elt;
      ensures \result ≡ 1;
    
    behavior not_exists:
      assumes ∀ ℤ j; 0 ≤ j < 10 ⇒ A[j] ≢ elt;
      ensures \result ≡ 0;
 */
int search(int elt)
{
  int __retres;
  int k;
  k = 0;
  {
    int __gen_e_acsl_forall;
    int __gen_e_acsl_i;
    int __gen_e_acsl_and;
    __gen_e_acsl_forall = 1;
    __gen_e_acsl_i = 0;
    while (1) {
      if (__gen_e_acsl_i < k) ; else break;
      __e_acsl_assert(__gen_e_acsl_i < 10,(char *)"RTE",(char *)"search",
                      (char *)"index_bound: __gen_e_acsl_i < 10",18);
      __e_acsl_assert(0 <= __gen_e_acsl_i,(char *)"RTE",(char *)"search",
                      (char *)"index_bound: 0 <= __gen_e_acsl_i",18);
      if (A[__gen_e_acsl_i] < elt) ;
      else {
        __gen_e_acsl_forall = 0;
        goto e_acsl_end_loop1;
      }
      __gen_e_acsl_i = (int)(__gen_e_acsl_i + 1L);
    }
    e_acsl_end_loop1: ;
    __e_acsl_assert(__gen_e_acsl_forall,(char *)"Invariant",(char *)"search",
                    (char *)"\\forall integer i; 0 <= i < k ==> A[i] < elt",
                    18);
    if (0 <= k) __gen_e_acsl_and = k <= 10; else __gen_e_acsl_and = 0;
    __e_acsl_assert(__gen_e_acsl_and,(char *)"Invariant",(char *)"search",
                    (char *)"0 <= k <= 10",17);
    /*@ loop invariant 0 ≤ k ≤ 10;
        loop invariant ∀ ℤ i; 0 ≤ i < k ⇒ A[i] < elt;
    */
    while (k < 10) {
      if (A[k] == elt) {
        __retres = 1;
        goto return_label;
      }
      else 
        if (A[k] > elt) {
          __retres = 0;
          goto return_label;
        }
      {
        int __gen_e_acsl_and_2;
        int __gen_e_acsl_forall_2;
        int __gen_e_acsl_i_2;
        k ++;
        if (0 <= k) __gen_e_acsl_and_2 = k <= 10;
        else __gen_e_acsl_and_2 = 0;
        __e_acsl_assert(__gen_e_acsl_and_2,(char *)"Invariant",
                        (char *)"search",(char *)"0 <= k <= 10",17);
        __gen_e_acsl_forall_2 = 1;
        __gen_e_acsl_i_2 = 0;
        while (1) {
          if (__gen_e_acsl_i_2 < k) ; else break;
          __e_acsl_assert(__gen_e_acsl_i_2 < 10,(char *)"RTE",
                          (char *)"search",
                          (char *)"index_bound: __gen_e_acsl_i_2 < 10",18);
          __e_acsl_assert(0 <= __gen_e_acsl_i_2,(char *)"RTE",
                          (char *)"search",
                          (char *)"index_bound: 0 <= __gen_e_acsl_i_2",18);
          if (A[__gen_e_acsl_i_2] < elt) ;
          else {
            __gen_e_acsl_forall_2 = 0;
            goto e_acsl_end_loop2;
          }
          __gen_e_acsl_i_2 = (int)(__gen_e_acsl_i_2 + 1L);
        }
        e_acsl_end_loop2: ;
        __e_acsl_assert(__gen_e_acsl_forall_2,(char *)"Invariant",
                        (char *)"search",
                        (char *)"\\forall integer i; 0 <= i < k ==> A[i] < elt",
                        18);
      }
    }
  }
  __retres = 0;
  return_label: return __retres;
}

int main(void)
{
  int __retres;
  int found;
  {
    int i;
    i = 0;
    while (i < 10) {
      A[i] = i * i;
      i ++;
    }
  }
  found = __gen_e_acsl_search(36);
  /*@ assert found ≡ 1; */
  __e_acsl_assert(found == 1,(char *)"Assertion",(char *)"main",
                  (char *)"found == 1",31);
  found = __gen_e_acsl_search(5);
  /*@ assert found ≡ 0; */
  __e_acsl_assert(found == 0,(char *)"Assertion",(char *)"main",
                  (char *)"found == 0",34);
  __retres = 0;
  return __retres;
}

/*@ requires ∀ ℤ i; 0 ≤ i < 9 ⇒ A[i] ≤ A[i + 1];
    
    behavior exists:
      assumes ∃ ℤ j; 0 ≤ j < 10 ∧ A[j] ≡ elt;
      ensures \result ≡ 1;
    
    behavior not_exists:
      assumes ∀ ℤ j; 0 ≤ j < 10 ⇒ A[j] ≢ elt;
      ensures \result ≡ 0;
 */
int __gen_e_acsl_search(int elt)
{
  int __gen_e_acsl_at_2;
  int __gen_e_acsl_at;
  int __retres;
  {
    int __gen_e_acsl_forall;
    int __gen_e_acsl_i;
    __gen_e_acsl_forall = 1;
    __gen_e_acsl_i = 0;
    while (1) {
      if (__gen_e_acsl_i < 9) ; else break;
      __e_acsl_assert(__gen_e_acsl_i + 1L < 10L,(char *)"RTE",
                      (char *)"search",
                      (char *)"index_bound: (long)(__gen_e_acsl_i + 1) < 10",
                      7);
      __e_acsl_assert(0L <= __gen_e_acsl_i + 1L,(char *)"RTE",
                      (char *)"search",
                      (char *)"index_bound: 0 <= (long)(__gen_e_acsl_i + 1)",
                      7);
      __e_acsl_assert(__gen_e_acsl_i < 10,(char *)"RTE",(char *)"search",
                      (char *)"index_bound: __gen_e_acsl_i < 10",7);
      __e_acsl_assert(0 <= __gen_e_acsl_i,(char *)"RTE",(char *)"search",
                      (char *)"index_bound: 0 <= __gen_e_acsl_i",7);
      if (A[__gen_e_acsl_i] <= A[__gen_e_acsl_i + 1]) ;
      else {
        __gen_e_acsl_forall = 0;
        goto e_acsl_end_loop3;
      }
      __gen_e_acsl_i ++;
    }
    e_acsl_end_loop3: ;
    __e_acsl_assert(__gen_e_acsl_forall,(char *)"Precondition",
                    (char *)"search",
                    (char *)"\\forall integer i; 0 <= i < 9 ==> A[i] <= A[i + 1]",
                    7);
    {
      int __gen_e_acsl_forall_2;
      int __gen_e_acsl_j_2;
      __gen_e_acsl_forall_2 = 1;
      __gen_e_acsl_j_2 = 0;
      while (1) {
        if (__gen_e_acsl_j_2 < 10) ; else break;
        __e_acsl_assert(__gen_e_acsl_j_2 < 10,(char *)"RTE",(char *)"search",
                        (char *)"index_bound: __gen_e_acsl_j_2 < 10",12);
        __e_acsl_assert(0 <= __gen_e_acsl_j_2,(char *)"RTE",(char *)"search",
                        (char *)"index_bound: 0 <= __gen_e_acsl_j_2",12);
        if (A[__gen_e_acsl_j_2] != elt) ;
        else {
          __gen_e_acsl_forall_2 = 0;
          goto e_acsl_end_loop5;
        }
        __gen_e_acsl_j_2 ++;
      }
      e_acsl_end_loop5: ;
      __gen_e_acsl_at_2 = __gen_e_acsl_forall_2;
    }
    {
      int __gen_e_acsl_exists;
      int __gen_e_acsl_j;
      __gen_e_acsl_exists = 0;
      __gen_e_acsl_j = 0;
      while (1) {
        if (__gen_e_acsl_j < 10) ; else break;
        __e_acsl_assert(__gen_e_acsl_j < 10,(char *)"RTE",(char *)"search",
                        (char *)"index_bound: __gen_e_acsl_j < 10",9);
        __e_acsl_assert(0 <= __gen_e_acsl_j,(char *)"RTE",(char *)"search",
                        (char *)"index_bound: 0 <= __gen_e_acsl_j",9);
        if (! (A[__gen_e_acsl_j] == elt)) ;
        else {
          __gen_e_acsl_exists = 1;
          goto e_acsl_end_loop4;
        }
        __gen_e_acsl_j ++;
      }
      e_acsl_end_loop4: ;
      __gen_e_acsl_at = __gen_e_acsl_exists;
    }
    __retres = search(elt);
  }
  {
    int __gen_e_acsl_implies;
    int __gen_e_acsl_implies_2;
    if (! __gen_e_acsl_at) __gen_e_acsl_implies = 1;
    else __gen_e_acsl_implies = __retres == 1;
    __e_acsl_assert(__gen_e_acsl_implies,(char *)"Postcondition",
                    (char *)"search",
                    (char *)"\\old(\\exists integer j; 0 <= j < 10 && A[j] == elt) ==> \\result == 1",
                    10);
    if (! __gen_e_acsl_at_2) __gen_e_acsl_implies_2 = 1;
    else __gen_e_acsl_implies_2 = __retres == 0;
    __e_acsl_assert(__gen_e_acsl_implies_2,(char *)"Postcondition",
                    (char *)"search",
                    (char *)"\\old(\\forall integer j; 0 <= j < 10 ==> A[j] != elt) ==> \\result == 0",
                    13);
    return __retres;
  }
}


