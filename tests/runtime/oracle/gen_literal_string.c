/* Generated by Frama-C */
char *__gen_e_acsl_literal_string_6;
char *__gen_e_acsl_literal_string_5;
char *__gen_e_acsl_literal_string;
char *__gen_e_acsl_literal_string_4;
char *__gen_e_acsl_literal_string_3;
char *__gen_e_acsl_literal_string_2;
int main(void);

char *T = (char *)"bar";
int G = 0;
void f(void)
{
  /*@ assert *(T + G) ≡ 'b'; */
  {
    int __gen_e_acsl_valid_read;
    __gen_e_acsl_valid_read = __e_acsl_valid_read((void *)(T + G),
                                                  sizeof(char));
    __e_acsl_assert(__gen_e_acsl_valid_read,(char *)"RTE",(char *)"f",
                    (char *)"mem_access: \\valid_read(T + G)",11);
    __e_acsl_assert(*(T + G) == 'b',(char *)"Assertion",(char *)"f",
                    (char *)"*(T + G) == \'b\'",11);
  }
  G ++;
  return;
}

char *S = (char *)"foo";
char *S2 = (char *)"foo2";
int IDX = 1;
int G2 = 2;
char const *s_str = "the cat";
char const *l_str = "the dog and the cat";
char *U = (char *)"baz";
void __e_acsl_globals_init(void)
{
  __gen_e_acsl_literal_string_6 = "the dog and the cat";
  __e_acsl_store_block((void *)__gen_e_acsl_literal_string_6,
                       sizeof("the dog and the cat"));
  __e_acsl_full_init((void *)__gen_e_acsl_literal_string_6);
  __e_acsl_readonly((void *)__gen_e_acsl_literal_string_6);
  __gen_e_acsl_literal_string_5 = "the cat";
  __e_acsl_store_block((void *)__gen_e_acsl_literal_string_5,
                       sizeof("the cat"));
  __e_acsl_full_init((void *)__gen_e_acsl_literal_string_5);
  __e_acsl_readonly((void *)__gen_e_acsl_literal_string_5);
  __gen_e_acsl_literal_string = "ss";
  __e_acsl_store_block((void *)__gen_e_acsl_literal_string,sizeof("ss"));
  __e_acsl_full_init((void *)__gen_e_acsl_literal_string);
  __e_acsl_readonly((void *)__gen_e_acsl_literal_string);
  __gen_e_acsl_literal_string_4 = "foo2";
  __e_acsl_store_block((void *)__gen_e_acsl_literal_string_4,sizeof("foo2"));
  __e_acsl_full_init((void *)__gen_e_acsl_literal_string_4);
  __e_acsl_readonly((void *)__gen_e_acsl_literal_string_4);
  __gen_e_acsl_literal_string_3 = "foo";
  __e_acsl_store_block((void *)__gen_e_acsl_literal_string_3,sizeof("foo"));
  __e_acsl_full_init((void *)__gen_e_acsl_literal_string_3);
  __e_acsl_readonly((void *)__gen_e_acsl_literal_string_3);
  __gen_e_acsl_literal_string_2 = "bar";
  __e_acsl_store_block((void *)__gen_e_acsl_literal_string_2,sizeof("bar"));
  __e_acsl_full_init((void *)__gen_e_acsl_literal_string_2);
  __e_acsl_readonly((void *)__gen_e_acsl_literal_string_2);
  __e_acsl_store_block((void *)(& l_str),8UL);
  __e_acsl_full_init((void *)(& l_str));
  __e_acsl_store_block((void *)(& s_str),8UL);
  __e_acsl_full_init((void *)(& s_str));
  __e_acsl_store_block((void *)(& S2),8UL);
  __e_acsl_full_init((void *)(& S2));
  __e_acsl_store_block((void *)(& S),8UL);
  __e_acsl_full_init((void *)(& S));
  __e_acsl_store_block((void *)(& T),8UL);
  __e_acsl_full_init((void *)(& T));
  return;
}

int main(void)
{
  int __retres;
  char *SS;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __e_acsl_globals_init();
  __e_acsl_store_block((void *)(& SS),8UL);
  __e_acsl_full_init((void *)(& SS));
  SS = (char *)__gen_e_acsl_literal_string;
  /*@ assert *(S + G2) ≡ 'o'; */
  {
    int __gen_e_acsl_valid_read;
    __gen_e_acsl_valid_read = __e_acsl_valid_read((void *)(S + G2),
                                                  sizeof(char));
    __e_acsl_assert(__gen_e_acsl_valid_read,(char *)"RTE",(char *)"main",
                    (char *)"mem_access: \\valid_read(S + G2)",25);
    __e_acsl_assert(*(S + G2) == 'o',(char *)"Assertion",(char *)"main",
                    (char *)"*(S + G2) == \'o\'",25);
  }
  /*@ assert \initialized(S); */
  {
    int __gen_e_acsl_initialized;
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)S,sizeof(char));
    __e_acsl_assert(__gen_e_acsl_initialized,(char *)"Assertion",
                    (char *)"main",(char *)"\\initialized(S)",26);
  }
  /*@ assert \valid_read(S2); */
  {
    int __gen_e_acsl_valid_read_2;
    __gen_e_acsl_valid_read_2 = __e_acsl_valid_read((void *)S2,sizeof(char));
    __e_acsl_assert(__gen_e_acsl_valid_read_2,(char *)"Assertion",
                    (char *)"main",(char *)"\\valid_read(S2)",27);
  }
  /*@ assert ¬\valid(SS); */
  {
    int __gen_e_acsl_initialized_2;
    int __gen_e_acsl_and;
    __gen_e_acsl_initialized_2 = __e_acsl_initialized((void *)(& SS),
                                                      sizeof(char *));
    if (__gen_e_acsl_initialized_2) {
      int __gen_e_acsl_valid;
      __gen_e_acsl_valid = __e_acsl_valid((void *)SS,sizeof(char));
      __gen_e_acsl_and = __gen_e_acsl_valid;
    }
    else __gen_e_acsl_and = 0;
    __e_acsl_assert(! __gen_e_acsl_and,(char *)"Assertion",(char *)"main",
                    (char *)"!\\valid(SS)",28);
  }
  f();
  s_str ++;
  l_str ++;
  __retres = 0;
  __e_acsl_delete_block((void *)(& l_str));
  __e_acsl_delete_block((void *)(& s_str));
  __e_acsl_delete_block((void *)(& S2));
  __e_acsl_delete_block((void *)(& S));
  __e_acsl_delete_block((void *)(& T));
  __e_acsl_delete_block((void *)(& SS));
  __e_acsl_memory_clean();
  return __retres;
}


