/* Generated by Frama-C */
char *__gen_e_acsl_literal_string_2;
char *__gen_e_acsl_literal_string;
void __e_acsl_globals_init(void)
{
  __gen_e_acsl_literal_string_2 = "wb";
  __e_acsl_store_block((void *)__gen_e_acsl_literal_string_2,sizeof("wb"));
  __e_acsl_full_init((void *)__gen_e_acsl_literal_string_2);
  __e_acsl_readonly((void *)__gen_e_acsl_literal_string_2);
  __gen_e_acsl_literal_string = "/tmp/foo";
  __e_acsl_store_block((void *)__gen_e_acsl_literal_string,
                       sizeof("/tmp/foo"));
  __e_acsl_full_init((void *)__gen_e_acsl_literal_string);
  __e_acsl_readonly((void *)__gen_e_acsl_literal_string);
  __e_acsl_store_block((void *)(& stdout),8UL);
  __e_acsl_full_init((void *)(& stdout));
  return;
}

int main(void)
{
  int __retres;
  FILE *f;
  FILE *f2;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __e_acsl_globals_init();
  __e_acsl_store_block((void *)(& f),8UL);
  __e_acsl_full_init((void *)(& f));
  f = stdout;
  f2 = __gen_e_acsl_fopen(__gen_e_acsl_literal_string,
                          __gen_e_acsl_literal_string_2);
  /*@ assert f ≡ __fc_stdout; */
  __e_acsl_assert(f == stdout,(char *)"Assertion",(char *)"main",
                  (char *)"f == __fc_stdout",10);
  __retres = 0;
  __e_acsl_delete_block((void *)(& stdout));
  __e_acsl_delete_block((void *)(& f));
  __e_acsl_memory_clean();
  return __retres;
}

