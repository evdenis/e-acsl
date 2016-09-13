/****************************************************************************/
/*                                                                          */
/*  Copyright (c) 2004,2012 Kustaa Nyholm / SpareTimeLabs                   */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  Redistribution and use in source and binary forms, with or without      */
/*  modification, are permitted provided that the following conditions      */
/*  are met:                                                                */
/*                                                                          */
/*  Redistributions of source code must retain the above copyright          */
/*  notice, this list of conditions and the following disclaimer.           */
/*                                                                          */
/*  Redistributions in binary form must reproduce the above copyright       */
/*  notice, this list of conditions and the following disclaimer in the     */
/*  documentation and/or other materials provided with the distribution.    */
/*                                                                          */
/*  Neither the name of the Kustaa Nyholm or SpareTimeLabs nor the names    */
/*  of its contributors may be used to endorse or promote products derived  */
/*  from this software without specific prior written permission.           */
/*                                                                          */
/*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS     */
/*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT       */
/*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR   */
/*  A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT   */
/*  HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,  */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,   */
/*  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY   */
/*  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT     */
/*  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE   */
/*  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.    */
/*                                                                          */
/****************************************************************************/

#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>

// For PATH_MAX in Linux
#ifdef __linux__
  #include <linux/limits.h>
#endif

static void printf(char *fmt, ...);

static void eprintf(char *fmt, ...);

static void dprintf(int fd, char *fmt, ...);

static void sprintf(char* s,char *fmt, ...);

static void vabort(char *fmt, ...);

typedef void (*putcf) (void*,char);

static void uli2a(unsigned long int num, unsigned int base, int uc,char * bf) {
  int n=0;
  unsigned int d=1;
  while (num/d >= base)
    d*=base;
  while (d!=0) {
    int dgt = num / d;
    num%=d;
    d/=base;
    if (n || dgt>0|| d==0) {
      *bf++ = dgt+(dgt<10 ? '0' : (uc ? 'A' : 'a')-10);
      ++n;
    }
  }
  *bf=0;
}

static void li2a (long num, char * bf) {
  if (num<0) {
    num=-num;
    *bf++ = '-';
  }
  uli2a(num,10,0,bf);
}

static void ui2a(unsigned int num, unsigned int base, int uc,char * bf) {
  int n=0;
  unsigned int d=1;
  while (num/d >= base)
    d*=base;
  while (d!=0) {
    int dgt = num / d;
    num%= d;
    d/=base;
    if (n || dgt>0 || d==0) {
      *bf++ = dgt+(dgt<10 ? '0' : (uc ? 'A' : 'a')-10);
      ++n;
    }
  }
  *bf=0;
}

static void i2a (int num, char * bf) {
  if (num<0) {
    num=-num;
    *bf++ = '-';
  }
  ui2a(num,10,0,bf);
}

static int a2d(char ch) {
  if (ch>='0' && ch<='9')
    return ch-'0';
  else if (ch>='a' && ch<='f')
    return ch-'a'+10;
  else if (ch>='A' && ch<='F')
    return ch-'A'+10;
  else return -1;
}

static char a2i(char ch, char** src,int base,int* nump) {
  char* p= *src;
  int num=0;
  int digit;
  while ((digit=a2d(ch))>=0) {
    if (digit>base) break;
    num=num*base+digit;
    ch=*p++;
  }
  *src=p;
  *nump=num;
  return ch;
}

static void putchw(void* putp,putcf putf,int n, char z, char* bf) {
  char fc=z? '0' : ' ';
  char ch;
  char* p=bf;
  while (*p++ && n > 0)
    n--;
  while (n-- > 0)
    putf(putp,fc);
  while ((ch= *bf++))
    putf(putp,ch);
}

static void putcp(void* p,char c) {
  *(*((char**)p))++ = c;
}

static void _format(void* putp, putcf putf, char *fmt, va_list va) {
  char bf[12];
  char ch;
  while ((ch=*(fmt++))) {
    if (ch!='%')
      putf(putp,ch);
    else {
      char lz=0;
      char lng=0;
      int w=0;
      ch=*(fmt++);
      if (ch=='0') {
        ch=*(fmt++);
        lz=1;
      }
      if (ch>='0' && ch<='9') {
        ch=a2i(ch,&fmt,10,&w);
      }
      if (ch=='l') {
        ch=*(fmt++);
        lng=1;
      }
      switch (ch) {
        case 0:
          goto abort;
        case 'u' : {
          if (lng)
            uli2a(va_arg(va, unsigned long int),10,0,bf);
          else
            ui2a(va_arg(va, unsigned int),10,0,bf);
          putchw(putp,putf,w,lz,bf);
          break;
        }
        case 'd': {
          if (lng)
            li2a(va_arg(va, unsigned long int),bf);
          else
            i2a(va_arg(va, int),bf);
          putchw(putp,putf,w,lz,bf);
          break;
        }
        case 'x':
        case 'X':
          if (lng)
            uli2a(va_arg(va, unsigned long int),16,(ch=='X'),bf);
          else
            ui2a(va_arg(va, unsigned int),16,(ch=='X'),bf);
          putchw(putp,putf,w,lz,bf);
          break;
        case 'f' : {
          double num = va_arg(va, double);
          int ord = (int)num;
          i2a(ord,bf);
          putchw(putp,putf,w,lz,bf);
          putf(putp,'.');
          num = num - ord;
          num *= 1000;
          ord = (int)num;
          i2a(ord,bf);
          putchw(putp,putf,w,lz,bf);
          break;
        }
        case 'c' :
          putf(putp,(char)(va_arg(va, int)));
          break;
        case 's' :
          putchw(putp,putf,w,0,va_arg(va, char*));
          break;
        case '%' :
          putf(putp,ch);
        default:
          break;
      }
    }
  }
abort:
  ;
}

static void _charc_stdout (void* p, char c) { write(1,&c,1); }
static void _charc_stderr (void* p, char c) { write(2,&c,1); }
static void _charc_file (void* p, char c) { write((size_t)p,&c,1); }

static void _charc_literal  (void* p, char c) {
  switch(c) {
    case '\r':
      write((size_t)p,"\\r",2);
      break;
    case '\f':
      write((size_t)p,"\\f",2);
      break;
    case '\b':
      write((size_t)p,"\\b",2);
      break;
    case '\a':
      write((size_t)p,"\\a",2);
      break;
    case '\n':
      write((size_t)p,"\\n",2);
      break;
    case '\t':
      write((size_t)p,"\\t",2);
      break;
    case '\0':
      write((size_t)p,"\\0",2);
      break;
    default:
      write((size_t)p,&c,1);
  }
}

static void printf(char *fmt, ...) {
  va_list va;
  va_start(va,fmt);
  _format(NULL,_charc_stdout,fmt,va);
  va_end(va);
}

static void eprintf(char *fmt, ...) {
  va_list va;
  va_start(va,fmt);
  _format(NULL,_charc_stderr,fmt,va);
  va_end(va);
}

static void vabort(char *fmt, ...) {
  va_list va;
  va_start(va,fmt);
  _format(NULL,_charc_stderr,fmt,va);
  va_end(va);
  abort();
}

static void dprintf(int fd, char *fmt, ...) {
  va_list va;
  va_start(va,fmt);
  intptr_t fd_long = fd;
  _format((void*)fd_long,_charc_file,fmt,va);
  va_end(va);
}

static void sprintf(char* s,char *fmt, ...) {
  va_list va;
  va_start(va,fmt);
  _format(&s,putcp,fmt,va);
  putcp(&s,0);
  va_end(va);
}

#define assert(expr) \
  ((expr) ? (void)(0) : vabort("%s at %s:%d\n", \
    #expr, __FILE__,__LINE__))

static void vassert_fail(int expr, int line, char *file, char *fmt,  ...) {
  if (!expr) {
    char *afmt = "%s at %s:%d\n";
    char buf [strlen(fmt) + strlen(afmt) + PATH_MAX +  11];
    sprintf(buf, afmt, fmt, file, line);
    fmt = buf;

    va_list va;
    va_start(va,fmt);
    _format(NULL,_charc_stderr,fmt,va);
    va_end(va);
    abort();
  }
}

#define vassert(expr, fmt, ...) \
    vassert_fail(expr, __LINE__, __FILE__, fmt, __VA_ARGS__)
