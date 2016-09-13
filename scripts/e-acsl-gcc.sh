##########################################################################
#                                                                        #
#  This file is part of the Frama-C's E-ACSL plug-in.                    #
#                                                                        #
#  Copyright (C) 2012-2016                                               #
#    CEA (Commissariat à l'énergie atomique et aux énergies              #
#         alternatives)                                                  #
#                                                                        #
#  you can redistribute it and/or modify it under the terms of the GNU   #
#  Lesser General Public License as published by the Free Software       #
#  Foundation, version 2.1.                                              #
#                                                                        #
#  It is distributed in the hope that it will be useful,                 #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU Lesser General Public License for more details.                   #
#                                                                        #
#  See the GNU Lesser General Public License version 2.1                 #
#  for more details (enclosed in the file license/LGPLv2.1).             #
#                                                                        #
##########################################################################

#!/bin/sh -e

# Convenience wrapper for small runs of E-ACSL Frama-C plugin

# Print a message to STDERR and exit. If the second argument (exit code)
# is provided and it is '0' then do nothing.
error () {
  if [ -z "$2" ] || ! [ "$2" = 0 ]; then
    echo "e-acsl-gcc: fatal error: $1" 1>&2
    exit 1;
  fi
}

# Check if a given executable name can be found by in the PATH
has_tool() {
  which "$@" >/dev/null 2>&1 && return 0 || return 1
}

# Check if a given executable name is indeed an executable or can be found
# in the $PATH. Abort the execution if not.
check_tool() {
   { has_tool "$1" || test -e "$1"; } || error "No executable $1 found";
}

# Getopt options
LONGOPTIONS="help,compile,compile-only,print,debug:,ocode:,oexec:,verbose:, \
  frama-c-only,extra-cpp-args:,frama-c-stdlib,full-mmodel,gmp,quiet,logfile:,
  ld-flags:,cpp-flags:,frama-c-extra:,memory-model:,production,no-stdlib,
  debug-log:,frama-c:,gcc:"
SHORTOPTIONS="h,c,C,p,d:,o:,O:,v:,f,E:,L,M,l:,e:,g,q,s:,F:,m:,P,N,D:I:G:"
# Prefix for an error message due to wrong arguments
ERROR="ERROR parsing arguments:"

# Variables holding getopt options
OPTION_CFLAGS=                           # Compiler flags
OPTION_CPPFLAGS=                         # Preprocessor flags
OPTION_LDFLAGS=                          # Linker flags
OPTION_FRAMAC="frama-c"                  # Frama-C executable name
OPTION_CC="gcc"                          # GCC executable name
OPTION_ECHO="set -x"                     # Echo executed commands to STDOUT
OPTION_INSTRUMENT=1                      # Perform E-ACSL instrumentation
OPTION_PRINT=                            # Output instrumented code
OPTION_DEBUG=                            # Set Frama-C debug flag
OPTION_VERBOSE=                          # Set Frama-C verbose flag
OPTION_COMPILE=                          # Compile instrumented program
OPTION_OUTPUT_CODE="a.out.frama.c"       # Name of the translated file
OPTION_OUTPUT_EXEC="a.out"               # Generated executable name
OPTION_EACSL="-e-acsl -then-last"        # Specifies E-ACSL run
OPTION_FRAMA_STDLIB="-no-frama-c-stdlib" # Use Frama-C stdlib
OPTION_FULL_MMODEL=                      # Instrument as much as possible
OPTION_GMP=                              # Use GMP integers everywhere
OPTION_DEBUG_MACRO="-DE_ACSL_DEBUG"      # Debug macro
OPTION_DEBUG_LOG_MACRO=""                # Specification of debug log file
OPTION_FRAMAC_CPP_EXTRA=""               # Extra CPP flags for Frama-C
OPTION_EACSL_MMODEL="bittree"            # Memory model used
# The following option controls whether to use gcc builtins
# (e.g., __builtin_strlen) in RTL or fall back to custom implementations
# of standard functions.
OPTION_BUILTINS="-DE_ACSL_BUILTINS"

manpage() {
  printf "e-acsl-gcc.sh - instrument and compile C files with E-ACSL
Usage: e-acsl-gcc.sh [options] files
Options:
  -h         show this help page
  -c         compile instrumented code
  -l         pass additional options to the linker
  -e         pass additional options to the pre-preprocessor
  -E         pass additional arguments to the Frama-C pre-processor
  -p         output the generated code with rich formatting to STDOUT
  -o <file>  output the generated code to <file> [a.out.frama.c]
  -O <file>  output the generated executables to <file> [a.out, a.out.e-acsl]
  -M         maximize memory-related instrumentation
  -g         always use GMP integers instead of C integral types
  -q         suppress any output except for errors and warnings
  -s <file>  redirect all output to <file>
  -P         compile executable without debug features
  -I <file>  specify Frama-C executable [frama-c]
  -G <file>  specify C compiler executable [gcc]

Notes:
  This help page shows only basic options.
  See man (1) e-acsl-gcc.sh for full up-to-date documentation.\n"
  exit 1
}

# See if pygmentize if available for color highlighting and default to plain
# cat command otherwise
if has_tool 'pygmentize'; then
  CAT="pygmentize -g -O style=colorful,linenos=1"
else
  CAT="cat"
fi

# Run getopt
ARGS=`getopt -n "$ERROR" -l "$LONGOPTIONS" -o "$SHORTOPTIONS" -- "$@"`

# Print and exit if getopt fails
if [ $? != 0 ]; then
  exit 1;
fi

# Set all options in $@ before -- and other after
eval set -- "$ARGS"

# Switch statements for other options
for i in $@
do
  case "$i" in
    # Do compile instrumented code
    --help|-h)
      shift;
      manpage;
    ;;
    # Do not echo commands to STDOUT
    # Set log and debug flags to minimal verbosity levels
    --quiet|-q)
      shift;
      OPTION_ECHO=
      OPTION_DEBUG="-debug 0"
      OPTION_VERBOSE="-verbose 0"
    ;;
    # Redirect all output to a given file
    --logfile|-s)
      shift;
      exec > $1
      exec 2> $1
      shift;
    ;;
    # Pass an option to a Frama-C invocation
    --frama-c-extra|-F)
      shift;
      FRAMAC_FLAGS="$FRAMAC_FLAGS $1"
      shift;
    ;;
    # Do compile instrumented code
    --compile|-c)
      shift;
      OPTION_COMPILE=1
    ;;
    # Print the result of instrumenation
    --print|-p)
      shift;
      OPTION_PRINT=1
    ;;
    # Set Frama-C debug flag
    --debug|-d)
      shift;
      if [ "$1" -eq "$1" ] 2>/dev/null; then
        OPTION_DEBUG="-debug $1"
      else
        error "-d|--debug option requires integer argument"
      fi
      shift;
    ;;
    # Set Frama-C verbose flag
    --verbose|-v)
      shift;
      if [ "$1" -eq "$1" ] 2>/dev/null; then
        OPTION_VERBOSE="-verbose $1"
      else
        error "-v|--verbose option requires integer argument"
      fi
      shift;
    ;;
    # Specify the name of the default source file where instrumented
    # code is to be written
    --ocode|-o)
      shift;
      OPTION_OUTPUT_CODE="$1"
      shift
    ;;
    # Specify the base name of the executable generated from the
    # instrumented and non-instrumented sources.
    --oexec|-O)
      shift;
      OPTION_OUTPUT_EXEC="$1"
      shift
    ;;
    # Additional CPP arguments
    --extra-cpp-args|-E)
      shift;
      OPTION_FRAMAC_CPP_EXTRA="$OPTION_FRAMAC_CPP_EXTRA $1"
      shift;
    ;;
    # Additional flags passed to the linker
    --ld-flags|-l)
      shift;
      OPTION_LDFLAGS="$OPTION_LDFLAGS $1"
      shift;
    ;;
    # Additional flags passed to the pre-processor (compile-time)
    --cpp-flags|-e)
      shift;
      OPTION_CPPFLAGS="$OPTION_CPPFLAGS $1"
      shift;
    ;;
    # Do not perform the instrumentation, only compile the provided sources
    # This option assumes that the source files provided at input have
    # already been instrumented
    --compile-only|-C)
      shift;
      OPTION_INSTRUMENT=
      OPTION_COMPILE="1"
    ;;
    # Run only Frama-C related instrumentation
    --frama-c-only|-f)
      shift;
      OPTION_EACSL=
    ;;
    # Do use Frama-C stdlib, which is the default behaviour of Frama-C
    --frama-c-stdlib|-L)
      shift;
      OPTION_FRAMA_STDLIB=""
    ;;
    # Use as much memory-related instrumentation as possible
    -M|--full-mmodel)
      shift;
      OPTION_FULL_MMODEL="-e-acsl-full-mmodel"
    ;;
    # Use GMP everywhere
    -g|--gmp)
      shift;
      OPTION_GMP="-e-acsl-gmp-only"
    ;;
    -P|--production)
      shift;
      OPTION_DEBUG_MACRO=""
    ;;
    -N|--no-stdlib)
      shift;
      OPTION_BUILTINS=""
    ;;
    -D|--debug-log)
      shift;
      OPTION_DEBUG_LOG_MACRO="-DE_ACSL_DEBUG_LOG=$1"
      shift;
    ;;
    # Supply Frama-C executable name
    -I|--frama-c)
      shift;
      OPTION_FRAMAC="$1"
      shift;
    ;;
    # Supply GCC executable name
    -G|--gcc)
      shift;
      OPTION_CC="$1"
      shift;
    ;;
    # A memory model to link against
    -m|--memory-model)
      shift;
      echo $1 | grep "\(tree\|bittree\|splay_tree\|list\)"
      error "no such memory model: $1" $?
      OPTION_EACSL_MMODEL="$1"
      shift;
    ;;
  esac
done
shift;

# Bail if no files to translate are given
if [ -z "$1" ]; then
  error "no input files";
fi

# Architecture-dependent flags. Since by default Frama-C uses 32-bit
# architecture we need to make sure that same architecture is used for
# instrumentation and for compilation.
MACHDEPFLAGS="`getconf LONG_BIT`"
# Check if getconf gives out the value accepted by Frama-C/GCC
echo "$MACHDEPFLAGS" | grep '16\|32\|64' 2>&1 >/dev/null \
  || error "$MACHDEPFLAGS-bit architecture not supported"
# -machdep option sent to Frama-C
MACHDEP="-machdep gcc_x86_$MACHDEPFLAGS"
# Macro for correct preprocessing of Frama-C generated code
CPPMACHDEP="-D__FC_MACHDEP_X86_$MACHDEPFLAGS"
# GCC machine option
GCCMACHDEP="-m$MACHDEPFLAGS"

# Check if Frama-C and GCC executable names
check_tool "$OPTION_FRAMAC"
check_tool "$OPTION_CC"

# Frama-C and related flags
FRAMAC="$OPTION_FRAMAC"
FRAMAC_SHARE="`$FRAMAC -print-share-path`"
FRAMAC_CPP_EXTRA="
  $OPTION_FRAMAC_CPP_EXTRA
  -D$EACSL_MACRO_ID
  -I$FRAMAC_SHARE/libc
  $CPPMACHDEP"
EACSL_SHARE="$FRAMAC_SHARE/e-acsl"
EACSL_MMODEL="$OPTION_EACSL_MMODEL"

# Macro that identifies E-ACSL compilation. Passed to Frama-C
# and GCC runs but not to the original compilation
EACSL_MACRO_ID="__E_ACSL__"

# Gcc and related flags
CC="$OPTION_CC"
CFLAGS="$OPTION_CFLAGS
  -std=c99 $GCCMACHDEP -g3 -O2 -pedantic -fno-builtin
  -Wall \
  -Wno-long-long \
  -Wno-attributes \
  -Wno-unused \
  -Wno-unused-function \
  -Wno-unused-result \
  -Wno-unused-value \
  -Wno-unused-function \
  -Wno-unused-variable \
  -Wno-unused-but-set-variable \
  -Wno-implicit-function-declaration \
  -Wno-unknown-warning-option \
  -Wno-extra-semi \
  -Wno-tautological-compare \
  -Wno-gnu-empty-struct \
  -Wno-incompatible-pointer-types-discards-qualifiers \
  -Wno-empty-body"
CPPFLAGS="$OPTION_CPPFLAGS"
LDFLAGS="$OPTION_LDFLAGS"

# C, CPP and LD flags for compilation of E-ACSL-generated sources
EACSL_CFLAGS=""
EACSL_CPPFLAGS="
  -I$EACSL_SHARE
  -D$EACSL_MACRO_ID
  -D__FC_errno=(*__errno_location())"
EACSL_LDFLAGS="-lgmp -lm"
# Memory model sources
EACSL_RTL="$EACSL_SHARE/e_acsl.c \
  $EACSL_SHARE/memory_model/e_acsl_mmodel.c \
  $EACSL_SHARE/memory_model/e_acsl_$OPTION_EACSL_MMODEL.c"

# Output file names
OUTPUT_CODE="$OPTION_OUTPUT_CODE" # E-ACSL instrumented source
OUTPUT_EXEC="$OPTION_OUTPUT_EXEC" # Output name of the original executable
# Output name of E-ACSL-modified executable
EACSL_OUTPUT_EXEC="$OPTION_OUTPUT_EXEC.e-acsl"

# Instrument
if [ -n "$OPTION_INSTRUMENT" ]; then
  ($OPTION_ECHO; \
    $FRAMAC \
    $FRAMAC_FLAGS \
    $MACHDEP \
    -cpp-extra-args="$OPTION_FRAMAC_CPP_EXTRA" \
    -e-acsl-share $EACSL_SHARE \
    $OPTION_VERBOSE \
    $OPTION_DEBUG \
    $OPTION_FRAMA_STDLIB \
    $OPTION_FULL_MMODEL \
    $OPTION_GMP \
    "$@" \
    $OPTION_EACSL \
    -print \
    -ocode "$OPTION_OUTPUT_CODE");
    error "aborted by Frama-C" $?;
  # Print translated code
  if [ -n "$OPTION_PRINT" ]; then
    $CAT $OPTION_OUTPUT_CODE
  fi
fi

# Compile
if [ -n "$OPTION_COMPILE" ]; then
  # Compile the original files only if the instrumentation option is given,
  # otherwise the provided sources are assumed to be E-ACSL instrumented files
  if [ -n "$OPTION_INSTRUMENT" ]; then
    ($OPTION_ECHO; $CC $CPPFLAGS $CFLAGS "$@" -o "$OUTPUT_EXEC" $LDFLAGS);
    error "fail to compile/link un-instrumented code: $@" $?;
  else
    OUTPUT_CODE="$@"
  fi
  # Compile and link E-ACSL-instrumented file
  ($OPTION_ECHO;
   $CC \
     $CFLAGS $CPPFLAGS \
     $EACSL_CFLAGS $EACSL_CPPFLAGS \
     $EACSL_RTL \
     $OPTION_DEBUG_MACRO \
     $OPTION_DEBUG_LOG_MACRO \
     $OPTION_BUILTINS \
     -o "$EACSL_OUTPUT_EXEC" \
     "$OUTPUT_CODE" \
     $LDFLAGS $EACSL_LDFLAGS)
  error "fail to compile/link instrumented code: $@" $?;
fi
exit 0;
