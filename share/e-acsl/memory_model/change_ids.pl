#!/usr/bin/env perl

use warnings;
use strict;

use File::Slurp qw/read_file write_file/;

my %ids = qw/
__malloc __kmalloc_eacsl
__free __kfree_eacsl
__freeable __freeable_eacsl
__realloc __krealloc_eacsl
__calloc __kcalloc_eacsl
__init_args __init_args_eacsl
__initialize __initialize_eacsl
__full_init __full_init_eacsl
assert BUG_ON
malloc kmalloc
free kfree
realloc krealloc
calloc kcalloc
/;

foreach my $file (@ARGV) {
   my $f = read_file $file;

   foreach (keys %ids) {
      $f =~ s/\b$_\b/$ids{$_}/g
   }

   write_file $file, $f;
}



