#!/usr/bin/perl -pw
#
# Auction Theory Toolbox (http://formare.github.io/auctions/)
# 
# Authors:
# * Manfred Kerber <mnfrd.krbr@gmail.com>
# * Christoph Lange <math.semantic.web@gmail.com>
# * Colin Rowat <c.rowat@bham.ac.uk>
# 
# Licenced under
# * ISC License (1-clause BSD License)
# See LICENSE file for details
#
# Script to split a Scala source file (to be supplied as standard input) into
# multiple Scala files, one per object.

use strict;
use File::Spec;
use v5.10;

# the package declaration
our $package_decl;

BEGIN {
    $package_decl = "";
    # suppress output until we find the first object
    open STDOUT, '>', File::Spec->devnull();
}

# initialise package declaration
$package_decl = $1 if /^(package .+)$/;

# when a new object declaration is found in the input:
if (/^(object ([^ ]+)) {/) {
    say STDERR $1;
    # from now on, redirect output to a new per-object Scala source file
    open STDOUT, '>', "$2.scala";
    # first print package declaration (assuming it exists)
    say "$package_decl\n" if $package_decl;
}
