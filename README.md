Sail model of CHERI-MIPS ISA
============================

This repository contains a model of the CHERI-MIPS ISA in the [Sail
language](https://github.com/rems-project/sail). Sail can build an ISA
simulator, convert to theorem prover input or generate latex for
inclusion in the CHERI ISA manual.

Sail via OPAM
=============

We recommend to install the Sail compiler using the opam package. See
the following [wiki page](https://github.com/rems-project/sail/wiki/OPAMInstall).

Building
========

The following emulator targets are available:

| Subdirectory | Target | Description |
|--------------|--------|-------------|
| mips         | mips   | MIPS emulator built from sail-generated OCaml |
| mips         | mips_c | MIPS emualtor built from sail-generated C |
| cheri         | cheri   | CHERI-MIPS-256 emulator built from sail-generated OCaml |
| cheri         | cheri_c | CHERI-MIPS-256 emualtor built from sail-generated C |
| cheri         | cheri128   | CHERI-MIPS-128 emulator built from sail-generated OCaml |
| cheri         | cheri128_c | CHERI-MIPS-128 emualtor built from sail-generated C |

The C emulator is faster and therefore generally preferable but the OCaml one may be useful for debugging (e.g. any discrepancy in output indicates a bug in Sail or its external function libraries).

The default make target in the top-level directory will build all of the above.

Funding
=======

This software was developed within the Rigorous Engineering of
Mainstream Systems (REMS) project, partly funded by EPSRC grant
EP/K008528/1, at the Universities of Cambridge and Edinburgh.

This software was developed by SRI International and the University of
Cambridge Computer Laboratory (Department of Computer Science and
Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV").
