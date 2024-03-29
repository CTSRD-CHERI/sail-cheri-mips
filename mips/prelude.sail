/*==========================================================================*/
/*     Sail CHERI-MIPS                                                      */
/*                                                                          */
/*  The Sail architecture models here are subject to the BSD two-clause     */
/*  licence below.  The snapshots of the Lem, Sail, and bbv libraries in    */
/*  the prover_snapshots directory contain copies of their licences.        */
/*                                                                          */
/*  Copyright (c) 2013-2021                                                 */
/*    Alasdair Armstrong                                                    */
/*    Thomas Bauereiss                                                      */
/*    Brian Campbell                                                        */
/*    Jessica Clarke                                                        */
/*    Nathaniel Filardo                                                     */
/*    Shaked Flur                                                           */
/*    Jon French                                                            */
/*    Kathryn Gray                                                          */
/*    Alexandre Joannou                                                     */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Alexander Richardson                                                  */
/*    Peter Sewell                                                          */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This software was developed within the Rigorous Engineering of          */
/*  Mainstream Systems (REMS) project, partly funded by EPSRC grant         */
/*  EP/K008528/1, at the Universities of Cambridge and Edinburgh.           */
/*                                                                          */
/*  This project has received funding from the European Research Council    */
/*  (ERC) under the European Union’s Horizon 2020 research and innovation   */
/*  programme (grant agreement No 789108, ELVER).                           */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contract FA8650-18-C-7809 ("CIFV").        */
/*                                                                          */
/*                                                                          */
/*  Redistribution and use in source and binary forms, with or without      */
/*  modification, are permitted provided that the following conditions      */
/*  are met:                                                                */
/*  1. Redistributions of source code must retain the above copyright       */
/*     notice, this list of conditions and the following disclaimer.        */
/*  2. Redistributions in binary form must reproduce the above copyright    */
/*     notice, this list of conditions and the following disclaimer in      */
/*     the documentation and/or other materials provided with the           */
/*     distribution.                                                        */
/*                                                                          */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      */
/*  SUCH DAMAGE.                                                            */
/*==========================================================================*/

default Order dec

/* this is here because if we don't have it before including vector_dec
   we get infinite loops caused by interaction with bool/bit casts */
val eq_bit2 = "eq_bit" : (bit, bit) -> bool
overload operator == = {eq_bit2}

$include <smt.sail>
$include <flow.sail>
$include <arith.sail>
$include <option.sail>
$include <vector_dec.sail>
$include <string.sail>

val eq_anything = {ocaml: "(fun (x, y) -> x = y)", lem: "eq", coq: "generic_eq", _:"eq_anything"} : forall ('a : Type). ('a, 'a) -> bool
overload operator == = {eq_anything}

overload ~ = {not_bool, not_vec}
$latex noref not
overload not = {not_bool}

val neq_anything = {lem: "neq", coq: "generic_neq"} : forall ('a : Type). ('a, 'a) -> bool
function neq_anything (x, y) = not_bool(x == y)

overload operator != = {neq_anything}

val cast cast_unit_vec : bit -> bits(1)

function cast_unit_vec b = match b {
  bitzero => 0b0,
  _ => 0b1
}

overload print = {print_endline}

val "prerr" : string -> unit

val putchar = {c:"sail_putchar", _:"putchar"} : int -> unit

val string_of_int = "string_of_int" : int -> string

val BitStr = "string_of_bits" : forall 'n. bits('n) -> string

val xor_vec = {c: "xor_bits" , _: "xor_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val int_power = {ocaml: "int_power", lem: "pow", coq: "Z.pow"} : (int, int) -> int

overload operator ^ = {xor_vec, int_power, concat_str}

val add_range = {ocaml: "add_int", lem: "integerAdd", coq: "add_range", c: "add_int"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val add_vec = "add_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val add_vec_int = "add_vec_int" : forall 'n. (bits('n), int) -> bits('n)

overload operator + = {add_range, add_int, add_vec, add_vec_int}

val sub_range = {ocaml: "sub_int", lem: "integerMinus", coq: "sub_range"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n - 'p, 'm - 'o)

val sub_vec = {c : "sub_bits", _:"sub_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val sub_vec_int = {c:"sub_bits_int", _: "sub_vec_int"} : forall 'n. (bits('n), int) -> bits('n)

val negate_range = {ocaml: "minus_big_int", lem: "integerNegate", coq: "negate_range"} : forall 'n 'm. range('n, 'm) -> range(- 'm, - 'n)

overload operator - = {sub_range, sub_int, sub_vec, sub_vec_int}

overload negate = {negate_range, negate_int}

overload operator * = {mult_int}

/*
Use Euclidean div and mod.
Plain 'div' and 'mod' are are for compatibility with versions of sail prior to 0.9
*/
overload operator / = {ediv_int, div}
overload operator % = {emod_int, mod}

val quot_round_zero = {ocaml: "quot_round_zero", lem: "hardware_quot", coq: "Z.quot", _ : "tdiv_int"} : (int, int) -> int
val rem_round_zero = {ocaml: "rem_round_zero", lem: "hardware_mod", coq: "Z.rem", _ : "tmod_int"} : (int, int) -> int

val min_nat = {lem: "min", coq: "min_nat", _: "min_int"} : (nat, nat) -> nat

val min_int = {lem: "min", coq: "Z.min", _: "min_int"} : (int, int) -> int

val max_nat = {lem: "max", coq: "Z.max", _: "max_int"} : (nat, nat) -> nat

val max_int = {lem: "max", coq: "Z.max", _: "max_int"} : (int, int) -> int

val min_atom = {ocaml: "min_int", lem: "min", coq: "min_atom", c:"min_int"} : forall 'a 'b . (atom('a), atom('b)) -> {'c, ('c == 'a | 'c == 'b) & 'c <= 'a & 'c <= 'b . atom('c)}

val max_atom = {ocaml: "max_int", lem: "max", coq: "max_atom", c:"max_int"} : forall 'a 'b . (atom('a), atom('b)) -> {'c, ('c == 'a | 'c == 'b) & 'c >= 'a & 'c >= 'b . atom('c)}

overload min = {min_atom, min_nat, min_int}

overload max = {max_atom, max_nat, max_int}

val __WriteRAM = "write_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> bool effect {wmv}

val __MIPS_write : forall 'n. (bits(64), atom('n), bits(8 * 'n)) -> unit effect {wmv}
function __MIPS_write (addr, width, data) = let _ = __WriteRAM(64, width, 0x0000_0000_0000_0000, addr, data) in ()

val __ReadRAM = "read_ram" : forall 'n 'm, 'n >= 0.
  (atom('m), atom('n), bits('m), bits('m)) -> bits(8 * 'n) effect {rmem}

val __MIPS_read : forall 'n, 'n >= 0. (bits(64), atom('n)) -> bits(8 * 'n) effect {rmem}
function __MIPS_read (addr, width) = __ReadRAM(64, width, 0x0000_0000_0000_0000, addr)

infix 8 ^^
val operator ^^ = {lem: "replicate_bits"} : forall 'n 'm, 'm >= 0 . (bits('n), atom('m)) -> bits('n * 'm)
function operator ^^ (bs, n) = replicate_bits (bs, n)

/*!
THIS(n) returns 2 raised to the power _n_.
 */
val pow2 = "pow2" : forall 'n , 'n >= 0 . atom('n) -> atom(2 ^ 'n)

union exception = {
  ISAException : unit,
  Error_not_implemented : string,
  Error_misaligned_access : unit,
  Error_EBREAK : unit,
  Error_internal_error : unit
}

$ifndef FEATURE_IMPLICITS

/* These functions make the first parameter to builtin extension
functions implicit from length of returned vector.  */

val mips_sign_extend : forall 'n 'm , 'm >= 'n . bits('n) -> bits('m)
val mips_zero_extend : forall 'n 'm , 'm >= 'n . bits('n) -> bits('m)

function mips_sign_extend v = sail_sign_extend(v, sizeof('m))
function mips_zero_extend v = sail_zero_extend(v, sizeof('m))

/*!
THIS extends a bit vector by copying the most significant bit (thereby preserving the represented value in twos-complement).
 */
val sign_extend : forall 'n 'm , 'm >= 'n . bits('n) -> bits('m)

/*!
THIS extends a bit vector by adding zeros in the most significant bits. The length of the returned vector is implied from the context.
*/
val zero_extend : forall 'n 'm , 'm >= 'n . bits('n) -> bits('m)

/* Because sail already has builtins with these names we use overload to rename above. */
overload sign_extend = {mips_sign_extend}
overload zero_extend = {mips_zero_extend}

val zeros_implicit : forall 'n, 'n >= 0 . unit -> bits('n)
function zeros_implicit () = sail_zeros('n)
overload zeros = {zeros_implicit, sail_zeros}

val ones_implicit : forall 'n, 'n >= 0 . unit -> bits('n)
function ones_implicit () = sail_ones ('n)

overload ones = {ones_implicit, sail_ones}

$else

/* These functions make the first parameter to builtin extension
functions implicit from length of returned vector.  */

val mips_sign_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
val mips_zero_extend : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)

function mips_sign_extend(m, v) = sail_sign_extend(v, m)
function mips_zero_extend(m, v) = sail_zero_extend(v, m)

/* Because sail already has builtins with these names we use overload to rename above. */
overload sign_extend = {mips_sign_extend}
overload zero_extend = {mips_zero_extend}

val zeros_implicit : forall 'n, 'n >= 0. (implicit('n), unit) -> bits('n)
function zeros_implicit(n, _) = sail_zeros(n)
overload zeros = {zeros_implicit, sail_zeros}

val ones_implicit : forall 'n, 'n >= 0. (implicit('n), unit) -> bits('n)
function ones_implicit(n, _) = sail_ones(n)

overload ones = {ones_implicit, sail_ones}

$endif

infix 4 <_s
infix 4 >=_s
infix 4 <_u
infix 4 >=_u

val operator <_s  : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator >=_s : forall 'n, 'n > 0. (bits('n), bits('n)) -> bool
val operator <_u  : forall 'n, 'n >= 0. (bits('n), bits('n)) -> bool
val operator >=_u : forall 'n, 'n >= 0. (bits('n), bits('n)) -> bool

function operator <_s  (x, y) = signed(x) < signed(y)
function operator >=_s (x, y) = signed(x) >= signed(y)
function operator <_u  (x, y) = unsigned(x) < unsigned(y)
function operator >=_u (x, y) = unsigned(x) >= unsigned(y)

val cast bool_to_bits : bool -> bits(1)
function bool_to_bits x = if x then 0b1 else 0b0

val cast bool_to_bit : bool -> bit
function bool_to_bit x = if x then bitone else bitzero

val cast bit_to_bool : bit -> bool
function bit_to_bool b = match b {
  bitone => true,
  _ => false
}

val cast bits_to_bool : bits(1) -> bool
function bits_to_bool x = bit_to_bool(x[0])

infix 1 >>
infix 1 <<
infix 1 >>_s

val "shift_bits_right" : forall 'n 'm. (bits('n), bits('m)) -> bits('n) effect {undef}
val "shift_bits_left" : forall 'n 'm. (bits('n), bits('m)) -> bits('n) effect {undef}

val "shiftl" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)
val "shiftr" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)

overload operator >> = {shift_bits_right, shiftr}
overload operator << = {shift_bits_left, shiftl}
val operator >>_s = "shift_bits_right_arith" : forall 'n 'm. (bits('n), bits('m)) -> bits('n) effect {undef}

infix 7 *_s
val operator *_s = "mults_vec" : forall 'n . (bits('n), bits('n)) -> bits(2 * 'n)
infix 7 *_u
val operator *_u = "mult_vec" : forall 'n . (bits('n), bits('n)) -> bits(2 * 'n)

/*!
THIS`(l, v)` converts an integer, `v`,  to a bit vector of length `l`. If `v` is negative a twos-complement representation is used. If `v` is too large (or too negative) to fit in the requested length then it is truncated to the least significant bits.
*/
val to_bits : forall 'l, 'l >= 0 .(atom('l), int) -> bits('l)
function to_bits (l, n) = get_slice_int(l, n, 0)

$ifndef FEATURE_IMPLICITS
val mask : forall 'm 'n, 'm >= 'n > 0. bits('m) -> bits('n)
function mask(bs) = bs['n - 1 .. 0]
$else
val mask : forall 'm 'n, 'm >= 'n > 0. (implicit('n), bits('m)) -> bits('n)
function mask(n, bs) = bs[n - 1 .. 0]
$endif

val "get_time_ns" : unit -> int
