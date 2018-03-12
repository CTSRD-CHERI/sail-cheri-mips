default Order dec

type bits ('n : Int) = vector('n, dec, bit)
union option ('a : Type) = {None : unit, Some : 'a}

val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bits('n), bits('n)) -> bool

val eq_string = {ocaml: "eq_string", lem: "eq"} : (string, string) -> bool

val eq_real = {ocaml: "eq_real", lem: "eq"} : (real, real) -> bool

val eq_anything = {ocaml: "(fun (x, y) -> x = y)", lem: "eq"} : forall ('a : Type). ('a, 'a) -> bool

val bitvector_length = {ocaml: "length", lem: "length"} : forall 'n. bits('n) -> atom('n)
val vector_length = {ocaml: "length", lem: "length_list"} : forall 'n ('a : Type). vector('n, dec, 'a) -> atom('n)
val list_length = {ocaml: "length", lem: "length_list"} : forall ('a : Type). list('a) -> int

overload length = {bitvector_length, vector_length, list_length}

val "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}
/* sneaky deref with no effect necessary for bitfield writes */
val _reg_deref = "reg_deref" : forall ('a : Type). register('a) -> 'a

overload operator == = {eq_atom, eq_int, eq_vec, eq_string, eq_real, eq_anything}

val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_dec"} : forall ('n : Int) ('m : Int) ('o : Int), 'o <= 'm <= 'n.
  (bits('n), atom('m), atom('o)) -> bits('m - ('o - 1))

val bitvector_access = {ocaml: "access", lem: "access_vec_dec"} : forall ('n : Int) ('m : Int), 0 <= 'm < 'n.
  (bits('n), atom('m)) -> bit

val any_vector_access = {ocaml: "access", lem: "access_list_dec"} : forall ('n : Int) ('m : Int) ('a : Type), 0 <= 'm < 'n.
  (vector('n, dec, 'a), atom('m)) -> 'a

overload vector_access = {bitvector_access, any_vector_access}

val bitvector_update = {ocaml: "update", lem: "update_vec_dec"} : forall 'n.
  (bits('n), int, bit) -> bits('n)

val any_vector_update = {ocaml: "update", lem: "update_list_dec"} : forall 'n ('a : Type).
  (vector('n, dec, 'a), int, 'a) -> vector('n, dec, 'a)

overload vector_update = {bitvector_update, any_vector_update}

val update_subrange = {ocaml: "update_subrange", lem: "update_subrange_vec_dec"} : forall 'n 'm 'o.
  (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)

val vcons = {lem: "cons_vec"} : forall ('n : Int) ('a : Type).
  ('a, vector('n, dec, 'a)) -> vector('n + 1, dec, 'a)

val bitvector_concat = {ocaml: "append", lem: "concat_vec"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)

val vector_concat = {ocaml: "append", lem: "append_list"} : forall ('n : Int) ('m : Int) ('a : Type).
  (vector('n, dec, 'a), vector('m, dec, 'a)) -> vector('n + 'm, dec, 'a)

overload append = {bitvector_concat, vector_concat}

val not_vec = "not_vec" : forall 'n. bits('n) -> bits('n)

overload ~ = {not_bool, not_vec}

val not = "not" : bool -> bool

val neq_vec = {lem: "neq"} : forall 'n. (bits('n), bits('n)) -> bool
function neq_vec (x, y) = not_bool(eq_vec(x, y))

val neq_anything = {lem: "neq"} : forall ('a : Type). ('a, 'a) -> bool
function neq_anything (x, y) = not_bool(x == y)

overload operator != = {neq_atom, neq_int, neq_vec, neq_anything}

val builtin_and_vec = {ocaml: "and_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val and_vec = {lem: "and_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

function and_vec (xs, ys) = builtin_and_vec(xs, ys)

overload operator & = {and_bool, and_vec}

val builtin_or_vec = {ocaml: "or_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

val or_vec = {lem: "or_vec"} : forall 'n. (bits('n), bits('n)) -> bits('n)

function or_vec (xs, ys) = builtin_or_vec(xs, ys)

overload operator | = {or_bool, or_vec}

val unsigned = {ocaml: "uint", lem: "unsigned"} : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)

val signed = {ocaml: "sint", lem: "signed"} : forall 'n. bits('n) -> range(- (2 ^ ('n - 1)), 2 ^ ('n - 1) - 1)

val hex_slice = "hex_slice" : forall 'n 'm. (string, atom('n), atom('m)) -> bits('n - 'm)

val __SetSlice_bits = "set_slice" : forall 'n 'm.
  (atom('n), atom('m), bits('n), int, bits('m)) -> bits('n)

val __SetSlice_int = "set_slice_int" : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_SetSlice_int : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_GetSlice_int = "get_slice_int" : forall 'w. (atom('w), int, int) -> bits('w)

val __GetSlice_int : forall 'n. (atom('n), int, int) -> bits('n)

function __GetSlice_int (n, m, o) = __raw_GetSlice_int(n, m, o)

val __raw_SetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int, bits('w)) -> bits('n)

val __raw_GetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int) -> bits('w)

val __SignExtendSlice = {lem: "exts_slice"} : forall 'm. (bits('m), int, int) -> bits('m)

val __ZeroExtendSlice = {lem: "extz_slice"} : forall 'm. (bits('m), int, int) -> bits('m)

val cast cast_unit_vec : bit -> bits(1)

function cast_unit_vec bitzero = 0b0
and cast_unit_vec bitone = 0b1

val print = "prerr_endline" : string -> unit

val putchar = "putchar" : forall ('a : Type). 'a -> unit

val concat_str = {ocaml: "concat_str", lem: "stringAppend"} : (string, string) -> string

val string_of_int = "string_of_int" : int -> string

val DecStr : int -> string

val HexStr : int -> string

val BitStr = "string_of_bits" : forall 'n. bits('n) -> string

val xor_vec = "xor_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val int_power = {ocaml: "int_power", lem: "pow"} : (int, int) -> int

val real_power = {ocaml: "real_power", lem: "realPowInteger"} : (real, int) -> real

overload operator ^ = {xor_vec, int_power, real_power}

val add_range = {ocaml: "add_int", lem: "integerAdd"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val add_int = {ocaml: "add_int", lem: "integerAdd"} : (int, int) -> int

val add_vec = "add_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val add_vec_int = "add_vec_int" : forall 'n. (bits('n), int) -> bits('n)

val add_real = {ocaml: "add_real", lem: "realAdd"} : (real, real) -> real

overload operator + = {add_range, add_int, add_vec, add_vec_int, add_real}

val sub_range = {ocaml: "sub_int", lem: "integerMinus"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n - 'p, 'm - 'o)

val sub_int = {ocaml: "sub_int", lem: "integerMinus"} : (int, int) -> int

val "sub_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val "sub_vec_int" : forall 'n. (bits('n), int) -> bits('n)

val sub_real = {ocaml: "sub_real", lem: "realMinus"} : (real, real) -> real

val negate_range = {ocaml: "minus_big_int", lem: "integerNegate"} : forall 'n 'm. range('n, 'm) -> range(- 'm, - 'n)

val negate_int = {ocaml: "minus_big_int", lem: "integerNegate"} : int -> int

val negate_real = {ocaml: "Num.minus_num", lem: "realNegate"} : real -> real

overload operator - = {sub_range, sub_int, sub_vec, sub_vec_int, sub_real}

overload negate = {negate_range, negate_int, negate_real}

val mult_range = {ocaml: "mult", lem: "integerMult"} : forall 'n 'm 'o 'p.
  (range('n, 'm), range('o, 'p)) -> range('n * 'o, 'm * 'p)

val mult_int = {ocaml: "mult", lem: "integerMult"} : (int, int) -> int

val mult_real = {ocaml: "mult_real", lem: "realMult"} : (real, real) -> real

overload operator * = {mult_range, mult_int, mult_real}

val Sqrt = {ocaml: "sqrt_real", lem: "realSqrt"} : real -> real

val gteq_real = {ocaml: "gteq_real", lem: "gteq"} : (real, real) -> bool

overload operator >= = {gteq_atom, gteq_int, gteq_real}

val lteq_real = {ocaml: "lteq_real", lem: "lteq"} : (real, real) -> bool

overload operator <= = {lteq_atom, lteq_int, lteq_real}

val gt_real = {ocaml: "gt_real", lem: "gt"} : (real, real) -> bool

overload operator > = {gt_atom, gt_int, gt_real}

val lt_real = {ocaml: "lt_real", lem: "lt"} : (real, real) -> bool

overload operator < = {lt_atom, lt_int, lt_real}

val RoundDown = {ocaml: "round_down", lem: "realFloor"} : real -> int

val RoundUp = {ocaml: "round_up", lem: "realCeiling"} : real -> int

val abs_int = {ocaml: "abs_int", lem: "abs"} : int -> int

val abs_real = {ocaml: "abs_real", lem: "abs"} : real -> real

overload abs = {abs_int, abs_real}

val quotient_nat = {ocaml: "quotient", lem: "integerDiv"} : (nat, nat) -> nat

val quotient_real = {ocaml: "quotient_real", lem: "realDiv"} : (real, real) -> real

val quotient = {ocaml: "quotient", lem: "integerDiv"} : (int, int) -> int

overload operator / = {quotient_nat, quotient, quotient_real}

val quot_round_zero = {ocaml: "quot_round_zero", lem: "hardware_quot"} : (int, int) -> int
val rem_round_zero = {ocaml: "rem_round_zero", lem: "hardware_mod"} : (int, int) -> int

val modulus = {ocaml: "modulus", lem: "hardware_mod"} : forall 'n, 'n > 0 .  (int, atom('n)) -> range(0, 'n - 1)

overload operator % = {modulus}

val Real = {ocaml: "Num.num_of_big_int", lem: "realFromInteger"} : int -> real

val shl_int = "shl_int" : (int, int) -> int

val shr_int = "shr_int" : (int, int) -> int

val min_nat = {ocaml: "min_int", lem: "min"} : (nat, nat) -> nat

val min_int = {ocaml: "min_int", lem: "min"} : (int, int) -> int

val max_nat = {ocaml: "max_int", lem: "max"} : (nat, nat) -> nat

val max_int = {ocaml: "max_int", lem: "max"} : (int, int) -> int

val min_atom = {ocaml: "min_int", lem: "min"} : forall 'a 'b . (atom('a), atom('b)) -> {'c, ('c = 'a | 'c = 'b) & 'c <= 'a & 'c <= 'b . atom('c)}

val max_atom = {ocaml: "max_int", lem: "max"} : forall 'a 'b . (atom('a), atom('b)) -> {'c, ('c = 'a | 'c = 'b) & 'c >= 'a & 'c >= 'b . atom('c)}

overload min = {min_atom, min_nat, min_int}

overload max = {max_atom, max_nat, max_int}

val __WriteRAM = "write_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m), bits(8 * 'n)) -> unit effect {wmv}

val __MIPS_write : forall 'n. (bits(64), atom('n), bits(8 * 'n)) -> unit effect {wmv}
function __MIPS_write (addr, width, data) = __WriteRAM(64, width, 0x0000_0000_0000_0000, addr, data)

val __TraceMemoryWrite : forall 'n 'm.
  (atom('n), bits('m), bits(8 * 'n)) -> unit

val __ReadRAM = "read_ram" : forall 'n 'm.
  (atom('m), atom('n), bits('m), bits('m)) -> bits(8 * 'n) effect {rmem}

val __MIPS_read : forall 'n. (bits(64), atom('n)) -> bits(8 * 'n) effect {rmem}
function __MIPS_read (addr, width) = __ReadRAM(64, width, 0x0000_0000_0000_0000, addr)

val __TraceMemoryRead : forall 'n 'm. (atom('n), bits('m), bits(8 * 'n)) -> unit

val replicate_bits = "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)

infix 8 ^^
val operator ^^ = {lem: "replicate_bits"} : forall 'n 'm . (bits('n), atom('m)) -> bits('n * 'm)
function operator ^^ (bs, n) = replicate_bits (bs, n)

val cast ex_nat : nat -> {'n, 'n >= 0. atom('n)}

function ex_nat 'n = n

val cast ex_int : int -> {'n, true. atom('n)}

function ex_int 'n = n

/*
val cast ex_range : forall 'n 'm. range('n, 'm) -> {'o, 'n <= 'o <= 'm. atom('o)}

function ex_range (n as 'N) = n
*/

val coerce_int_nat : int -> nat effect {escape}

function coerce_int_nat 'x = {
  assert(constraint('x >= 0));
  x
}

val slice = "slice" : forall ('n : Int) ('m : Int), 'm >= 0 & 'n >= 0.
  (bits('m), int, atom('n)) -> bits('n)

val pow2 = "pow2" : forall 'n. atom('n) -> atom(2 ^ 'n)

val print_int = "print_int" : (string, int) -> unit
val print_bits = "print_bits" : forall 'n. (string, bits('n)) -> unit
val print_string = "print_string" : (string, string) -> unit

union exception = {
  ISAException : unit,
  Error_not_implemented : string,
  Error_misaligned_access : unit,
  Error_EBREAK : unit,
  Error_internal_error : unit
}

val "sign_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)
val "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), atom('m)) -> bits('m)

val EXTS : forall 'n 'm , 'm >= 'n . bits('n) -> bits('m)
val EXTZ : forall 'n 'm , 'm >= 'n . bits('n) -> bits('m)

function EXTS v = sign_extend(v, sizeof('m))
function EXTZ v = zero_extend(v, sizeof('m))

val zeros : forall 'n, 'n >= 0 . unit -> bits('n)
function zeros() = replicate_bits (0b0,'n)

val ones : forall 'n, 'n >= 0 . unit -> bits('n)
function ones() = replicate_bits (0b1,'n)

infix 4 <_s
infix 4 >=_s
infix 4 <_u
infix 4 >=_u

val operator <_s  = {lem: "slt_vec"}   : forall 'n. (bits('n), bits('n)) -> bool
val operator >=_s = {lem: "sgteq_vec"} : forall 'n. (bits('n), bits('n)) -> bool
val operator <_u  = {lem: "ult_vec"}   : forall 'n. (bits('n), bits('n)) -> bool
val operator >=_u = {lem: "ugteq_vec"} : forall 'n. (bits('n), bits('n)) -> bool

function operator <_s  (x, y) = signed(x) < signed(y)
function operator >=_s (x, y) = signed(x) >= signed(y)
function operator <_u  (x, y) = unsigned(x) < unsigned(y)
function operator >=_u (x, y) = unsigned(x) >= unsigned(y)

val cast bool_to_bits : bool -> bits(1)
function bool_to_bits x = if x then 0b1 else 0b0

val cast bit_to_bool : bit -> bool
function bit_to_bool bitone  = true
and      bit_to_bool bitzero = false

val cast bits_to_bool : bits(1) -> bool
function bits_to_bool x = bit_to_bool(x[0])

infix 1 >>
infix 1 <<
infix 1 >>_s

val "shift_bits_right" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)
val "shift_bits_left" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)

val "shiftl" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)
val "shiftr" : forall 'm 'n, 'n >= 0. (bits('m), atom('n)) -> bits('m)

overload operator >> = {shift_bits_right, shiftr}
overload operator << = {shift_bits_left, shiftl}
val operator >>_s = "shift_bits_right_arith" : forall 'n 'm. (bits('n), bits('m)) -> bits('n)

infix 7 *_s
val operator *_s = "smult_vec" : forall 'n . (bits('n), bits('n)) -> bits(2 * 'n)
infix 7 *_u
val operator *_u = "mult_vec" : forall 'n . (bits('n), bits('n)) -> bits(2 * 'n)

val vector64 : int -> bits(64)

function vector64 n = __raw_GetSlice_int(64, n, 0)

val to_bits : forall 'l.(atom('l), int) -> bits('l)
function to_bits (l, n) = __raw_GetSlice_int(l, n, 0)

function break () : unit -> unit = ()

val vector_update_subrange_dec = {ocaml: "update_subrange", lem: "update_subrange_vec_dec"} : forall 'n 'm 'o.
  (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)

val vector_update_subrange_inc = {ocaml: "update_subrange", lem: "update_subrange_vec_inc"} : forall 'n 'm 'o.
  (vector('n, inc, bit), atom('m), atom('o), vector('o - ('m - 1), inc, bit)) -> vector('n, inc, bit)

overload vector_update_subrange = {vector_update_subrange_dec, vector_update_subrange_inc}

val mask : forall 'm 'n , 'm >= 'n > 0 . bits('m) -> bits('n)
function mask bs = bs['n - 1 .. 0]