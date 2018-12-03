open Sail_lib
module BI = Nat_big_num

let gen_sailbits n =
  QCheck.Gen.(list_repeat n (map Sail_lib.bit_of_bool bool))

(* Generate bitvectors of n bits biased towards smaller values *)
let gen_sailbits_geom n s =
  let zeros = Random.State.int s (n-1) in
  let lowerBits = gen_sailbits (n - zeros) s in
  Sail_lib.zeros (BI.of_int zeros) @ lowerBits
  
let arbitrary_cap_bits = QCheck.make ~print:Sail_lib.string_of_bits (gen_sailbits 128)

let test_cap_decode_encode capbits =
  Sail_lib.eq_list (Cheri_cc.zcapToBits (Cheri_cc.zcapBitsToCapability (true, capbits)), capbits)

(* XXX this never generates 2^64 for tops... *) 
let gen_bounds =
  QCheck.Gen.(list_repeat 4 (gen_sailbits_geom 64))

let print_bounds = QCheck.Print.list Sail_lib.string_of_bits
let arbitrary_bounds = QCheck.make ~print:print_bounds gen_bounds

(* Round trip Capability through bits. This is an important step in some
   tests because the expanded Capability can represent some things that
   bits can't and we probably want to ensure that we are only generating 
   values in normal form (that can be represented as bits).
   XXX maybe we could eliminate the non-normal values from type *)
let cap_encode_decode  (c : Cheri_cc.zCapability)  =
  let cbits = Cheri_cc.zcapToBits c in
  let c2 = Cheri_cc.zcapBitsToCapability (c.ztag, cbits) in
  begin
    assert(c = c2);
    c2
  end

let test_setBounds bounds =
  (* pair each bit list with Big_int representation for easy comparison etc. *)
  let zippedBounds = List.combine bounds (List.map Sail_lib.uint bounds) in
  let sortedBounds = List.sort (fun (_, a) (_, b) -> BI.compare a b) zippedBounds in
  let [base1; base2; top2; top1] = sortedBounds in
  let (exact1, cap1) = Cheri_cc.zsetCapBounds(Cheri_cc.zdefault_cap, fst(base1), B0::fst(top1)) in
  let (exact2, cap2) = Cheri_cc.zsetCapBounds(Cheri_cc.zdefault_cap, fst(base2), B0::fst(top2)) in
  let (newBase1, newTop1) = Cheri_cc.zgetCapBounds(cap_encode_decode cap1) in
  let (newBase2, newTop2) = Cheri_cc.zgetCapBounds(cap_encode_decode cap2) in
  begin
    (*print_endline (print_bounds bounds); *)
    (*print_endline ("base1 " ^ (Z.format "x" newBase1) ^ " " ^ (Z.format "%x" (snd base1)));*)
    (*if exact1 && not cap1.zinternal_e then
      print_endline ((if exact1 then "exact1" else "!exact1") ^ (if exact2 then " exact2" else " !exact2"));*)
  (* check cap1 includes the bounds requested - it's probably safe
     to assume that cap1 is within default_cap... *)
  BI.less_equal newBase1 (snd base1) &&
  BI.less_equal (snd top1) newTop1 &&
  (* check cap2 includes requested bounds *)
  BI.less_equal newBase2 (snd base2) &&
  BI.less_equal (snd top2) newTop2 &&
  (* check cap2 is within cap1 *)
  BI.less_equal newBase1 newBase2 &&
  BI.less_equal newTop2 newTop1
  (* XXX would be nice to have upper bound of length of caps that is less than 
     length of original cap *)
  end

let testsuite = [
  QCheck.Test.make ~count:10000 ~long_factor:1000 ~name:"cap_decode_encode" arbitrary_cap_bits test_cap_decode_encode;
  QCheck.Test.make ~count:10000 ~long_factor:1000 ~name:"setCapBounds"  arbitrary_bounds test_setBounds;
]

let () =
  begin
    QCheck_runner.run_tests_main testsuite
  end
