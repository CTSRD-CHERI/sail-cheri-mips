$property
function prop_inc_bounds_eq(c : Capability, delta : bits(64)) -> bool = {
  let (representable, c') = incCapOffset(c, delta) in
  ~(representable) | capBoundsEqual(c, c')
}

$property
function prop_set_bounds_exact(c : Capability, base' : bits(64), top' : bits(65)) -> bool = {
  let (exact, c') = setCapBounds(c, base', top');
  let (base'', top'') = getCapBounds(c');
  ~(exact) | (base'' == unsigned(base') & top'' == unsigned(top'))
}

$property
function prop_set_bounds_mono(c_bits : CapBits, len' : bits(64)) -> bool =
  let c = capBitsToCapability(true, c_bits) in
  let (base, top) = getCapBounds(c) in
  let base' = getCapCursor(c) in
  let top' = base' + unsigned(len') in
  let (_, c') = setCapBounds(c, to_bits(64, base'), to_bits(65, top')) in
  let (base'', top'') = getCapBounds(c') in
  if (base <= base' & top' <= top) then (base <= base'' & top'' <= top) else true


/* For any base and len does cram / crap give the same bounds as setCapBounds?
  That turns out not to be true, but we can prove that cram / crap give
  at least as strict bounds as setCapBounds alone */
$counterexample
function prop_crap_cram_setbounds(base : bits(64), len : bits(64)) -> bool = {
  let top = (0b0 @ base) + (0b0 @ len);
  let (exact, c) = setCapBounds(default_cap, base, top);
  let (base', top') = getCapBounds(c);
  let m = getRepresentableAlignmentMask(len);
  let l2 = getRepresentableLength(len);
  let sensibleBounds = unsigned(top) < pow2(64);
  not(sensibleBounds) | (top' - base') >= unsigned(l2)
}

/* Check that crap and crap always give exact bounds */
$property
function prop_crap_cram_exact(base : bits(64), len : bits(64)) -> bool = {
  let m = getRepresentableAlignmentMask(len);
  let l2 = getRepresentableLength(len);
  let masked_base = base & m;
  let top = masked_base + l2;
  let sensibleBounds = masked_base <_u top;
  let (exact, c) = setCapBounds(default_cap, masked_base, 0b0 @ top);
  not(sensibleBounds) | exact
}

/* This property is not true because of the corner case where length rounds up to 2**64 */
$counterexample
function prop_crap_ge (len : bits(64)) -> bool = {
  getRepresentableLength(len) >=_u len
}

/* The following are implementations of crap / cram from first
   principles. This duplicates a lot of logic of setCapBounds hence
   why implementations in cheri_prelude_128 uses that
   instead. Properties below prove that they are equivalent. */

function getRepresentableAlignmentMask2(len : bits(64)) -> bits(64) = {
  let e = 51 - count_leading_zeros(len[63..13]);
  // Use use internal exponent if e is non-zero or if e is zero but
  // but the implied bit of length is not zero (denormal vs. normal case)
  let ie = (e != 0) | len[12];
  if ie then {
    let maskLen = e + 3;
    let lenSignificant = len >> maskLen;
    let m : bits(64) = zeros(64 - maskLen) @ ones(maskLen);
    let exact = (len & m) == zeros();
    if exact then {
      ~(m)
    } else {
      let roundedLen = lenSignificant + 1;
      if (roundedLen[10] == bitone) then {
        ones(63 - maskLen) @ zeros(maskLen + 1)
      } else {
        ~(m)
      }
    }
  } else
    zeros() // all lengths exactly representable when ie=0

}

function getRepresentableLength2(len) : bits(64) -> bits(64) = {
  let e = 51 - count_leading_zeros(len[63..13]);
  // Use use internal exponent if e is non-zero or if e is zero but
  // but the implied bit of length is not zero (denormal vs. normal case)
  let ie = (e != 0) | len[12];
  if ie then {
    let maskLen = e + 3;
    let lenSignificant = len >> maskLen;
    let m : bits(64) = zero_extend(ones(maskLen)); //zeros(64 - maskLen) @ ones(maskLen);
    let exact = (len & m) == zeros();
    if exact then {
      lenSignificant << maskLen
    } else {
      let roundedLen = lenSignificant + 1;
      if (roundedLen[10] == bitone) then {
        // overflow
        (roundedLen >> 1) << (maskLen + 1)
      } else {
        roundedLen << maskLen
      }
    }
  } else
    len // all lengths exactly representable when ie=0
}

$property
function prop_crap2(len : bits(64)) -> bool = {
  getRepresentableLength(len) == getRepresentableLength2(len)
}

$property
function prop_cram2(len : bits(64)) -> bool = {
  getRepresentableAlignmentMask(len) == getRepresentableAlignmentMask2(len)
}
