/*========================================================================*/
/*                                                                        */
/*  Copyright (c) 2015-2017 Robert M. Norton                              */
/*  Copyright (c) 2015-2017 Kathyrn Gray                                  */
/*  All rights reserved.                                                  */
/*                                                                        */
/*  This software was developed by the University of Cambridge Computer   */
/*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  */
/*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*     notice, this list of conditions and the following disclaimer.      */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*     notice, this list of conditions and the following disclaimer in    */
/*     the documentation and/or other materials provided with the         */
/*     distribution.                                                      */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    */
/*  SUCH DAMAGE.                                                          */
/*========================================================================*/

type CapBits = bits(128)
let max_otype = MAX(18)

/*
A partially decompressed version of a capability -- E, B, T,
lenMSB, sealed and otype fields are not present in all formats and are
populated by capBitsToCapability
 */
struct Capability = {
  tag                    : bool    ,
  uperms                 : bits(4) ,
  access_system_regs     : bool    ,
  permit_unseal          : bool    ,
  permit_ccall           : bool    ,
  permit_seal            : bool    ,
  permit_store_local_cap : bool    ,
  permit_store_cap       : bool    ,
  permit_load_cap        : bool    ,
  permit_store           : bool    ,
  permit_load            : bool    ,
  permit_execute         : bool    ,
  global                 : bool    ,
  reserved               : bits(3) ,
  internal_e             : bool    ,
  E                      : bits(6) ,
  lenMSB                 : bit     ,
  sealed                 : bool    ,
  B                      : bits(23),
  T                      : bits(23),
  otype                  : bits(24),
  address                : bits(64)
}

/* Reset E and T calculated to make top 2**65. */
let resetE = 0b101011 /* 43 */
let resetT = 0b010 @ 0x00000 /* bit 22 set */

let null_cap : Capability = struct {
  tag                    = false,
  uperms                 = zeros(),
  access_system_regs     = false,
  permit_unseal          = false,
  permit_ccall           = false,
  permit_seal            = false,
  permit_store_local_cap = false,
  permit_store_cap       = false,
  permit_load_cap        = false,
  permit_store           = false,
  permit_load            = false,
  permit_execute         = false,
  global                 = false,
  reserved               = zeros(),
  internal_e             = true,
  E                      = resetE,
  lenMSB                 = bitzero,
  sealed                 = false,
  B                      = zeros(),
  T                      = resetT,
  otype                  = zeros(),
  address                = zeros()
}

let default_cap : Capability = struct {
  tag                    = true,
  uperms                 = ones(),
  access_system_regs     = true,
  permit_unseal          = true,
  permit_ccall           = true,
  permit_seal            = true,
  permit_store_local_cap = true,
  permit_store_cap       = true,
  permit_load_cap        = true,
  permit_store           = true,
  permit_load            = true,
  permit_execute         = true,
  global                 = true,
  reserved               = zeros(),
  internal_e             = true,
  E                      = resetE,
  lenMSB                 = bitzero,
  sealed                 = false,
  B                      = zeros(),
  T                      = resetT,
  otype                  = zeros(),
  address                = zeros()
}

let 'cap_size = 16

/*
Convert from capabilty bits (128 bits with tag) to a more convenient struct.
 */
function capBitsToCapability(t, c) : (bool, CapBits) -> Capability = {
  internal_exponent : bool = c[109];
  E : bits(6)  = zeros();
  Bs : bits(23) = zeros();
  T : bits(21) = zeros();
  lenMSBs : bits(2) = zeros();
  otype : bits(24) = zeros();
  sealed : bool = c[108];
  if internal_exponent then {
    /* Exponent stored instead of T[2..0] and B[2..0] */
    E = c[89..87] @ c [66..64];
    /* Exponent chosen so that length MSBs is 01 */
    lenMSBs = 0b01;
    /* Sealed bit stored instead of second top bit of T */
    if sealed then {
      /* otype stored in T[11..3] and B[11..3] */
      otype = zero_extend(c[98..90] @ c[75..67]);
      T = c[107..99] @ 0x000;
      Bs = c[86..76] @ 0x000;
    } else {
      T = c[107..90] @ 0b000;
      Bs = c[86..67] @ 0b000;
    };
  } else {
    /* Exponent zero */
    lenMSBs = 0b0 @ c[108];
    T = c[107..87];
    Bs = c[86..64];
  };
  /* 
  Reconstruct top two bits of T given T = B + len and:
  1) the top two bits of B 
  2) most significant two bits of length derived from format above
  3) carry out of B[20..0] + len[20..0] that is implied if T[20..0] < B[20..0]
  */
  carry_out = if T[20..0] <_u Bs[20..0] then 0b01 else 0b00;
  Ttop2 = Bs[22..21] + lenMSBs + carry_out;
  return struct {
    tag                    = t,
    uperms                 = c[127..124],
    access_system_regs     = c[123],
    permit_unseal          = c[122],
    permit_ccall           = c[121],
    permit_seal            = c[120],
    permit_store_local_cap = c[119],
    permit_store_cap       = c[118],
    permit_load_cap        = c[117],
    permit_store           = c[116],
    permit_load            = c[115],
    permit_execute         = c[114],
    global                 = c[113],
    reserved               = c[112..110],
    internal_e             = internal_exponent,
    E                      = E,
    lenMSB                 = c[108],
    sealed                 = sealed,
    B                      = Bs,
    T                      = Ttop2 @ T,
    otype                  = otype,
    address                = c[63..0]
  }
}

function getCapHardPerms(cap) : Capability -> bits(11) =
   (cap.access_system_regs
  @ cap.permit_unseal
  @ cap.permit_ccall
  @ cap.permit_seal
  @ cap.permit_store_local_cap
  @ cap.permit_store_cap
  @ cap.permit_load_cap
  @ cap.permit_store
  @ cap.permit_load
  @ cap.permit_execute
  @ cap.global)

/*
Convert from capabilty struct to bits (128 -- no tag) 
 */
function capToBits(cap) : Capability -> bits(128) = {
  sealedOrLenMSB : bits(1) = cap.lenMSB;
  t_hi : bits(9)  = cap.T[20..12];
  t_mid : bits(9) = cap.T[11..3];
  t_lo : bits(3)  = cap.T[2..0];
  b_hi : bits(11) = cap.B[22..12];
  b_mid : bits(9) = cap.B[11..3];
  b_lo : bits(3)  = cap.B[2..0];
  if cap.internal_e then {
    sealedOrLenMSB = cap.sealed;
    t_lo = cap.E[5..3];
    b_lo = cap.E[2..0];
    if cap.sealed then {
      t_mid = cap.otype[17..9];
      b_mid = cap.otype[8..0];
    }
  };
  return (cap.uperms
    @ getCapHardPerms(cap)
    @ cap.reserved
    @ cap.internal_e
    @ sealedOrLenMSB
    @ t_hi
    @ t_mid
    @ t_lo
    @ b_hi
    @ b_mid
    @ b_lo
    @ cap.address
  );
}
 
/* When saving/restoring capabilities xor them with bits of null_cap --
   this ensures that canonical null_cap is always all-zeros in memory
   even though it may have bits set logically (e.g. length or exponent */

let null_cap_bits : bits(128) = capToBits(null_cap)

function capToMemBits(cap) : Capability -> bits(128) =
  capToBits(cap) ^ null_cap_bits

function memBitsToCapability(tag, b) : (bool, bits(128)) -> Capability =
  capBitsToCapability(tag, b ^ null_cap_bits)

function getCapPerms(cap) : Capability -> bits(31) = 
    let perms : bits(15) = zero_extend(getCapHardPerms(cap)) in
    (0x000 /* uperms 30-19 */
  @ cap.uperms
  @ perms)

function setCapPerms(cap, perms) : (Capability, bits(31)) -> Capability =
    { cap with
      uperms                 = perms[18..15],
      /* 14..11 reserved -- ignore */
      access_system_regs     = perms[10],
      permit_unseal          = perms[9],
      permit_ccall           = perms[8],
      permit_seal            = perms[7],
      permit_store_local_cap = perms[6],
      permit_store_cap       = perms[5],
      permit_load_cap        = perms[4],
      permit_store           = perms[3],
      permit_load            = perms[2],
      permit_execute         = perms[1],
      global                 = perms[0]
      }

function sealCap(cap, otype) : (Capability, bits(24)) -> (bool, Capability) =
    if (((cap.T)[11..0] == zeros()) & ((cap.B)[11..0] == zeros())) then /* XXX check internal_e */
        (true, {cap with sealed=true, internal_e=true, otype=otype})
    else
        (false, cap /* XXX should be undefined? */ )

function a_top_correction(a_mid, R, bound) : (bits(3), bits(3), bits(3)) -> bits(66) =
    match (a_mid <_u R, bound <_u R) {
      (false, false)  => zeros(),
      (false, true)   => zero_extend(0b1),
      (true, false)   => ones(),
      (true, true)    => zeros()
    }

function getCapBase(c) : Capability -> uint64 =
    let E = unsigned(c.E) in
    let B3 : bits(3) = c.B[22..20] in
    let a : bits(66) = zero_extend(c.address) in
    let R : bits(3) = B3 - 0b001 in /* wraps */
    let a_mid : bits(23) = mask(a >> E) in
    let correction = a_top_correction(a_mid[22..20], R, B3) in
    let a_top = (a >> E+23) in
    let base : bits(64) = mask((a_top + correction) @ c.B @ replicate_bits(0b0, E)) in
    unsigned(base)

function getCapTop (c) : Capability -> CapLen = 
    let E = unsigned(c.E) in
    let B3 : bits(3) = c.B[22..20] in
    let T3 : bits(3) = c.T[22..20] in
    let a : bits(66) = zero_extend(c.address)  in
    let R : bits(3) = B3 - 0b001 in /* wraps */
    let a_mid : bits(23) = mask(a >> E) in
    let correction = a_top_correction(a_mid[22..20], R, T3) in
    let a_top = a >> E+23 in
    let top : bits(65) = mask((a_top + correction) @ c.T @ replicate_bits(0b0, E)) in
    unsigned(top)

function getCapOffset(c) : Capability -> uint64 = 
    let base = getCapBase(c) in
    (unsigned(c.address) - base) % pow2(64)

function getCapLength(c) : Capability -> CapLen =
         let 'top = getCapTop(c) in
         let 'base = getCapBase(c) in {
             assert (top >= base);
             top - base
         }

function getCapCursor(cap) : Capability -> uint64 = unsigned(cap.address)

/*
function fastRepCheck(c, i) : (Capability, bits(64)) -> bool=
    let 'E = unsigned(c.E) in
    if (E >= resetE) then
        true /* in this case representable region is whole address space */
    else
        let E'       = min(E, resetE) in
        let i_top    = signed(i >>_s (E+23)) in
        let i_mid : bits(23) = truncate(i >>_s E)in
        let a_mid : bits(23) = truncate(c.address >> E) in
        let R : bits(20)     = (c.B) - 0x01000 in
        let diff : bits(20)  = R - a_mid in
        let diff1 : bits(20) = diff - 1 in
        /* i_top determines 1. whether the increment is inRange
           i.e. less than the size of the representable region
           (2**(E+20)) and 2. whether it is positive or negative. To
           satisfy 1. all top bits must be the same so we are
           interested in the cases i_top is 0 or -1 */
        if (i_top == 0) then
          i_mid <_u diff1
        else if (i_top == -1) then
          (i_mid >=_u diff) & (R != a_mid)
        else
          false
*/

function capBoundsEqual (c1, c2) : (Capability, Capability) -> bool = 
    let base1 = getCapBase(c1) in
    let base2 = getCapBase(c2) in
    let top1 = getCapTop(c1) in
    let top2 = getCapTop(c2) in
    (base1 == base2) & (top1 == top2)

function setCapOffset(c, offset) : (Capability, bits(64)) -> (bool, Capability) =
    let base64 : bits(64) = to_bits(64, getCapBase(c)) in
    let newAddress : bits(64) = base64 + offset in
    let newCap     = { c with address = newAddress } in
    let representable = capBoundsEqual(c, newCap) in
/*    let representable = fastRepCheck(c, (newAddress - c.address)) in*/
    (representable, newCap)

function incCapOffset(c, delta) : (Capability, bits(64)) -> (bool, Capability) =
    let newAddress : bits(64) = c.address + delta in
    let newCap     = { c with address = newAddress } in
    let representable = capBoundsEqual(c, newCap) in
/*    let representable = fastRepCheck(c, delta) in*/
    (representable, newCap)

val CountLeadingZeros : forall 'N , 'N >= 2. bits('N) -> {'n, 0 <= 'n <= 'N . atom('n)}
function CountLeadingZeros x = {
  foreach (i from ('N - 1) to 0 by 1 in dec)
    if [x[i]] == 0b1 then return 'N - i - 1;
  return 'N;
}

function setCapBounds(cap, base, top) : (Capability, bits(64), bits(65)) -> (bool, Capability) = {
  /* {cap with base=base; length=(bits(64)) length; offset=0} */
  base66 = 0b00 @ base;
  top66  = 0b0  @ top;
  let length : bits(66) = top66 - base66; // why 66?
  /* roughly index of highest set bit excluding (MW-1) lower bits */
  let e = 43 - CountLeadingZeros(length[64..22]);
  let e0 = e == 0; // maxZero in bsv  
  let lenMSB = if e0 then length[21] else bitzero; // sample len MW-2
  // extract MW + 1 bits of top and base -- we might need extra one if we round up e
  Bs : bits(23) = zeros();
  T : bits(23) = zeros();
  let newBaseBits : bits(24) = mask(base >> e);
  let newTopBits  : bits(24) = mask(top >> e);
  // If top has significant bits we are going to lose then we must round up T by one
  // Construct a mask of e bits
  roundedLength = length + (length >> 18);
  newTopBitsRounded : bits(20) = mask((base66 + roundedLength) >> (e + 3));
  roundedLength2 = length + (length >> 16);
  newTopBitsRoundedHigher : bits(20) = mask((base66 + roundedLength2) >> (e + 4));
  lmask : bits(66) = zero_extend(replicate_bits(0b1, e));
  lmaskLo = lmask >> 19;
  lostSignificantTop = ((top66 & lmaskLo) != zeros()) & not(e0);
  lostSignificantBase = ((base66 & lmaskLo) != zeros()) & not(e0);
  lengthMax = (length & (~(lmaskLo)))==(lmask&(~(lmaskLo)));
  incE = false;
  if (lengthMax & not(e0)) then {
    // rounding means we have to increase e by one
    incE = true;
    Bs = newBaseBits[23..4] @ 0b000;
    T = newTopBitsRoundedHigher @ 0b000;
  } else if (lostSignificantTop) then {
    // embedded exp case
    Bs = newBaseBits[22..3] @ 0b000;
    T = newTopBitsRounded @ 0b000;
  } else {
    /* e0 case */
    Bs = newBaseBits[22..0];
    T = newTopBits[22..0];
  };
  let newCap  = {cap with address=base, E=to_bits(6, if incE then e + 1 else e ), B=Bs, T=T, lenMSB=lenMSB, internal_e=not(e0)};
  let newBase = getCapBase(newCap);
  let newTop  = getCapTop(newCap);
  let exact   = (unsigned(base) == newBase) & (unsigned(top) == newTop);
  (exact, newCap)
}

function int_to_cap (offset) : bits(64) -> Capability = 
    {null_cap with address = offset}
