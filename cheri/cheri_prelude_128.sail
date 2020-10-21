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
let max_otype = MAX(18) - reserved_otypes

/*
A partially decompressed version of a capability -- E, B, T,
lenMSB, sealed and otype fields are not present in all formats and are
populated by capBitsToCapability
 */
struct Capability = {
  tag                    : bool    ,
  uperms                 : bits(4) ,
  permit_set_CID         : bool    ,
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
  sealed                 : bool    ,
  B                      : bits(14),
  T                      : bits(14),
  otype                  : bits(18),
  address                : bits(64)
}

/* Reset E and T calculated to make top 2**64. */
let resetE = to_bits(6, 52)
let resetT = 0b01 @ 0x000 /* bit 12 set */

let null_cap : Capability = struct {
  tag                    = false,
  uperms                 = zeros(),
  permit_set_CID         = false,
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
  sealed                 = false,
  B                      = zeros(),
  T                      = resetT,
  otype                  = ones(),
  address                = zeros()
}

let default_cap : Capability = struct {
  tag                    = true,
  uperms                 = ones(),
  permit_set_CID         = true,
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
  sealed                 = false,
  B                      = zeros(),
  T                      = resetT,
  otype                  = ones(),
  address                = zeros()
}

let 'cap_size = 16
let 'caps_per_cacheline = 8

/*
Convert from capabilty bits (128 bits with tag) to a more convenient struct.
 */
function capBitsToCapability(t, c) : (bool, CapBits) -> Capability = {
  internal_exponent : bool = c[90];
  otype : bits(18) = c[108..91];
  let sealed : bool = otype != ones();
  E : bits(6)  = zeros();
  Bs : bits(14) = zeros();
  T : bits(12) = zeros();
  lenMSBs : bits(2) = zeros();
  if internal_exponent then {
    /* Exponent stored instead of T[2..0] and B[2..0] */
    E = c[80..78] @ c [66..64];
    /* Exponent chosen so that length MSBs is 01 */
    lenMSBs = 0b01;
    T = c[89..81] @ 0b000;
    Bs = c[77..67] @ 0b000;
  } else {
    /* Exponent zero */
    lenMSBs = 0b00;
    T = c[89..78];
    Bs = c[77..64];
  };
  /*
  Reconstruct top two bits of T given T = B + len and:
  1) the top two bits of B
  2) most significant two bits of length derived from format above
  3) carry out of B[20..0] + len[20..0] that is implied if T[20..0] < B[20..0]
  */
  carry_out = if T <_u Bs[11..0] then 0b01 else 0b00;
  Ttop2 = Bs[13..12] + lenMSBs + carry_out;
  return struct {
    tag                    = t,
    uperms                 = c[127..124],
    permit_set_CID         = c[123],
    access_system_regs     = c[122],
    permit_unseal          = c[121],
    permit_ccall           = c[120],
    permit_seal            = c[119],
    permit_store_local_cap = c[118],
    permit_store_cap       = c[117],
    permit_load_cap        = c[116],
    permit_store           = c[115],
    permit_load            = c[114],
    permit_execute         = c[113],
    global                 = c[112],
    reserved               = c[111..109],
    internal_e             = internal_exponent,
    E                      = E,
    sealed                 = sealed,
    B                      = Bs,
    T                      = Ttop2 @ T,
    otype                  = otype,
    address                = c[63..0]
  }
}

function getCapHardPerms(cap) : Capability -> bits(12) =
   (cap.permit_set_CID
  @ cap.access_system_regs
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
  t_hi : bits(9)  = cap.T[11..3];
  t_lo : bits(3)  = cap.T[2..0];
  b_hi : bits(11) = cap.B[13..3];
  b_lo : bits(3)  = cap.B[2..0];
  if cap.internal_e then {
    t_lo = cap.E[5..3];
    b_lo = cap.E[2..0];
  };
  return (cap.uperms
    @ getCapHardPerms(cap)
    @ cap.reserved
    @ cap.otype
    @ cap.internal_e
    @ t_hi
    @ t_lo
    @ b_hi
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
      /* 14..12 reserved -- ignore */
      permit_set_CID         = perms[11],
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

function sealCap(cap, otyp) : (Capability, bits(24)) -> (bool, Capability) =
    (true, {cap with sealed=true, otype=otyp[17..0]})

function unsealCap(cap) : Capability -> Capability =
    {cap with sealed=false, otype=ones()}

function getCapBounds(c) : Capability -> (uint64, CapLen) =
  let E = unsigned(c.E) in
  let a : bits(64) = c.address in
  /* Extract bits we need to make the top correction and calculate representable limit */
  let a3 = truncate(a >> (E + 11), 3) in
  let B3 = truncateLSB(c.B, 3) in
  let T3 = truncateLSB(c.T, 3) in
  let R3 = B3 - 0b001 in /* wraps */
  /* Do address, base and top lie in the R aligned region above the one containing R? */
  let aHi = if a3 <_u R3 then 1 else 0 in
  let bHi = if B3 <_u R3 then 1 else 0 in
  let tHi = if T3 <_u R3 then 1 else 0 in
  /* Compute region corrections for top and base relative to a */
  let correction_base = bHi - aHi in
  let correction_top  = tHi - aHi in
  let a_top = (a >> (E + 14)) in {
    base : bits(65) = truncate((a_top + correction_base) @ c.B @ zeros(E), 65);
    top  : bits(65) = truncate((a_top + correction_top)  @ c.T @ zeros(E), 65);
    if (base[64] == bitone) then {
      /* If base[64] is set this indicates under or overflow i.e. a has
         wrapped around the address space and been corrected. In this case
         we need to correct top[64] because top is not quite modulo 2**64 due
         to having max top == 2**64 in one particular case: */
       top[64] = if (aHi == 1) & (tHi == 1) then bitone else bitzero;
    };
    /* The following is apparently equivalent to above and used by hw. */
    /*
    let base2 : bits(2) = bitzero @ base[63];
    let top2  : bits(2) = top[64..63];
    if (E < (unsigned(resetE) - 1)) & (unsigned(top2 - base2) > 1) then {
      top[64] = ~(top[64]);
    };
    */
    (unsigned(base[63..0]), unsigned(top))
  }

function getCapBase(c) : Capability -> uint64 =
    let (base, _) = getCapBounds(c) in
    base

function getCapTop (c) : Capability -> CapLen =
    let (_, top) = getCapBounds(c) in
    top

function getCapOffset(c) : Capability -> uint64 =
    let base = getCapBase(c) in
    (unsigned(c.address) - base) % pow2(64)

function getCapLength(c) : Capability -> CapLen =
    let ('base, 'top) = getCapBounds(c) in {
        /* For valid capabilties we expect top >= base and hence
           length >= 0 but representation does allow top < base in some
           cases so might encounter on untagged capabilities. Here we just
           pretend it is a 65-bit quantitiy and wrap. */
        assert (not(c.tag) | top >= base);
        (top - base) % pow2(65)
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
    let (base1, top1) = getCapBounds(c1) in
    let (base2, top2) = getCapBounds(c2) in
    (base1 == base2) & (top1 == top2)

val setCapAddr : (Capability, bits(64)) -> (bool, Capability)
function setCapAddr(c, addr) =
    let newCap = { c with address = addr } in
    let representable = capBoundsEqual(c, newCap) in
    (representable, newCap)

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

/*
An 'ideal' version of setCapBounds as described in paper.
 */
function setCapBounds(cap, base, top) : (Capability, bits(64), bits(65)) -> (bool, Capability) = {
  /* {cap with base=base; length=(bits(64)) length; offset=0} */
  let base65 = 0b0 @ base;
  let length = top - base65;
  /* Find an exponent that will put the most significant bit of length
     second from the top as assumed during decoding. We ignore the bottom
     MW - 1 bits because those are handled by the ie = 0 format. */
  let e = 52 - count_leading_zeros(length[64..13]);
  // Use use internal exponent if e is non-zero or if e is zero but
  // but the implied bit of length is not zero (denormal vs. normal case)
  let ie = (e != 0) | length[12];

  /* The non-ie e == 0 case is easy. It is exact so just extract relevant bits. */
  Bbits = truncate(base, 14);
  Tbits = truncate(top, 14);
  lostSignificantTop  : bool = false;
  lostSignificantBase : bool = false;
  incE : bool = false;

  if ie then {
    /* the internal exponent case is trickier */

    /* Extract B and T bits (we lose 3 bits of each to store the exponent) */
    B_ie = truncate(base >> (e + 3), 11);
    T_ie = truncate(top >> (e + 3), 11);

    /* Find out whether we have lost significant bits of base and top using a
       mask of bits that we will lose (including 3 extra for exp). */
    maskLo : bits(65) = zero_extend(ones(e + 3));
    z65    : bits(65) = zeros();
    lostSignificantBase = (base65 & maskLo) != z65;
    lostSignificantTop = (top & maskLo) != z65;

    if lostSignificantTop then {
      /* we must increment T to make sure it is still above top even with lost bits.
         It might wrap around but if that makes B<T then decoding will compensate. */
      T_ie = T_ie + 1;
    };

    /* Has the length overflowed? We chose e so that the top two bits of len would be 0b01,
       but either because of incrementing T or losing bits of base it might have grown. */
    len_ie = T_ie - B_ie;
    if len_ie[10] then {
      /* length overflow -- increment E by one and then recalculate
         T, B etc accordingly */
      incE = true;

      lostSignificantBase = lostSignificantBase | B_ie[0];
      lostSignificantTop  = lostSignificantTop | T_ie[0];

      B_ie = truncate(base >> (e + 4), 11);
      let incT : range(0,1) = if lostSignificantTop then 1 else 0;
      T_ie = truncate(top >> (e + 4), 11) + incT;
    };

    Bbits = B_ie @ 0b000;
    Tbits = T_ie @ 0b000;
  };
  let newCap = {cap with address=base, E=to_bits(6, if incE then e + 1 else e), B=Bbits, T=Tbits, internal_e=ie};
  let exact = not(lostSignificantBase | lostSignificantTop);
  (exact, newCap)
}

function getRepresentableAlignmentMask(len) : bits(64) -> bits(64) = {
  let (exact, c) = setCapBounds(default_cap,  ones() - len, 0b0 @ 0xffffffffffffffff);
  let e : range(0, 52) = min(unsigned(c.E), 52);
  let e' : range(0, 55) = if c.internal_e then e + 3 else 0;
  ones(64-e') @ zeros(e')
}

function getRepresentableLength(len) : bits(64) -> bits(64) = {
  let m = getRepresentableAlignmentMask(len);
  (len + ~(m)) & m
}


/*
This version of setCapBounds was transcribed from Bluespec. It uses some approximations to help pass timing that can result in wider bounds than returned by above version.
 */
/*
function setCapBounds_hw(cap, base, top) : (Capability, bits(64), bits(65)) -> (bool, Capability) = {
  /* {cap with base=base; length=(bits(64)) length; offset=0} */
  base66 = 0b00 @ base;
  top66  = 0b0  @ top;
  let length : bits(66) = top66 - base66; // why 66?
  /* roughly index of highest set bit excluding (MW-1) lower bits */
  let e = 43 - count_leading_zeros(length[64..22]);
  let e0 = e == 0; // called maxZero in bsv
  let lenMSB = if e0 then length[21] else bitzero; // sample len MW-2
  // extract MW + 1 bits of top and base -- we might need extra one if we round up e
  Bs : bits(23) = zeros();
  T : bits(23) = zeros();
  let newBaseBits : bits(24) = mask(base >> e);
  let newTopBits  : bits(23) = mask(top >> e);

  incE = false;
  if (e0) then {
    /* e0 case */
    Bs = newBaseBits[22..0];
    T = newTopBits[22..0];
  } else {
    // embedded exp cases
    // Mask of all significant bits of length (msb and below)
    // NB this differs from smearMSBRight used in bsv when e == 0 but don't think this matters
    let lmask    : bits(66) = zero_extend(replicate_bits(0b1, e + 22));
    // mask which when combined with lmask will give just 18 bits of length (note ~)
    // strangely this ignores 2 bits of length mantissa. why?
    let lmaskLo2 : bits(66) = ~(zero_extend(replicate_bits(0b1, e + 5)));
    let lengthMax = (length & lmaskLo2) == (lmask & lmaskLo2);
    if not (lengthMax) then {
      Bs = newBaseBits[22..3] @ 0b000;
      // If top has significant bits we are going to lose then we must round up T by one
      // Mask of bits of base / top that we will lose for e != 0 (including 3 for exp).
      lmaskLo : bits(66) = zero_extend(replicate_bits(0b1, e + 3));
      lostSignificantTop = ((top66 & lmaskLo) != zeros());
      // We don't actually use this because we do exact bounds check at end
      // lostSignificantBase = ((base66 & lmaskLo) != zeros()) & not(e0);
      if (lostSignificantTop) then {
        // shift by MW - 2 - 3 (HalfExp) putting MSB just above (e + 3)
        roundedLength = length + (length >> 18);
        // TODO are bottom e + 3 bits of roundedLength important here?
        newTopBitsRounded : bits(20) = mask((base66 + roundedLength) >> (e + 3));
        T = newTopBitsRounded @ 0b000;
      } else {
        T = newTopBits[22..3] @ 0b000;
      }
    } else {
      // rounding means we have to increase e by one
      // may not be strictly necessary if we have not lost significant bits...
      incE = true;
      Bs = newBaseBits[23..4] @ 0b000;
      roundedLength2 = length + (length >> 16);
      newTopBitsRoundedHigher : bits(20) = mask((base66 + roundedLength2) >> (e + 4));
      T = newTopBitsRoundedHigher @ 0b000;
    }
  };
  let newCap  = {cap with address=base, E=to_bits(6, if incE then e + 1 else e ), B=Bs, T=T, lenMSB=lenMSB, internal_e=not(e0)};
  let (newBase, newTop) = getCapBounds(newCap);
  let exact   = (unsigned(base) == newBase) & (unsigned(top) == newTop);
  (exact, newCap)
}
*/
