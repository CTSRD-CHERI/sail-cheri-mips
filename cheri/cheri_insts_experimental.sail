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

/*
 * These instructions are currently considered experimental to some degree
 * or another.  At the very least, they appear in the experimetnal appendix
 * of the CHERI ISA document and are sorted here by their corresponding
 * section therein.
 *
 * They live in this file, separate from the main cheri_insts.sail, to
 * facilitate down-stream users of the core CHERI-MIPS specification.  We
 * may propose things that change aspects of the CHERI security proofs, for
 * example, and do not wish to disrupt the work of proving properties of
 * CHERI per se.
 */

/* Capability Flags (D.1) <<< */

union clause ast = CGetFlags : (regno, regno)
function clause execute (CGetFlags(rd, cb)) =
{
  checkCP2usable();
  let capVal = readCapReg(cb);
  wGPR(rd) = zero_extend(getCapFlags(capVal));
}

union clause ast = CSetFlags : (regno, regno, regno)
function clause execute(CSetFlags(cd, cb, rt)) = 
{
  checkCP2usable();
  let cb_val = readCapReg(cb);
  let rt_val = rGPR(rt);
  if cb_val.tag & cb_val.sealed then
    raise_c2_exception(CapEx_SealViolation, cb)
  else
  {
    let newCap  = setCapFlags(cb_val, truncate(rt_val, num_flags));
    writeCapReg(cd, newCap);
  }
}

function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ rt : regno @ 0b001110) = Some(CSetFlags(cd, cs, rt))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @    0b10010 @ 0b111111) = Some(CGetFlags(rd, cb))

/* >>> */
/* CRAM and CRAP (D.2) <<< */

union clause ast = CRAP : (regno, regno)
function clause execute(CRAP(rt, rs)) =
{
  checkCP2usable();
  let len = rGPR(rs);
  wGPR(rt) = getRepresentableLength(len);
}

union clause ast = CRAM : (regno, regno)
function clause execute(CRAM(rt, rs)) =
{
  checkCP2usable();
  let len = rGPR(rs);
  wGPR(rt) = getRepresentableAlignmentMask(len);
}

function clause decode (0b010010 @ 0b00000 @ rt : regno @ rs : regno @   0b10000 @ 0b111111) = Some(CRAP(rt, rs))
function clause decode (0b010010 @ 0b00000 @ rt : regno @ rs : regno @   0b10001 @ 0b111111) = Some(CRAM(rt, rs))

/* >>> */
/* Fast Capability Subset Testing (D.3) <<< */

union clause ast = CTestSubset : (regno, regno, regno)
function clause execute (CTestSubset(rd, cb, ct)) =
{
  checkCP2usable();
  let cb_val = readCapRegDDC(cb);
  let ct_val = readCapReg(ct);
  let ct_top   = getCapTop(ct_val);
  let ct_base  = getCapBase(ct_val);
  let ct_perms = getCapPerms(ct_val);
  let cb_top   = getCapTop(cb_val);
  let cb_base  = getCapBase(cb_val);
  let cb_perms = getCapPerms(cb_val);
  let result = if cb_val.tag != ct_val.tag then
                0b0
           else if ct_base < cb_base then
                0b0
           else if ct_top > cb_top then
                0b0
           else if (ct_perms & cb_perms) != ct_perms then
                0b0
           else
                0b1;
  wGPR(rd) = zero_extend(result);
}

function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ ct : regno @ 0b100000) = Some(CTestSubset(rd, cb, ct))

/* >>> */
/* CLoadTags (D.4) <<< */

union clause ast = CLoadTags : (regno, regno)
function clause execute (CLoadTags(rd, cb)) =
{
  checkCP2usable();
  let cb_val = readCapRegDDC(cb);
  if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if cb_val.sealed then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if not (cb_val.permit_load) then
    raise_c2_exception(CapEx_PermitLoadViolation, cb)
  else if not (cb_val.permit_load_cap) then
    raise_c2_exception(CapEx_PermitLoadCapViolation, cb)
  else
  {
    let vAddr   = getCapCursor(cb_val);
    let vAddr64 = to_bits(64, getCapCursor(cb_val));
    if (vAddr + caps_per_cacheline * cap_size) > getCapTop(cb_val) then
      raise_c2_exception(CapEx_LengthViolation, cb)
    else if vAddr < getCapBase(cb_val) then
      raise_c2_exception(CapEx_LengthViolation, cb)
    else if not(vAddr % (cap_size * caps_per_cacheline) == 0) then
      SignalExceptionBadAddr(AdEL, vAddr64)
    else
      {
        x : bits(64)  = zeros();
        foreach(i from 0 to (caps_per_cacheline - 1)) {
          let pAddr    = TLBTranslate(vAddr64 + i*cap_size, LoadData);
          let (tag, _) = MEMr_tagged(pAddr, cap_size, true);
          x[i] = tag;
        };
        wGPR(rd) = x;
      }
  }
}

function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @    0b11110 @ 0b111111) = Some(CLoadTags(rd, cb))

/* >>> */
/* Capability Reconstruction (D.5) <<< */

union clause ast = CBuildCap : (regno, regno, regno)
function clause execute (CBuildCap(cd, cb, ct)) =
{
  checkCP2usable();
  let cb_val = readCapRegDDC(cb);
  let ct_val = readCapReg(ct);
  let cb_base = getCapBase(cb_val);
  let ct_base = getCapBase(ct_val);
  let cb_top = getCapTop(cb_val);
  let ct_top = getCapTop(ct_val);
  let cb_perms = getCapPerms(cb_val);
  let ct_perms = getCapPerms(ct_val);
  let ct_offset = getCapOffset(ct_val);
  if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if cb_val.sealed then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if ct_base < cb_base then
    raise_c2_exception(CapEx_LengthViolation, cb)
  else if ct_top > cb_top then
    raise_c2_exception(CapEx_LengthViolation, cb)
   else if ct_base > ct_top then /* check for length < 0 - possible because ct might be untagged */
    raise_c2_exception(CapEx_LengthViolation, ct)
   else if (ct_perms & cb_perms) != ct_perms then
    raise_c2_exception(CapEx_UserDefViolation, cb)
  else
  {
    let (exact, cd1) = setCapBounds(cb_val, to_bits(64, ct_base), to_bits(65, ct_top));
    let (representable, cd2) = setCapOffset(cd1, to_bits(64, ct_offset));
    let cd3 = setCapPerms(cd2, ct_perms);
    {
      assert(exact, "CBuildCap: setCapBounds was not exact"); /* base and top came from ct originally so will be exact */
      assert(representable, "CBuildCap: offset was not representable"); /* similarly offset should be representable XXX except for fastRepCheck */
      writeCapReg(cd, cd3);
    }
  }
}

union clause ast = CCopyType : (regno, regno, regno)
function clause execute (CCopyType(cd, cb, ct)) =
{
  checkCP2usable();
  let cb_val = readCapReg(cb);
  let ct_val = readCapReg(ct);
  let cb_base = getCapBase(cb_val);
  let cb_top  = getCapTop(cb_val);
  let ct_otype = unsigned(ct_val.otype);
  if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if cb_val.sealed then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if ct_val.sealed then
  {
    if ct_otype < cb_base then
      raise_c2_exception(CapEx_LengthViolation, cb)
    else if ct_otype >= cb_top then
      raise_c2_exception(CapEx_LengthViolation, cb)
    else
    {
      let (success, cap) = setCapOffset(cb_val, to_bits(64, ct_otype - cb_base));
      assert(success, "CopyType: offset is in bounds so should be representable");
      writeCapReg(cd, cap);
    }
  }
  else
    writeCapReg(cd, {null_cap with address=ones()})
}

union clause ast = CCSeal : (regno, regno, regno)
function clause execute (CCSeal(cd, cs, ct)) =
{
  checkCP2usable();
  let cs_val = readCapReg(cs);
  let ct_val = readCapReg(ct);
  let ct_cursor = getCapCursor(ct_val);
  let ct_top    = getCapTop(ct_val);
  let ct_base   = getCapBase(ct_val);
  if not (cs_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cs)
  else if not (ct_val.tag) | (getCapCursor(ct_val) == MAX_U64) then
    writeCapReg(cd, cs_val)
  else if cs_val.sealed then
    raise_c2_exception(CapEx_SealViolation, cs)
  else if ct_val.sealed then
    raise_c2_exception(CapEx_SealViolation, ct)
  else if not (ct_val.permit_seal) then
    raise_c2_exception(CapEx_PermitSealViolation, ct)
  else if ct_cursor < ct_base then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else if ct_cursor >= ct_top then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else if ct_cursor > max_otype then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else
  {
    let (success, newCap) = sealCap(cs_val, to_bits(24, ct_cursor));
    if not (success) then
        raise_c2_exception(CapEx_InexactBounds, cs)
    else
        writeCapReg(cd, newCap)
  }
}

function clause decode (0b010010 @ 0b00000 @ cd : regno @ cb : regno @ ct : regno @ 0b011101) = Some(CBuildCap(cd, cb, ct))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cb : regno @ ct : regno @ 0b011110) = Some(CCopyType(cd, cb, ct))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ ct : regno @ 0b011111) = Some(CCSeal(cd, cs, ct))

/* >>> */
/* Assisting Revocation (D.6) <<< */

/* XXX: Missing NTCLC, CClearTags */

union clause ast = CCLC : (regno, regno)
function clause execute (CCLC(cd, cb)) =
{
  checkCP2usable();
  if (CP0LLBit[0]) then
  {
    let cb_val = readCapRegDDC(cb);

    if not (cb_val.tag) then
      raise_c2_exception(CapEx_TagViolation, cb)
    else if cb_val.sealed then
      raise_c2_exception(CapEx_SealViolation, cb)
    else if not (cb_val.permit_load) then
      raise_c2_exception(CapEx_PermitLoadViolation, cb)
    else
    {
      let vAddr   = getCapCursor(cb_val);
      let vAddr64 = to_bits(64, vAddr);
      if (vAddr + cap_size) > getCapTop(cb_val) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if vAddr < getCapBase(cb_val) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if (vAddr % cap_size) != 0 then
        SignalExceptionBadAddr(AdEL, vAddr64)
      else
      {
        let (pAddr, suppressTag) = TLBTranslateC(vAddr64, LoadData);
        let (tag, mem) : (bool, CapBits) =
          MEMr_tagged_reserve(pAddr, cap_size, cb_val.permit_load_cap & not(suppressTag));
        let cap = memBitsToCapability(tag, mem);
        writeCapReg(cd, cap);
      }
    }
  }
  else
    writeCapReg(cd, null_cap);
}

function clause decode (0b010010 @ 0b10000 @ cd : regno @ cb : regno@ 0b0000001 @ 0b1111) = Some(CCLC(cd, cb))

/* 

/* >>> */
/* TODO: Memory Versioning (D.10) <<< */

/* >>> */
/* TODO: Linear Capabilities (D.11) <<< */

/* >>> */
/* TODO: Indirect Capabilities (D.12) <<< */

/* >>> */
/* TODO: Sentries (D.13) <<< */

/* >>> */
/* TODO: Indirect Sentries (D.14) <<< */

/* >>> */
/* TODO: Capability Coloring (D.15) <<< */

/* >>> */
/* TODO: In-Memory Sealing Types (D.16) <<< */

/* >>> */
/* TODO: Short Capabilities (D.17) <<< */

/* >>> */
