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

/* 256 bit cap + tag */
type CapBits = bits(257)
let max_otype = MAX(24) /*0xffffff*/

struct CapStruct = {
  tag                     : bool    ,
  padding                 : bits(8) ,
  otype                   : bits(24),
  uperms                  : bits(16),
  perm_reserved11_14      : bits(4) ,
  access_system_regs      : bool    ,
  permit_unseal           : bool    ,
  permit_ccall            : bool    ,
  permit_seal             : bool    ,
  permit_store_local_cap  : bool    ,
  permit_store_cap        : bool    ,
  permit_load_cap         : bool    ,
  permit_store            : bool    ,
  permit_load             : bool    ,
  permit_execute          : bool    ,
  global                  : bool    ,
  sealed                  : bool    ,
  address                 : bits(64),
  base                    : bits(64),
  length                  : bits(64),
}

type CapReg = CapStruct

let null_cap : CapStruct = struct {
  tag = false,
  padding = zeros(),
  otype = zeros(),
  uperms = zeros(),
  perm_reserved11_14 = zeros(),
  access_system_regs = false,
  permit_unseal = false,
  permit_ccall = false,
  permit_seal = false,
  permit_store_local_cap = false,
  permit_store_cap = false,
  permit_load_cap = false,
  permit_store = false,
  permit_load = false,
  permit_execute = false,
  global = false,
  sealed = false,
  address = zeros(),
  base = zeros(),
  length = 0xffffffffffffffff
}

let default_cap : CapStruct = struct {
  tag = true,
  padding = zeros(),
  otype = zeros(),
  uperms = ones(),
  perm_reserved11_14 = zeros(),
  access_system_regs = true,
  permit_unseal = true,
  permit_ccall = true,
  permit_seal = true,
  permit_store_local_cap = true,
  permit_store_cap = true,
  permit_load_cap = true,
  permit_store = true,
  permit_load = true,
  permit_execute = true,
  global = true,
  sealed = false,
  address = zeros(),
  base = zeros(),
  length = 0xffffffffffffffff
}

let 'cap_size = 32

function capBitsToCapStruct(capBits) : CapBits -> CapStruct =
  struct {
    tag                        = capBits[256],
    padding                    = capBits[255..248],
    otype                      = capBits[247..224],
    uperms                     = capBits[223..208],
    perm_reserved11_14         = capBits[207..204],
    access_system_regs         = capBits[203],
    permit_unseal              = capBits[202],
    permit_ccall               = capBits[201],
    permit_seal                = capBits[200],
    permit_store_local_cap     = capBits[199],
    permit_store_cap           = capBits[198],
    permit_load_cap            = capBits[197],
    permit_store               = capBits[196],
    permit_load                = capBits[195],
    permit_execute             = capBits[194],
    global                     = capBits[193],
    sealed                     = capBits[192],
    address                    = capBits[191..128],
    base                       = capBits[127..64],
    length                     = capBits[63..0]
  }

/*!
gets the permissions of the capabilty as a 31-bit vector. The architecturally defined permissions are in bits 0-10 and user defined permissions are in bits 15 and above. Bits 11-14 are reserved: if they are present (CHERI 256) they act as extra user permissions but when using compressed capabilities they will be zero.
 */
val getCapPerms : CapStruct -> bits(31) 
function getCapPerms(cap) = 
  (
    cap.uperms
      @ cap.perm_reserved11_14
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
      @ cap.global
  )


/* Function to convert capabilities to in-memory format. */
function capStructToMemBits256(cap) : CapStruct -> bits(256) =
  (
        cap.padding
      @ cap.otype
      @ getCapPerms(cap)
      @ cap.sealed
      @ cap.address
      @ cap.base
      @ cap.length
  )


/* When saving/restoring capabilities xor them with bits of null_cap --
   this ensures that canonical null_cap is always all-zeros in memory
   even though it may have bits set logically (e.g. length or exponent) */

let null_cap_bits : bits(256) = capStructToMemBits256(null_cap)


/*!
THIS is the reverse of [memBitsToCapReg].
 */
val capStructToMemBits : CapStruct -> bits(256)
function capStructToMemBits(cap) =
  capStructToMemBits256(cap) ^ null_cap_bits

/*!
THIS converts from the in-memory capability format to a convenient structure for ease of field access. Note that the bit representation is xored with the bit representation of the null capability to ensure that null is always stored as all-zeros in memory.
 */
val memBitsToCapReg : (bool, bits(256)) -> CapReg
function memBitsToCapReg(tag, b) =
  capBitsToCapStruct(tag @ (b ^ null_cap_bits))

/*!
sets the permission of the capabiltiy as a 31-bit vector. Writes to reserved permissions are ignored when using compressed capabilities, although this behaviour is subject to change in future revisions.
 */
val setCapPerms : (CapStruct, bits(31)) -> CapStruct
function setCapPerms(cap, perms) =
    { cap with
      uperms                 = perms[30..15],
      /* perm_reserved11_14     = perms[14..11], XXX should allow to set? only affects cbuildcap. */
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

/*!
THIS(cap, otype) returns a new capability derived from `cap` but with the sealed bit set and otype set to `otype`. The returned boolean indicates whether the sealed capability is exactly representable (there may be additional restrictions on sealed capabilities depending on the compression used).
 */
val sealCap : (CapStruct, bits(24)) -> (bool, CapStruct)
function sealCap(cap, otype) =
    (true, {cap with sealed=true, otype=otype})

/*!
returns the base of the given capability as an integer in the range $0$ to $2^{64} - 1$.
 */
val getCapBase : CapStruct -> uint64
function getCapBase(c) = unsigned(c.base)

/*!
returns the top of the given capability as an integer in the range $0$ to $2^{65}$.
 */
val getCapTop : CapStruct -> CapLen
function getCapTop(c) = unsigned(c.base) + unsigned(c.length) /* XXX bug here? -- should be mod 2^64 */

/*!
returns the offset of the capability (i.e. address relative to base) as an integer in the range $0$ to $2^{64} - 1$ 
 */
val getCapOffset : CapStruct -> uint64
function getCapOffset(c) = (unsigned(c.address) - unsigned(c.base)) % (pow2(64))

/*!
returns the length of the given capability as an integer in the range $0$ to $2^{65}$.
 */
val getCapLength : CapStruct -> CapLen
function getCapLength(c) = unsigned(c.length)

/*!
returns the address of the capability as an integer in the range $0$ to $2^{64} - 1$.
 */
val getCapCursor : CapStruct -> uint64
function getCapCursor(c) = unsigned(c.address)

/*!
THIS(cap, off) returns a new capability derived from `cap` with the offset set to `off` (i.e. with $\mathit{address} = \mathit{cap.base} + \mathit{off}$). If the operation fails due to representability checks then the result will have the expected address but the bounds may be incorrect. Note that, for performance reasons, an approximate representability check may be used that means the operation could fail even though the result would be representable.
 */
val setCapOffset : (CapStruct, bits(64)) -> (bool, CapStruct)
function setCapOffset(c, offset) =
    (true, {c with address=c.base + offset})

/*!
THIS is the same as [setCapOffset] except that the 64-bit value is added to the current capability offset modulo $2^{64}$ (i.e. signed twos-complement arithemtic).
 */
val incCapOffset : (CapStruct, bits(64)) -> (bool, CapStruct)
function incCapOffset(c, delta) =
    let newAddr : bits(64) = c.address + delta in
    (true, {c with address = newAddr})

/*!
THIS`(cap, base, top)` returns a new capabiltiy value derived from cap
with given base and top and the address set to `base`. The returned
boolean value indicates whether the requested bounds were exactly
representable. When capability compression is in use the base and top
of the returned capabiltiy may cover a larger region than requested in
order to comply with alignment requirements, however the bounds will
never exceed the bounds of the original capabiltiy and the address
will still point to the requested base.
 */
val setCapBounds : (CapStruct, bits(64), bits(65)) -> (bool, CapStruct)
function setCapBounds(cap, base, top) =
    let length : bits(65) = top - (0b0 @ base) in
    (true, {cap with base = base, length = length[63..0], address = base})




/*!
creates a capability with the given 64-bit vector in its offset field. The resulting capability is untagged and has base zero but the other fields are undefined and may vary, depending on the capabilty compression format, to ensure that any offset can be represented.
*/
val int_to_cap : bits(64) -> CapStruct 
function int_to_cap (address) = 
    {null_cap with address = address}
