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

/* mips_prelude.sail: declarations of mips registers, and functions common
   to mips instructions (e.g. address translation) */

register PC : bits(64)
register NextPC : bits(64)

/* CP0 Registers */

bitfield CauseReg : bits(32) = {
  BD : 31, /* branch delay */
  /*Z0 : 30,*/
  CE : 29.. 28, /* for coprocessor enable exception */
  /*Z1 : 27.. 24,*/
  IV : 23, /* special interrupt vector not supported */
  WP : 22, /* watchpoint exception occurred */
  /*Z2 : 21.. 16, */
  IP : 15.. 8, /* interrupt pending bits */
  /*Z3 : 7,*/
  ExcCode : 6.. 2, /* code of last exception */
  /*Z4 : 1.. 0,*/
}

bitfield TLBEntryLoReg : bits(64) = {
  CapS : 63, /* CHERI: Capability Store Inhibit */
  CapL : 62, /* CHERI: Capability Load Inhibit */
  CapLG : 61, /* CHERI: Capability Load Generation */
  PFN : 29.. 6,
  C : 5.. 3,
  D : 2,
  V : 1,
  G : 0,
}

bitfield TLBEntryHiReg : bits(64) = {
  R : 63.. 62,
  CLGK : 61, /* CHERI: Capability Load Generation for Kernel pages */
  CLGS : 60, /* ... Supervisor pages */
  CLGU : 59, /* ... User pages */
  VPN2 : 39.. 13,
  ASID : 7..  0,
}

bitfield ContextReg : bits(64) = {
  PTEBase : 63.. 23,
  BadVPN2 : 22.. 4,
  /*ZR : 3.. 0,*/
}

bitfield XContextReg : bits(64) = {
  XPTEBase : 63.. 33,
  XR : 32.. 31,
  XBadVPN2 : 30..  4,
}

let TLBNumEntries = 64
type TLBIndexT = (bits(6))
let TLBIndexMax : TLBIndexT = 0b111111

val MAX : forall 'n, 'n >= 0 . atom('n) -> atom(2 ^ 'n - 1) effect pure
function MAX(n) = pow2(n) - 1

let MAX_U64 = MAX(64) /*unsigned(0xffffffffffffffff)*/
let MAX_VA  = MAX(40) /*unsigned(0xffffffffff)*/
let MAX_PA  = MAX(36) /*unsigned(0xfffffffff)*/

bitfield TLBEntry : bits(119) = {
  pagemask : 118..  103,
  r        : 102..  101,
  vpn2     : 100..  74,
  asid     : 73..  66,
  g        : 65,
  valid    : 64,
  caplg1   : 63,
  caps1    : 62,
  capl1    : 61,
  pfn1     : 60..  37,
  c1       : 36..  34,
  d1       : 33,
  v1       : 32,
  caplg0   : 31,
  caps0    : 30,
  capl0    : 29,
  pfn0     : 28..  5,
  c0       : 4..  2,
  d0       : 1,
  v0       : 0,
}

register TLBProbe : bits(1)
register TLBIndex : TLBIndexT
register TLBRandom : TLBIndexT
register TLBEntryLo0 : TLBEntryLoReg
register TLBEntryLo1 : TLBEntryLoReg
register TLBContext : ContextReg
register TLBPageMask : bits(16)
register TLBWired : TLBIndexT
register TLBEntryHi : TLBEntryHiReg
register TLBXContext : XContextReg

register TLBEntry00 : TLBEntry
register TLBEntry01 : TLBEntry
register TLBEntry02 : TLBEntry
register TLBEntry03 : TLBEntry
register TLBEntry04 : TLBEntry
register TLBEntry05 : TLBEntry
register TLBEntry06 : TLBEntry
register TLBEntry07 : TLBEntry
register TLBEntry08 : TLBEntry
register TLBEntry09 : TLBEntry
register TLBEntry10 : TLBEntry
register TLBEntry11 : TLBEntry
register TLBEntry12 : TLBEntry
register TLBEntry13 : TLBEntry
register TLBEntry14 : TLBEntry
register TLBEntry15 : TLBEntry
register TLBEntry16 : TLBEntry
register TLBEntry17 : TLBEntry
register TLBEntry18 : TLBEntry
register TLBEntry19 : TLBEntry
register TLBEntry20 : TLBEntry
register TLBEntry21 : TLBEntry
register TLBEntry22 : TLBEntry
register TLBEntry23 : TLBEntry
register TLBEntry24 : TLBEntry
register TLBEntry25 : TLBEntry
register TLBEntry26 : TLBEntry
register TLBEntry27 : TLBEntry
register TLBEntry28 : TLBEntry
register TLBEntry29 : TLBEntry
register TLBEntry30 : TLBEntry
register TLBEntry31 : TLBEntry
register TLBEntry32 : TLBEntry
register TLBEntry33 : TLBEntry
register TLBEntry34 : TLBEntry
register TLBEntry35 : TLBEntry
register TLBEntry36 : TLBEntry
register TLBEntry37 : TLBEntry
register TLBEntry38 : TLBEntry
register TLBEntry39 : TLBEntry
register TLBEntry40 : TLBEntry
register TLBEntry41 : TLBEntry
register TLBEntry42 : TLBEntry
register TLBEntry43 : TLBEntry
register TLBEntry44 : TLBEntry
register TLBEntry45 : TLBEntry
register TLBEntry46 : TLBEntry
register TLBEntry47 : TLBEntry
register TLBEntry48 : TLBEntry
register TLBEntry49 : TLBEntry
register TLBEntry50 : TLBEntry
register TLBEntry51 : TLBEntry
register TLBEntry52 : TLBEntry
register TLBEntry53 : TLBEntry
register TLBEntry54 : TLBEntry
register TLBEntry55 : TLBEntry
register TLBEntry56 : TLBEntry
register TLBEntry57 : TLBEntry
register TLBEntry58 : TLBEntry
register TLBEntry59 : TLBEntry
register TLBEntry60 : TLBEntry
register TLBEntry61 : TLBEntry
register TLBEntry62 : TLBEntry
register TLBEntry63 : TLBEntry

let TLBEntries : vector(64, dec, register(TLBEntry)) = [
    ref TLBEntry63,
    ref TLBEntry62,
    ref TLBEntry61,
    ref TLBEntry60,
    ref TLBEntry59,
    ref TLBEntry58,
    ref TLBEntry57,
    ref TLBEntry56,
    ref TLBEntry55,
    ref TLBEntry54,
    ref TLBEntry53,
    ref TLBEntry52,
    ref TLBEntry51,
    ref TLBEntry50,
    ref TLBEntry49,
    ref TLBEntry48,
    ref TLBEntry47,
    ref TLBEntry46,
    ref TLBEntry45,
    ref TLBEntry44,
    ref TLBEntry43,
    ref TLBEntry42,
    ref TLBEntry41,
    ref TLBEntry40,
    ref TLBEntry39,
    ref TLBEntry38,
    ref TLBEntry37,
    ref TLBEntry36,
    ref TLBEntry35,
    ref TLBEntry34,
    ref TLBEntry33,
    ref TLBEntry32,
    ref TLBEntry31,
    ref TLBEntry30,
    ref TLBEntry29,
    ref TLBEntry28,
    ref TLBEntry27,
    ref TLBEntry26,
    ref TLBEntry25,
    ref TLBEntry24,
    ref TLBEntry23,
    ref TLBEntry22,
    ref TLBEntry21,
    ref TLBEntry20,
    ref TLBEntry19,
    ref TLBEntry18,
    ref TLBEntry17,
    ref TLBEntry16,
    ref TLBEntry15,
    ref TLBEntry14,
    ref TLBEntry13,
    ref TLBEntry12,
    ref TLBEntry11,
    ref TLBEntry10,
    ref TLBEntry09,
    ref TLBEntry08,
    ref TLBEntry07,
    ref TLBEntry06,
    ref TLBEntry05,
    ref TLBEntry04,
    ref TLBEntry03,
    ref TLBEntry02,
    ref TLBEntry01,
    ref TLBEntry00
]

register CP0Compare : bits(32)
register CP0Cause : CauseReg
/* CP0EPC is accessed via getter/setters for CHERI extensibility */
val get_CP0EPC : unit -> bits(64) effect {rreg}
val set_CP0EPC : bits(64) -> unit effect {rreg, wreg}
/* similarly for ErrorEPC  */
val get_CP0ErrorEPC : unit -> bits(64) effect {rreg}
val set_CP0ErrorEPC : bits(64) -> unit effect {rreg, wreg}
register CP0LLBit : bits(1)
register CP0LLAddr : bits(64)
register CP0BadVAddr : bits(64)
/* XXXAR: The following two registers are a hack to implement in BadInstr/BadInstrP */
register CurrentInstrBits : bits(32)
register LastInstrBits : bits(32)
register CP0BadInstr : bits(32)
register CP0BadInstrP : bits(32)
register CP0Count : bits(32)
register CP0HWREna : bits(32)
register CP0UserLocal : bits(64)
register CP0ConfigK0 : bits(3)

bitfield StatusReg : bits(32) = {
  CU : 31.. 28,  /* co-processor enable bits */
  /* RP/FR/RE/MX/PX not implemented */
  BEV : 22, /* use boot exception vectors (initialised to one) */
  /* TS/SR/NMI not implemented */
  IM : 15.. 8,  /* Interrupt mask */
  KX : 7,  /* kernel 64-bit enable */
  SX : 6,  /* supervisor 64-bit enable */
  UX : 5,  /* user 64-bit enable */
  KSU : 4.. 3, /* Processor mode */
  ERL : 2, /* error level (should be initialised to one, but BERI is different) */
  EXL : 1, /* exception level */
  IE : 0,  /* interrupt enable */
}
register CP0Status : StatusReg

/* Implementation registers -- not ISA defined */
register NextInBranchDelay : bits(1)  /* Set by branch instructions to indicate that next instruction is branch delay slot (even if branch not-taken) */
register InBranchDelay : bits(1)      /* Set by main loop when in branch delay slot */
register BranchPending : bits(1)      /* Set by branch instructions when branch taken so know to branch to DelayedPC after branch delay slot */
register DelayedPC : bits(64)         /* Set by branch instructions to target of branch */

/*!
THIS checks the given offset against the bounds of PCC and raises a capability length exception if it is out of bounds, otherwise a branch occurs in the normal manner for the architecture (on MIPS this implies a branch delay slot, so `NextInBranchDelay` is set to true).
 */
val execute_branch : bits(64) -> unit effect {rreg, wreg, escape}
val execute_branch_mips : bits(64) -> unit effect {wreg}
function execute_branch_mips(pc) = {
  DelayedPC = pc;
  BranchPending = 0b1;
  NextInBranchDelay = 0b1;
}

/* General purpose registers */


/* Special registers For MUL/DIV */
register HI : bits(64)
register LO : bits(64)

register GPR : vector(32, dec, bits(64))

/* JTAG Uart registers */

register UART_WDATA : bits(8)
register UART_WRITTEN : bits(1)
register UART_RDATA : bits(8)
register UART_RVALID : bits(1)

/* Check whether a given 64-bit vector is a properly sign extended 32-bit word */
val NotWordVal : bits(64) -> bool effect pure
function NotWordVal (word) =
    (word[31] ^^ 32) != word[63..32]

/*!
Reads the value of the given general purpose register as a 64-bit vector. Register zero is always zero.
*/
val rGPR : bits(5) -> bits(64) effect {rreg}
function rGPR idx = {
         let i as atom(_) = unsigned(idx) in
         if i == 0 then 0x0000000000000000 else GPR[i]
}

/*!
THIS(rd, v) writes the 64-bit value, _v_, to the general purpose register _rd_. Writes to register zero are ignored.
*/
val wGPR : (bits(5), bits(64)) -> unit effect {wreg}
function wGPR (idx, v) = {
  let i as atom(_) = unsigned(idx) in
  if i != 0 then {
    if trace then {
      prerr(string_of_int(i));
      prerr_bits(" <- ", v);
    };
    GPR[i] = v;
  };
}

val MEMr = {lem: "MEMr", coq: "MEMr"} : forall 'n, 'n >= 0.
  ( bits(64) , atom('n) ) -> (bits(8 * 'n)) effect { rmem }
val MEMr_reserve = {lem: "MEMr_reserve", coq: "MEMr_reserve"} : forall 'n, 'n >= 0.
  ( bits(64) , atom('n) ) -> (bits(8 * 'n)) effect { rmem }
val MEM_sync = {lem: "MEM_sync", coq: "MEM_sync"} :
  unit -> unit effect { barr }

val MEMea = {lem: "MEMea", coq: "MEMea"} : forall 'n.
  ( bits(64) , atom('n)) -> unit effect { eamem }
val MEMea_conditional = {lem: "MEMea_conditional", coq: "MEMea_conditional"} : forall 'n.
  ( bits(64) , atom('n)) -> unit effect { eamem }
val MEMval = {lem: "MEMval", coq: "MEMval"} : forall 'n.
  ( bits(64) , atom('n), bits(8*'n)) -> unit effect { wmv }
val MEMval_conditional = {lem: "MEMval_conditional", coq: "MEMval_conditional"} : forall 'n.
  ( bits(64) , atom('n), bits(8*'n)) -> bool effect { wmv }

/* Extern nops with effects, sometimes useful for faking effect */
val skip_eamem = "skip" : unit -> unit effect {eamem}
val skip_barr = "skip" : unit -> unit effect {barr}
val skip_wreg = "skip" : unit -> unit effect {wreg}
val skip_rreg = "skip" : unit -> unit effect {rreg}
val skip_wmvt = "skip" : unit -> unit effect {wmvt}
val skip_rmemt = "skip" : unit -> unit effect {rmemt}
val skip_escape = "skip" : unit -> unit effect {escape}

function MEMr (addr, size) = __MIPS_read(addr, size)
function MEMr_reserve (addr, size) = __MIPS_read(addr, size)
function MEM_sync () = skip_barr()

function MEMea (addr, size) = skip_eamem()
function MEMea_conditional (addr, size) = skip_eamem()
function MEMval (addr, size, data) = __MIPS_write(addr, size, data)
function MEMval_conditional (addr, size, data) = { __MIPS_write(addr, size, data); true }

enum Exception =
{
   Interrupt, TLBMod, TLBL, TLBS, AdEL, AdES, Sys, Bp, ResI, CpU, Ov, Tr, C2E, C2Trap,
   XTLBRefillL, XTLBRefillS, XTLBInvL, XTLBInvS, MCheck
}

/* Return the ISA defined code for an exception condition */
function ExceptionCode (ex) : Exception -> bits(5)=
   let x : bits(8) = match ex
   {
      Interrupt    => 0x00, /* Interrupt */
      TLBMod       => 0x01, /* TLB modification exception */
      TLBL         => 0x02, /* TLB exception (load or fetch) */
      TLBS         => 0x03, /* TLB exception (store) */
      AdEL         => 0x04, /* Address error (load or fetch) */
      AdES         => 0x05, /* Address error (store) */
      Sys          => 0x08, /* Syscall */
      Bp           => 0x09, /* Breakpoint */
      ResI         => 0x0a, /* Reserved instruction */
      CpU          => 0x0b, /* Coprocessor Unusable */
      Ov           => 0x0c, /* Arithmetic overflow */
      Tr           => 0x0d, /* Trap */
      C2E          => 0x12, /* C2E coprocessor 2 exception */
      C2Trap       => 0x12, /* C2Trap maps to same exception code, different vector */
      XTLBRefillL  => 0x02,
      XTLBRefillS  => 0x03,
      XTLBInvL     => 0x02,
      XTLBInvS     => 0x03,
      MCheck       => 0x18
   } in x[4..0]

function string_of_exception(ex) : Exception -> string =
   match ex {
      Interrupt    => "Interrupt",
      TLBMod       => "TLBMod",
      TLBL         => "TLBL",
      TLBS         => "TLBS",
      AdEL         => "AdEL",
      AdES         => "AdES",
      Sys          => "Sys",
      Bp           => "Bp  ",
      ResI         => "ResI",
      CpU          => "CpU",
      Ov           => "Ov",
      Tr           => "Tr",
      C2E          => "C2E",
      C2Trap       => "C2Trap",
      XTLBRefillL  => "XTLBRefillL",
      XTLBRefillS  => "XTLBRefillS",
      XTLBInvL     => "XTLBInvL",
      XTLBInvS     => "XTLBInvS",
      MCheck       => "MCheck"
   }

val traceException : Exception -> unit
function traceException (ex : Exception) = {
  if trace then {
    prerr(" EXCEPTION ");
    prerr_endline(string_of_exception(ex));
  };
}
/*!
Choose an exception vector offset based on current state of processor
and exception type. Some are not supported e.g. Reset.
*/
val exceptionVectorOffset : Exception -> bits(12) effect {rreg}
function exceptionVectorOffset (ex) =
  if (CP0Status.EXL()) then
    0x180 /* Always use common vector if in exception mode already */
  else if ((ex == XTLBRefillL) | (ex == XTLBRefillS)) then
    0x080
  else if (ex == C2Trap) then
    0x280 /* Special vector for CHERI traps */
  else
    0x180 /* Common vector */

/*!
Choose appropariate exception vector base for current processor state.
 */
val exceptionVectorBase : unit -> bits(64) effect {rreg}
function exceptionVectorBase () =
  if CP0Status.BEV() then
   0xFFFFFFFFBFC00200
  else
   0xFFFFFFFF80000000

/*!
Update CP0BadInstr and CP0BadInstrP for exception.
 */
val updateBadInstr : unit -> unit effect{rreg, wreg}
function updateBadInstr () = {
  if (InBranchDelay[0]) then {
    CP0BadInstrP = LastInstrBits; /* PC - 4 */
  };
  CP0BadInstr = CurrentInstrBits; /* PC */
}

/*
 Defined either in mips_wrappers (directly calling SignalExceptionMIPS) or in cheri_prelude_common (cheri things plus above)
*/
/*!
Causes the processor to raise the given exception in the usual manner defined by the processor architecture (as modified for CHERI).
*/
val SignalException : forall ('o : Type) . Exception -> 'o effect {escape, rreg, wreg}
/*!
causes the processor to raise the given exception as per [SignalException], but with an associated bad address (on MIPS this is written to the BadVAddr register to aid with exception handling).
 */
val SignalExceptionBadAddr : forall ('o : Type) . (Exception, bits(64)) -> 'o effect {escape, rreg, wreg}
function  SignalExceptionBadAddr(ex, badAddr) =
  {
    CP0BadVAddr = badAddr;
    SignalException(ex);
  }

val SignalExceptionTLB : forall ('o : Type) . (Exception, bits(64)) -> 'o effect {escape, rreg, wreg}
function SignalExceptionTLB(ex, badAddr) = {
  CP0BadVAddr = badAddr;
  TLBContext->BadVPN2()  = (badAddr[31..13]);
  TLBXContext->XBadVPN2()= (badAddr[39..13]);
  TLBXContext->XR()      = (badAddr[63..62]);
  TLBEntryHi->R()        = (badAddr[63..62]);
  TLBEntryHi->VPN2()     = (badAddr[39..13]);
  SignalException(ex);
}

enum MemAccessType = {Instruction, LoadData, StoreData}

enum MemAccessCapRestriction = { Unrestricted, Trap, Clear }

enum AccessLevel = {User, Supervisor, Kernel}

val int_of_AccessLevel : AccessLevel -> {|0, 1, 2|} effect pure
function int_of_AccessLevel level =
  match level {
    User        => 0,
    Supervisor  => 1,
    Kernel      => 2
  }

/*!
Returns whether the first AccessLevel is sufficient to grant access at the second, required, access level.
 */
val grantsAccess : (AccessLevel, AccessLevel) -> bool
function grantsAccess (currentLevel, requiredLevel) =
  int_of_AccessLevel(currentLevel) >= int_of_AccessLevel(requiredLevel)

/*!
Returns the current effective access level (User, Supervisor or Kernel) determined by accessing the relevant parts of the MIPS status register.
 */
val getAccessLevel : unit -> AccessLevel effect {rreg}
function getAccessLevel() =
  if ((CP0Status.EXL()) | (CP0Status.ERL())) then
    Kernel
  else match CP0Status.KSU()
    {
      0b00  => Kernel,
      0b01  => Supervisor,
      0b10  => User,
      _     => User /* behaviour undefined, assume user */
    }

val checkCP0AccessHook : unit->unit effect{escape, rreg, wreg}
val checkCP0Access : unit->unit effect{escape, rreg, wreg}
function checkCP0Access () =
  {
    let accessLevel = getAccessLevel() in
    if ((accessLevel != Kernel) & (~(CP0Status.CU()[0]))) then
      {
        CP0Cause->CE() = 0b00;
        SignalException(CpU);
      };
    checkCP0AccessHook();
  }

val incrementCP0Count : unit -> unit effect {rreg,wreg,escape}
function incrementCP0Count() = {
  TLBRandom = (if (TLBRandom == TLBWired)
    then (TLBIndexMax) else (TLBRandom - 1));

  CP0Count = (CP0Count + 1);
  if (CP0Count == CP0Compare) then {
    CP0Cause->IP() = CP0Cause.IP() | 0x80; /* IP7 is timer interrupt  */
  };

  let ims = CP0Status.IM() in
  let ips = CP0Cause.IP() in
  let ie  = CP0Status.IE() in
  let exl = CP0Status.EXL() in
  let erl = CP0Status.ERL() in
  if ((~(exl)) & (~(erl)) & ie & ((ips & ims) != 0x00)) then
    SignalException(Interrupt);
}

type regno = bits(5)                      /* a register number */
type IntRegEnc = bits(5)                  /* a register number */
type imm16 = bits(16)                     /* 16-bit immediate */

function strReg(r) : regno -> string = concat_str_dec("$", unsigned(r))
function strRRRArgs(r2 : regno, r1 : regno, rd : regno) -> string = strReg(rd) ^ ", " ^ strReg(r1) ^ ", " ^ strReg(r2)
val strRRIArgs : forall 'n, 'n > 0 . (regno, regno, bits('n)) -> string
function strRRIArgs(rs, rd, imm) = strReg(rd) ^ ", " ^ strReg(rs) ^ ", " ^ dec_str(signed(imm))
val strRRIUArgs : forall 'n, 'n > 0 . (regno, regno, bits('n)) -> string
function strRRIUArgs(rs, rd, imm) = strReg(rd) ^ ", " ^ strReg(rs) ^ ", " ^ hex_str(unsigned(imm))
val strRIArgs : forall 'n, 'n > 0 . (regno, bits('n)) -> string
function strRIArgs(rd, imm) = strReg(rd) ^ ", " ^ hex_str(unsigned(imm))
val strMemArgs : forall 'n, 'n > 0 . (regno, regno, bits('n)) -> string
function strMemArgs(base, rt, offset) = strReg(rt) ^ ", " ^ dec_str(signed(offset)) ^ "(" ^ strReg(base) ^ ")"
enum decode_failure = {
  no_matching_pattern,
  unsupported_instruction,
  illegal_instruction,
  internal_error
}

/* Used by branch and trap instructions */
enum Comparison = {
  EQ, /* equal */
  NE, /* not equal */
  GE, /* signed greater than or equal */
  GEU,/* unsigned greater than or equal */
  GT, /* signed strictly greater than */
  LE, /* signed less than or equal */
  LT, /* signed strictly less than */
  LTU /* unsigned less than or qual */
}

function strCmp (cmp : Comparison) -> string = match cmp {
  EQ  => "eq",
  NE  => "ne",
  GE  => "ge",
  GEU => "geu",
  GT  => "gt",
  LE  => "le",
  LT  => "lt",
  LTU => "ltu"
}

val compare : (Comparison, bits(64), bits(64)) -> bool
function compare (cmp, valA, valB) =
  match cmp {
    EQ   => valA ==   valB,
    NE   => valA !=   valB,
    GE   => valA >=_s valB,
    GEU  => valA >=_u valB,
    GT   => valB <_s  valA,
    LE   => valB >=_s valA,
    LT   => valA <_s  valB,
    LTU  => valA <_u  valB
  }
enum WordType = { B, H, W, D}
enum WordTypeUnaligned = { WL, WR, DL, DR }

function strWordType(w : WordType) -> string = match w {
  B => "b",
  H => "h",
  W => "w",
  D => "d"
}

/* Compute the address and number of bytes touched by an unaligned memory operation.
   Assumes big-endian mode. */
function unalignedBytesTouched(vAddr : int, width : WordTypeUnaligned) -> (int, int) = {
  woffset = vAddr % 4;
  doffset = vAddr % 8;
  match width {
    WL => (vAddr, 4 - woffset),
    WR => (vAddr - woffset, woffset + 1),
    DL => (vAddr, 8 - doffset),
    DR => (vAddr - doffset, doffset + 1)
  }
}

/*!
 Returns the width of the given WordType (byte, half, word, double) in bytes.
 */
val wordWidthBytes : WordType -> range(1, 8)
function wordWidthBytes(w) =
  match w {
    B  => 1,
    H  => 2,
    W  => 4,
    D  => 8
  }

/* This function checks that memory accesses are naturally aligned
   -- it is disabled in favour of BERI specific behaviour below.
function bool isAddressAligned(addr, (WordType) wordType) =
  match wordType {
    B  => true
    H  => (addr[0]    == 0)
    W  => (addr[1..0] == 0b00)
    D  => (addr[2..0] == 0b000)
  }
*/

/* BERI relaxes the natural alignment requirement for loads and stores
   but still throws an exception if an access spans a cache line
   boundary.  Here we assume this is 32 bytes so that we don't have to
   worry about clearing multiple tags when an access spans more than
   one capability. Capability load/stores are still naturally
   aligned. Provided this is a factor of smallest supported page size
   (4k) we don't need to worry about accesses spanning page boundaries
   either.
*/
let alignment_width = 16
/*!
  THIS`(address, wordtype)` returns whether `address` is naturally aligned for the given `wordtype`.
 */
val isAddressAligned : (bits(64), WordType) -> bool
function isAddressAligned (addr, wordType) =
  let a = unsigned(addr) in
  a / alignment_width == (a + wordWidthBytes(wordType) - 1) / alignment_width

val reverse_endianness = "reverse_endianness" : forall 'n, mod('n, 8) == 0 & 'n >= 8. bits('n) -> bits('n) effect pure

/*!
  THIS`(val, signed)` extends `val` to 64-bits in either sign extended or zero extended fashion according to `signed`.
 */
val extendLoad : forall 'sz, 'sz <= 64 .  (bits('sz), bool) -> bits(64) effect pure
function extendLoad(memResult, sign) = {
  if (sign) then
    sign_extend(memResult)
  else
    zero_extend(memResult)
}

/*
function rec forall Nat 'W, 'W >= 1. bits(8 * 'W) reverse_endianness' (w, value) =
{
    ([:8 * 'W:]) width = length(value);
    if width <= 8
    then value
    else value[7..0] : reverse_endianness'(w - 1, value[(width - 1) .. 8])
}



function rec forall Nat 'W, 'W >= 1. bits(8 * 'W) reverse_endianness ((bits(8 * 'W)) value) =
{
    reverse_endianness'(sizeof 'W, value)
}*/

/*!
THIS`(addr, size)` reads a vector of `size` bytes of memory from physical address `addr` (big-endian byte order on CHERI-MIPS).
 */
val MEMr_wrapper : forall 'n, 1 <= 'n <= 8 . (bits(64), atom('n)) -> bits(8*'n) effect {rmem, rreg, wreg}
function MEMr_wrapper (addr, size) =
    if (addr == 0x000000007f000000) then
      {
        let rvalid = UART_RVALID in
        {
          UART_RVALID = [bitzero];
          mask(0x00000000 @ UART_RDATA @ rvalid @ 0b0000000 @ 0x0000)
        }
      }
    else if (addr == 0x000000007f000004) then
      mask(0x000000000004ffff) /* Always plenty of write space available and jtag activity */
    else
      reverse_endianness(MEMr(addr, size)) /* MEMr assumes little endian */

/*!
is the same as [MEMr_wrapper] except that the read is marked as part of a load linked / store conditional pair.
 */
val MEMr_reserve_wrapper : forall 'n, 1 <= 'n <= 8 . ( bits(64) , atom('n) ) -> (bits(8 * 'n)) effect { rmem }
function MEMr_reserve_wrapper (addr , size) =
    reverse_endianness(MEMr_reserve(addr, size))


function init_cp0_state () : unit -> unit = {
  CP0Status->BEV() = bitone;
}

val init_cp2_state : unit -> unit effect {wreg, escape}
val cp2_next_pc:     unit -> unit effect {rreg, wreg}
val dump_cp2_state : unit -> unit effect {rreg, escape}
