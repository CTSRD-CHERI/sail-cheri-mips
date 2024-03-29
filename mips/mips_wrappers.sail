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

/* mips_wrappers.sail: wrappers functions and hooks for CHERI extensibility
   (mostly identity functions here) */

register CP0EPC : bits(64)
function get_CP0EPC() = CP0EPC
function set_CP0EPC(v) = {
  CP0EPC = v;
  skip_rreg();
}

register CP0ErrorEPC : bits(64)
function get_CP0ErrorEPC() = CP0ErrorEPC
function set_CP0ErrorEPC(v) = {
  CP0ErrorEPC = v;
  skip_rreg();
}

val MEMw_wrapper : forall 'n, 1 <= 'n <= 8. (bits(64), atom('n), bits(8 * 'n)) -> unit effect {eamem, wmv, wreg}

function MEMw_wrapper(addr, size, data) =
    let ledata = reverse_endianness(data) in
    if (addr == 0x000000007f000000) then
      {
        UART_WDATA   = ledata[7..0];
        UART_WRITTEN = bitone;
      } else {
        MEMea(addr, size);
        MEMval(addr, size, ledata);
      }

val MEMw_conditional_wrapper : forall 'n,  1 <= 'n <= 8. (bits(64), atom('n), bits(8 * 'n)) -> bool effect {eamem, wmv}

function MEMw_conditional_wrapper(addr, size, data) =
    {
      MEMea_conditional(addr, size);
      MEMval_conditional(addr, size, reverse_endianness(data))
    }

val addrWrapper : (bits(64), MemAccessType, WordType) -> bits(64)
function addrWrapper(addr, accessType, width) =
    addr

val addrWrapperUnaligned : (bits(64), MemAccessType, WordTypeUnaligned) -> (bits(64), int)
function addrWrapperUnaligned(addr, accessType, width) =
  let (addr, size) = unalignedBytesTouched(unsigned(addr), width) in
  (to_bits(64, addr), size)

$ifdef _MIPS_TLB_STUB
val TranslatePC : bits(64) -> bits(64) effect {rreg, wreg, escape}
$else
val TranslatePC : bits(64) -> bits(64) effect {rreg, wreg, escape, undef}
$endif

function TranslatePC (vAddr) = {
    incrementCP0Count();
    if (vAddr[1..0] != 0b00) then /* bad PC alignment */
      (SignalExceptionBadAddr(AdEL, vAddr))
    else
      TLBTranslate(vAddr, Instruction)
}

let have_cp2 = false

function SignalException (ex) = {
  traceException(ex);
  /* Only update EPC and BD if not already in EXL mode */
  if (~ (CP0Status.EXL())) then
  {
    if (InBranchDelay[0]) then
    {
      set_CP0EPC(PC - 4);
      CP0Cause->BD() = 0b1;
    }
    else {
      set_CP0EPC(PC);
      CP0Cause->BD() = 0b0;
    }
  };
  /* Fill in BadInstr + BadInstrP. */
  updateBadInstr();
  let vectorOffset = exceptionVectorOffset(ex);
  let vectorBase = exceptionVectorBase();
  NextPC = vectorBase + zero_extend(vectorOffset);
  CP0Cause->ExcCode() = ExceptionCode(ex);
  CP0Status->EXL()    = 0b1;
  throw (ISAException());
}

val ERETHook : unit -> unit
function ERETHook() = ()
function checkCP0AccessHook () : unit -> unit = ()

function init_cp2_state () = {skip_wreg(); skip_escape()}
function cp2_next_pc()     = {skip_wreg(); skip_rreg()}
function dump_cp2_state () = {skip_rreg(); skip_escape();}
function execute_branch (pc) = {skip_rreg(); skip_escape(); execute_branch_mips(pc);}

