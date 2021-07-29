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

val cycle_limit_reached = { ocaml: "cycle_limit_reached", c: "cycle_limit_reached" } : unit -> bool

function cycle_limit_reached() = false

register InstCount : int

val fetch_and_execute : unit -> bool effect {barr, eamem, escape, rmem, rreg, wmv, wreg, undef, wmvt, rmemt}
function fetch_and_execute () = {
  PC = NextPC;
  InBranchDelay = NextInBranchDelay;
  NextPC = if BranchPending then DelayedPC else PC + 4;
  NextInBranchDelay = 0b0;
  BranchPending = 0b0;
  cp2_next_pc();
  InstCount = InstCount + 1;
  if UART_WRITTEN then {
    putchar(unsigned(UART_WDATA));
    UART_WRITTEN = 0b0;
  };
  /* the following skips are required on mips to fake the tag effects otherwise type checker complains  */
  skip_rmemt();
  skip_wmvt();
  if trace then {
    prerr("PC: ");
    prerr(BitStr(PC));
  };
  loop_again : bool = true;
  try {
    let pc_pa = TranslatePC(PC);
    /*print_bits("pa: ", pc_pa);*/
    LastInstrBits = CurrentInstrBits;
    let instr_next = MEMr_wrapper(pc_pa, 4);
    if trace then
        prerr_bits(" op:", instr_next);
    let instr_ast = decode(instr_next);
    CurrentInstrBits = instr_next;
    match instr_ast {
      Some(HCF()) => {
                     print("simulation stopped due to halt instruction.");
                     loop_again = false
                   },
      Some(ast) => {
                if trace then {
                  prerr(assembly(ast));
                  prerr("\n");
                };
                execute(ast)
      },
      None()    => { print("Decode failed"); loop_again=false } /* Never expect this -- unknown instruction should actually result in reserved instruction ISA-level exception (see mips_ri.sail). */
    }
  } catch {
    ISAException() => ()
    /* ISA-level exception occurrred either during TranslatePC or execute --
       just continue from NextPC, which should have been set to the appropriate
       exception vector (along with clearing BranchPending etc.) . */
  };
  loop_again & not (cycle_limit_reached());
}

val elf_entry = {
  ocaml: "Elf_loader.elf_entry",
  lem: "elf_entry",
  c: "elf_entry"
} : unit -> int

val init_registers : bits(64) -> unit effect {wreg, escape}

function init_registers (initialPC) = {
  init_cp0_state();
  init_cp2_state();
  NextPC = initialPC;
}

function dump_mips_state () : unit -> unit = {
  print_bits("DEBUG MIPS PC ", PC);
  foreach (idx from 0 to 31) {
    print(concat_str("DEBUG MIPS REG ", concat_str(string_of_int(idx), concat_str(" ", BitStr(rGPR(to_bits(5,idx)))))));
  }
}

val main : unit -> unit effect {barr, eamem, escape, rmem, rreg, undef, wmv, wreg, rmemt, wmvt}

function main () = {
  init_registers(to_bits(64, elf_entry()));
  startTime = get_time_ns();
  intervalStart = startTime;
  intervalCount : int = 0;
  while (fetch_and_execute()) do {
    /* uncomment to print IPS every 10M instructions (~10s)
    intervalCount = intervalCount + 1;
    if (intervalCount == 10000000) then {
      endTime = get_time_ns();
      elapsed = endTime - intervalStart;
      inst_1e9 = intervalCount * 1000000000;
      ips = inst_1e9 / elapsed;
      print_int("*IPS*: ", ips);
      intervalStart = get_time_ns();
      intervalCount = 0;
    };
    */
    ();
  };

  endTime = get_time_ns();
  elapsed = endTime - startTime;
  inst_1e9 = InstCount * 1000000000;
  ips = inst_1e9 / elapsed;
  dump_mips_state ();
  dump_cp2_state ();
  print_int("Executed instructions: ", InstCount);
  print_int("Nanoseconds elapsed: ", elapsed);
  print_int("Instructions per second: ", ips);
}
