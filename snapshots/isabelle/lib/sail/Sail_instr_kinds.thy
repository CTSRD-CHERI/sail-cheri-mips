chapter \<open>Generated by Lem from ../../src/lem_interp/sail_instr_kinds.lem.\<close>

theory "Sail_instr_kinds" 

imports 
 	 Main
	 "Lem_pervasives_extra" 

begin 

(*========================================================================*)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(*========================================================================*)

(*open import Pervasives_extra*)


record 'a EnumerationType_class= 

  toNat_method ::" 'a \<Rightarrow> nat "




(*val enumeration_typeCompare : forall 'a. EnumerationType 'a => 'a -> 'a -> ordering*)
definition enumeration_typeCompare  :: " 'a EnumerationType_class \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ordering "  where 
     " enumeration_typeCompare dict_Sail_instr_kinds_EnumerationType_a e1 e2 = (
  (genericCompare (op<) (op=) (
  (toNat_method   dict_Sail_instr_kinds_EnumerationType_a) e1) ((toNat_method   dict_Sail_instr_kinds_EnumerationType_a) e2)))"



definition instance_Basic_classes_Ord_var_dict  :: " 'a EnumerationType_class \<Rightarrow> 'a Ord_class "  where 
     " instance_Basic_classes_Ord_var_dict dict_Sail_instr_kinds_EnumerationType_a = ((|

  compare_method = 
  (enumeration_typeCompare dict_Sail_instr_kinds_EnumerationType_a),

  isLess_method = (\<lambda>  r1 r2. (enumeration_typeCompare 
  dict_Sail_instr_kinds_EnumerationType_a r1 r2) = LT),

  isLessEqual_method = (\<lambda> r1 r2. (enumeration_typeCompare 
  dict_Sail_instr_kinds_EnumerationType_a r1 r2) \<noteq> GT),

  isGreater_method = (\<lambda>  r1 r2. (enumeration_typeCompare 
  dict_Sail_instr_kinds_EnumerationType_a r1 r2) = GT),

  isGreaterEqual_method = (\<lambda> r1 r2. (enumeration_typeCompare 
  dict_Sail_instr_kinds_EnumerationType_a r1 r2) \<noteq> LT)|) )"



(* Data structures for building up instructions *)

(* careful: changes in the read/write/barrier kinds have to be
   reflected in deep_shallow_convert *)
datatype read_kind =
  (* common reads *)
    Read_plain
  (* Power reads *)
  | Read_reserve
  (* AArch64 reads *)
  | Read_acquire | Read_exclusive | Read_exclusive_acquire | Read_stream
  (* RISC-V reads *)
  | Read_RISCV_acquire  | Read_RISCV_strong_acquire
  | Read_RISCV_reserved | Read_RISCV_reserved_acquire
  | Read_RISCV_reserved_strong_acquire
  (* x86 reads *)
  | Read_X86_locked (* the read part of a lock'd instruction (rmw) *)

definition instance_Show_Show_Sail_instr_kinds_read_kind_dict  :: "(read_kind)Show_class "  where 
     " instance_Show_Show_Sail_instr_kinds_read_kind_dict = ((|

  show_method = (\<lambda>x .  
  (case  x of
        Read_plain => (''Read_plain'')
    | Read_reserve => (''Read_reserve'')
    | Read_acquire => (''Read_acquire'')
    | Read_exclusive => (''Read_exclusive'')
    | Read_exclusive_acquire => (''Read_exclusive_acquire'')
    | Read_stream => (''Read_stream'')
    | Read_RISCV_acquire => (''Read_RISCV_acquire'')
    | Read_RISCV_strong_acquire => (''Read_RISCV_strong_acquire'')
    | Read_RISCV_reserved => (''Read_RISCV_reserved'')
    | Read_RISCV_reserved_acquire => (''Read_RISCV_reserved_acquire'')
    | Read_RISCV_reserved_strong_acquire => (''Read_RISCV_reserved_strong_acquire'')
    | Read_X86_locked => (''Read_X86_locked'')
  ))|) )"


datatype write_kind =
  (* common writes *)
    Write_plain
  (* Power writes *)
  | Write_conditional
  (* AArch64 writes *)
  | Write_release | Write_exclusive | Write_exclusive_release
  (* RISC-V *)
  | Write_RISCV_release     | Write_RISCV_strong_release
  | Write_RISCV_conditional | Write_RISCV_conditional_release
  | Write_RISCV_conditional_strong_release
  (* x86 writes *)
  | Write_X86_locked (* the write part of a lock'd instruction (rmw) *)

definition instance_Show_Show_Sail_instr_kinds_write_kind_dict  :: "(write_kind)Show_class "  where 
     " instance_Show_Show_Sail_instr_kinds_write_kind_dict = ((|

  show_method = (\<lambda>x .  
  (case  x of
        Write_plain => (''Write_plain'')
    | Write_conditional => (''Write_conditional'')
    | Write_release => (''Write_release'')
    | Write_exclusive => (''Write_exclusive'')
    | Write_exclusive_release => (''Write_exclusive_release'')
    | Write_RISCV_release => (''Write_RISCV_release'')
    | Write_RISCV_strong_release => (''Write_RISCV_strong_release'')
    | Write_RISCV_conditional => (''Write_RISCV_conditional'')
    | Write_RISCV_conditional_release => (''Write_RISCV_conditional_release'')
    | Write_RISCV_conditional_strong_release => (''Write_RISCV_conditional_strong_release'')
    | Write_X86_locked => (''Write_X86_locked'')
  ))|) )"


datatype barrier_kind =
  (* Power barriers *)
  Barrier_Sync | Barrier_LwSync | Barrier_Eieio | Barrier_Isync
  (* AArch64 barriers *)
  | Barrier_DMB | Barrier_DMB_ST | Barrier_DMB_LD | Barrier_DSB
  | Barrier_DSB_ST | Barrier_DSB_LD | Barrier_ISB
  | Barrier_TM_COMMIT
  (* MIPS barriers *)
  | Barrier_MIPS_SYNC
  (* RISC-V barriers *)
  | Barrier_RISCV_rw_rw
  | Barrier_RISCV_r_rw
  | Barrier_RISCV_r_r
  | Barrier_RISCV_rw_w
  | Barrier_RISCV_w_w
  | Barrier_RISCV_i
  (* X86 *)
  | Barrier_x86_MFENCE


definition instance_Show_Show_Sail_instr_kinds_barrier_kind_dict  :: "(barrier_kind)Show_class "  where 
     " instance_Show_Show_Sail_instr_kinds_barrier_kind_dict = ((|

  show_method = (\<lambda>x .  
  (case  x of
        Barrier_Sync => (''Barrier_Sync'')
    | Barrier_LwSync => (''Barrier_LwSync'')
    | Barrier_Eieio => (''Barrier_Eieio'')
    | Barrier_Isync => (''Barrier_Isync'')
    | Barrier_DMB => (''Barrier_DMB'')
    | Barrier_DMB_ST => (''Barrier_DMB_ST'')
    | Barrier_DMB_LD => (''Barrier_DMB_LD'')
    | Barrier_DSB => (''Barrier_DSB'')
    | Barrier_DSB_ST => (''Barrier_DSB_ST'')
    | Barrier_DSB_LD => (''Barrier_DSB_LD'')
    | Barrier_ISB => (''Barrier_ISB'')
    | Barrier_TM_COMMIT => (''Barrier_TM_COMMIT'')
    | Barrier_MIPS_SYNC => (''Barrier_MIPS_SYNC'')
    | Barrier_RISCV_rw_rw => (''Barrier_RISCV_rw_rw'')
    | Barrier_RISCV_r_rw => (''Barrier_RISCV_r_rw'')
    | Barrier_RISCV_r_r => (''Barrier_RISCV_r_r'')
    | Barrier_RISCV_rw_w => (''Barrier_RISCV_rw_w'')
    | Barrier_RISCV_w_w => (''Barrier_RISCV_w_w'')
    | Barrier_RISCV_i => (''Barrier_RISCV_i'')
    | Barrier_x86_MFENCE => (''Barrier_x86_MFENCE'')
  ))|) )"


datatype trans_kind =
  (* AArch64 *)
    Transaction_start | Transaction_commit | Transaction_abort

definition instance_Show_Show_Sail_instr_kinds_trans_kind_dict  :: "(trans_kind)Show_class "  where 
     " instance_Show_Show_Sail_instr_kinds_trans_kind_dict = ((|

  show_method = (\<lambda>x .  
  (case  x of
        Transaction_start => (''Transaction_start'')
    | Transaction_commit => (''Transaction_commit'')
    | Transaction_abort => (''Transaction_abort'')
  ))|) )"


datatype instruction_kind =
    IK_barrier   " barrier_kind "
  | IK_mem_read  " read_kind "
  | IK_mem_write " write_kind "
  | IK_mem_rmw   " (read_kind * write_kind)"
  | IK_branch (* this includes conditional-branch (multiple nias, none of which is NIA_indirect_address),
  indirect/computed-branch (single nia of kind NIA_indirect_address)
  and branch/jump (single nia of kind NIA_concrete_address) *)
  | IK_trans     " trans_kind "
  | IK_simple


definition instance_Show_Show_Sail_instr_kinds_instruction_kind_dict  :: "(instruction_kind)Show_class "  where 
     " instance_Show_Show_Sail_instr_kinds_instruction_kind_dict = ((|

  show_method = (\<lambda>x .  
  (case  x of
        IK_barrier barrier_kind => (''IK_barrier '') @
                                     (((\<lambda>x .  (case  x of
                                                            Barrier_Sync => 
                                                      (''Barrier_Sync'')
                                                        | Barrier_LwSync => 
                                                      (''Barrier_LwSync'')
                                                        | Barrier_Eieio => 
                                                      (''Barrier_Eieio'')
                                                        | Barrier_Isync => 
                                                      (''Barrier_Isync'')
                                                        | Barrier_DMB => 
                                                      (''Barrier_DMB'')
                                                        | Barrier_DMB_ST => 
                                                      (''Barrier_DMB_ST'')
                                                        | Barrier_DMB_LD => 
                                                      (''Barrier_DMB_LD'')
                                                        | Barrier_DSB => 
                                                      (''Barrier_DSB'')
                                                        | Barrier_DSB_ST => 
                                                      (''Barrier_DSB_ST'')
                                                        | Barrier_DSB_LD => 
                                                      (''Barrier_DSB_LD'')
                                                        | Barrier_ISB => 
                                                      (''Barrier_ISB'')
                                                        | Barrier_TM_COMMIT => 
                                                      (''Barrier_TM_COMMIT'')
                                                        | Barrier_MIPS_SYNC => 
                                                      (''Barrier_MIPS_SYNC'')
                                                        | Barrier_RISCV_rw_rw => 
                                                      (''Barrier_RISCV_rw_rw'')
                                                        | Barrier_RISCV_r_rw => 
                                                      (''Barrier_RISCV_r_rw'')
                                                        | Barrier_RISCV_r_r => 
                                                      (''Barrier_RISCV_r_r'')
                                                        | Barrier_RISCV_rw_w => 
                                                      (''Barrier_RISCV_rw_w'')
                                                        | Barrier_RISCV_w_w => 
                                                      (''Barrier_RISCV_w_w'')
                                                        | Barrier_RISCV_i => 
                                                      (''Barrier_RISCV_i'')
                                                        | Barrier_x86_MFENCE => 
                                                      (''Barrier_x86_MFENCE'')
                                                      )) barrier_kind))
    | IK_mem_read read_kind => (''IK_mem_read '') @
                                 (((\<lambda>x .  (case  x of
                                                        Read_plain => 
                                                  (''Read_plain'')
                                                    | Read_reserve => 
                                                  (''Read_reserve'')
                                                    | Read_acquire => 
                                                  (''Read_acquire'')
                                                    | Read_exclusive => 
                                                  (''Read_exclusive'')
                                                    | Read_exclusive_acquire => 
                                                  (''Read_exclusive_acquire'')
                                                    | Read_stream => 
                                                  (''Read_stream'')
                                                    | Read_RISCV_acquire => 
                                                  (''Read_RISCV_acquire'')
                                                    | Read_RISCV_strong_acquire => 
                                                  (''Read_RISCV_strong_acquire'')
                                                    | Read_RISCV_reserved => 
                                                  (''Read_RISCV_reserved'')
                                                    | Read_RISCV_reserved_acquire => 
                                                  (''Read_RISCV_reserved_acquire'')
                                                    | Read_RISCV_reserved_strong_acquire => 
                                                  (''Read_RISCV_reserved_strong_acquire'')
                                                    | Read_X86_locked => 
                                                  (''Read_X86_locked'')
                                                  )) read_kind))
    | IK_mem_write write_kind => (''IK_mem_write '') @
                                   (((\<lambda>x .  (case  x of
                                                          Write_plain => 
                                                    (''Write_plain'')
                                                      | Write_conditional => 
                                                    (''Write_conditional'')
                                                      | Write_release => 
                                                    (''Write_release'')
                                                      | Write_exclusive => 
                                                    (''Write_exclusive'')
                                                      | Write_exclusive_release => 
                                                    (''Write_exclusive_release'')
                                                      | Write_RISCV_release => 
                                                    (''Write_RISCV_release'')
                                                      | Write_RISCV_strong_release => 
                                                    (''Write_RISCV_strong_release'')
                                                      | Write_RISCV_conditional => 
                                                    (''Write_RISCV_conditional'')
                                                      | Write_RISCV_conditional_release => 
                                                    (''Write_RISCV_conditional_release'')
                                                      | Write_RISCV_conditional_strong_release => 
                                                    (''Write_RISCV_conditional_strong_release'')
                                                      | Write_X86_locked => 
                                                    (''Write_X86_locked'')
                                                    )) write_kind))
    | IK_mem_rmw (r, w) => (''IK_mem_rmw '') @
                             ((((\<lambda>x .  (case  x of
                                                     Read_plain => (''Read_plain'')
                                                 | Read_reserve => (''Read_reserve'')
                                                 | Read_acquire => (''Read_acquire'')
                                                 | Read_exclusive => 
                                               (''Read_exclusive'')
                                                 | Read_exclusive_acquire => 
                                               (''Read_exclusive_acquire'')
                                                 | Read_stream => (''Read_stream'')
                                                 | Read_RISCV_acquire => 
                                               (''Read_RISCV_acquire'')
                                                 | Read_RISCV_strong_acquire => 
                                               (''Read_RISCV_strong_acquire'')
                                                 | Read_RISCV_reserved => 
                                               (''Read_RISCV_reserved'')
                                                 | Read_RISCV_reserved_acquire => 
                                               (''Read_RISCV_reserved_acquire'')
                                                 | Read_RISCV_reserved_strong_acquire => 
                                               (''Read_RISCV_reserved_strong_acquire'')
                                                 | Read_X86_locked => 
                                               (''Read_X86_locked'')
                                               )) r)) @
                                (('' '') @
                                   (((\<lambda>x .  (case  x of
                                                          Write_plain => 
                                                    (''Write_plain'')
                                                      | Write_conditional => 
                                                    (''Write_conditional'')
                                                      | Write_release => 
                                                    (''Write_release'')
                                                      | Write_exclusive => 
                                                    (''Write_exclusive'')
                                                      | Write_exclusive_release => 
                                                    (''Write_exclusive_release'')
                                                      | Write_RISCV_release => 
                                                    (''Write_RISCV_release'')
                                                      | Write_RISCV_strong_release => 
                                                    (''Write_RISCV_strong_release'')
                                                      | Write_RISCV_conditional => 
                                                    (''Write_RISCV_conditional'')
                                                      | Write_RISCV_conditional_release => 
                                                    (''Write_RISCV_conditional_release'')
                                                      | Write_RISCV_conditional_strong_release => 
                                                    (''Write_RISCV_conditional_strong_release'')
                                                      | Write_X86_locked => 
                                                    (''Write_X86_locked'')
                                                    )) w))))
    | IK_branch => (''IK_branch'')
    | IK_trans trans_kind => (''IK_trans '') @
                               (((\<lambda>x .  (case  x of
                                                      Transaction_start => 
                                                (''Transaction_start'')
                                                  | Transaction_commit => 
                                                (''Transaction_commit'')
                                                  | Transaction_abort => 
                                                (''Transaction_abort'')
                                                )) trans_kind))
    | IK_simple => (''IK_simple'')
  ))|) )"



definition read_is_exclusive  :: " read_kind \<Rightarrow> bool "  where 
     " read_is_exclusive = ( \<lambda>x .  
  (case  x of
        Read_plain => False
    | Read_reserve => True
    | Read_acquire => False
    | Read_exclusive => True
    | Read_exclusive_acquire => True
    | Read_stream => False
    | Read_RISCV_acquire => False
    | Read_RISCV_strong_acquire => False
    | Read_RISCV_reserved => True
    | Read_RISCV_reserved_acquire => True
    | Read_RISCV_reserved_strong_acquire => True
    | Read_X86_locked => True
  ) )"




definition instance_Sail_instr_kinds_EnumerationType_Sail_instr_kinds_read_kind_dict  :: "(read_kind)EnumerationType_class "  where 
     " instance_Sail_instr_kinds_EnumerationType_Sail_instr_kinds_read_kind_dict = ((|

  toNat_method = (\<lambda>x .  
  (case  x of
        Read_plain =>( 0 :: nat)
    | Read_reserve =>( 1 :: nat)
    | Read_acquire =>( 2 :: nat)
    | Read_exclusive =>( 3 :: nat)
    | Read_exclusive_acquire =>( 4 :: nat)
    | Read_stream =>( 5 :: nat)
    | Read_RISCV_acquire =>( 6 :: nat)
    | Read_RISCV_strong_acquire =>( 7 :: nat)
    | Read_RISCV_reserved =>( 8 :: nat)
    | Read_RISCV_reserved_acquire =>( 9 :: nat)
    | Read_RISCV_reserved_strong_acquire =>( 10 :: nat)
    | Read_X86_locked =>( 11 :: nat)
  ))|) )"


definition instance_Sail_instr_kinds_EnumerationType_Sail_instr_kinds_write_kind_dict  :: "(write_kind)EnumerationType_class "  where 
     " instance_Sail_instr_kinds_EnumerationType_Sail_instr_kinds_write_kind_dict = ((|

  toNat_method = (\<lambda>x .  
  (case  x of
        Write_plain =>( 0 :: nat)
    | Write_conditional =>( 1 :: nat)
    | Write_release =>( 2 :: nat)
    | Write_exclusive =>( 3 :: nat)
    | Write_exclusive_release =>( 4 :: nat)
    | Write_RISCV_release =>( 5 :: nat)
    | Write_RISCV_strong_release =>( 6 :: nat)
    | Write_RISCV_conditional =>( 7 :: nat)
    | Write_RISCV_conditional_release =>( 8 :: nat)
    | Write_RISCV_conditional_strong_release =>( 9 :: nat)
    | Write_X86_locked =>( 10 :: nat)
  ))|) )"


definition instance_Sail_instr_kinds_EnumerationType_Sail_instr_kinds_barrier_kind_dict  :: "(barrier_kind)EnumerationType_class "  where 
     " instance_Sail_instr_kinds_EnumerationType_Sail_instr_kinds_barrier_kind_dict = ((|

  toNat_method = (\<lambda>x .  
  (case  x of
        Barrier_Sync =>( 0 :: nat)
    | Barrier_LwSync =>( 1 :: nat)
    | Barrier_Eieio =>( 2 :: nat)
    | Barrier_Isync =>( 3 :: nat)
    | Barrier_DMB =>( 4 :: nat)
    | Barrier_DMB_ST =>( 5 :: nat)
    | Barrier_DMB_LD =>( 6 :: nat)
    | Barrier_DSB =>( 7 :: nat)
    | Barrier_DSB_ST =>( 8 :: nat)
    | Barrier_DSB_LD =>( 9 :: nat)
    | Barrier_ISB =>( 10 :: nat)
    | Barrier_TM_COMMIT =>( 11 :: nat)
    | Barrier_MIPS_SYNC =>( 12 :: nat)
    | Barrier_RISCV_rw_rw =>( 13 :: nat)
    | Barrier_RISCV_r_rw =>( 14 :: nat)
    | Barrier_RISCV_r_r =>( 15 :: nat)
    | Barrier_RISCV_rw_w =>( 16 :: nat)
    | Barrier_RISCV_w_w =>( 17 :: nat)
    | Barrier_RISCV_i =>( 18 :: nat)
    | Barrier_x86_MFENCE =>( 19 :: nat)
  ))|) )"

end