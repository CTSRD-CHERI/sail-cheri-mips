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

$ifndef _MIPS_TLB_STUB
$define _MIPS_TLB_STUB

val tlbEntryMatch : (bits(2), bits(27), bits(8), TLBEntry) -> bool effect pure
function tlbSearch(VAddr) : bits(64) -> option(TLBIndexT) = None()

val TLBTranslate2 : (bits(64), MemAccessType) -> (bits(64), bool) effect pure
function TLBTranslate (vAddr, accessType) : (bits(64), MemAccessType) -> bits(64) =
      vAddr

val TLBTranslateC : (bits(64), MemAccessType) -> (bits(64), bool) effect pure
function TLBTranslateC (vAddr, accessType) : (bits(64), MemAccessType) -> (bits(64), bool) = (vAddr, false)

$endif
