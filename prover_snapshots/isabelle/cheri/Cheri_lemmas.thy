theory Cheri_lemmas
  imports
    Sail.Sail2_values_lemmas
    Sail.Sail2_state_lemmas
    Cheri
begin

abbreviation liftS ("\<lbrakk>_\<rbrakk>\<^sub>S") where "liftS \<equiv> liftState (get_regval, set_regval)"

lemmas register_defs = get_regval_def set_regval_def InstCount_ref_def CID_ref_def ErrorEPCC_ref_def
  KDC_ref_def KR2C_ref_def KR1C_ref_def CPLR_ref_def CULR_ref_def C31_ref_def C30_ref_def
  C29_ref_def C28_ref_def C27_ref_def C26_ref_def C25_ref_def C24_ref_def C23_ref_def C22_ref_def
  C21_ref_def C20_ref_def C19_ref_def C18_ref_def C17_ref_def C16_ref_def C15_ref_def C14_ref_def
  C13_ref_def C12_ref_def C11_ref_def C10_ref_def C09_ref_def C08_ref_def C07_ref_def C06_ref_def
  C05_ref_def C04_ref_def C03_ref_def C02_ref_def C01_ref_def DDC_ref_def CapCause_ref_def
  NextPCC_ref_def DelayedPCC_ref_def PCC_ref_def KCC_ref_def EPCC_ref_def UART_RVALID_ref_def
  UART_RDATA_ref_def UART_WRITTEN_ref_def UART_WDATA_ref_def GPR_ref_def LO_ref_def HI_ref_def
  DelayedPC_ref_def BranchPending_ref_def InBranchDelay_ref_def NextInBranchDelay_ref_def
  CP0Status_ref_def CP0ConfigK0_ref_def CP0UserLocal_ref_def CP0HWREna_ref_def CP0Count_ref_def
  CP0BadInstrP_ref_def CP0BadInstr_ref_def LastInstrBits_ref_def CurrentInstrBits_ref_def
  CP0BadVAddr_ref_def CP0LLAddr_ref_def CP0LLBit_ref_def CP0Cause_ref_def CP0Compare_ref_def
  TLBEntry63_ref_def TLBEntry62_ref_def TLBEntry61_ref_def TLBEntry60_ref_def TLBEntry59_ref_def
  TLBEntry58_ref_def TLBEntry57_ref_def TLBEntry56_ref_def TLBEntry55_ref_def TLBEntry54_ref_def
  TLBEntry53_ref_def TLBEntry52_ref_def TLBEntry51_ref_def TLBEntry50_ref_def TLBEntry49_ref_def
  TLBEntry48_ref_def TLBEntry47_ref_def TLBEntry46_ref_def TLBEntry45_ref_def TLBEntry44_ref_def
  TLBEntry43_ref_def TLBEntry42_ref_def TLBEntry41_ref_def TLBEntry40_ref_def TLBEntry39_ref_def
  TLBEntry38_ref_def TLBEntry37_ref_def TLBEntry36_ref_def TLBEntry35_ref_def TLBEntry34_ref_def
  TLBEntry33_ref_def TLBEntry32_ref_def TLBEntry31_ref_def TLBEntry30_ref_def TLBEntry29_ref_def
  TLBEntry28_ref_def TLBEntry27_ref_def TLBEntry26_ref_def TLBEntry25_ref_def TLBEntry24_ref_def
  TLBEntry23_ref_def TLBEntry22_ref_def TLBEntry21_ref_def TLBEntry20_ref_def TLBEntry19_ref_def
  TLBEntry18_ref_def TLBEntry17_ref_def TLBEntry16_ref_def TLBEntry15_ref_def TLBEntry14_ref_def
  TLBEntry13_ref_def TLBEntry12_ref_def TLBEntry11_ref_def TLBEntry10_ref_def TLBEntry09_ref_def
  TLBEntry08_ref_def TLBEntry07_ref_def TLBEntry06_ref_def TLBEntry05_ref_def TLBEntry04_ref_def
  TLBEntry03_ref_def TLBEntry02_ref_def TLBEntry01_ref_def TLBEntry00_ref_def TLBXContext_ref_def
  TLBEntryHi_ref_def TLBWired_ref_def TLBPageMask_ref_def TLBContext_ref_def TLBEntryLo1_ref_def
  TLBEntryLo0_ref_def TLBRandom_ref_def TLBIndex_ref_def TLBProbe_ref_def NextPC_ref_def PC_ref_def

lemma regval_CapCauseReg[simp]:
  "CapCauseReg_of_regval (regval_of_CapCauseReg v) = Some v"
  by (auto simp: regval_of_CapCauseReg_def)

lemma regval_Capability[simp]:
  "Capability_of_regval (regval_of_Capability v) = Some v"
  by (auto simp: regval_of_Capability_def)

lemma regval_CauseReg[simp]:
  "CauseReg_of_regval (regval_of_CauseReg v) = Some v"
  by (auto simp: regval_of_CauseReg_def)

lemma regval_ContextReg[simp]:
  "ContextReg_of_regval (regval_of_ContextReg v) = Some v"
  by (auto simp: regval_of_ContextReg_def)

lemma regval_StatusReg[simp]:
  "StatusReg_of_regval (regval_of_StatusReg v) = Some v"
  by (auto simp: regval_of_StatusReg_def)

lemma regval_TLBEntry[simp]:
  "TLBEntry_of_regval (regval_of_TLBEntry v) = Some v"
  by (auto simp: regval_of_TLBEntry_def)

lemma regval_TLBEntryHiReg[simp]:
  "TLBEntryHiReg_of_regval (regval_of_TLBEntryHiReg v) = Some v"
  by (auto simp: regval_of_TLBEntryHiReg_def)

lemma regval_TLBEntryLoReg[simp]:
  "TLBEntryLoReg_of_regval (regval_of_TLBEntryLoReg v) = Some v"
  by (auto simp: regval_of_TLBEntryLoReg_def)

lemma regval_XContextReg[simp]:
  "XContextReg_of_regval (regval_of_XContextReg v) = Some v"
  by (auto simp: regval_of_XContextReg_def)

lemma regval_bit[simp]:
  "bit_of_regval (regval_of_bit v) = Some v"
  by (auto simp: regval_of_bit_def)

lemma regval_bitvector_16_dec[simp]:
  "bitvector_16_dec_of_regval (regval_of_bitvector_16_dec v) = Some v"
  by (auto simp: regval_of_bitvector_16_dec_def)

lemma regval_bitvector_1_dec[simp]:
  "bitvector_1_dec_of_regval (regval_of_bitvector_1_dec v) = Some v"
  by (auto simp: regval_of_bitvector_1_dec_def)

lemma regval_bitvector_32_dec[simp]:
  "bitvector_32_dec_of_regval (regval_of_bitvector_32_dec v) = Some v"
  by (auto simp: regval_of_bitvector_32_dec_def)

lemma regval_bitvector_3_dec[simp]:
  "bitvector_3_dec_of_regval (regval_of_bitvector_3_dec v) = Some v"
  by (auto simp: regval_of_bitvector_3_dec_def)

lemma regval_bitvector_64_dec[simp]:
  "bitvector_64_dec_of_regval (regval_of_bitvector_64_dec v) = Some v"
  by (auto simp: regval_of_bitvector_64_dec_def)

lemma regval_bitvector_6_dec[simp]:
  "bitvector_6_dec_of_regval (regval_of_bitvector_6_dec v) = Some v"
  by (auto simp: regval_of_bitvector_6_dec_def)

lemma regval_bitvector_8_dec[simp]:
  "bitvector_8_dec_of_regval (regval_of_bitvector_8_dec v) = Some v"
  by (auto simp: regval_of_bitvector_8_dec_def)

lemma regval_int[simp]:
  "int_of_regval (regval_of_int v) = Some v"
  by (auto simp: regval_of_int_def)

lemma vector_of_rv_rv_of_vector[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "vector_of_regval of_rv (regval_of_vector rv_of v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  then show ?thesis by (auto simp: vector_of_regval_def regval_of_vector_def)
qed

lemma option_of_rv_rv_of_option[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "option_of_regval of_rv (regval_of_option rv_of v) = Some v"
  using assms by (cases v) (auto simp: option_of_regval_def regval_of_option_def)

lemma list_of_rv_rv_of_list[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "list_of_regval of_rv (regval_of_list rv_of v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  with assms show ?thesis by (induction v) (auto simp: list_of_regval_def regval_of_list_def)
qed

lemma liftS_read_reg_InstCount[liftState_simp]:
  "\<lbrakk>read_reg InstCount_ref\<rbrakk>\<^sub>S = read_regS InstCount_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_InstCount[liftState_simp]:
  "\<lbrakk>write_reg InstCount_ref v\<rbrakk>\<^sub>S = write_regS InstCount_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CID[liftState_simp]:
  "\<lbrakk>read_reg CID_ref\<rbrakk>\<^sub>S = read_regS CID_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CID[liftState_simp]:
  "\<lbrakk>write_reg CID_ref v\<rbrakk>\<^sub>S = write_regS CID_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_ErrorEPCC[liftState_simp]:
  "\<lbrakk>read_reg ErrorEPCC_ref\<rbrakk>\<^sub>S = read_regS ErrorEPCC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_ErrorEPCC[liftState_simp]:
  "\<lbrakk>write_reg ErrorEPCC_ref v\<rbrakk>\<^sub>S = write_regS ErrorEPCC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_KDC[liftState_simp]:
  "\<lbrakk>read_reg KDC_ref\<rbrakk>\<^sub>S = read_regS KDC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_KDC[liftState_simp]:
  "\<lbrakk>write_reg KDC_ref v\<rbrakk>\<^sub>S = write_regS KDC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_KR2C[liftState_simp]:
  "\<lbrakk>read_reg KR2C_ref\<rbrakk>\<^sub>S = read_regS KR2C_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_KR2C[liftState_simp]:
  "\<lbrakk>write_reg KR2C_ref v\<rbrakk>\<^sub>S = write_regS KR2C_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_KR1C[liftState_simp]:
  "\<lbrakk>read_reg KR1C_ref\<rbrakk>\<^sub>S = read_regS KR1C_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_KR1C[liftState_simp]:
  "\<lbrakk>write_reg KR1C_ref v\<rbrakk>\<^sub>S = write_regS KR1C_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CPLR[liftState_simp]:
  "\<lbrakk>read_reg CPLR_ref\<rbrakk>\<^sub>S = read_regS CPLR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CPLR[liftState_simp]:
  "\<lbrakk>write_reg CPLR_ref v\<rbrakk>\<^sub>S = write_regS CPLR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CULR[liftState_simp]:
  "\<lbrakk>read_reg CULR_ref\<rbrakk>\<^sub>S = read_regS CULR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CULR[liftState_simp]:
  "\<lbrakk>write_reg CULR_ref v\<rbrakk>\<^sub>S = write_regS CULR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C31[liftState_simp]:
  "\<lbrakk>read_reg C31_ref\<rbrakk>\<^sub>S = read_regS C31_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C31[liftState_simp]:
  "\<lbrakk>write_reg C31_ref v\<rbrakk>\<^sub>S = write_regS C31_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C30[liftState_simp]:
  "\<lbrakk>read_reg C30_ref\<rbrakk>\<^sub>S = read_regS C30_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C30[liftState_simp]:
  "\<lbrakk>write_reg C30_ref v\<rbrakk>\<^sub>S = write_regS C30_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C29[liftState_simp]:
  "\<lbrakk>read_reg C29_ref\<rbrakk>\<^sub>S = read_regS C29_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C29[liftState_simp]:
  "\<lbrakk>write_reg C29_ref v\<rbrakk>\<^sub>S = write_regS C29_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C28[liftState_simp]:
  "\<lbrakk>read_reg C28_ref\<rbrakk>\<^sub>S = read_regS C28_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C28[liftState_simp]:
  "\<lbrakk>write_reg C28_ref v\<rbrakk>\<^sub>S = write_regS C28_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C27[liftState_simp]:
  "\<lbrakk>read_reg C27_ref\<rbrakk>\<^sub>S = read_regS C27_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C27[liftState_simp]:
  "\<lbrakk>write_reg C27_ref v\<rbrakk>\<^sub>S = write_regS C27_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C26[liftState_simp]:
  "\<lbrakk>read_reg C26_ref\<rbrakk>\<^sub>S = read_regS C26_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C26[liftState_simp]:
  "\<lbrakk>write_reg C26_ref v\<rbrakk>\<^sub>S = write_regS C26_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C25[liftState_simp]:
  "\<lbrakk>read_reg C25_ref\<rbrakk>\<^sub>S = read_regS C25_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C25[liftState_simp]:
  "\<lbrakk>write_reg C25_ref v\<rbrakk>\<^sub>S = write_regS C25_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C24[liftState_simp]:
  "\<lbrakk>read_reg C24_ref\<rbrakk>\<^sub>S = read_regS C24_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C24[liftState_simp]:
  "\<lbrakk>write_reg C24_ref v\<rbrakk>\<^sub>S = write_regS C24_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C23[liftState_simp]:
  "\<lbrakk>read_reg C23_ref\<rbrakk>\<^sub>S = read_regS C23_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C23[liftState_simp]:
  "\<lbrakk>write_reg C23_ref v\<rbrakk>\<^sub>S = write_regS C23_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C22[liftState_simp]:
  "\<lbrakk>read_reg C22_ref\<rbrakk>\<^sub>S = read_regS C22_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C22[liftState_simp]:
  "\<lbrakk>write_reg C22_ref v\<rbrakk>\<^sub>S = write_regS C22_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C21[liftState_simp]:
  "\<lbrakk>read_reg C21_ref\<rbrakk>\<^sub>S = read_regS C21_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C21[liftState_simp]:
  "\<lbrakk>write_reg C21_ref v\<rbrakk>\<^sub>S = write_regS C21_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C20[liftState_simp]:
  "\<lbrakk>read_reg C20_ref\<rbrakk>\<^sub>S = read_regS C20_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C20[liftState_simp]:
  "\<lbrakk>write_reg C20_ref v\<rbrakk>\<^sub>S = write_regS C20_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C19[liftState_simp]:
  "\<lbrakk>read_reg C19_ref\<rbrakk>\<^sub>S = read_regS C19_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C19[liftState_simp]:
  "\<lbrakk>write_reg C19_ref v\<rbrakk>\<^sub>S = write_regS C19_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C18[liftState_simp]:
  "\<lbrakk>read_reg C18_ref\<rbrakk>\<^sub>S = read_regS C18_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C18[liftState_simp]:
  "\<lbrakk>write_reg C18_ref v\<rbrakk>\<^sub>S = write_regS C18_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C17[liftState_simp]:
  "\<lbrakk>read_reg C17_ref\<rbrakk>\<^sub>S = read_regS C17_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C17[liftState_simp]:
  "\<lbrakk>write_reg C17_ref v\<rbrakk>\<^sub>S = write_regS C17_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C16[liftState_simp]:
  "\<lbrakk>read_reg C16_ref\<rbrakk>\<^sub>S = read_regS C16_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C16[liftState_simp]:
  "\<lbrakk>write_reg C16_ref v\<rbrakk>\<^sub>S = write_regS C16_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C15[liftState_simp]:
  "\<lbrakk>read_reg C15_ref\<rbrakk>\<^sub>S = read_regS C15_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C15[liftState_simp]:
  "\<lbrakk>write_reg C15_ref v\<rbrakk>\<^sub>S = write_regS C15_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C14[liftState_simp]:
  "\<lbrakk>read_reg C14_ref\<rbrakk>\<^sub>S = read_regS C14_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C14[liftState_simp]:
  "\<lbrakk>write_reg C14_ref v\<rbrakk>\<^sub>S = write_regS C14_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C13[liftState_simp]:
  "\<lbrakk>read_reg C13_ref\<rbrakk>\<^sub>S = read_regS C13_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C13[liftState_simp]:
  "\<lbrakk>write_reg C13_ref v\<rbrakk>\<^sub>S = write_regS C13_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C12[liftState_simp]:
  "\<lbrakk>read_reg C12_ref\<rbrakk>\<^sub>S = read_regS C12_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C12[liftState_simp]:
  "\<lbrakk>write_reg C12_ref v\<rbrakk>\<^sub>S = write_regS C12_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C11[liftState_simp]:
  "\<lbrakk>read_reg C11_ref\<rbrakk>\<^sub>S = read_regS C11_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C11[liftState_simp]:
  "\<lbrakk>write_reg C11_ref v\<rbrakk>\<^sub>S = write_regS C11_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C10[liftState_simp]:
  "\<lbrakk>read_reg C10_ref\<rbrakk>\<^sub>S = read_regS C10_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C10[liftState_simp]:
  "\<lbrakk>write_reg C10_ref v\<rbrakk>\<^sub>S = write_regS C10_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C09[liftState_simp]:
  "\<lbrakk>read_reg C09_ref\<rbrakk>\<^sub>S = read_regS C09_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C09[liftState_simp]:
  "\<lbrakk>write_reg C09_ref v\<rbrakk>\<^sub>S = write_regS C09_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C08[liftState_simp]:
  "\<lbrakk>read_reg C08_ref\<rbrakk>\<^sub>S = read_regS C08_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C08[liftState_simp]:
  "\<lbrakk>write_reg C08_ref v\<rbrakk>\<^sub>S = write_regS C08_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C07[liftState_simp]:
  "\<lbrakk>read_reg C07_ref\<rbrakk>\<^sub>S = read_regS C07_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C07[liftState_simp]:
  "\<lbrakk>write_reg C07_ref v\<rbrakk>\<^sub>S = write_regS C07_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C06[liftState_simp]:
  "\<lbrakk>read_reg C06_ref\<rbrakk>\<^sub>S = read_regS C06_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C06[liftState_simp]:
  "\<lbrakk>write_reg C06_ref v\<rbrakk>\<^sub>S = write_regS C06_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C05[liftState_simp]:
  "\<lbrakk>read_reg C05_ref\<rbrakk>\<^sub>S = read_regS C05_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C05[liftState_simp]:
  "\<lbrakk>write_reg C05_ref v\<rbrakk>\<^sub>S = write_regS C05_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C04[liftState_simp]:
  "\<lbrakk>read_reg C04_ref\<rbrakk>\<^sub>S = read_regS C04_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C04[liftState_simp]:
  "\<lbrakk>write_reg C04_ref v\<rbrakk>\<^sub>S = write_regS C04_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C03[liftState_simp]:
  "\<lbrakk>read_reg C03_ref\<rbrakk>\<^sub>S = read_regS C03_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C03[liftState_simp]:
  "\<lbrakk>write_reg C03_ref v\<rbrakk>\<^sub>S = write_regS C03_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C02[liftState_simp]:
  "\<lbrakk>read_reg C02_ref\<rbrakk>\<^sub>S = read_regS C02_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C02[liftState_simp]:
  "\<lbrakk>write_reg C02_ref v\<rbrakk>\<^sub>S = write_regS C02_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_C01[liftState_simp]:
  "\<lbrakk>read_reg C01_ref\<rbrakk>\<^sub>S = read_regS C01_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_C01[liftState_simp]:
  "\<lbrakk>write_reg C01_ref v\<rbrakk>\<^sub>S = write_regS C01_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DDC[liftState_simp]:
  "\<lbrakk>read_reg DDC_ref\<rbrakk>\<^sub>S = read_regS DDC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DDC[liftState_simp]:
  "\<lbrakk>write_reg DDC_ref v\<rbrakk>\<^sub>S = write_regS DDC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CapCause[liftState_simp]:
  "\<lbrakk>read_reg CapCause_ref\<rbrakk>\<^sub>S = read_regS CapCause_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CapCause[liftState_simp]:
  "\<lbrakk>write_reg CapCause_ref v\<rbrakk>\<^sub>S = write_regS CapCause_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_NextPCC[liftState_simp]:
  "\<lbrakk>read_reg NextPCC_ref\<rbrakk>\<^sub>S = read_regS NextPCC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_NextPCC[liftState_simp]:
  "\<lbrakk>write_reg NextPCC_ref v\<rbrakk>\<^sub>S = write_regS NextPCC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DelayedPCC[liftState_simp]:
  "\<lbrakk>read_reg DelayedPCC_ref\<rbrakk>\<^sub>S = read_regS DelayedPCC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DelayedPCC[liftState_simp]:
  "\<lbrakk>write_reg DelayedPCC_ref v\<rbrakk>\<^sub>S = write_regS DelayedPCC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PCC[liftState_simp]:
  "\<lbrakk>read_reg PCC_ref\<rbrakk>\<^sub>S = read_regS PCC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PCC[liftState_simp]:
  "\<lbrakk>write_reg PCC_ref v\<rbrakk>\<^sub>S = write_regS PCC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_KCC[liftState_simp]:
  "\<lbrakk>read_reg KCC_ref\<rbrakk>\<^sub>S = read_regS KCC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_KCC[liftState_simp]:
  "\<lbrakk>write_reg KCC_ref v\<rbrakk>\<^sub>S = write_regS KCC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_EPCC[liftState_simp]:
  "\<lbrakk>read_reg EPCC_ref\<rbrakk>\<^sub>S = read_regS EPCC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_EPCC[liftState_simp]:
  "\<lbrakk>write_reg EPCC_ref v\<rbrakk>\<^sub>S = write_regS EPCC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_UART_RVALID[liftState_simp]:
  "\<lbrakk>read_reg UART_RVALID_ref\<rbrakk>\<^sub>S = read_regS UART_RVALID_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_UART_RVALID[liftState_simp]:
  "\<lbrakk>write_reg UART_RVALID_ref v\<rbrakk>\<^sub>S = write_regS UART_RVALID_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_UART_RDATA[liftState_simp]:
  "\<lbrakk>read_reg UART_RDATA_ref\<rbrakk>\<^sub>S = read_regS UART_RDATA_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_UART_RDATA[liftState_simp]:
  "\<lbrakk>write_reg UART_RDATA_ref v\<rbrakk>\<^sub>S = write_regS UART_RDATA_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_UART_WRITTEN[liftState_simp]:
  "\<lbrakk>read_reg UART_WRITTEN_ref\<rbrakk>\<^sub>S = read_regS UART_WRITTEN_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_UART_WRITTEN[liftState_simp]:
  "\<lbrakk>write_reg UART_WRITTEN_ref v\<rbrakk>\<^sub>S = write_regS UART_WRITTEN_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_UART_WDATA[liftState_simp]:
  "\<lbrakk>read_reg UART_WDATA_ref\<rbrakk>\<^sub>S = read_regS UART_WDATA_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_UART_WDATA[liftState_simp]:
  "\<lbrakk>write_reg UART_WDATA_ref v\<rbrakk>\<^sub>S = write_regS UART_WDATA_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_GPR[liftState_simp]:
  "\<lbrakk>read_reg GPR_ref\<rbrakk>\<^sub>S = read_regS GPR_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_GPR[liftState_simp]:
  "\<lbrakk>write_reg GPR_ref v\<rbrakk>\<^sub>S = write_regS GPR_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LO[liftState_simp]:
  "\<lbrakk>read_reg LO_ref\<rbrakk>\<^sub>S = read_regS LO_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LO[liftState_simp]:
  "\<lbrakk>write_reg LO_ref v\<rbrakk>\<^sub>S = write_regS LO_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_HI[liftState_simp]:
  "\<lbrakk>read_reg HI_ref\<rbrakk>\<^sub>S = read_regS HI_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_HI[liftState_simp]:
  "\<lbrakk>write_reg HI_ref v\<rbrakk>\<^sub>S = write_regS HI_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_DelayedPC[liftState_simp]:
  "\<lbrakk>read_reg DelayedPC_ref\<rbrakk>\<^sub>S = read_regS DelayedPC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_DelayedPC[liftState_simp]:
  "\<lbrakk>write_reg DelayedPC_ref v\<rbrakk>\<^sub>S = write_regS DelayedPC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_BranchPending[liftState_simp]:
  "\<lbrakk>read_reg BranchPending_ref\<rbrakk>\<^sub>S = read_regS BranchPending_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_BranchPending[liftState_simp]:
  "\<lbrakk>write_reg BranchPending_ref v\<rbrakk>\<^sub>S = write_regS BranchPending_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_InBranchDelay[liftState_simp]:
  "\<lbrakk>read_reg InBranchDelay_ref\<rbrakk>\<^sub>S = read_regS InBranchDelay_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_InBranchDelay[liftState_simp]:
  "\<lbrakk>write_reg InBranchDelay_ref v\<rbrakk>\<^sub>S = write_regS InBranchDelay_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_NextInBranchDelay[liftState_simp]:
  "\<lbrakk>read_reg NextInBranchDelay_ref\<rbrakk>\<^sub>S = read_regS NextInBranchDelay_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_NextInBranchDelay[liftState_simp]:
  "\<lbrakk>write_reg NextInBranchDelay_ref v\<rbrakk>\<^sub>S = write_regS NextInBranchDelay_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0Status[liftState_simp]:
  "\<lbrakk>read_reg CP0Status_ref\<rbrakk>\<^sub>S = read_regS CP0Status_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0Status[liftState_simp]:
  "\<lbrakk>write_reg CP0Status_ref v\<rbrakk>\<^sub>S = write_regS CP0Status_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0ConfigK0[liftState_simp]:
  "\<lbrakk>read_reg CP0ConfigK0_ref\<rbrakk>\<^sub>S = read_regS CP0ConfigK0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0ConfigK0[liftState_simp]:
  "\<lbrakk>write_reg CP0ConfigK0_ref v\<rbrakk>\<^sub>S = write_regS CP0ConfigK0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0UserLocal[liftState_simp]:
  "\<lbrakk>read_reg CP0UserLocal_ref\<rbrakk>\<^sub>S = read_regS CP0UserLocal_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0UserLocal[liftState_simp]:
  "\<lbrakk>write_reg CP0UserLocal_ref v\<rbrakk>\<^sub>S = write_regS CP0UserLocal_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0HWREna[liftState_simp]:
  "\<lbrakk>read_reg CP0HWREna_ref\<rbrakk>\<^sub>S = read_regS CP0HWREna_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0HWREna[liftState_simp]:
  "\<lbrakk>write_reg CP0HWREna_ref v\<rbrakk>\<^sub>S = write_regS CP0HWREna_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0Count[liftState_simp]:
  "\<lbrakk>read_reg CP0Count_ref\<rbrakk>\<^sub>S = read_regS CP0Count_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0Count[liftState_simp]:
  "\<lbrakk>write_reg CP0Count_ref v\<rbrakk>\<^sub>S = write_regS CP0Count_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0BadInstrP[liftState_simp]:
  "\<lbrakk>read_reg CP0BadInstrP_ref\<rbrakk>\<^sub>S = read_regS CP0BadInstrP_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0BadInstrP[liftState_simp]:
  "\<lbrakk>write_reg CP0BadInstrP_ref v\<rbrakk>\<^sub>S = write_regS CP0BadInstrP_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0BadInstr[liftState_simp]:
  "\<lbrakk>read_reg CP0BadInstr_ref\<rbrakk>\<^sub>S = read_regS CP0BadInstr_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0BadInstr[liftState_simp]:
  "\<lbrakk>write_reg CP0BadInstr_ref v\<rbrakk>\<^sub>S = write_regS CP0BadInstr_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_LastInstrBits[liftState_simp]:
  "\<lbrakk>read_reg LastInstrBits_ref\<rbrakk>\<^sub>S = read_regS LastInstrBits_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_LastInstrBits[liftState_simp]:
  "\<lbrakk>write_reg LastInstrBits_ref v\<rbrakk>\<^sub>S = write_regS LastInstrBits_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CurrentInstrBits[liftState_simp]:
  "\<lbrakk>read_reg CurrentInstrBits_ref\<rbrakk>\<^sub>S = read_regS CurrentInstrBits_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CurrentInstrBits[liftState_simp]:
  "\<lbrakk>write_reg CurrentInstrBits_ref v\<rbrakk>\<^sub>S = write_regS CurrentInstrBits_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0BadVAddr[liftState_simp]:
  "\<lbrakk>read_reg CP0BadVAddr_ref\<rbrakk>\<^sub>S = read_regS CP0BadVAddr_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0BadVAddr[liftState_simp]:
  "\<lbrakk>write_reg CP0BadVAddr_ref v\<rbrakk>\<^sub>S = write_regS CP0BadVAddr_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0LLAddr[liftState_simp]:
  "\<lbrakk>read_reg CP0LLAddr_ref\<rbrakk>\<^sub>S = read_regS CP0LLAddr_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0LLAddr[liftState_simp]:
  "\<lbrakk>write_reg CP0LLAddr_ref v\<rbrakk>\<^sub>S = write_regS CP0LLAddr_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0LLBit[liftState_simp]:
  "\<lbrakk>read_reg CP0LLBit_ref\<rbrakk>\<^sub>S = read_regS CP0LLBit_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0LLBit[liftState_simp]:
  "\<lbrakk>write_reg CP0LLBit_ref v\<rbrakk>\<^sub>S = write_regS CP0LLBit_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0Cause[liftState_simp]:
  "\<lbrakk>read_reg CP0Cause_ref\<rbrakk>\<^sub>S = read_regS CP0Cause_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0Cause[liftState_simp]:
  "\<lbrakk>write_reg CP0Cause_ref v\<rbrakk>\<^sub>S = write_regS CP0Cause_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_CP0Compare[liftState_simp]:
  "\<lbrakk>read_reg CP0Compare_ref\<rbrakk>\<^sub>S = read_regS CP0Compare_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_CP0Compare[liftState_simp]:
  "\<lbrakk>write_reg CP0Compare_ref v\<rbrakk>\<^sub>S = write_regS CP0Compare_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry63[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry63_ref\<rbrakk>\<^sub>S = read_regS TLBEntry63_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry63[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry63_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry63_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry62[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry62_ref\<rbrakk>\<^sub>S = read_regS TLBEntry62_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry62[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry62_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry62_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry61[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry61_ref\<rbrakk>\<^sub>S = read_regS TLBEntry61_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry61[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry61_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry61_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry60[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry60_ref\<rbrakk>\<^sub>S = read_regS TLBEntry60_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry60[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry60_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry60_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry59[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry59_ref\<rbrakk>\<^sub>S = read_regS TLBEntry59_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry59[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry59_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry59_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry58[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry58_ref\<rbrakk>\<^sub>S = read_regS TLBEntry58_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry58[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry58_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry58_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry57[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry57_ref\<rbrakk>\<^sub>S = read_regS TLBEntry57_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry57[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry57_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry57_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry56[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry56_ref\<rbrakk>\<^sub>S = read_regS TLBEntry56_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry56[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry56_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry56_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry55[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry55_ref\<rbrakk>\<^sub>S = read_regS TLBEntry55_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry55[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry55_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry55_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry54[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry54_ref\<rbrakk>\<^sub>S = read_regS TLBEntry54_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry54[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry54_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry54_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry53[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry53_ref\<rbrakk>\<^sub>S = read_regS TLBEntry53_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry53[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry53_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry53_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry52[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry52_ref\<rbrakk>\<^sub>S = read_regS TLBEntry52_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry52[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry52_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry52_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry51[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry51_ref\<rbrakk>\<^sub>S = read_regS TLBEntry51_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry51[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry51_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry51_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry50[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry50_ref\<rbrakk>\<^sub>S = read_regS TLBEntry50_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry50[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry50_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry50_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry49[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry49_ref\<rbrakk>\<^sub>S = read_regS TLBEntry49_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry49[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry49_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry49_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry48[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry48_ref\<rbrakk>\<^sub>S = read_regS TLBEntry48_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry48[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry48_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry48_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry47[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry47_ref\<rbrakk>\<^sub>S = read_regS TLBEntry47_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry47[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry47_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry47_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry46[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry46_ref\<rbrakk>\<^sub>S = read_regS TLBEntry46_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry46[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry46_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry46_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry45[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry45_ref\<rbrakk>\<^sub>S = read_regS TLBEntry45_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry45[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry45_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry45_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry44[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry44_ref\<rbrakk>\<^sub>S = read_regS TLBEntry44_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry44[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry44_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry44_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry43[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry43_ref\<rbrakk>\<^sub>S = read_regS TLBEntry43_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry43[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry43_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry43_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry42[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry42_ref\<rbrakk>\<^sub>S = read_regS TLBEntry42_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry42[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry42_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry42_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry41[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry41_ref\<rbrakk>\<^sub>S = read_regS TLBEntry41_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry41[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry41_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry41_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry40[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry40_ref\<rbrakk>\<^sub>S = read_regS TLBEntry40_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry40[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry40_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry40_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry39[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry39_ref\<rbrakk>\<^sub>S = read_regS TLBEntry39_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry39[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry39_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry39_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry38[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry38_ref\<rbrakk>\<^sub>S = read_regS TLBEntry38_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry38[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry38_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry38_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry37[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry37_ref\<rbrakk>\<^sub>S = read_regS TLBEntry37_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry37[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry37_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry37_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry36[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry36_ref\<rbrakk>\<^sub>S = read_regS TLBEntry36_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry36[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry36_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry36_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry35[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry35_ref\<rbrakk>\<^sub>S = read_regS TLBEntry35_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry35[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry35_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry35_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry34[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry34_ref\<rbrakk>\<^sub>S = read_regS TLBEntry34_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry34[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry34_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry34_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry33[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry33_ref\<rbrakk>\<^sub>S = read_regS TLBEntry33_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry33[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry33_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry33_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry32[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry32_ref\<rbrakk>\<^sub>S = read_regS TLBEntry32_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry32[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry32_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry32_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry31[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry31_ref\<rbrakk>\<^sub>S = read_regS TLBEntry31_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry31[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry31_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry31_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry30[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry30_ref\<rbrakk>\<^sub>S = read_regS TLBEntry30_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry30[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry30_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry30_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry29[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry29_ref\<rbrakk>\<^sub>S = read_regS TLBEntry29_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry29[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry29_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry29_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry28[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry28_ref\<rbrakk>\<^sub>S = read_regS TLBEntry28_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry28[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry28_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry28_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry27[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry27_ref\<rbrakk>\<^sub>S = read_regS TLBEntry27_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry27[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry27_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry27_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry26[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry26_ref\<rbrakk>\<^sub>S = read_regS TLBEntry26_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry26[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry26_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry26_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry25[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry25_ref\<rbrakk>\<^sub>S = read_regS TLBEntry25_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry25[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry25_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry25_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry24[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry24_ref\<rbrakk>\<^sub>S = read_regS TLBEntry24_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry24[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry24_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry24_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry23[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry23_ref\<rbrakk>\<^sub>S = read_regS TLBEntry23_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry23[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry23_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry23_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry22[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry22_ref\<rbrakk>\<^sub>S = read_regS TLBEntry22_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry22[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry22_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry22_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry21[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry21_ref\<rbrakk>\<^sub>S = read_regS TLBEntry21_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry21[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry21_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry21_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry20[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry20_ref\<rbrakk>\<^sub>S = read_regS TLBEntry20_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry20[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry20_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry20_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry19[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry19_ref\<rbrakk>\<^sub>S = read_regS TLBEntry19_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry19[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry19_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry19_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry18[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry18_ref\<rbrakk>\<^sub>S = read_regS TLBEntry18_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry18[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry18_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry18_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry17[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry17_ref\<rbrakk>\<^sub>S = read_regS TLBEntry17_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry17[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry17_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry17_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry16[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry16_ref\<rbrakk>\<^sub>S = read_regS TLBEntry16_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry16[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry16_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry16_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry15[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry15_ref\<rbrakk>\<^sub>S = read_regS TLBEntry15_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry15[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry15_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry15_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry14[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry14_ref\<rbrakk>\<^sub>S = read_regS TLBEntry14_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry14[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry14_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry14_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry13[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry13_ref\<rbrakk>\<^sub>S = read_regS TLBEntry13_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry13[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry13_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry13_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry12[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry12_ref\<rbrakk>\<^sub>S = read_regS TLBEntry12_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry12[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry12_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry12_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry11[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry11_ref\<rbrakk>\<^sub>S = read_regS TLBEntry11_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry11[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry11_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry11_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry10[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry10_ref\<rbrakk>\<^sub>S = read_regS TLBEntry10_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry10[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry10_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry10_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry09[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry09_ref\<rbrakk>\<^sub>S = read_regS TLBEntry09_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry09[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry09_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry09_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry08[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry08_ref\<rbrakk>\<^sub>S = read_regS TLBEntry08_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry08[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry08_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry08_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry07[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry07_ref\<rbrakk>\<^sub>S = read_regS TLBEntry07_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry07[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry07_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry07_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry06[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry06_ref\<rbrakk>\<^sub>S = read_regS TLBEntry06_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry06[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry06_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry06_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry05[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry05_ref\<rbrakk>\<^sub>S = read_regS TLBEntry05_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry05[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry05_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry05_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry04[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry04_ref\<rbrakk>\<^sub>S = read_regS TLBEntry04_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry04[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry04_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry04_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry03[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry03_ref\<rbrakk>\<^sub>S = read_regS TLBEntry03_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry03[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry03_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry03_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry02[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry02_ref\<rbrakk>\<^sub>S = read_regS TLBEntry02_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry02[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry02_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry02_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry01[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry01_ref\<rbrakk>\<^sub>S = read_regS TLBEntry01_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry01[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry01_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry01_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntry00[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry00_ref\<rbrakk>\<^sub>S = read_regS TLBEntry00_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntry00[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry00_ref v\<rbrakk>\<^sub>S = write_regS TLBEntry00_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBXContext[liftState_simp]:
  "\<lbrakk>read_reg TLBXContext_ref\<rbrakk>\<^sub>S = read_regS TLBXContext_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBXContext[liftState_simp]:
  "\<lbrakk>write_reg TLBXContext_ref v\<rbrakk>\<^sub>S = write_regS TLBXContext_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntryHi[liftState_simp]:
  "\<lbrakk>read_reg TLBEntryHi_ref\<rbrakk>\<^sub>S = read_regS TLBEntryHi_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntryHi[liftState_simp]:
  "\<lbrakk>write_reg TLBEntryHi_ref v\<rbrakk>\<^sub>S = write_regS TLBEntryHi_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBWired[liftState_simp]:
  "\<lbrakk>read_reg TLBWired_ref\<rbrakk>\<^sub>S = read_regS TLBWired_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBWired[liftState_simp]:
  "\<lbrakk>write_reg TLBWired_ref v\<rbrakk>\<^sub>S = write_regS TLBWired_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBPageMask[liftState_simp]:
  "\<lbrakk>read_reg TLBPageMask_ref\<rbrakk>\<^sub>S = read_regS TLBPageMask_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBPageMask[liftState_simp]:
  "\<lbrakk>write_reg TLBPageMask_ref v\<rbrakk>\<^sub>S = write_regS TLBPageMask_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBContext[liftState_simp]:
  "\<lbrakk>read_reg TLBContext_ref\<rbrakk>\<^sub>S = read_regS TLBContext_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBContext[liftState_simp]:
  "\<lbrakk>write_reg TLBContext_ref v\<rbrakk>\<^sub>S = write_regS TLBContext_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntryLo1[liftState_simp]:
  "\<lbrakk>read_reg TLBEntryLo1_ref\<rbrakk>\<^sub>S = read_regS TLBEntryLo1_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntryLo1[liftState_simp]:
  "\<lbrakk>write_reg TLBEntryLo1_ref v\<rbrakk>\<^sub>S = write_regS TLBEntryLo1_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBEntryLo0[liftState_simp]:
  "\<lbrakk>read_reg TLBEntryLo0_ref\<rbrakk>\<^sub>S = read_regS TLBEntryLo0_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBEntryLo0[liftState_simp]:
  "\<lbrakk>write_reg TLBEntryLo0_ref v\<rbrakk>\<^sub>S = write_regS TLBEntryLo0_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBRandom[liftState_simp]:
  "\<lbrakk>read_reg TLBRandom_ref\<rbrakk>\<^sub>S = read_regS TLBRandom_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBRandom[liftState_simp]:
  "\<lbrakk>write_reg TLBRandom_ref v\<rbrakk>\<^sub>S = write_regS TLBRandom_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBIndex[liftState_simp]:
  "\<lbrakk>read_reg TLBIndex_ref\<rbrakk>\<^sub>S = read_regS TLBIndex_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBIndex[liftState_simp]:
  "\<lbrakk>write_reg TLBIndex_ref v\<rbrakk>\<^sub>S = write_regS TLBIndex_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_TLBProbe[liftState_simp]:
  "\<lbrakk>read_reg TLBProbe_ref\<rbrakk>\<^sub>S = read_regS TLBProbe_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_TLBProbe[liftState_simp]:
  "\<lbrakk>write_reg TLBProbe_ref v\<rbrakk>\<^sub>S = write_regS TLBProbe_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_NextPC[liftState_simp]:
  "\<lbrakk>read_reg NextPC_ref\<rbrakk>\<^sub>S = read_regS NextPC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_NextPC[liftState_simp]:
  "\<lbrakk>write_reg NextPC_ref v\<rbrakk>\<^sub>S = write_regS NextPC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

lemma liftS_read_reg_PC[liftState_simp]:
  "\<lbrakk>read_reg PC_ref\<rbrakk>\<^sub>S = read_regS PC_ref"
  by (intro liftState_read_reg) (auto simp: register_defs)

lemma liftS_write_reg_PC[liftState_simp]:
  "\<lbrakk>write_reg PC_ref v\<rbrakk>\<^sub>S = write_regS PC_ref v"
  by (intro liftState_write_reg) (auto simp: register_defs)

end
