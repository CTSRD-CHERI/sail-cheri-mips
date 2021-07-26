Require Import Sail.Values.

(*

lemma while_domI:
  fixes V :: "'vars \<Rightarrow> nat"
  assumes "\<And>vars. cond vars \<Longrightarrow> V (body vars) < V vars"
  shows "while_dom (vars, cond, body)"
  by (induction vars rule: measure_induct_rule[where f = V])
     (use assms in \<open>auto intro: while.domintros\<close>)

lemma nat_of_int_nat_simps[simp]: "nat_of_int = nat" by (auto simp: nat_of_int_def)

termination reverse_endianness_list by (lexicographic_order simp add: drop_list_def)
declare reverse_endianness_list.simps[simp del]
declare take_list_def[simp]
declare drop_list_def[simp]
*)
Import ListNotations.
Require Program.Wf.

Lemma skipn_length T n (xs : list T) :
  n <> 0%nat ->
  xs <> [] ->
  (List.length (skipn n xs) < List.length xs)%nat.
revert n.
induction xs.
* congruence.
* destruct n.
  + congruence.
  + intros _ _. simpl.
    destruct xs.
    - destruct n; simpl; auto.
    - destruct n; auto.
      apply Nat.lt_lt_succ_r.
      apply IHxs; congruence.
Qed.

Program Fixpoint take_chunks {a} (n : nat) (xs : list a) {measure (List.length xs)} : list (list a) :=
  match xs with
  | [] => []
  | _ => match n with O => [] | _ => (firstn n xs)::take_chunks n (skipn n xs) end
  end.
Next Obligation.
apply skipn_length; auto.
Qed.

(*
lemma take_chunks_length_leq_n: "length xs \<le> n \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> take_chunks n xs = [xs]"
  by (cases n) auto

lemma take_chunks_append: "n dvd length a \<Longrightarrow> take_chunks n (a @ b) = take_chunks n a @ take_chunks n b"
  by (induction n a rule: take_chunks.induct) (auto simp: dvd_imp_le)

lemma Suc8_plus8: "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc x))))))) = 8 + x"
  by auto

lemma byte_chunks_take_chunks_8:
  assumes "8 dvd length xs"
  shows "byte_chunks xs = Some (take_chunks 8 xs)"
proof -
  have Suc8_plus8: "Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc x))))))) = 8 + x" for x
    by auto
  from assms show ?thesis
    by (induction xs rule: byte_chunks.induct) (auto simp: Suc8_plus8 nat_dvd_not_less)
qed

lemma reverse_endianness_list_rev_take_chunks:
  "reverse_endianness_list bits = List.concat (rev (take_chunks 8 bits))"
  by (induction "8 :: nat" bits rule: take_chunks.induct)
     (auto simp: reverse_endianness_list.simps)

lemma reverse_endianness_list_simps:
  "length bits \<le> 8 \<Longrightarrow> reverse_endianness_list bits = bits"
  "length bits > 8 \<Longrightarrow> reverse_endianness_list bits = reverse_endianness_list (drop 8 bits) @ take 8 bits"
  by (cases bits; auto simp: reverse_endianness_list_rev_take_chunks)+

lemma reverse_endianness_list_append:
  assumes "8 dvd length a"
  shows "reverse_endianness_list (a @ b) = reverse_endianness_list b @ reverse_endianness_list a"
  using assms by (auto simp: reverse_endianness_list_rev_take_chunks take_chunks_append)

lemma length_reverse_endianness_list[simp]:
  "length (reverse_endianness_list l) = length l"
  by (induction l rule: reverse_endianness_list.induct) (auto simp: reverse_endianness_list.simps)

lemma reverse_endianness_list_take_8[simp]:
  "reverse_endianness_list (take 8 bits) = take 8 bits"
  by (auto simp: reverse_endianness_list_simps)

lemma reverse_reverse_endianness_list[simp]:
  assumes "8 dvd length l"
  shows "reverse_endianness_list (reverse_endianness_list l) = l"
proof (use assms in \<open>induction l rule: reverse_endianness_list.induct[case_names Step]\<close>)
  case (Step bits)
  then show ?case
    by (auto simp: reverse_endianness_list.simps[of bits] reverse_endianness_list_append)
qed

declare repeat.simps[simp del]

lemma length_repeat[simp]: "length (repeat xs n) = nat n * length xs"
proof (induction xs n rule: repeat.induct[case_names Step])
  case (Step xs n)
  then show ?case unfolding repeat.simps[of xs n]
    by (auto simp del: mult_Suc simp: mult_Suc[symmetric])
qed

lemma nth_repeat:
  assumes "i < nat n * length xs"
  shows "repeat xs n ! i = xs ! (i mod length xs)"
proof (use assms in \<open>induction xs n arbitrary: i rule: repeat.induct[case_names Step]\<close>)
  case (Step xs n i)
  show ?case
    using Step.prems Step.IH[of "i - length xs"]
    unfolding repeat.simps[of xs n]
    by (auto simp: nth_append mod_geq[symmetric] nat_diff_distrib diff_mult_distrib)
qed

termination index_list
  by (relation "measure (\<lambda>(i, j, step). nat ((j - i + step) * sgn step))") auto

lemma index_list_Zero[simp]: "index_list i j 0 = []"
  by auto

lemma index_list_singleton[simp]: "n \<noteq> 0 \<Longrightarrow> index_list i i n = [i]"
  by auto

lemma index_list_simps:
  "0 < step \<Longrightarrow> from \<le> to \<Longrightarrow> index_list from to step = from # index_list (from + step) to step"
  "0 < step \<Longrightarrow> from > to \<Longrightarrow> index_list from to step = []"
  "0 > step \<Longrightarrow> from \<ge> to \<Longrightarrow> index_list from to step = from # index_list (from + step) to step"
  "0 > step \<Longrightarrow> from < to \<Longrightarrow> index_list from to step = []"
  by auto

lemma index_list_step1_upto[simp]: "index_list i j 1 = [i..j]"
  by (induction i j "1 :: int" rule: index_list.induct)
     (auto simp: index_list_simps upto.simps)

lemma length_upto[simp]: "i \<le> j \<Longrightarrow> length [i..j] = nat (j - i + 1)"
  by (induction i j rule: upto.induct) (auto simp: upto.simps)

lemma nth_upto[simp]: "i + int n \<le> j \<Longrightarrow> [i..j] ! n = i + int n"
  by (induction i j arbitrary: n rule: upto.induct)
     (auto simp: upto.simps nth_Cons split: nat.splits)

declare index_list.simps[simp del]

lemma genlist_add_upt[simp]: "genlist ((+) start) len = [start..<start + len]"
  by (auto simp: genlist_def map_add_upt add.commute cong: map_cong)

lemma just_list_map_Some[simp]: "just_list (map Some v) = Some v" by (induction v) auto

lemma just_list_None_iff[simp]: "just_list xs = None \<longleftrightarrow> None \<in> set xs"
  by (induction xs) (auto split: option.splits)

lemma just_list_None_member_None: "None \<in> set xs \<Longrightarrow> just_list xs = None"
  by auto

lemma just_list_Some_iff[simp]: "just_list xs = Some ys \<longleftrightarrow> xs = map Some ys"
  by (induction xs arbitrary: ys) (auto split: option.splits)

lemma just_list_cases:
  assumes "just_list xs = y"
  obtains (None) "None \<in> set xs" and "y = None"
        | (Some) ys where "xs = map Some ys" and "y = Some ys"
  using assms by (cases y) auto

lemma repeat_singleton_replicate[simp]:
  "repeat [x] n = replicate (nat n) x"
proof (induction n)
  case (nonneg n)
  have "nat (1 + int m) = Suc m" for m by auto
  then show ?case by (induction n) (auto simp: repeat.simps)
next
  case (neg n)
  then show ?case by (auto simp: repeat.simps)
qed

lemma and_bit_B1[simp]: "and_bit B1 b = b"
  by (cases b) auto

lemma and_bit_idem[simp]: "and_bit b b = b"
  by (cases b) auto

lemma and_bit_eq_iff:
  "and_bit b b' = B0 \<longleftrightarrow> (b = B0 \<or> b' = B0)"
  "and_bit b b' = BU \<longleftrightarrow> (b = BU \<or> b' = BU) \<and> b \<noteq> B0 \<and> b' \<noteq> B0"
  "and_bit b b' = B1 \<longleftrightarrow> (b = B1 \<and> b' = B1)"
  by (cases b; cases b'; auto)+

lemma foldl_and_bit_eq_iff:
  shows "foldl and_bit b bs = B0 \<longleftrightarrow> (b = B0 \<or> B0 \<in> set bs)" (is ?B0)
    and "foldl and_bit b bs = B1 \<longleftrightarrow> (b = B1 \<and> set bs \<subseteq> {B1})" (is ?B1)
    and "foldl and_bit b bs = BU \<longleftrightarrow> (b = BU \<or> BU \<in> set bs) \<and> b \<noteq> B0 \<and> B0 \<notin> set bs" (is ?BU)
proof -
  have "?B0 \<and> ?B1 \<and> ?BU"
  proof (induction bs arbitrary: b)
    case (Cons b' bs)
    show ?case using Cons.IH by (cases b; cases b') auto
  qed auto
  then show ?B0 and ?B1 and ?BU by auto
qed

lemma bool_of_bitU_simps[simp]:
  "bool_of_bitU B0 = Some False"
  "bool_of_bitU B1 = Some True"
  "bool_of_bitU BU = None"
  by (auto simp: bool_of_bitU_def)

lemma bitops_bitU_of_bool[simp]:
  "and_bit (bitU_of_bool x) (bitU_of_bool y) = bitU_of_bool (x \<and> y)"
  "or_bit (bitU_of_bool x) (bitU_of_bool y) = bitU_of_bool (x \<or> y)"
  "xor_bit (bitU_of_bool x) (bitU_of_bool y) = bitU_of_bool ((x \<or> y) \<and> \<not>(x \<and> y))"
  "not_bit (bitU_of_bool x) = bitU_of_bool (\<not>x)"
  "not_bit \<circ> bitU_of_bool = bitU_of_bool \<circ> Not"
  by (auto simp: bitU_of_bool_def not_bit_def)

lemma image_bitU_of_bool_B0_B1: "bitU_of_bool ` bs \<subseteq> {B0, B1}"
  by (auto simp: bitU_of_bool_def split: if_splits)

lemma bool_of_bitU_bitU_of_bool[simp]:
  "bool_of_bitU \<circ> bitU_of_bool = Some"
  "bool_of_bitU \<circ> (bitU_of_bool \<circ> f) = Some \<circ> f"
  "bool_of_bitU (bitU_of_bool x) = Some x"
  by (intro ext, auto simp: bool_of_bitU_def bitU_of_bool_def)+

abbreviation "BC_bitU_list \<equiv> instance_Sail2_values_Bitvector_list_dict instance_Sail2_values_BitU_Sail2_values_bitU_dict"
lemmas BC_bitU_list_def = instance_Sail2_values_Bitvector_list_dict_def instance_Sail2_values_BitU_Sail2_values_bitU_dict_def
abbreviation "BC_mword \<equiv> instance_Sail2_values_Bitvector_Machine_word_mword_dict"
lemmas BC_mword_defs = instance_Sail2_values_Bitvector_Machine_word_mword_dict_def
  access_mword_def access_mword_inc_def access_mword_dec_def
  (*update_mword_def update_mword_inc_def update_mword_dec_def*)
  subrange_list_def subrange_list_inc_def subrange_list_dec_def
  update_subrange_list_def update_subrange_list_inc_def update_subrange_list_dec_def

declare size_itself_int_def[simp]
declare size_itself_def[simp]
declare word_size[simp]

lemma int_of_mword_simps[simp]:
  "int_of_mword False w = uint w"
  "int_of_mword True w = sint w"
  "int_of_bv BC_mword False w = Some (uint w)"
  "int_of_bv BC_mword True w = Some (sint w)"
  by (auto simp: int_of_mword_def int_of_bv_def BC_mword_defs)

lemma BC_mword_simps[simp]:
  "unsigned_method BC_mword a = Some (uint a)"
  "signed_method BC_mword a = Some (sint a)"
  "length_method BC_mword (a :: ('a :: len) word) = int (LENGTH('a))"
  by (auto simp: BC_mword_defs)

lemma of_bits_mword_of_bl[simp]:
  assumes "just_list (map bool_of_bitU bus) = Some bs"
  shows "of_bits_method BC_mword bus = Some (of_bl bs)"
    and "of_bits_failwith BC_mword bus = of_bl bs"
  using assms by (auto simp: BC_mword_defs of_bits_failwith_def maybe_failwith_def)

lemma nat_of_bits_aux_bl_to_bin_aux:
  "nat_of_bools_aux acc bs = nat (bl_to_bin_aux bs (int acc))"
  by (induction acc bs rule: nat_of_bools_aux.induct)
     (auto simp: Bit_def intro!: arg_cong[where f = nat] arg_cong2[where f = bl_to_bin_aux] split: if_splits)

lemma nat_of_bits_bl_to_bin[simp]:
  "nat_of_bools bs = nat (bl_to_bin bs)"
  by (auto simp: nat_of_bools_def bl_to_bin_def nat_of_bits_aux_bl_to_bin_aux)

lemma unsigned_bits_of_mword[simp]:
  "unsigned_method BC_bitU_list (bits_of_method BC_mword a) = Some (uint a)"
  by (auto simp: BC_bitU_list_def BC_mword_defs unsigned_of_bits_def unsigned_of_bools_def)
*)
Definition mem_bytes_of_word {a} (w : mword a) : list (list bitU) :=
  List.rev (take_chunks 8 (bits_of w)).
(*
lemma mem_bytes_of_bits_mem_bytes_of_word[simp]:
  assumes "8 dvd LENGTH('a)"
  shows "mem_bytes_of_bits BC_mword (w :: 'a::len word) = Some (mem_bytes_of_word w)"
  using assms
  by (auto simp: mem_bytes_of_bits_def bytes_of_bits_def BC_mword_defs byte_chunks_take_chunks_8 mem_bytes_of_word_def)

lemma bits_of_bitU_list[simp]:
  "bits_of_method BC_bitU_list v = v"
  "of_bits_method BC_bitU_list v = Some v"
  by (auto simp: BC_bitU_list_def)

lemma subrange_list_inc_drop_take:
  "subrange_list_inc xs i j = drop (nat i) (take (nat (j + 1)) xs)"
  by (auto simp: subrange_list_inc_def split_at_def)

lemma subrange_list_dec_drop_take:
  assumes "i \<ge> 0" and "j \<ge> 0"
  shows "subrange_list_dec xs i j = drop (length xs - nat (i + 1)) (take (length xs - nat j) xs)"
  using assms unfolding subrange_list_dec_def
  by (auto simp: subrange_list_inc_drop_take add.commute diff_diff_add nat_minus_as_int)

lemma update_subrange_list_inc_drop_take:
  assumes "i \<ge> 0" and "j \<ge> i"
  shows "update_subrange_list_inc xs i j xs' = take (nat i) xs @ xs' @ drop (nat (j + 1)) xs"
  using assms unfolding update_subrange_list_inc_def
  by (auto simp: split_at_def min_def)

lemma update_subrange_list_dec_drop_take:
  assumes "j \<ge> 0" and "i \<ge> j"
  shows "update_subrange_list_dec xs i j xs' = take (length xs - nat (i + 1)) xs @ xs' @ drop (length xs - nat j) xs"
  using assms unfolding update_subrange_list_dec_def update_subrange_list_inc_def
  by (auto simp: split_at_def min_def Let_def add.commute diff_diff_add nat_minus_as_int)

declare access_list_inc_def[simp]

lemma access_list_dec_rev_nth:
  assumes "0 \<le> i" and "nat i < length xs"
  shows "access_list_dec xs i = rev xs ! (nat i)"
  using assms
  by (auto simp: access_list_dec_def rev_nth intro!: arg_cong2[where f = List.nth])

lemma access_bv_dec_mword[simp]:
  fixes w :: "('a::len) word"
  assumes "0 \<le> n" and "nat n < LENGTH('a)"
  shows "access_bv_dec BC_mword w n = bitU_of_bool (w !! (nat n))"
  using assms unfolding access_bv_dec_def access_list_def
  by (auto simp: access_list_dec_rev_nth BC_mword_defs rev_map test_bit_bl)

lemma access_list_dec_nth[simp]:
  assumes "0 \<le> i"
  shows "access_list_dec xs i = xs ! (length xs - nat (i + 1))"
  using assms
  by (auto simp: access_list_dec_def add.commute diff_diff_add nat_minus_as_int)

lemma update_list_inc_update[simp]:
  "update_list_inc xs n x = xs[nat n := x]"
  by (auto simp: update_list_inc_def)

lemma update_list_dec_update[simp]:
  "update_list_dec xs n x = xs[length xs - nat (n + 1) := x]"
  by (auto simp: update_list_dec_def add.commute diff_diff_add nat_minus_as_int)

lemma update_list_dec_update_rev:
  "0 \<le> n \<Longrightarrow> nat n < length xs \<Longrightarrow> update_list_dec xs n x = rev ((rev xs)[nat n := x])"
  by (auto simp: update_list_dec_def add.commute diff_diff_add nat_minus_as_int rev_update)

lemma access_list_dec_update_list_dec[simp]:
  "0 \<le> n \<Longrightarrow> nat n < length xs \<Longrightarrow> access_list_dec (update_list_dec xs n x) n = x"
  by (auto simp: access_list_dec_rev_nth update_list_dec_update_rev)

lemma bools_of_nat_aux_simps[simp]:
  "\<And>len. len \<le> 0 \<Longrightarrow> bools_of_nat_aux len x acc = acc"
  "\<And>len. bools_of_nat_aux (int (Suc len)) x acc =
     bools_of_nat_aux (int len) (x div 2) ((if x mod 2 = 1 then True else False) # acc)"
  by auto
declare bools_of_nat_aux.simps[simp del]

lemma bools_of_nat_aux_bin_to_bl_aux:
  "bools_of_nat_aux len n acc = bin_to_bl_aux (nat len) (int n) acc"
proof (cases len)
  case (nonneg len')
  show ?thesis unfolding nonneg
  proof (induction len' arbitrary: n acc)
    case (Suc len'' n acc)
    then show ?case
      using zmod_int[of n 2]
      by (auto simp del: of_nat_simps simp add: bin_rest_def bin_last_def zdiv_int)
  qed auto
qed auto

lemma bools_of_nat_bin_to_bl[simp]:
  "bools_of_nat len n = bin_to_bl (nat len) (int n)"
  by (auto simp: bools_of_nat_def bools_of_nat_aux_bin_to_bl_aux)

lemma add_one_bool_ignore_overflow_aux_rbl_succ[simp]:
  "add_one_bool_ignore_overflow_aux xs = rbl_succ xs"
  by (induction xs) auto

lemma add_one_bool_ignore_overflow_rbl_succ[simp]:
  "add_one_bool_ignore_overflow xs = rev (rbl_succ (rev xs))"
  unfolding add_one_bool_ignore_overflow_def by auto

lemma map_Not_bin_to_bl:
  "map Not (bin_to_bl_aux len n acc) = bin_to_bl_aux len (-n - 1) (map Not acc)"
proof (induction len arbitrary: n acc)
  case (Suc len n acc)
  moreover have "(- (n div 2) - 1) = ((-n - 1) div 2)" by auto
  moreover have "(n mod 2 = 0) = ((- n - 1) mod 2 = 1)" by presburger
  ultimately show ?case by (auto simp: bin_rest_def bin_last_def)
qed auto

lemma bools_of_int_bin_to_bl[simp]:
  "bools_of_int len n = bin_to_bl (nat len) n"
  by (auto simp: bools_of_int_def Let_def map_Not_bin_to_bl rbl_succ[unfolded bin_to_bl_def])

end
*)
