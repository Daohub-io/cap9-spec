section \<open>Preliminaries\<close>

theory Cap9
imports
  "HOL-Word.Word"
  "Word_Lib/Word_Lemmas"
begin

section \<open>Preliminaries\<close>

text \<open>
  Instantiate @{class len0} type class to extract lengths from word
  types avoiding repeated explicit numeric specification of the length.
\<close>

instantiation word :: (len) len begin
definition len_word[simp]: "len_of (_ :: 'a::len word itself) = LENGTH('a)"
instance by (standard, simp)
end

instantiation itself :: (len) size
begin
definition size_itself where [simp, code]: "size (n::'a::len itself) = LENGTH('a)"
instance ..
end

declare unat_word_ariths[simp] word_size[simp]

definition "width w \<equiv> LEAST n. unat w < 2 ^ n" for w :: "'a::len word"

lemma widthI[intro]: "\<lbrakk>\<And> u. u < n \<Longrightarrow> 2 ^ u \<le> unat w; unat w < 2 ^ n\<rbrakk> \<Longrightarrow> width w = n"
  unfolding width_def Least_def
  using not_le
  apply (intro the_equality, blast)
  by (meson nat_less_le)

lemma width_wf[simp]: "\<exists>! n. (\<forall> u < n. 2 ^ u \<le> unat w) \<and> unat w < 2 ^ n"
  (is "?Ex1 (unat w)")
proof (induction ("unat w"))
  case 0
  show "?Ex1 0" by (intro ex1I[of _ 0], auto)
next
  case (Suc x)
  then obtain n where x:"(\<forall>u<n. 2 ^ u \<le> x) \<and> x < 2 ^ n " by auto
  show  "?Ex1 (Suc x)"
  proof (cases "Suc x < 2 ^ n")
    case True
    thus "?Ex1 (Suc x)"
      using x
      apply (intro ex1I[of _ "n"], auto)
      by (meson Suc_lessD leD linorder_neqE_nat)
  next
    case False
    thus "?Ex1 (Suc x)"
      using x
      apply (intro ex1I[of _ "Suc n"], auto simp add: less_Suc_eq)
      apply (intro antisym)
       apply (metis One_nat_def Suc_lessI Suc_n_not_le_n leI numeral_2_eq_2 power_increasing_iff)
      by (metis Suc_lessD le_antisym not_le not_less_eq_eq)
  qed
qed

lemma width_iff[iff]: "(width w = n) = ((\<forall> u < n. 2 ^ u \<le> unat w) \<and> unat w < 2 ^ n)"
  using width_wf widthI by metis

lemma width_le_size: "width x \<le> size x"
proof-
  {
    assume "size x < width x"
    hence "2 ^ size x \<le> unat x" using width_iff by metis
    hence "2 ^ size x \<le> uint x" unfolding unat_def by simp
  }
  thus ?thesis using uint_range_size[of x] by (force simp del:word_size)
qed

lemma width_le_size'[simp]: "size x \<le> n \<Longrightarrow> width x \<le> n" by (insert width_le_size[of x], simp)

lemma nth_width_high[simp]: "width x \<le> i \<Longrightarrow> \<not> x !! i"
proof (cases "i < size x")
  case False
  thus ?thesis by (simp add: test_bit_bin')
next
  case True
  hence "(x < 2 ^ i) = (unat x < 2 ^ i)"
    unfolding unat_def
    using word_2p_lem by fastforce
  moreover assume "width x \<le> i"
  then obtain n where "unat x < 2 ^ n" and "n \<le> i" using width_iff by metis
  hence "unat x < 2 ^ i"
    by (meson le_less_trans nat_power_less_imp_less not_less zero_less_numeral)
  ultimately show ?thesis using bang_is_le by force
qed

lemma width_zero[iff]: "(width x = 0) = (x = 0)"
proof
  show "width x = 0 \<Longrightarrow> x = 0" using nth_width_high[of x] word_eq_iff[of x 0] nth_0 by (metis le0)
  show "x = 0 \<Longrightarrow> width x = 0" by simp
qed

lemma width_zero'[simp]: "width 0 = 0" by simp

lemma width_one[simp]: "width 1 = 1" by simp

lemma high_zeros_less: "(\<forall> i \<ge> u. \<not> x !! i) \<Longrightarrow> unat x < 2 ^ u"
  (is "?high \<Longrightarrow> _") for x :: "'a::len word"
proof-
  assume ?high
  have size:"size (mask u :: 'a word) = size x" by simp
  {
    fix i
    from \<open>?high\<close> have "(x AND mask u) !! i = x !! i"
      using nth_mask[of u i] size test_bit_size[of x i]
      by (subst word_ao_nth) (elim allE[of _ i], auto)
  }
  with \<open>?high\<close> have "x AND mask u = x" using word_eq_iff by blast
  thus ?thesis unfolding unat_def using mask_eq_iff by auto
qed

lemma nth_width_msb[simp]: "x \<noteq> 0 \<Longrightarrow> x !! (width x - 1)"
proof (rule ccontr)
  fix x :: "'a word"
  assume "x \<noteq> 0"
  hence width:"width x > 0" using width_zero by fastforce
  assume "\<not> x !! (width x - 1)"
  with width have "\<forall> i \<ge> width x - 1. \<not> x !! i"
    using nth_width_high[of x] antisym_conv2 by fastforce
  hence "unat x < 2 ^ (width x - 1)" using high_zeros_less[of "width x - 1" x] by simp
  moreover from width have "unat x \<ge> 2 ^ (width x - 1)" using width_iff[of x "width x"] by simp
  ultimately show False by simp
qed

lemma width_iff': "((\<forall> i > u. \<not> x !! i) \<and> x !! u) = (width x = Suc u)"
proof (rule; (elim conjE | intro conjI))
  assume "x !! u" and "\<forall> i > u. \<not> x !! i"
  show "width x = Suc u"
  proof (rule antisym)
    from \<open>x !! u\<close> show "width x \<ge> Suc u" using not_less nth_width_high by force
    from \<open>x !! u\<close> have "x \<noteq> 0" by auto
    with \<open>\<forall> i > u. \<not> x !! i\<close> have "width x - 1 \<le> u" using not_less nth_width_msb by metis
    thus "width x \<le> Suc u" by simp
  qed
next
  assume "width x = Suc u"
  show "\<forall>i>u. \<not> x !! i" by (simp add:\<open>width x = Suc u\<close>)
  from \<open>width x = Suc u\<close> show "x !! u" using nth_width_msb width_zero
    by (metis diff_Suc_1 old.nat.distinct(2))
qed

lemma width_word_log2: "x \<noteq> 0 \<Longrightarrow> width x = Suc (word_log2 x)"
  using word_log2_nth_same word_log2_nth_not_set width_iff' test_bit_size
  by metis

lemma width_ucast[OF refl, simp]: "uc = ucast \<Longrightarrow> is_up uc \<Longrightarrow> width (uc x) = width x"
  by (metis uint_up_ucast unat_def width_def)

lemma width_ucast'[OF refl, simp]:
  "uc = ucast \<Longrightarrow> width x \<le> size (uc x) \<Longrightarrow> width (uc x) = width x"
proof-
  have "unat x < 2 ^ width x" unfolding width_def by (rule LeastI_ex, auto)
  moreover assume "width x \<le> size (uc x)"
  ultimately have "unat x < 2 ^ size (uc x)" by (simp add: less_le_trans)
  moreover assume "uc = ucast"
  ultimately have "unat x = unat (uc x)" by (metis unat_ucast mod_less word_size)
  thus ?thesis unfolding width_def by simp
qed

lemma width_lshift[simp]:
  "\<lbrakk>x \<noteq> 0; n \<le> size x - width x\<rbrakk> \<Longrightarrow> width (x << n) = width x + n"
  (is "\<lbrakk>_; ?nbound\<rbrakk> \<Longrightarrow> _")
proof-
  assume "x \<noteq> 0"
  hence 0:"width x = Suc (width x - 1)" using width_zero by (metis Suc_pred' neq0_conv)
  from \<open>x \<noteq> 0\<close> have 1:"width x > 0" by (auto intro:gr_zeroI)
  assume ?nbound
  {
    fix i
    from \<open>?nbound\<close> have "i \<ge> size x \<Longrightarrow> \<not> x !! (i - n)" by (auto simp add:le_diff_conv2)
    hence "(x << n) !! i = (n \<le> i \<and> x !! (i - n))" using nth_shiftl'[of x n i] by auto
  } note corr = this
  hence "\<forall> i > width x + n - 1. \<not> (x << n) !! i" by auto
  moreover from corr have "(x << n) !! (width x + n - 1)"
    using width_iff'[of "width x - 1" x] 1
    by auto
  ultimately have "width (x << n) = Suc (width x + n - 1)" using width_iff' by auto
  thus ?thesis using 0 by simp
qed

lemma width_lshift'[simp]: "n \<le> size x - width x \<Longrightarrow> width (x << n) \<le> width x + n"
  using width_zero width_lshift shiftl_0 by (metis eq_iff le0)

lemma width_or[simp]: "width (x OR y) = max (width x) (width y)"
proof-
  {
    fix a b
    assume "width x = Suc a" and "width y = Suc b"
    hence "width (x OR y) = Suc (max a b)"
      using width_iff' word_ao_nth[of x y] max_less_iff_conj[of "a" "b"]
      by (metis (no_types) max_def)
  } note succs = this
  thus ?thesis
  proof (cases "width x = 0 \<or> width y = 0")
    case True
    thus ?thesis using width_zero word_log_esimps(3,9) by (metis max_0L max_0R)
  next
    case False
    with succs show ?thesis by (metis max_Suc_Suc not0_implies_Suc)
  qed
qed

definition rpad where "rpad x \<equiv> x << size x - width x"

lemma rpad_low[simp]: "i < size x - width x \<Longrightarrow> \<not> (rpad x) !! i"
  unfolding rpad_def by (simp add:nth_shiftl)

lemma rpad_high[simp]:
  "size x - width x \<le> i \<Longrightarrow> (rpad x) !! i = x !! (i + width x - size x)"
  (is "i \<ge> ?bound \<Longrightarrow> ?goal i")
proof-
  fix i
  assume "i \<ge> ?bound"
  moreover have "i + width x - size x = i - ?bound" by simp
  moreover have "x !! (i + width x - size x) \<Longrightarrow> i < size x" by (rule ccontr, auto)
  ultimately show "?goal i"
    unfolding rpad_def
    by (subst nth_shiftl', metis)
qed

lemma rpad_inj: "width x = width y \<Longrightarrow> rpad x = rpad y \<Longrightarrow> x = y"
  unfolding inj_def word_eq_iff
proof (intro allI impI)
  fix x y :: "'a word" and i
  assume "width x = width y"
  assume "\<forall>j < LENGTH('a). rpad x !! j = rpad y !! j"
  hence "\<And> j. rpad x !! j = rpad y !! j" using test_bit_bin by blast
  from this[of "i + size x - width x"] show "x !! i = y !! i"
    using width_le_size[of x] by (simp add:\<open>width x = width y\<close>)
qed

definition pad_join :: "'a::len word \<Rightarrow> 'c::len itself \<Rightarrow> 'b::len word \<Rightarrow> 'c word"
  ("_ \<diamond>\<^bsub>_\<^esub> _" [58, 1000, 59] 58) where
  "x \<diamond>\<^bsub>l\<^esub> y \<equiv> rpad (ucast x) OR ucast y"

notation (input) pad_join ("_ \<diamond>\<^sub>_ _" [58, 1000, 59] 58)

abbreviation ucastl ("'(ucast')\<^bsub>_\<^esub> _" [1000, 100] 100) where
  "(ucast)\<^bsub>l\<^esub> a \<equiv> ucast a :: 'b word" for l :: "'b::len0 itself"

notation (input) ucastl ("'(ucast')\<^sub>_ _" [1000, 100] 100)

lemma pad_join_high:
  "\<lbrakk>width a \<le> size l; width b \<le> size l - width a; size l - width a \<le> i\<rbrakk>
   \<Longrightarrow> (a \<diamond>\<^sub>l b) !! i = a !! (i + width a - size l)"
  unfolding pad_join_def
  using nth_ucast nth_width_high by fastforce
 
lemma pad_join_high'[simp]:
  "\<lbrakk>width a \<le> size l; width b \<le> size l - width a\<rbrakk> \<Longrightarrow> a !! i = (a \<diamond>\<^sub>l b) !! (i + size l - width a)"
  using pad_join_high[of a l b "i + size l - width a"] by simp

lemma pad_join_mid[simp]:
  "\<lbrakk>width a \<le> size l; width b \<le> size l - width a; width b \<le> i; i < size l - width a\<rbrakk>
   \<Longrightarrow> \<not> (a \<diamond>\<^sub>l b) !! i"
  unfolding pad_join_def by auto

lemma pad_join_low[simp]:
  "\<lbrakk>width a \<le> size l; width b \<le> size l - width a; i < width b\<rbrakk> \<Longrightarrow> (a \<diamond>\<^sub>l b) !! i = b !! i"
  unfolding pad_join_def by (auto simp add: nth_ucast)

lemma pad_join_inj:
  assumes eq:"a \<diamond>\<^sub>l b = c \<diamond>\<^sub>l d"
  assumes width_al: "width a \<le> size l"
  assumes width_ba:"width b \<le> size l - width a"
  assumes width_dc:"width d \<le> size l - width c"
  assumes eq_width:"width a = width c"
  shows   "a = c" and "b = d"
proof-
  from eq have eq':"\<And>j. (a \<diamond>\<^sub>l b) !! j = (c \<diamond>\<^sub>l d) !! j"
    using test_bit_bin unfolding word_eq_iff by blast
  moreover from width_al and width_ba
  have "\<And> i. a !! i = (a \<diamond>\<^sub>l b) !! (i + size l - width a)" by simp
  moreover from width_al eq_width width_dc
  have "\<And> i. c !! i = (c \<diamond>\<^sub>l d) !! (i + size l - width c)" by simp
  ultimately show "a = c" using eq_width unfolding word_eq_iff by metis

  {
    fix n
    from width_ba have "n < width b \<Longrightarrow> b !! n = (a \<diamond>\<^sub>l b) !! n" by simp
    moreover from width_dc have "n < width d \<Longrightarrow> d !! n = (c \<diamond>\<^sub>l d) !! n" by simp
    moreover have "n \<ge> width b \<Longrightarrow> \<not> b !! n" and "n \<ge> width d \<Longrightarrow> \<not> d !! n" by auto
    ultimately have "b !! n = d !! n"
      using eq'[of n] width_ba width_dc eq_width
        pad_join_mid[of a l b n, OF width_al width_ba]
        pad_join_mid[of c l d n, OF width_al[simplified eq_width] width_dc]
      by (metis leI less_le_trans)
  }
  thus "b = d" unfolding word_eq_iff by simp
qed

lemma pad_join_inj'[dest!]:
 "\<lbrakk>a \<diamond>\<^sub>l b = c \<diamond>\<^sub>l d;
   width a \<le> size l;
   width b \<le> size l - width a;
   width d \<le> size l - width c;
   width a = width c\<rbrakk> \<Longrightarrow> a = c \<and> b = d"
  apply (rule conjI)
  subgoal by (frule (4) pad_join_inj(1))
  by (frule (4) pad_join_inj(2))

definition join :: "'a::len word \<Rightarrow> 'c::len itself \<Rightarrow> nat \<Rightarrow> 'b::len word \<Rightarrow> 'c word"
  ("_ \<^bsub>_\<^esub>\<Join>\<^bsub>_\<^esub> _" [60,1000,1000,59] 59) where
  "(a \<^bsub>l\<^esub>\<Join>\<^bsub>n\<^esub> b) \<equiv> (ucast a << n) OR (ucast b)"

notation (input) join ("_ \<^sub>_\<Join>\<^sub>_ _" [60,1000,1000,59] 59)

lemma width_join:
  "\<lbrakk>width a + n \<le> size l; width b \<le> n\<rbrakk> \<Longrightarrow> width (a \<^sub>l\<Join>\<^sub>n b) \<le> width a + n"
  (is "\<lbrakk>?abound; ?bbound\<rbrakk> \<Longrightarrow> _")
proof-
  assume ?abound and ?bbound
  moreover hence "width b \<le> size l" by simp
  ultimately show ?thesis
    using width_lshift'[of n "(ucast)\<^sub>l a"]
    unfolding join_def
    by simp
qed

lemma width_join'[simp]:
  "\<lbrakk>width a + n \<le> size l; width b \<le> n; width a + n \<le> q\<rbrakk> \<Longrightarrow> width (a \<^sub>l\<Join>\<^sub>n b) \<le> q"
  by (drule (1) width_join, simp)

lemma join_high[simp]:
  "\<lbrakk>width a + n \<le> size l; width b \<le> n; width a + n \<le> i\<rbrakk> \<Longrightarrow> \<not> (a \<^sub>l\<Join>\<^sub>n b) !! i"
  by (drule (1) width_join, simp)

lemma join_mid:
  "\<lbrakk>width a + n \<le> size l; width b \<le> n; n \<le> i; i < width a + n\<rbrakk> \<Longrightarrow> (a \<^sub>l\<Join>\<^sub>n b) !! i = a !! (i - n)"
  apply (subgoal_tac "i < size ((ucast)\<^sub>l a) \<and> size ((ucast)\<^sub>l a) = size l")
  unfolding join_def
  using word_ao_nth nth_ucast nth_width_high nth_shiftl'
   apply (metis less_imp_diff_less order_trans word_size)
  by simp

lemma join_mid'[simp]:
  "\<lbrakk>width a + n \<le> size l; width b \<le> n\<rbrakk> \<Longrightarrow> a !! i = (a \<^sub>l\<Join>\<^sub>n b) !! (i + n)"
  using join_mid[of a n l b "i + n"] nth_width_high[of a i] join_high[of a n l b "i + n"]
  by force

lemma join_low[simp]:
  "\<lbrakk>width a + n \<le> size l; width b \<le> n; i < n\<rbrakk> \<Longrightarrow> (a \<^sub>l\<Join>\<^sub>n b) !! i = b !! i"
  unfolding join_def
  by (simp add: nth_shiftl nth_ucast)

lemma join_inj:
  assumes eq:"a \<^sub>l\<Join>\<^sub>n b = c \<^sub>l\<Join>\<^sub>n d"
  assumes "width a + n \<le> size l" and "width b \<le> n"
  assumes "width c + n \<le> size l" and "width d \<le> n"
  shows   "a = c" and "b = d"
proof-
  from assms show "a = c" unfolding word_eq_iff using join_mid' eq by metis
  from assms show "b = d" unfolding word_eq_iff using join_low nth_width_high
    by (metis eq less_le_trans not_le)
qed

lemma join_inj'[dest!]:
  "\<lbrakk>a \<^sub>l\<Join>\<^sub>n b = c \<^sub>l\<Join>\<^sub>n d;
    width a + n \<le> size l; width b \<le> n;
    width c + n \<le> size l; width d \<le> n\<rbrakk> \<Longrightarrow> a = c \<and> b = d"
  apply (rule conjI)
  subgoal by (frule (4) join_inj(1))
  by (frule (4) join_inj(2))

text \<open>We start with some types and definitions that will be used later.\<close>

subsection \<open>Procedure keys\<close>

text \<open>
  Procedure keys are represented as 24-byte (192 bits) machine words.
  Keys will be used both in the abstract and concrete states.
\<close>

type_synonym word24 = "192 word"
type_synonym key = word24

text \<open>Byte is 8-bit machine word:\<close>
type_synonym byte = "8 word"

section \<open>Storage state\<close>

text \<open>32-byte machine words that are used to model keys and values of the storage.\<close>
type_synonym word32 = "256 word" (* 32 bytes *)

text \<open>
  Storage is a function that takes a 32-byte word (key) and returns another
  32-byte word (value).
\<close>
type_synonym storage = "word32 \<Rightarrow> word32"

abbreviation "len (_ :: 'a::len word itself) \<equiv> TYPE('a)"

no_notation join  ("_ \<^bsub>_\<^esub>\<Join>\<^bsub>_\<^esub> _" [60,1000,1000,59] 59)
no_notation (input) join ("_ \<^sub>_\<Join>\<^sub>_ _" [60,1000,1000,59] 59)

abbreviation join32 ("_ \<Join>\<^bsub>_\<^esub> _" [60,1000,59] 59) where
  "a \<Join>\<^bsub>n\<^esub> b \<equiv> join a (len TYPE(word32)) (n * 8) b"
abbreviation (output) join32_out ("_ \<Join>\<^bsub>_\<^esub> _" [60,1000,59] 59) where
  "join32_out a n b \<equiv> join a (TYPE(256)) n b"
notation (input) join32 ("_ \<Join>\<^sub>_ _" [60,1000,59] 59)

no_notation pad_join  ("_ \<diamond>\<^bsub>_\<^esub> _" [58,1000,59] 58)
no_notation (input) pad_join ("_ \<diamond>\<^sub>_ _" [58,1000,59] 58)

abbreviation pad_join32 ("_ \<diamond> _" [58,59] 58) where "a \<diamond> b \<equiv> pad_join a (len TYPE(word32)) b"
abbreviation (output) pad_join32_out ("_ \<diamond> _" [58,59] 58) where
  "pad_join32_out a b \<equiv> pad_join a (TYPE(256)) b"

no_notation floor ("\<lfloor>_\<rfloor>")

consts rep :: "'a \<Rightarrow> 'b word" ("\<lfloor>_\<rfloor>")

datatype capability =
    Call
  | Reg
  | Del
  | Entry
  | Write
  | Log
  | Gas

definition cap_type_rep :: "capability \<Rightarrow> byte" where
  "cap_type_rep c \<equiv> case c of 
      Call  \<Rightarrow> 0x3 
    | Reg   \<Rightarrow> 0x4
    | Del   \<Rightarrow> 0x5
    | Entry \<Rightarrow> 0x6
    | Write \<Rightarrow> 0x7
    | Log   \<Rightarrow> 0x8
    | Gas   \<Rightarrow> 0x9"

overloading
  rep_cap_type \<equiv> "rep :: capability \<Rightarrow> byte"
begin
  fun rep_cap_type :: "capability \<Rightarrow> byte" where "rep_cap_type r = cap_type_rep r"
end

lemmas cap_type = rep_cap_type.simps cap_type_rep_def

abbreviation (input) byte ("_\<^bsub>1\<^esub>" [1000] 1000) where "n\<^bsub>1\<^esub> \<equiv> n :: byte"

lemma cap_type_rng[simp]: "\<lfloor>c ::capability\<rfloor>\<^bsub>1\<^esub> \<in> {0x3..0x9}"
  unfolding cap_type by (simp split:capability.split)

lemma cap_type_inj[simp]: "\<lfloor>c\<^sub>1 :: capability\<rfloor>\<^bsub>1\<^esub> = \<lfloor>c\<^sub>2\<rfloor> \<Longrightarrow> c\<^sub>1 = c\<^sub>2"
  unfolding cap_type
  by (simp split:capability.splits)

lemma width_cap_type: "width (\<lfloor>x :: capability\<rfloor>\<^bsub>1\<^esub>+ 1) \<le> 4"
proof (rule ccontr, drule not_le_imp_less)
  assume "4 < width (\<lfloor>x\<rfloor>\<^bsub>1\<^esub> + 1)"
  moreover hence "(\<lfloor>x\<rfloor>\<^bsub>1\<^esub> + 1) !! (width (\<lfloor>x\<rfloor>\<^bsub>1\<^esub> + 1) - 1)" using nth_width_msb by force
  ultimately obtain n where "(\<lfloor>x\<rfloor>\<^bsub>1\<^esub> + 1) !! n" and "n \<ge> 4" by (metis le_step_down_nat nat_less_le)
  thus False unfolding cap_type by (simp split:capability.splits)
qed

lemma width_cap_type'[simp]: "4 \<le> n \<Longrightarrow> width (\<lfloor>x :: capability\<rfloor>\<^bsub>1\<^esub> + 1) \<le> n"
  using width_cap_type[of x] by simp

lemma cap_type_nonzero[simplified rep_cap_type.simps, simp]: "\<lfloor>x :: capability\<rfloor>\<^bsub>1\<^esub> \<noteq> 0"
  unfolding cap_type by (simp split:capability.splits)

typedef capability_index = "{x :: byte. x < 0xff}" morphisms cap_index_rep cap_index_abs
  by (intro exI[of _ "0"], simp)

overloading
  rep_cap_index \<equiv> "rep :: capability_index \<Rightarrow> byte"
begin
  fun rep_cap_index :: "capability_index \<Rightarrow> byte" where "rep_cap_index r = cap_index_rep r"
end

lemmas cap_index = rep_cap_index.simps cap_index_rep

lemma width_cap_index: "width (\<lfloor>x :: capability_index\<rfloor>\<^bsub>1\<^esub>+ 1) \<le> 8"  by simp

lemma width_cap_index'[simp]: "8 \<le> n \<Longrightarrow> width (\<lfloor>x :: capability_index\<rfloor>\<^bsub>1\<^esub> + 1) \<le> n" by simp

lemma cap_index_nonzero[simplified rep_cap_index.simps, simp]: "\<lfloor>x :: capability_index\<rfloor>\<^bsub>1\<^esub> + 1 \<noteq> 0"
  apply (insert cap_index[of x]) 
  unfolding cap_index
  using less_is_non_zero_p1 by auto

type_synonym capability_offset = byte

datatype data_offset =
  Addr
  | Index
  | Ncaps capability
  | Cap capability capability_index capability_offset

definition data_offset_rep :: "data_offset \<Rightarrow> word32" where
 "data_offset_rep off \<equiv> case off of
     Addr         \<Rightarrow> 0x00\<^bsub>1\<^esub> \<Join>\<^sub>2 0x00\<^bsub>1\<^esub>   \<Join>\<^sub>1 0x00\<^bsub>1\<^esub>
   | Index        \<Rightarrow> 0x00\<^bsub>1\<^esub> \<Join>\<^sub>2 0x00\<^bsub>1\<^esub>   \<Join>\<^sub>1 0x01\<^bsub>1\<^esub>
   | Ncaps ty     \<Rightarrow> \<lfloor>ty\<rfloor>\<^bsub>1\<^esub> \<Join>\<^sub>2 0x00\<^bsub>1\<^esub>   \<Join>\<^sub>1 0x00\<^bsub>1\<^esub>
   | Cap ty i off \<Rightarrow> \<lfloor>ty\<rfloor>\<^bsub>1\<^esub> \<Join>\<^sub>2 \<lfloor>i\<rfloor>\<^bsub>1\<^esub> + 1 \<Join>\<^sub>1 off"

overloading
  rep_data_offset \<equiv> "rep :: data_offset \<Rightarrow> word32"
begin
  fun rep_data_offset :: "data_offset \<Rightarrow> word32" where "rep_data_offset off = data_offset_rep off"
end

lemmas data_offset = rep_data_offset.simps data_offset_rep_def

abbreviation (input) word32 ("_\<^bsub>32\<^esub>" [1000] 1000) where "n\<^bsub>32\<^esub> \<equiv> n :: word32"

lemma data_offset_inj[simplified rep_data_offset.simps,simp]:
  "\<lfloor>d\<^sub>1 :: data_offset\<rfloor>\<^bsub>32\<^esub> = \<lfloor>d\<^sub>2 :: data_offset\<rfloor>\<^bsub>32\<^esub> \<Longrightarrow> d\<^sub>1 = d\<^sub>2"
  unfolding data_offset
  by (auto split:data_offset.splits simp add:cap_index_rep_inject)

datatype address =
   Heap_proc key data_offset
  | Nprocs
  | Proc_key nat
  | Kernel
  | Curr_proc
  | Entry_proc

abbreviation "pref \<equiv> 0xffffffff :: word32"

abbreviation "index i \<equiv> of_nat i :: key"

definition addr_rep :: "address \<Rightarrow> word32" where
  "addr_rep a \<equiv> case a of
    Heap_proc k ofs \<Rightarrow> pref \<Join>\<^sub>1 0x00\<^bsub>1\<^esub> \<diamond>      k  \<Join>\<^sub>3 \<lfloor>ofs\<rfloor>\<^bsub>32\<^esub>
  | Nprocs          \<Rightarrow> pref \<Join>\<^sub>1 0x01\<^bsub>1\<^esub> \<diamond> 0x00\<^bsub>1\<^esub> \<Join>\<^sub>3 0x00\<^bsub>1\<^esub> \<Join>\<^sub>2 0x00\<^bsub>1\<^esub> \<Join>\<^sub>1 0x00\<^bsub>1\<^esub>
  | Proc_key i      \<Rightarrow> pref \<Join>\<^sub>1 0x01\<^bsub>1\<^esub> \<diamond> index i \<Join>\<^sub>3 0x00\<^bsub>1\<^esub> \<Join>\<^sub>2 0x00\<^bsub>1\<^esub> \<Join>\<^sub>1 0x00\<^bsub>1\<^esub>
  | Kernel          \<Rightarrow> pref \<Join>\<^sub>1 0x02\<^bsub>1\<^esub> \<diamond> 0x00\<^bsub>1\<^esub> \<Join>\<^sub>3 0x00\<^bsub>1\<^esub> \<Join>\<^sub>2 0x00\<^bsub>1\<^esub> \<Join>\<^sub>1 0x00\<^bsub>1\<^esub>
  | Curr_proc       \<Rightarrow> pref \<Join>\<^sub>1 0x03\<^bsub>1\<^esub> \<diamond> 0x00\<^bsub>1\<^esub> \<Join>\<^sub>3 0x00\<^bsub>1\<^esub> \<Join>\<^sub>2 0x00\<^bsub>1\<^esub> \<Join>\<^sub>1 0x00\<^bsub>1\<^esub>
  | Entry_proc      \<Rightarrow> pref \<Join>\<^sub>1 0x04\<^bsub>1\<^esub> \<diamond> 0x00\<^bsub>1\<^esub> \<Join>\<^sub>3 0x00\<^bsub>1\<^esub> \<Join>\<^sub>2 0x00\<^bsub>1\<^esub> \<Join>\<^sub>1 0x00\<^bsub>1\<^esub>"

overloading
  rep_addr \<equiv> "rep :: address \<Rightarrow> word32"
begin
  fun rep_addr :: "address \<Rightarrow> word32" where "rep_addr off = addr_rep off"
end

lemmas address = rep_addr.simps addr_rep_def

lemma address_inj[simplified rep_addr.simps, simp]:
  "\<lfloor>a\<^sub>1 :: address\<rfloor>\<^bsub>32\<^esub> = \<lfloor>a\<^sub>2 :: address\<rfloor>\<^bsub>32\<^esub> \<Longrightarrow> a\<^sub>1 = a\<^sub>2"
  unfolding address
  apply (split address.splits)
       apply (split address.splits)
            apply (auto)[1]
  sorry

section \<open>Abstract state\<close>

text \<open>
  Abstract state is implemented as a record with a single component labeled "procs".
  This component is a mapping from the set of procedure keys to the
  direct product of procedure indexes and procedure data.
\<close>

record abs =
  keys      :: "key set"
  proc_id   :: "key \<Rightarrow> nat"

subsection \<open>Abbreviations\<close>

text \<open>
  Here we introduce some useful abbreviations that will simplify the expression of the abstract
  state properties.
\<close>

text \<open>Number of the procedures in the abstract state:\<close>
abbreviation "nprocs \<sigma> \<equiv> card (keys \<sigma>)"

text \<open>List of procedure indexes:\<close>
abbreviation "proc_ids \<sigma> \<equiv> {1..nprocs \<sigma>}"

text \<open>Maximum number of procedures in the abstract state:\<close>
abbreviation "max_nprocs \<equiv> 2 ^ LENGTH(key) - 1 :: nat"

subsubsection \<open>Well-formedness\<close>

text \<open>
  For each procedure key the following must be true:
  \begin{enumerate}
  \item corresponding procedure index on the interval from 1 to the number of procedures in
        the state;
  \item key is a valid hash of the procedure data;
  \item number of procedures in the state is smaller or equal to the maximum number.
  \end{enumerate}
\<close>

definition "proc_id_rng_wf \<sigma> \<equiv>
  (\<forall> k \<in> keys \<sigma>. proc_id \<sigma> k \<in> proc_ids \<sigma>) \<and>
  nprocs \<sigma> \<le> max_nprocs"

text \<open>Procedure indexes must be injective.\<close>
definition "procs_map_wf \<sigma> \<equiv> inj_on (proc_id \<sigma>) (keys \<sigma>)"

text \<open>Abstract state is well-formed if the previous two properties are satisfied.\<close>
definition abs_wf :: "abs \<Rightarrow> bool" ("\<turnstile> _" [60] 60) where
  "\<turnstile> \<sigma> \<equiv>
      proc_id_rng_wf \<sigma>
    \<and> procs_map_wf \<sigma>"

lemmas procs_rng_wf = abs_wf_def proc_id_rng_wf_def

lemmas procs_map_wf = abs_wf_def procs_map_wf_def

text \<open>Storage key that corresponds to the number of procedures in the list:\<close>
abbreviation nprocs_addr ("@nprocs") where "nprocs_addr \<equiv> 0xffffffff01 0...0 :: word32"

lemma "width (0xffffffff01 :: word32) = 5 * 8 " unfolding width_def Least_def
  apply (rule the_equality)
  apply simp

text \<open>Storage key that corresponds to the procedure key with index i:\<close>
definition proc_key_addr ("@proc'_key") where "@proc_key i \<equiv> @nprocs OR of_nat i"

text \<open>Procedure index that corresponds to some procedure key address:\<close>
definition id_of_proc_key_addr ("@proc'_key.id") where "@proc_key.id a \<equiv> unat (@nprocs XOR a)"

text \<open>Maximum number of procedures in the kernel, but in the form of a 32-byte machine word:\<close>
abbreviation "max_nprocs_word \<equiv> 2 ^ proc_id_len - 1 :: word32"

text \<open>Declare some lemmas as simplification rules:\<close>


text \<open>Storage address that corresponds to the procedure heap for a given procedure key:\<close>
abbreviation "proc_heap_mask \<equiv>  0xffffffff00 << (27 * 8) :: word32"
definition proc_heap_addr :: "key \<Rightarrow> word32" ("@proc'_heap") where
  "@proc_heap k \<equiv> proc_heap_mask OR ((ucast k) << (3 * 8))"

text \<open>Storage address that corresponds to the procedure address:\<close>
definition proc_addr_addr ("@proc'_addr") where "@proc_addr k \<equiv> @proc_heap k"

text \<open>Storage address that corresponds to the procedure index:\<close>
definition proc_id_addr ("@proc'_id") where "@proc_id k \<equiv> @proc_heap k OR 0x01"

text \<open>Procedure key that corresponds to some procedure index address:\<close>
definition proc_key_of_id_addr :: "word32 \<Rightarrow> key" ("@proc'_id.key") where
  "@proc_id.key a \<equiv> ucast (proc_heap_mask XOR a)"

text \<open>Storage address that corresponds to the number of capabilities of type @{text t}:\<close>
definition ncaps_addr :: "key \<Rightarrow> byte \<Rightarrow> word32" ("@ncaps") where
  "@ncaps k t \<equiv> @proc_heap k OR (ucast t << 2 * 8)"

text \<open>
  Storage address that corresponds to the capability of type @{text t},
  with index @{text "i - 1"},
  and offset @{text off} into that capability:
\<close>
definition proc_cap_addr :: "key \<Rightarrow> byte \<Rightarrow> byte \<Rightarrow> byte \<Rightarrow> word32" ("@proc'_cap") where
  "@proc_cap k t i off \<equiv> @proc_heap k OR (ucast t << 2 * 8) OR (ucast i << 8) OR ucast off"

subsection \<open>Lemmas\<close>

subsubsection \<open>Auxiliary lemmas about procedure key addresses\<close>

text \<open>Valid procedure id has all zeros in its higher bits.\<close>
lemma proc_id_high_zeros[simp]:
  "n \<le> max_nprocs_word \<Longrightarrow> \<forall>i\<in>{proc_id_len..<LENGTH(word32)}. \<not> n !! i"
  (is "?nbound \<Longrightarrow> \<forall>_ \<in> ?high. _")
proof
  fix i
  assume 0:"i \<in> ?high"
  from 0 have "2 ^ proc_id_len \<le> (2 :: nat) ^ i" by (simp add: numerals(2))
  moreover from 0 have "0 < (2 :: word32) ^ i"  by (subst word_2p_lem; simp)
  ultimately have "2 ^ proc_id_len \<le> (2 :: word32) ^ i"
    unfolding word_le_def
    by (subst (asm) of_nat_le_iff[symmetric], simp add:uint_2p)
  thus "?nbound \<Longrightarrow> \<not> n !! i"
    unfolding not_def
    by (intro impI) (drule bang_is_le, unat_arith)
qed

text \<open>Address of the \# of procedures has all zeros in its lower bits.\<close>
lemma nprocs_key_low_zeros[simp]: "\<forall>i\<in>{0..<proc_id_len}. \<not> @nprocs !! i"
  by (subst nth_shiftl, auto)

text \<open>
  Elimination (generalized split) rule for 32-byte words:
  a property holds on all bits if and only if it holds on the higher and lower bits.\<close>
lemma low_high_split:
   "(\<forall>n. P ((x :: word32) !! n)) =
    ((\<forall>n\<in>{0..<proc_id_len}. P (x !! n)) \<and>
     (\<forall>n\<in>{proc_id_len..<LENGTH(word32)}. P (x !! n)) \<and>
     P False)"
  (is "?left = ?right")
proof (intro iffI)
  have "\<not> x !! size x" using test_bit_size[of x "size x"] by blast
  hence "?left \<Longrightarrow> P False" by (metis (full_types))
  thus "?left \<Longrightarrow> ?right" by auto

  show "?right \<Longrightarrow> ?left" using test_bit_size[of x] by force
qed

text \<open>Computing procedure key address by its id is an invertible operation.\<close>
lemma id_of_key_addr_inv[simp]:
   "i \<le> max_nprocs \<Longrightarrow> @proc_key.id (@proc_key i) = i"
   (is "?ibound \<Longrightarrow> ?rev")
proof-
  assume 0:"?ibound"
  hence 1:"unat (of_nat i :: word32) = i"
    by (simp add: le_unat_uoi[where z=max_nprocs_word])
  hence "of_nat i \<le> max_nprocs_word"
    using 0
    by (simp add: word_le_nat_alt)
  hence "@nprocs XOR @nprocs OR (of_nat i) = of_nat i"
    using nprocs_key_low_zeros proc_id_high_zeros
    by (auto simp add: word_eq_iff word_ops_nth_size)
  thus "?rev"
    using 1
    unfolding proc_key_addr_def id_of_proc_key_addr_def
    by simp
qed

section \<open>Correspondence between abstract and storage states\<close>

text \<open>Number of procedures is stored by the corresponding address (@{text "@nprocs"}).\<close>
definition "models_nprocs s \<sigma> \<equiv> unat (s @nprocs) = nprocs \<sigma>"

text \<open>Each procedure key @{text k} is stored by the corresponding address
      (@{term "@proc_key k"}).\<close>
definition "models_proc_keys s \<sigma> \<equiv>
  \<forall> k \<in> proc_keys \<sigma>. s (@proc_key (proc_id \<sigma> k)) = ucast k"

text \<open>For each procedure key @{text k} its index is stored by the corresponding address
      (@{text "@proc_id k"}).\<close>
definition "models_proc_ids s \<sigma> \<equiv>
  \<forall> k \<in> proc_keys \<sigma>. unat (s (@proc_id k)) = proc_id \<sigma> k"

text \<open>A storage corresponds to the abstract state
     if and only if the above properties are satisfied.\<close>
definition models :: "storage \<Rightarrow> ('p :: proc_class) abs \<Rightarrow> bool" ("_ \<tturnstile> _" [65, 65] 65) where
  "s \<tturnstile> \<sigma> \<equiv>
    models_nprocs s \<sigma>
  \<and> models_proc_keys s \<sigma>
  \<and> models_proc_ids s \<sigma>"

lemmas models_nprocs = models_def models_nprocs_def
lemmas models_proc_keys = models_def models_proc_keys_def
lemmas models_proc_ids = models_def models_proc_ids_def

text \<open>In the following we aim to proof the existence of a storage corresponding to any
      well-formed abstract state (so that any well-formed abstract state can be encoded
      and stored). Then prove that the encoding is unambiguous.
\<close>

subsection \<open>Auxiliary definitions and lemmas\<close>

text \<open>An empty storage:\<close>
definition "zero_storage (_ :: word32) \<equiv> 0 :: word32"

text \<open>The set of all procedure key addresses:\<close>
definition proc_key_addrs ("@proc'_keys") where
  "@proc_keys \<sigma> \<equiv> { @proc_key (proc_id \<sigma> k) | k. k \<in> proc_keys \<sigma> }"

definition proc_id_addrs ("@proc'_ids") where "@proc_ids \<sigma> \<equiv> { @proc_id k | k. k \<in> proc_keys \<sigma> }"

datatype region =
    Nprocs
  | Proc_key nat
  | Proc_heap key

definition "nprocs_range \<equiv> {unat @nprocs}"
definition "proc_key_range n \<equiv> {unat @nprocs + n}"
definition "proc_heap_range k \<equiv> {unat (@proc_heap k)..unat (@proc_heap k) + 0xFFFF}"

lemma proc_heap_mask_low_zeros: "\<forall>i\<in>{0..<LENGTH(key) + 3 * 8}. \<not> proc_heap_mask !! i"
  by (subst nth_shiftl, auto)

lemma proc_key_lshift_high_zeros:
  "\<forall>i\<in>{LENGTH(key) + 3 * 8..LENGTH(word32)}. \<not> (ucast (k :: key) << (3 * 8) :: word32) !! i"
  by (auto simp add:nth_shiftl nth_ucast test_bit_bin[of k])

lemma proc_heap_mask_and_key_lshift: "proc_heap_mask AND (ucast (k :: key) << (3 * 8)) = 0"
  using proc_heap_mask_low_zeros proc_key_lshift_high_zeros
  by (auto simp add: word_eq_iff word_ao_nth)

lemma proc_heap_range_nat:
  "a \<in> proc_heap_range k =
    (let b = unat proc_heap_mask + unat k * 2 ^ (3 * 8) in a \<in> {b..b+0xFFFF})"
proof-
  let ?in_range = "\<lambda> x. x < 2 ^ LENGTH(word32)"
  have "is_up (ucast :: key \<Rightarrow> word32)"
    unfolding is_up_def source_size_def target_size_def by simp
  hence 0:"unat (ucast k :: word32) = unat k" unfolding unat_def by (simp add:uint_up_ucast)
  hence "?in_range (unat (ucast k :: word32) * 2 ^ (3 * 8))" by (unat_arith, simp)
  with 0 have 1:"unat k * 2 ^ (3 * 8) = unat ((ucast k :: word32) << (3 * 8))"
    by (simp add:unat_mult_lem shiftl_t2n)
  have "?in_range (unat proc_heap_mask + unat k * 2 ^ (3 * 8))" by (unat_arith, simp)
  with 1 have 2:"?in_range (unat proc_heap_mask + unat ((ucast k :: word32) << (3 * 8)))" by simp
  show ?thesis
    unfolding proc_heap_range_def proc_heap_addr_def Let_def
    apply (subst 1)+
    apply (subst iffD1[OF unat_add_lem 2[unfolded len_word], symmetric])+
    apply (subst (1 2) word_plus_and_or[symmetric])
    using word_plus_and_or[symmetric] proc_heap_mask_and_key_lshift by simp
qed

function region :: "word32 \<Rightarrow> region" where
  "unat a \<in> nprocs_range \<Longrightarrow> region a = Nprocs"
| "\<exists> n. unat a \<in> proc_key_range n \<Longrightarrow> region a = Proc_key (THE n. unat a \<in> proc_key_range n)"
| "\<exists> k. unat a \<in> proc_heap_range k \<Longrightarrow> region a = Proc_heap (THE k. unat a \<in> proc_heap_range k)"
  unfolding nprocs_range_def proc_key_range_def proc_heap_range_def


(* TODO: add some lemmas? *)

text \<open>Procedure id can be converted to a 32-byte word without overflow.\<close>
lemma proc_id_inv[simp]:
  "\<lbrakk>\<turnstile> \<sigma>; k \<in> proc_keys \<sigma>\<rbrakk> \<Longrightarrow> unat (of_nat (proc_id \<sigma> k) :: word32) = proc_id \<sigma> k"
  unfolding procs_rng_wf
  by (force intro:le_unat_uoi[where z=max_nprocs_word])

text \<open>Moreover, any procedure id is non-zero and bounded by the maximum available id
      (@{const max_nprocs_word}).\<close>
lemma proc_id_bounded[intro]:
  "\<lbrakk>\<turnstile> \<sigma>; k \<in> proc_keys \<sigma>\<rbrakk> \<Longrightarrow> of_nat (proc_id \<sigma> k) \<in> {0<..max_nprocs_word}"
  by (simp add:word_le_nat_alt word_less_nat_alt, force simp add:procs_rng_wf)

text \<open>Since it's non-zero, any procedure id has a non-zero bit in its lower part.\<close>
lemma proc_id_low_one:
  "n \<in> {0<..max_nprocs_word} \<Longrightarrow> \<exists>i\<in>{0..<proc_id_len}. n !! i"
  (is "?nbound \<Longrightarrow> _")
proof-
  assume 0:"?nbound"
  hence "\<not> ?thesis \<Longrightarrow> n = 0" by (auto simp add:inc_le intro!:word_eqI)
  moreover from 0 have "n \<noteq> 0" by auto
  ultimately show ?thesis by auto
qed

text \<open>And procedure key address is different from the address of the \# of procedures
      (@{text "@nprocs"}).\<close>
lemma proc_key_addr_neq_nprocs_key:
  "n \<in> {0<..max_nprocs_word} \<Longrightarrow> @nprocs OR n \<noteq> @nprocs"
  (is "?nbound \<Longrightarrow> _")
proof-
  assume 0:"?nbound"
  hence "\<exists> i\<in>{0..<proc_id_len}.(@nprocs !! i \<or> n  !! i) \<noteq> @nprocs !! i"
    using nprocs_key_low_zeros proc_id_low_one
    by fast
  thus ?thesis by (force simp add:word_eq_iff word_ao_nth)
qed

text \<open>Thus @{text "@nprocs"} doesn't belong to the set of procedure key addresses.\<close>
lemma nprocs_key_notin_proc_key_addrs: "\<turnstile> \<sigma> \<Longrightarrow> @nprocs \<notin> @proc_keys \<sigma>"
  using proc_id_bounded proc_key_addr_neq_nprocs_key
  unfolding proc_key_addrs_def proc_key_addr_def
  by auto

text \<open>Also procedure index address is different from the address of the \# of procedures
      (@{text "@nprocs"}).\<close>
lemma proc_id_addr_neq_nprocs_key: "@proc_id k \<noteq> @nprocs"
proof
  have 0: "\<not> @nprocs !! 0" by auto
  have 1: "@proc_id k !! 0" using lsb0 test_bit_1 unfolding proc_id_addr_def by blast
  assume "@proc_id k = @nprocs"
  hence "(@proc_id k !! 0) = (@nprocs !! 0)" by auto
  thus "False" using 0 1 by auto
qed

text \<open>Thus @{text "@nprocs"} doesn't belong to the set of procedure index addresses.\<close>
lemma nprocs_key_notin_proc_id_addrs: "\<turnstile> \<sigma> \<Longrightarrow> @nprocs \<notin> @proc_ids \<sigma>"
  unfolding proc_id_addrs_def
proof
  assume assms: "\<turnstile> \<sigma>" and "@nprocs \<in> {@proc_id k |k. k \<in> proc_keys \<sigma>}"
  hence "\<exists>k. @nprocs = @proc_id k \<and> k \<in> proc_keys \<sigma>" by blast
  then obtain k where " @nprocs = @proc_id k \<and> k \<in> proc_keys \<sigma>" by blast
  thus "False" using proc_id_addr_neq_nprocs_key assms by auto
qed

text \<open>The function mapping procedure id to the corresponding procedure key
      (in some abstract state):\<close>
definition proc_id_inv ("proc'_id\<inverse>") where "proc_id\<inverse> \<sigma> \<equiv> the_inv_into (proc_keys \<sigma>) (proc_id \<sigma>)"

text \<open>Invertibility of computing procedure id (by its key) in any abstract state:\<close>
lemma proc_key_of_id_inv[simp]: "\<lbrakk>\<turnstile>\<sigma>; k \<in> proc_keys \<sigma>\<rbrakk> \<Longrightarrow> proc_id\<inverse> \<sigma> (proc_id \<sigma> k) = k"
  unfolding procs_map_wf proc_id_inv_def
  using the_inv_into_f_f by fastforce

text \<open>For any valid procedure id in any well-formed abstract state there is a procedure key that
     corresponds to the id (this is not so trivial as we keep the reverse mapping in
     the abstract state, the proof is implicitly based on the pigeonhole principle).\<close>
lemma proc_key_exists: "\<lbrakk>\<turnstile>\<sigma>; i \<in> proc_ids \<sigma>\<rbrakk> \<Longrightarrow> \<exists> k \<in> proc_keys \<sigma>. proc_id \<sigma> k = i"
proof (rule ccontr, subst (asm) bex_simps(8))
  let ?rng = "{1 .. nprocs \<sigma>}"
  let ?prj = "proc_id \<sigma> ` proc_keys \<sigma>"
  assume "\<forall>k\<in>proc_keys \<sigma>. proc_id \<sigma> k \<noteq> i"
  hence 0:"i \<notin> ?prj"
    by auto
  assume "\<turnstile> \<sigma>"
  hence 1:"?prj \<subseteq> ?rng" and 2:"card ?prj = card ?rng"
    unfolding abs_wf_def procs_rng_wf_def procs_map_wf_def
    by (auto simp add: image_subset_iff card_image)
  assume *:"i\<in>?rng"
  have "card ?prj = card (?prj \<union> {i} - {i})"
    using 0 by simp
  also have "... < card (?prj \<union> {i})"
    by (rule card_Diff1_less, simp_all)
  also from * have "... \<le> card ?prj"
    using 1
    by (subst 2, intro card_mono, simp_all)
  finally show False ..
qed

text \<open>The function @{term "proc_id\<inverse>"} gives valid procedure ids.\<close>
lemma proc_key_of_id_in_keys[simp]: "\<lbrakk>\<turnstile>\<sigma>; i \<in> proc_ids \<sigma>\<rbrakk> \<Longrightarrow> proc_id\<inverse> \<sigma> i \<in> proc_keys \<sigma>"
  using proc_key_exists the_inv_into_into[of "proc_id \<sigma>" "proc_keys \<sigma>" i]
  unfolding proc_id_inv_def procs_map_wf
  by fast

text \<open>Invertibility of computing procedure key (by its id) in any abstract state:\<close>
lemma proc_key_of_id_inv'[simp]: "\<lbrakk>\<turnstile>\<sigma>; i \<in> proc_ids \<sigma>\<rbrakk> \<Longrightarrow> proc_id \<sigma> (proc_id\<inverse> \<sigma> i) = i"
  using proc_key_exists f_the_inv_into_f[of "proc_id \<sigma>" "proc_keys \<sigma>" i]
  unfolding proc_id_inv_def procs_map_wf
  by fast

subsection \<open>Any well-formed abstract state can be stored\<close>

text \<open>A mapping of addresses with specified (defined) values:\<close>
definition
  "con_wit_map \<sigma> :: _ \<rightharpoonup> word32 \<equiv>
        [@nprocs \<mapsto> of_nat (nprocs \<sigma>)]
     ++ (Some \<circ> ucast \<circ> proc_id\<inverse> \<sigma> \<circ> @proc_key.id) |` @proc_keys \<sigma>
     ++ (Some \<circ> ucast \<circ> @proc_id.key) |` @proc_ids \<sigma>"

text \<open>A sample storage extending the above mapping with default zero values:\<close>
definition "con_wit \<sigma> \<equiv> override_on zero_storage (the \<circ> con_wit_map \<sigma>) (dom (con_wit_map \<sigma>))"

lemmas con_wit = con_wit_def con_wit_map_def comp_def

lemma restrict_subst[simp]: "k \<in> s \<Longrightarrow> (f |` { g k | k. k \<in> s}) (g k) = f (g k)"
  unfolding restrict_map_def
  by auto

lemma restrict_rule: "x \<notin> A \<Longrightarrow> x \<notin> dom(f |` A)"
  by simp

text \<open>Existence of a storage corresponding to any well-formed abstract state:\<close>
theorem models_nonvac: "\<turnstile> \<sigma> \<Longrightarrow> \<exists>s. s \<tturnstile> \<sigma>"
  unfolding models_nprocs models_proc_keys models_proc_ids
proof (intro exI[of _ "con_wit \<sigma>"] conjI)
  assume wf:"\<turnstile>\<sigma>"
  thus "unat (con_wit \<sigma> @nprocs) = nprocs \<sigma>"
    unfolding con_wit
    using nprocs_key_notin_proc_key_addrs nprocs_key_notin_proc_id_addrs le_unat_uoi[where z=max_nprocs_word]
    apply (subst override_on_apply_in, simp, subst map_add_dom_app_simps(3))
    apply (rule restrict_rule, auto, subst map_add_dom_app_simps(3))
    by (auto simp add:procs_rng_wf)
  from wf have "\<And> k. k \<in> proc_keys \<sigma> \<Longrightarrow> proc_id\<inverse> \<sigma> (@proc_key.id (@proc_key (proc_id \<sigma> k))) = k"
    by (subst id_of_key_addr_inv) (auto simp add:procs_rng_wf, force)
  thus "\<forall>k\<in>proc_keys \<sigma>. con_wit \<sigma> (@proc_key (proc_id \<sigma> k)) = ucast k"
    unfolding con_wit proc_key_addrs_def proc_id_addrs_def
    apply (intro ballI, subst override_on_apply_in, (auto)[1])
    apply (subst map_add_dom_app_simps(3))
    (*apply (subst map_add_find_right)
    apply (subst restrict_subst)
    by auto *)
    sorry
  show "\<forall>k\<in>proc_keys \<sigma>. unat (con_wit \<sigma> (@proc_id k)) = proc_id \<sigma> k"
    unfolding con_wit proc_key_addrs_def proc_id_addrs_def
    sorry
qed

subsection \<open>Unambiguity of encoding\<close>

subsubsection \<open>Auxiliary lemmas\<close>

proposition word32_key_downcast:"is_down (ucast :: word32 \<Rightarrow> key)"
  unfolding is_down_def target_size_def source_size_def
  by simp

lemmas key_upcast =
  ucast_down_ucast_id[OF word32_key_downcast]
  down_ucast_inj[OF word32_key_downcast]

lemma con_id_inj[consumes 4]:
  "\<lbrakk>\<turnstile> \<sigma>; s \<tturnstile> \<sigma>;
    i\<^sub>1\<in>{1..nprocs \<sigma>}; i\<^sub>2\<in>{1..nprocs \<sigma>};
    s (@proc_key i\<^sub>1) = s (@proc_key i\<^sub>2)\<rbrakk> \<Longrightarrow> i\<^sub>1 = i\<^sub>2"
  unfolding models_proc_keys
  using proc_key_of_id_in_keys key_upcast
        proc_key_of_id_inv'[symmetric, of _ i\<^sub>1] proc_key_of_id_inv'[symmetric, of _ i\<^sub>2]
  by metis

text \<open>
  The concrete encoding of abstract storage is unambiguous, i. e. the same storage cannot
  model two distinct well-formed abstract states.
\<close>
theorem models_inj[simp]: "\<lbrakk>\<turnstile> \<sigma>\<^sub>1; \<turnstile> \<sigma>\<^sub>2; s \<tturnstile> \<sigma>\<^sub>1; s \<tturnstile> \<sigma>\<^sub>2\<rbrakk> \<Longrightarrow> (\<sigma>\<^sub>1 :: ('p :: proc_class) abs) = \<sigma>\<^sub>2"
  (is "\<lbrakk>?wf1; ?wf2; ?models1; ?models2\<rbrakk> \<Longrightarrow> _")
proof (intro abs.equality ext option.expand, rule ccontr)
  fix x
  {
    fix \<sigma> \<sigma>':: "'p abs"
    assume wf1:"\<turnstile> \<sigma>" and wf2:"\<turnstile> \<sigma>'"
    assume models1:"s \<tturnstile> \<sigma>" and models2:"s \<tturnstile> \<sigma>'"
    fix i p
    assume Some:"procs \<sigma> x = Some (i, p)"
    with wf1 have "i \<in> proc_ids \<sigma>" unfolding procs_rng_wf Ball_def by auto
    with wf2 models1 models2
    have "proc_id\<inverse> \<sigma>' i \<in> proc_keys \<sigma>' \<and> proc_id \<sigma>' (proc_id\<inverse> \<sigma>' i) = i"
      unfolding models_nprocs by simp
    moreover with Some models1 models2 have "proc_id\<inverse> \<sigma>' i = x"
      unfolding models_proc_keys
      using key_upcast by (metis domI fst_conv option.sel)
    ultimately have "procs \<sigma>' x \<noteq> None" by auto
  }
  note wlog = this
  assume ?wf1 ?wf2 ?models1 and ?models2
  {
    assume neq:"(procs \<sigma>\<^sub>1 x = None) \<noteq> (procs \<sigma>\<^sub>2 x = None)"
    show False
    proof (cases "procs \<sigma>\<^sub>1 x")
      case Some
      with wlog \<open>?wf1\<close> \<open>?wf2\<close> \<open>?models1\<close> \<open>?models2\<close> neq show ?thesis by fastforce
    next
      case None
      with neq have "procs \<sigma>\<^sub>2 x \<noteq> None" by simp
      with wlog \<open>?wf1\<close> \<open>?wf2\<close> \<open>?models1\<close> \<open>?models2\<close> neq show ?thesis by force
    qed
  }
  {
    assume in\<sigma>\<^sub>1:"procs \<sigma>\<^sub>1 x \<noteq> None" and in\<sigma>\<^sub>2:"procs \<sigma>\<^sub>2 x \<noteq> None"
    show "proc \<sigma>\<^sub>1 x = proc \<sigma>\<^sub>2 x"
    proof
      let ?i\<^sub>1 = "proc_id \<sigma>\<^sub>1 x" and ?i\<^sub>2 = "proc_id \<sigma>\<^sub>2 x"
      from in\<sigma>\<^sub>1 and in\<sigma>\<^sub>2
      have "procs \<sigma>\<^sub>1 x = Some (?i\<^sub>1, proc_bdy \<sigma>\<^sub>1 x)"
        and "procs \<sigma>\<^sub>2 x = Some (?i\<^sub>2, proc_bdy \<sigma>\<^sub>2 x)"
        by auto
      with \<open>?wf1\<close> and \<open>?wf2\<close>
      have "?i\<^sub>1\<in>{1..nprocs \<sigma>\<^sub>1}" and "?i\<^sub>2\<in>{1..nprocs \<sigma>\<^sub>2}" unfolding procs_rng_wf by auto
      moreover with in\<sigma>\<^sub>1 in\<sigma>\<^sub>2 \<open>?models1\<close> and \<open>?models2\<close>
      have "s (@proc_key ?i\<^sub>1) = s (@proc_key ?i\<^sub>2)" unfolding models_proc_keys by force
      moreover with \<open>?models1\<close> \<open>?models2\<close> and \<open>?i\<^sub>2\<in>{1..nprocs \<sigma>\<^sub>2}\<close>
      have "?i\<^sub>2\<in>{1..nprocs \<sigma>\<^sub>1}" unfolding models_nprocs by simp
      ultimately show "?i\<^sub>1 = ?i\<^sub>2" using \<open>?wf1\<close> \<open>?models1\<close> and con_id_inj[of \<sigma>\<^sub>1] by blast

      show "proc_bdy \<sigma>\<^sub>1 x = proc_bdy \<sigma>\<^sub>2 x"
        using in\<sigma>\<^sub>1 in\<sigma>\<^sub>2 \<open>?wf1\<close> \<open>?wf2\<close> key_inj
        unfolding procs_rng_wf by (metis UNIV_I domIff the_inv_into_f_f)
    qed
  }
qed (simp)

section \<open>Well-formedness of a storage state\<close>
text \<open>
  We need a decoding function on storage states. However, not every storage state can be
  decoded into an abstract state. So we introduce a minimal well-formedness predicate on
  storage states.
\<close>

text \<open>Number of procedures is bounded, otherwise procedure key addresses can become invalid and we
      cannot read the procedure keys from the storage.\<close>
definition "nprocs_wf s \<equiv> unat (s @nprocs) \<le> max_nprocs"

text \<open>Well-formedness of procedure keys:
      \begin{enumerate}
      \item procedure keys should fit into 24-byte words;
      \item they should represent some existing procedures
            (currently this is essentially a temporary work-around
             and is understood in a very abstract sense
             (Hilbert epsilon operator is used to ``retrieve'' procedures),
             really we need to formalize how the procedures themselves are stored);
      \item the same procedure key should not be stored by two distinct procedure key addresses;
      \item procedure heap should contain valid procedure index for each procedure key.
      \end{enumerate}\<close>
definition "proc_keys_wf (dummy :: 'a itself) (s :: storage) \<equiv>
    (\<forall>k\<in>{s (@proc_key i) | i. i\<in>{1..unat (s @nprocs)}}. ucast (ucast k :: key) = k)
  \<and> (\<forall>i\<in>{1..unat (s @nprocs)}. \<exists>p :: ('a :: proc_class). ucast (key p) = s (@proc_key i))
  \<and> inj_on (s \<circ> @proc_key) {1..unat (s @nprocs)}
  \<and> (\<forall>i \<in> {1 .. unat (s @nprocs)}. unat (s (@proc_id (ucast (s (@proc_key i))))) = i)"

text \<open>Well-formedness of a storage state: the two above requirements should hold.\<close>
definition con_wf ("\<TTurnstile>\<^bsub>_\<^esub> _" [1000, 60] 60)  where
  "\<TTurnstile>\<^bsub>(d :: ('a :: proc_class) itself)\<^esub> s \<equiv>
    nprocs_wf s
  \<and> proc_keys_wf d s"

notation (input) con_wf ("\<TTurnstile>\<^sub>__" [1000, 60] 60)

lemmas nprocs_wf = con_wf_def nprocs_wf_def

lemmas proc_keys_wf = con_wf_def proc_keys_wf_def

text \<open>We proceed with the proof that any storage state corresponding (in the @{text \<tturnstile>} sense) to
      a well-formed abstract state is well-formed.\<close>

subsection \<open>Auxiliary lemmas\<close>

text \<open>Any property on procedure ids can be reformulated on the corresponding procedure keys
      according to a well-formed abstract state (elimination rule for procedure ids).\<close>
lemma elim_proc_id[consumes 3]:
  assumes "i \<in> {1..unat (s @nprocs)}"
  assumes "\<turnstile> \<sigma>"
  assumes "s \<tturnstile> \<sigma>"
  obtains k where "k \<in> proc_keys \<sigma> \<and> i = proc_id \<sigma> k"
  using assms proc_key_exists
  unfolding models_nprocs
  by metis

subsection \<open>Storage corresponding to a well-formed state is well-formed\<close>
theorem model_wf[simp, intro]:"\<lbrakk>\<turnstile>(\<sigma> :: ('p :: proc_class) abs); s \<tturnstile> \<sigma>\<rbrakk> \<Longrightarrow> \<TTurnstile>\<^bsub>(p :: 'p itself)\<^esub>s"
  unfolding proc_keys_wf
proof (intro conjI ballI)
  assume wf:"\<turnstile> \<sigma>" and models:"s \<tturnstile> \<sigma>"
  thus "nprocs_wf s"
    unfolding procs_rng_wf models_nprocs nprocs_wf_def by simp
  note elim_id = elim_proc_id[OF _ wf models]
  show "inj_on (s \<circ> @proc_key) {1..unat (s @nprocs)}"
    unfolding inj_on_def
  proof (intro ballI impI)
    fix x y
    assume "x\<in>{1..unat (s @nprocs)}" and "y\<in>{1..unat (s @nprocs)}"
    from wf models and this
    show "(s \<circ> @proc_key) x = (s \<circ> @proc_key) y \<Longrightarrow> x = y"
      using key_upcast
      by (elim elim_id, auto simp add:models_proc_keys)
  qed
  {
    fix i
    assume "i\<in>{1..unat (s @nprocs)}"

    thus "\<exists>p :: 'p. ucast (key p) = s (@proc_key i)"
      using wf models
      apply (intro exI[of _ "proc_bdy \<sigma> (proc_id\<inverse> \<sigma> i)"])
      by (elim elim_id, simp add:models_proc_keys procs_rng_wf)
  }
  {
    fix k
    assume "k\<in>{s (@proc_key i) | i. i\<in>{1..unat (s @nprocs)}}"
    then obtain x where "x \<in> {1..unat (s @nprocs)}" and "k = s (@proc_key x)"
      by (simp only:Setcompr_eq_image image_iff, elim bexE)
    thus "ucast (ucast k :: key) = k"
      using wf models key_upcast
      by (elim elim_id, auto simp add:models_proc_keys)
  }
  fix i
  assume "i \<in> {1..unat (s @nprocs)}"
  thus "unat (s (@proc_id (ucast (s (@proc_key i))))) = i"
    using wf models
    sorry
qed

section \<open>Decoding of storage\<close>

text \<open>Auxiliary abbreviations\<close>

abbreviation "proc_pair (p :: ('p :: proc_class) itself) s i \<equiv>
  let k = ucast (s (@proc_key i)) in (k, (i, SOME p :: 'p. key p = k))"

abbreviation "proc_list p s \<equiv> [proc_pair p s i. i \<leftarrow> [1..<Suc (unat (s @nprocs))]]"

text \<open>The decoding function:\<close>
definition abs ("\<lbrace>_\<rbrace>\<^bsub>_\<^esub>" [1000, 1000] 1000) where "\<lbrace>s\<rbrace>\<^bsub>p\<^esub> = \<lparr> procs = map_of (proc_list p s) \<rparr>"

notation (input) abs ("\<lbrace>_\<rbrace>\<^sub>_" [1000, 1000] 1000)

lemmas abs_simps =
  Let_def set_map image_iff set_upt atLeastLessThanSuc_atLeastAtMost
  abs.simps option.sel fst_conv

theorem models_abs[simp, intro]: "\<TTurnstile>\<^sub>p s \<Longrightarrow> s \<tturnstile> \<lbrace>s\<rbrace>\<^sub>p"
  unfolding models_nprocs models_proc_keys models_proc_ids
proof (intro conjI ballI)
  assume wf:"\<TTurnstile>\<^sub>p s"
  hence "inj_on (\<lambda>i. ucast (s (@proc_key i)) :: key) {1..unat (s @nprocs)}"
    unfolding inj_on_def proc_keys_wf
    by (auto simp only:comp_apply Ball_def mem_Collect_eq) metis
  hence fst_inj:"inj_on fst (set (proc_list p s))"
    unfolding inj_on_def set_upt Ball_def abs_simps
    by simp
  have dist:"distinct (proc_list p s)"
    by (simp add:distinct_map inj_on_def Let_def)
  show models_nprocs:"unat (s @nprocs) = nprocs \<lbrace>s\<rbrace>\<^sub>p"
    unfolding abs_def
    by (simp only:abs.simps dom_map_of_conv_image_fst
        distinct_card[OF dist] card_image[OF fst_inj] length_map length_upt)

  have proc_pair_inj:"inj_on (proc_pair p s) {1..unat (s @nprocs)}"
    unfolding inj_on_def prod.inject Let_def by simp
  fix k
  {
    fix i q
    assume proc:"procs \<lbrace>s\<rbrace>\<^sub>p k = Some (i, q)"
    hence "(k, proc \<lbrace>s\<rbrace>\<^sub>p k) = proc_pair p s i"
      by (simp only:abs.simps abs_def) (frule map_of_SomeD, auto simp add:Let_def)
  } note proc_k_eq = this
  {
  assume k_in_keys:"k\<in>proc_keys \<lbrace>s\<rbrace>\<^sub>p"
  hence proc_id_in_range:"proc_id \<lbrace>s\<rbrace>\<^sub>p k \<in> {1..nprocs \<lbrace>s\<rbrace>\<^sub>p}"
    apply (subst models_nprocs[symmetric])
    unfolding abs_def by (auto simp only:abs_simps; frule map_of_SomeD)+
  have "map_of (proc_list p s) k = Some (proc \<lbrace>s\<rbrace>\<^sub>p k)"
    using fst_inj proc_pair_inj proc_k_eq k_in_keys
    apply (auto simp only:distinct_map distinct_upt abs_simps intro!:map_of_is_SomeI)
    using models_nprocs proc_id_in_range
    by (intro bexI[of _ "proc_id \<lbrace>s\<rbrace>\<^bsub>p\<^esub> k"], simp+)
  thus "s (@proc_key (proc_id \<lbrace>s\<rbrace>\<^sub>p k)) = ucast k"
    unfolding abs_def
    apply (cases "map_of (proc_list p s) k")
    apply (auto simp only: abs_simps, frule map_of_SomeD)
    using wf unfolding proc_keys_wf by (force simp only: abs_simps)
  }
  next
  fix k
  assume "k \<in> proc_keys \<lbrace>s\<rbrace>\<^sub>p"
  thus "unat (s (@proc_id k)) = proc_id \<lbrace>s\<rbrace>\<^sub>p k"
    sorry
qed

section \<open>System calls\<close>

text \<open>This section will contain specifications of the system calls.\<close>

locale syscall =
  fixes arg_wf :: "'p :: proc_class abs \<Rightarrow> 'b \<Rightarrow> bool" ("_ \<turnstile> _" [60, 60] 60)
  fixes arg_abs :: "'a \<Rightarrow> 'b" ("\<lbrace>_\<rbrace>")
  fixes pre :: "'a \<Rightarrow> storage \<Rightarrow> bool"
  fixes post :: "'a \<Rightarrow> storage \<Rightarrow> storage \<Rightarrow> bool"
  fixes app :: "'b \<Rightarrow> 'p abs \<Rightarrow> 'p abs"
  assumes preserves_wf: "\<lbrakk>\<turnstile>\<sigma>; \<sigma> \<turnstile> arg\<rbrakk> \<Longrightarrow> \<turnstile> app arg \<sigma>"
  assumes preserves_wf': "\<lbrakk>\<TTurnstile>\<^sub>p s; \<turnstile>\<lbrace>s\<rbrace>\<^sub>p; pre a s; post a s s'\<rbrakk> \<Longrightarrow> \<TTurnstile>\<^sub>p s'"
  assumes arg_wf: "\<lbrakk>\<TTurnstile>\<^sub>p s; \<turnstile>\<lbrace>s\<rbrace>\<^sub>p; pre a s\<rbrakk> \<Longrightarrow> \<lbrace>s\<rbrace>\<^sub>p \<turnstile> \<lbrace>a\<rbrace>"
  assumes consistent: "\<lbrakk>\<TTurnstile>\<^sub>p s; \<turnstile>\<lbrace>s\<rbrace>\<^sub>p; pre a s; post a s s'\<rbrakk> \<Longrightarrow> \<lbrace>s'\<rbrace>\<^sub>p = app \<lbrace>a\<rbrace> \<lbrace>s\<rbrace>\<^sub>p"
begin
theorem post_wf: "\<lbrakk>\<TTurnstile>\<^sub>p s; \<turnstile>(\<lbrace>s\<rbrace>\<^sub>p :: 'p abs); pre a s; post a s s'\<rbrakk> \<Longrightarrow> \<turnstile>\<lbrace>s'\<rbrace>\<^sub>p"
  using arg_wf preserves_wf consistent by metis
end

definition add_proc_arg_wf :: "'p :: proc_class abs \<Rightarrow> (key \<times> 'p) \<Rightarrow> bool" ("_ \<turnstile>\<^bsub>add'_proc\<^esub> _")
  where
  "\<sigma> \<turnstile>\<^bsub>add_proc\<^esub> kp \<equiv>
     let (k, p) = kp in
     nprocs \<sigma> < max_nprocs \<and>
     k \<notin> proc_keys \<sigma> \<and>
     key p = k"

definition "add_proc kp \<sigma> \<equiv> \<sigma> \<lparr> procs := procs \<sigma> (fst kp \<mapsto> (nprocs \<sigma> + 1, snd kp)) \<rparr>"

definition add_proc_arg_abs :: "(key \<times> 'p :: proc_class) \<Rightarrow> (key \<times> 'p)" ("\<lbrace>_\<rbrace>\<^bsub>add'_proc\<^esub>") where
  "\<lbrace>a\<rbrace>\<^bsub>add_proc\<^esub> = a"

definition
  "add_proc_pre (kp :: _ \<times> 'p :: proc_class) s \<equiv> \<lbrace>s\<rbrace>\<^bsub>TYPE('p)\<^esub> \<turnstile>\<^bsub>add_proc\<^esub> \<lbrace>kp\<rbrace>\<^bsub>add_proc\<^esub>"

definition
  "add_proc_post kp s s' \<equiv>
     let (k, p) = kp in
     s' @nprocs = s @nprocs + 1 \<and>
     (\<forall>a\<in>{ @proc_key i | i. i\<in>{1..unat (s @nprocs)}}. s' a = s a) \<and>
     s' (@proc_key (unat (s @nprocs) + 1)) = k"

lemma add_proc_preserves_wf: "\<lbrakk>\<turnstile>\<sigma>; \<sigma> \<turnstile>\<^bsub>add_proc\<^esub> (k, p)\<rbrakk> \<Longrightarrow> \<turnstile> add_proc (k, p) \<sigma>"
  (is "\<lbrakk>?wf\<sigma>; ?wf_arg\<rbrakk> \<Longrightarrow> _")
proof (subst abs_wf_def, unfold procs_rng_wf_def procs_map_wf_def, intro conjI ballI)
  let ?\<sigma>' = "add_proc (k, p) \<sigma>"
  assume ?wf\<sigma> and ?wf_arg

  thus "nprocs (?\<sigma>') \<le> max_nprocs" unfolding add_proc_arg_wf_def add_proc_def by simp

  have proc_keys':"proc_keys ?\<sigma>' = proc_keys \<sigma> \<union> {k}"  unfolding add_proc_def by simp
  have proc_id_k:"proc_id ?\<sigma>' k = nprocs \<sigma> + 1" unfolding add_proc_def by simp
  have proc_id_unch:"\<forall>k\<in>proc_keys \<sigma>. proc_id ?\<sigma>' k = proc_id \<sigma> k"
    using \<open>?wf_arg\<close> unfolding add_proc_def add_proc_arg_wf_def by simp

  show "inj_on (proc_id ?\<sigma>') (proc_keys ?\<sigma>')"
  proof (unfold inj_on_def, intro ballI impI)
    fix x y
    assume "x \<in> proc_keys ?\<sigma>'" and "y \<in> proc_keys ?\<sigma>'" and "proc_id ?\<sigma>' x = proc_id ?\<sigma>' y"
    with \<open>?wf\<sigma>\<close> proc_keys' proc_id_k proc_id_unch show "x = y"
      unfolding procs_map_wf procs_rng_wf inj_on_def add_proc_arg_wf_def
                Ball_def atLeastAtMost_iff
      by (cases "x \<in> proc_keys \<sigma>"; cases "y \<in> proc_keys \<sigma>", auto)
  qed

  fix k'
  assume k'_in_keys:"k'\<in>proc_keys ?\<sigma>'"

  with \<open>?wf\<sigma>\<close> \<open>?wf_arg\<close> proc_keys' proc_id_k proc_id_unch
  show "proc_id ?\<sigma>' k' \<in> {1..nprocs ?\<sigma>'}"
    unfolding add_proc_arg_wf_def procs_rng_wf Ball_def atLeastAtMost_iff
    by (cases "k' = k", auto)

  have "proc_bdy ?\<sigma>' k = p" unfolding add_proc_def by simp
  moreover have "\<forall>k\<in>proc_keys \<sigma>. proc_bdy ?\<sigma>' k = proc_bdy \<sigma> k"
    using \<open>?wf_arg\<close> unfolding add_proc_def add_proc_arg_wf_def by simp
  ultimately show "key (proc_bdy ?\<sigma>' k') = k'"
    using k'_in_keys \<open>?wf\<sigma>\<close> \<open>?wf_arg\<close> proc_keys'
    unfolding add_proc_arg_wf_def procs_rng_wf
    by (cases "k' = k", auto)
qed

subsection \<open>Register Procedure\<close>

text \<open>Early version of "register procedure" operation.\<close>

abbreviation higher32 where "higher32 k n \<equiv> n >> ((32 - k) * 8)"

definition is_kernel_storage_key :: "word32 \<Rightarrow> bool"
  where "is_kernel_storage_key w \<equiv> higher32 4 w = 0xffffffff"

(*
24 bytes aligned right in the 32 bytes
*)
definition n_of_procedures :: "storage \<Rightarrow> word32"
  where "n_of_procedures s = s @nprocs"

(*
When a procedure is added to the kernel:
  1. TODO: The procedure data is added to the procedure heap.
  2. The procedure key is appended to the end of the array.
  3. If the length value is equal to the maximum procedure index value, abort.
  4. The length value (the first value) is incremented by one.
  5. TODO: The procedure index value (in procedure metadata) is set to the new length value.
*)
definition add_proc' :: "key \<Rightarrow> storage \<Rightarrow> storage option"
  where
    "add_proc' p s \<equiv>
      if n_of_procedures s < max_nprocs_word
      then
        Some (s
              (@nprocs := n_of_procedures s + 1,
               @nprocs OR (n_of_procedures s + 1) := ucast p))
      else
        None"

lemma
  assumes "n_of_procedures s < max_nprocs_word"
  shows   "case (add_proc' p s) of
           Some s' \<Rightarrow> n_of_procedures s' = n_of_procedures s + 1"
proof-
  have "0 < n_of_procedures s + 1"
    using assms
    by (metis
         add_cancel_right_right
         inc_i word_le_0_iff word_le_sub1 word_neq_0_conv word_zero_le zero_neq_one)
  moreover have "n_of_procedures s + 1 \<le> max_nprocs_word"
    using assms
    by (metis add.commute add.right_neutral inc_i word_le_sub1 word_not_simps(1) word_zero_le)
  ultimately have "@nprocs OR n_of_procedures s + 1 \<noteq> @nprocs"
    using proc_key_addr_neq_nprocs_key by auto
  thus ?thesis
    unfolding add_proc'_def
    using assms
    by (simp add:n_of_procedures_def)
qed
end
