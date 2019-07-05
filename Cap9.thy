section \<open>Preliminaries\<close>

theory Cap9
imports
  "HOL-Word.Word"
  "HOL-Library.Adhoc_Overloading"
  "HOL-Library.DAList"
  "HOL-Library.AList"
  "HOL-Library.Rewrite"
  "Word_Lib/Word_Lemmas"
begin

subsection \<open>Type class instantiations\<close>

text \<open>
  Instantiate @{class len} type class to extract lengths from word
  types avoiding repeated explicit numeric specification of the length e.g.
  @{text "LENGTH(byte)"} or @{text "LENGTH('a :: len word)"} instead of @{text 8} or
  @{term "LENGTH('a :: len)"}, where @{text "'a"} cannot be directly extracted from a type
  such as @{text "'a word"}.
\<close>

instantiation word :: (len) len begin
definition len_word[simp]: "len_of (_ :: 'a::len word itself) = LENGTH('a)"
instance by (standard, simp)
end

lemma len_word': "LENGTH('a::len word) = LENGTH('a)" by (rule len_word)

text \<open>
  Instantiate @{class size} type class for types of the form @{text "'a itself"}. This allows
  us to parametrize operations by word lengths using the dummy variables of type
  @{text "'a word itself"}. The operations cannot be directly parametrized by numbers as there is
  no lifting from term numbers to type numbers due to the lack of dependent types.
\<close>

instantiation itself :: (len) size begin
definition size_itself where [simp, code]: "size (n::'a::len itself) = LENGTH('a)"
instance ..
end

declare unat_word_ariths[simp] word_size[simp] is_up_def[simp] wsst_TYs(1,2)[simp]

subsection \<open>Word width\<close>

text \<open>
  We introduce definition of the least number of bits to hold the current value of a word. This is
  needed because in our specification we often word with @{const "ucast"}'ed values
  (right aligned subranges of bits), largely
  again due to the lack of dependent types (or true type-level functions),
  e.g. the it's hard to specify that the length of
  @{text "a \<Join> b"} (where @{text "\<Join>"} stands for concatenation) is the sum of the length of
  @{text "a"} and @{text "b"}, since length is a type parameter and there's no equivalent of
  sum on the type level. So we instead fix the length of @{text "a \<Join> b"} to be the maximum
  possible one (say, 32 bytes) and then use conditions of the form @{text "width a \<le> s"} to
  specify that the actual ``size'' of @{text "a"} is @{text "s"}.
\<close>

definition "width w \<equiv> LEAST n. unat w < 2 ^ n" for w :: "'a::len word"

lemma widthI[intro]: "\<lbrakk>\<And> u. u < n \<Longrightarrow> 2 ^ u \<le> unat w; unat w < 2 ^ n\<rbrakk> \<Longrightarrow> width w = n"
  unfolding width_def Least_def
  using not_le
  apply (intro the_equality, blast)
  by (meson nat_less_le)

lemma width_wf: "\<exists>! n. (\<forall> u < n. 2 ^ u \<le> unat w) \<and> unat w < 2 ^ n"
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

subsection \<open>Right zero-padding\<close>

text \<open>
  Here's the first time we use @{const width}. If @{text x} is a value of size @{text n}
  right-aligned in a word of size @{text "s = size x"} (note there's nowhere to keep the value n,
  since the size of @{text x} is some @{text "s \<ge> n"}, so we require it to be
  provided explicitly),
  then @{text "rpad n x"} will move the value @{text x} to the left. For the operation to be
  correct (no losing of significant higher bits) we need the precondition @{text "width x \<le> n"}
  in all the lemmas, hence the need for @{const width}.
\<close>

definition rpad where "rpad n x \<equiv> x << size x - n"

lemma rpad_low[simp]: "\<lbrakk>width x \<le> n; i < size x - n\<rbrakk> \<Longrightarrow> \<not> (rpad n x) !! i"
  unfolding rpad_def by (simp add:nth_shiftl)

lemma rpad_high[simp]:
  "\<lbrakk>width x \<le> n; n \<le> size x; size x - n \<le> i\<rbrakk> \<Longrightarrow> (rpad n x) !! i = x !! (i + n - size x)"
  (is "\<lbrakk>?xbound; ?nbound; i \<ge> ?ibound\<rbrakk> \<Longrightarrow> ?goal i")
proof-
  fix i
  assume ?xbound ?nbound and "i \<ge> ?ibound"
  moreover from \<open>?nbound\<close> have "i + n - size x = i - ?ibound" by simp
  moreover from \<open>?xbound\<close> have "x !! (i + n - size x) \<Longrightarrow> i < size x" by - (rule ccontr, simp)
  ultimately show "?goal i" unfolding rpad_def by (subst nth_shiftl', metis)
qed

lemma rpad_inj: "\<lbrakk>width x \<le> n; width y \<le> n; n \<le> size x\<rbrakk> \<Longrightarrow> rpad n x = rpad n y \<Longrightarrow> x = y"
  (is "\<lbrakk>?xbound; ?ybound; ?nbound; _\<rbrakk> \<Longrightarrow> _")
  unfolding inj_def word_eq_iff
proof (intro allI impI)
  fix i
  let ?i' = "i + size x - n"
  assume ?xbound ?ybound ?nbound
  assume "\<forall>j < LENGTH('a). rpad n x !! j = rpad n y !! j"
  hence "\<And> j. rpad n x !! j = rpad n y !! j" using test_bit_bin by blast
  from this[of ?i'] and \<open>?xbound\<close> \<open>?ybound\<close> \<open>?nbound\<close> show "x !! i = y !! i" by simp
qed

subsection \<open>Spanning concatenation\<close>

abbreviation ucastl ("'(ucast')\<^bsub>_\<^esub> _" [1000, 100] 100) where
  "(ucast)\<^bsub>l\<^esub> a \<equiv> ucast a :: 'b word" for l :: "'b::len0 itself"

notation (input) ucastl ("'(ucast')\<^sub>_ _" [1000, 100] 100)

definition pad_join :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'c::len itself \<Rightarrow> 'b::len word \<Rightarrow> 'c word"
  ("_ \<^bsub>_\<^esub>\<diamond>\<^bsub>_\<^esub> _" [60, 1000, 1000, 61] 60) where
  "x \<^bsub>n\<^esub>\<diamond>\<^bsub>l\<^esub> y \<equiv> rpad n (ucast x) OR ucast y"

notation (input) pad_join ("_ \<^sub>_\<diamond>\<^sub>_ _" [60, 1000, 1000, 61] 60)

lemma pad_join_high:
  "\<lbrakk>width a \<le> n; n \<le> size l; width b \<le> size l - n; size l - n \<le> i\<rbrakk>
   \<Longrightarrow> (a \<^sub>n\<diamond>\<^sub>l b) !! i = a !! (i + n - size l)"
  unfolding pad_join_def
  using nth_ucast nth_width_high by fastforce

lemma pad_join_high'[simp]:
  "\<lbrakk>width a \<le> n; n \<le> size l; width b \<le> size l - n\<rbrakk> \<Longrightarrow> a !! i = (a \<^sub>n\<diamond>\<^sub>l b) !! (i + size l - n)"
  using pad_join_high[of a n l b "i + size l - n"] by simp

lemma pad_join_mid[simp]:
  "\<lbrakk>width a \<le> n; n \<le> size l; width b \<le> size l - n; width b \<le> i; i < size l - n\<rbrakk>
   \<Longrightarrow> \<not> (a \<^sub>n\<diamond>\<^sub>l b) !! i"
  unfolding pad_join_def by auto

lemma pad_join_low[simp]:
  "\<lbrakk>width a \<le> n; n \<le> size l; width b \<le> size l - n; i < width b\<rbrakk> \<Longrightarrow> (a \<^sub>n\<diamond>\<^sub>l b) !! i = b !! i"
  unfolding pad_join_def by (auto simp add: nth_ucast)

lemma pad_join_inj:
  assumes eq:"a \<^sub>n\<diamond>\<^sub>l b = c \<^sub>n\<diamond>\<^sub>l d"
  assumes a:"width a \<le> n" and c:"width c \<le> n"
  assumes n: "n \<le> size l"
  assumes b:"width b \<le> size l - n"
  assumes d:"width d \<le> size l - n"
  shows   "a = c" and "b = d"
proof-
  from eq have eq':"\<And>j. (a \<^sub>n\<diamond>\<^sub>l b) !! j = (c \<^sub>n\<diamond>\<^sub>l d) !! j"
    using test_bit_bin unfolding word_eq_iff by auto
  moreover from a n b
  have "\<And> i. a !! i = (a \<^sub>n\<diamond>\<^sub>l b) !! (i + size l - n)" by simp
  moreover from c n d
  have "\<And> i. c !! i = (c \<^sub>n\<diamond>\<^sub>l d) !! (i + size l - n)" by simp
  ultimately show "a = c" unfolding word_eq_iff by auto

  {
    fix i
    from a n b have "i < width b \<Longrightarrow> b !! i = (a \<^sub>n\<diamond>\<^sub>l b) !! i" by simp
    moreover from c n d have "i < width d \<Longrightarrow> d !! i = (c \<^sub>n\<diamond>\<^sub>l d) !! i" by simp
    moreover have "i \<ge> width b \<Longrightarrow> \<not> b !! i" and "i \<ge> width d \<Longrightarrow> \<not> d !! i" by auto
    ultimately have "b !! i = d !! i"
      using eq'[of i] b d
        pad_join_mid[of a n l b i, OF a n b]
        pad_join_mid[of c n l d i, OF c n d]
      by (meson leI less_le_trans)
  }
  thus "b = d" unfolding word_eq_iff by simp
qed

lemma pad_join_inj'[dest!]:
 "\<lbrakk>a \<^sub>n\<diamond>\<^sub>l b = c \<^sub>n\<diamond>\<^sub>l d;
   width a \<le> n; width c \<le> n; n \<le> size l;
   width b \<le> size l - n;
   width d \<le> size l - n\<rbrakk> \<Longrightarrow> a = c \<and> b = d"
  apply (rule conjI)
  subgoal by (frule (4) pad_join_inj(1))
  by (frule (4) pad_join_inj(2))

lemma pad_join_and[simp]:
  assumes "width x \<le> n" "n \<le> m" "width a \<le> m" "m \<le> size l" "width b \<le> size l - m"
  shows   "(a \<^sub>m\<diamond>\<^sub>l b) AND rpad n x = rpad m a AND rpad n x"
  unfolding word_eq_iff
proof ((subst word_ao_nth)+, intro allI impI)
  from assms have 0:"n \<le> size x" by simp
  from assms have 1:"m \<le> size a" by simp
  fix i
  assume "i < LENGTH('a)"
  from assms show "((a \<^bsub>m\<^esub>\<diamond>\<^bsub>l\<^esub> b) !! i \<and> rpad n x !! i) = (rpad m a !! i \<and> rpad n x !! i)"
    using rpad_low[of x n i, OF assms(1)] rpad_high[of x n i, OF assms(1) 0]
          rpad_low[of a m i, OF assms(3)] rpad_high[of a m i, OF assms(3) 1]
          pad_join_high[of a m l b i, OF assms(3,4,5)]
          size_itself_def[of l] word_size[of x] word_size[of a]
    by (metis add.commute add_lessD1 le_Suc_ex le_diff_conv not_le)
qed

subsection \<open>Deal with partially undefined results\<close>

definition restrict :: "'a::len word \<Rightarrow> nat set \<Rightarrow> 'a word" (infixl "\<restriction>" 60) where
  "restrict x s \<equiv> BITS i. i \<in> s \<and> x !! i"

lemma nth_restrict[iff]: "(x \<restriction> s) !! n = (n \<in> s \<and> x !! n)"
  unfolding restrict_def
  by (simp add: bang_conj_lt test_bit.eq_norm)

lemma restrict_inj2:
  assumes eq:"f x\<^sub>1 y\<^sub>1 OR v\<^sub>1 \<restriction> s = f x\<^sub>2 y\<^sub>2 OR v\<^sub>2 \<restriction> s"
  assumes fi:"\<And> x y i. i \<in> s \<Longrightarrow> \<not> f x y !! i"
  assumes inj:"\<And> x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2. f x\<^sub>1 y\<^sub>1 = f x\<^sub>2 y\<^sub>2 \<Longrightarrow> x\<^sub>1 = x\<^sub>2 \<and> y\<^sub>1 = y\<^sub>2"
  shows   "x\<^sub>1 = x\<^sub>2 \<and> y\<^sub>1 = y\<^sub>2"
proof-
  from eq and fi have "f x\<^sub>1 y\<^sub>1 = f x\<^sub>2 y\<^sub>2" unfolding word_eq_iff by auto
  with inj show ?thesis .
qed

lemma restrict_ucast_inv[simp]:
  "\<lbrakk>a = LENGTH('a); b = LENGTH('b)\<rbrakk> \<Longrightarrow> (ucast x OR y \<restriction> {a..<b}) AND mask a = ucast x"
  for x :: "'a::len word" and y :: "'b::len word"
  unfolding word_eq_iff
  by (rewrite nth_ucast word_ao_nth nth_mask nth_restrict test_bit_bin)+ auto

lemmas restrict_inj_pad_join[dest] = restrict_inj2[of "\<lambda> x y. x \<^sub>_\<diamond>\<^sub>_ y"]

subsection \<open>Plain concatenation\<close>

definition join :: "'a::len word \<Rightarrow> 'c::len itself \<Rightarrow> nat \<Rightarrow> 'b::len word \<Rightarrow> 'c word"
  ("_ \<^bsub>_\<^esub>\<Join>\<^bsub>_\<^esub> _" [62,1000,1000,61] 61) where
  "(a \<^bsub>l\<^esub>\<Join>\<^bsub>n\<^esub> b) \<equiv> (ucast a << n) OR (ucast b)"

notation (input) join ("_ \<^sub>_\<Join>\<^sub>_ _" [62,1000,1000,61] 61)

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

lemma join_and:
  assumes "width x \<le> n" "n \<le> size l" "k \<le> size l" "m \<le> k"
          "n \<le> k - m" "width a \<le> k - m" "width a + m \<le> k" "width b \<le> m"
  shows   "rpad k (a \<^sub>l\<Join>\<^sub>m b) AND rpad n x = rpad (k - m) a AND rpad n x"
  unfolding word_eq_iff
proof ((subst word_ao_nth)+, intro allI impI)
  from assms have 0:"n \<le> size x" by simp
  from assms have 1:"k - m \<le> size a" by simp
  from assms have 2:"width (a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b) \<le> k" by simp
  from assms have 3:"k \<le> size (a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b)" by simp
  from assms have 4:"width a + m \<le> size l" by simp
  fix i
  assume "i < LENGTH('a)"
  moreover with assms have "i + k - size (a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b) - m = i + (k - m) - size a" by simp
  moreover from assms have "i + k - size (a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b) < m \<Longrightarrow> i < size x - n" by simp
  moreover from assms have
    "\<lbrakk>i \<ge> size l - k; m \<le> i + k - size (a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b)\<rbrakk> \<Longrightarrow> size a - (k - m) \<le> i" by simp
  moreover from assms have "width a + m \<le> i + k - size (a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b) \<Longrightarrow> \<not> rpad (k - m) a !! i"
    by (simp add: nth_shiftl' rpad_def)
  moreover from assms have "\<not> i \<ge> size l - k \<Longrightarrow> i < size x - n" by simp
  ultimately show "(rpad k (a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b) !! i \<and> rpad n x !! i) =
                   (rpad (k - m) a !! i \<and> rpad n x !! i)"
    using assms
          rpad_high[of x n i, OF assms(1) 0] rpad_low[of x n i, OF assms(1)]
          rpad_high[of a "k - m" i, OF assms(6) 1] rpad_low[of a "k - m" i, OF assms(6)]
          rpad_high[of "a \<^sub>l\<Join>\<^sub>m b" k i, OF 2 3] rpad_low[of "a \<^sub>l\<Join>\<^sub>m b" k i, OF 2]
          join_high[of a m l b "i + k - size (a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b)", OF 4 assms(8)]
          join_mid[of a m l b "i + k - size (a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b)", OF 4 assms(8)]
          join_low[of a m l b "i + k - size (a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b)", OF 4 assms(8)]
          size_itself_def[of l] word_size[of x] word_size[of a] word_size[of "a \<^bsub>l\<^esub>\<Join>\<^bsub>m\<^esub> b"]
    by (metis not_le)
qed

lemma join_and'[simp]:
   "\<lbrakk>width x \<le> n; n \<le> size l; k \<le> size l; m \<le> k;
     n \<le> k - m; width a \<le> k - m; width a + m \<le> k; width b \<le> m\<rbrakk> \<Longrightarrow>
    rpad k (a \<^sub>l\<Join>\<^sub>m b) AND rpad n x = rpad (k - m) (ucast a) AND rpad n x"
  using join_and[of x n l k m "ucast a" b] unfolding join_def
  by (simp add: ucast_id)

section \<open>Data formats\<close>

text \<open>This section contains definitions of various data formats used in the specification.\<close>

subsection \<open>Common notation\<close>

text \<open>Before we proceed some common notation that would be used later will be established.\<close>

subsubsection \<open>Machine words\<close>

text \<open>Procedure keys are represented as 24-byte (192 bits) machine words.\<close>

type_synonym word24 = "192 word" \<comment> \<open>24 bytes\<close>
type_synonym key = word24

text \<open>Byte is 8-bit machine word.\<close>
type_synonym byte = "8 word"

text \<open>32-byte machine words that are used to model keys and values of the storage.\<close>
type_synonym word32 = "256 word" \<comment> \<open>32 bytes\<close>

text \<open>
  Storage is a function that takes a 32-byte word (key) and returns another
  32-byte word (value).
\<close>
type_synonym storage = "word32 \<Rightarrow> word32"

subsubsection \<open>Concatenation operations\<close>

text \<open>
  Specialize previously defined general concatenation operations for the fixed result size of
  32 bytes. Thus we avoid lots of redundant type annotations for every intermediate result
  (note that these intermediate types cannot be inferred automatically
  (in a purely Hindley-Milner setting as in Isabelle),
  because this would require type-level functions/dependent types).
\<close>

abbreviation "len (_ :: 'a::len word itself) \<equiv> TYPE('a)"

no_notation join  ("_ \<^bsub>_\<^esub>\<Join>\<^bsub>_\<^esub> _" [62,1000,1000,61] 61)
no_notation (input) join ("_ \<^sub>_\<Join>\<^sub>_ _" [62,1000,1000,61] 61)

abbreviation join32 ("_ \<Join>\<^bsub>_\<^esub> _" [62,1000,61] 61) where
  "a \<Join>\<^bsub>n\<^esub> b \<equiv> join a (len TYPE(word32)) (n * 8) b"
abbreviation (output) join32_out ("_ \<Join>\<^bsub>_\<^esub> _" [62,1000,61] 61) where
  "join32_out a n b \<equiv> join a (TYPE(256)) n b"
notation (input) join32 ("_ \<Join>\<^sub>_ _" [62,1000,61] 61)

no_notation pad_join  ("_ \<^bsub>_\<^esub>\<diamond>\<^bsub>_\<^esub> _" [60,1000,1000,61] 60)
no_notation (input) pad_join ("_ \<^sub>_\<diamond>\<^sub>_ _" [60,1000,1000,61] 60)

abbreviation pad_join32 ("_ \<^bsub>_\<^esub>\<diamond> _" [60,1000,61] 60) where
  "a \<^bsub>n\<^esub>\<diamond> b \<equiv> pad_join a (n * 8) (len TYPE(word32)) b"
abbreviation (output) pad_join32_out ("_ \<^bsub>_\<^esub>\<diamond> _" [60,1000,61] 60) where
  "pad_join32_out a n b \<equiv> pad_join a n (TYPE(256)) b"
notation (input) pad_join32 ("_ \<^sub>_\<diamond> _" [60,1000,61] 60)

text \<open>
  Override treatment of hexidecimal numeric constants to make them monomorphic words of
  fixed length, mimicking the notation used in the informal specification (e.g. @{term "0x01"})
  is always a word 1 byte long and is not, say, the natural number one). Otherwise, again, lots
  of redundant type annotations would arise.
\<close>

parse_ast_translation \<open>
  let
    open Ast
    fun mk_numeral t = mk_appl (Constant @{syntax_const "_Numeral"}) t
    fun mk_word_numeral num t =
      if String.isPrefix "0x" num then
        mk_appl (Constant @{syntax_const "_constrain"})
          [mk_numeral t,
           mk_appl (Constant @{type_syntax "word"})
             [mk_appl (Constant @{syntax_const "_NumeralType"})
             [Variable (4 * (size num - 2) |> string_of_int)]]]
      else
        mk_numeral t
    fun numeral_ast_tr ctxt (t as [Appl [Constant @{syntax_const "_constrain"},
                                         Constant num,
                                         _]])
                                                  = mk_word_numeral num t
      | numeral_ast_tr ctxt (t as [Constant num]) = mk_word_numeral num t
      | numeral_ast_tr _ t                        = mk_numeral t
      | numeral_ast_tr _ t                        = raise AST (@{syntax_const "_Numeral"}, t)
  in
     [(@{syntax_const "_Numeral"}, numeral_ast_tr)]
  end
\<close>

subsection \<open>Datatypes\<close>

text \<open>
  Introduce generic notation for mapping of various entities into high-level and low-level
  representations. A high-level representation of an entity @{text e} would be written as
  @{text "\<lceil>e\<rceil>"} and a low-level as @{text "\<lfloor>e\<rfloor>"} accordingly. Using a high-level representation it is
  easier to express and proof some properties and invariants, but some of them can be expressed only
  using a low-level representation.

  We use adhoc overloading to use the same notation for various types of entities (indices, offsets,
  addresses, capabilities etc.).
\<close>

no_notation floor ("\<lfloor>_\<rfloor>")

consts rep :: "'a \<Rightarrow> 'b" ("\<lfloor>_\<rfloor>")

no_notation ceiling ("\<lceil>_\<rceil>")

consts abs :: "'a \<Rightarrow> 'b" ("\<lceil>_\<rceil>")

subsubsection \<open>Deterministic inverse functions\<close>

definition "maybe_inv f y \<equiv> if y \<in> range f then Some (the_inv f y) else None"

lemma maybe_inv_inj[intro]: "inj f \<Longrightarrow> maybe_inv f (f x) = Some x"
  unfolding maybe_inv_def
  by (auto simp add:inj_def the_inv_f_f)

lemma maybe_inv_inj'[dest]: "\<lbrakk>inj f; maybe_inv f y = Some x\<rbrakk> \<Longrightarrow> f x = y"
  unfolding maybe_inv_def
  by (auto intro:f_the_inv_into_f simp add:inj_def split:if_splits)

locale invertible =
  fixes rep :: "'a \<Rightarrow> 'b" ("\<lfloor>_\<rfloor>")
  assumes inj:"inj rep"
begin
definition inv :: "'b \<Rightarrow> 'a option" where "inv \<equiv> maybe_inv rep"

lemmas inv_inj[folded inv_def, simp] = maybe_inv_inj[OF inj]

lemmas inv_inj'[folded inv_def, dest] = maybe_inv_inj'[OF inj]
end

definition "range2 f \<equiv> {y. \<exists>x\<^sub>1 \<in> UNIV. \<exists> x\<^sub>2 \<in> UNIV. y = f x\<^sub>1 x\<^sub>2}"

definition "the_inv2 f \<equiv> \<lambda> x. THE y. \<exists> y'. f y y' = x"

definition "maybe_inv2 f y \<equiv> if y \<in> range2 f then Some (the_inv2 f y) else None"

definition "inj2 f \<equiv> \<forall> x\<^sub>1 x\<^sub>2 y\<^sub>1 y\<^sub>2. f x\<^sub>1 y\<^sub>1 = f x\<^sub>2 y\<^sub>2 \<longrightarrow> x\<^sub>1 = x\<^sub>2"

lemma inj2I: "(\<And> x\<^sub>1 x\<^sub>2 y\<^sub>1 y\<^sub>2. f x\<^sub>1 y\<^sub>1 = f x\<^sub>2 y\<^sub>2 \<Longrightarrow> x\<^sub>1 = x\<^sub>2) \<Longrightarrow> inj2 f" unfolding inj2_def
  by blast

lemma maybe_inv2_inj[intro]: "inj2 f \<Longrightarrow> maybe_inv2 f (f x y) = Some x"
  unfolding maybe_inv2_def the_inv2_def inj2_def range2_def
  by (simp split:if_splits, blast)

lemma maybe_inv2_inj'[dest]:
  "\<lbrakk>inj2 f; maybe_inv2 f y = Some x\<rbrakk> \<Longrightarrow> \<exists> y'. f x y' = y"
  unfolding maybe_inv2_def the_inv2_def range2_def inj2_def
  by (force split:if_splits intro:theI)

locale invertible2 =
  fixes rep :: "'a \<Rightarrow> 'c \<Rightarrow> 'c" ("\<lfloor>_\<rfloor>")
  assumes inj:"inj2 rep"
begin
definition inv2 :: "'c \<Rightarrow> 'a option" where "inv2 \<equiv> maybe_inv2 rep"

lemmas inv2_inj[folded inv2_def, simp] = maybe_inv2_inj[OF inj]

lemmas inv2_inj'[folded inv_def, dest] = maybe_inv2_inj'[OF inj]
end

subsubsection \<open>Capability\<close>

text \<open>
  Introduce capability type. Note that we don't include @{text Null} capability into it.
  @{text Null} is only handled specially inside the call delegation, otherwise it only complicates
  the proofs with side additional cases.

  There will be separate type @{text call} defined as @{text "capability option"} to respect
  the fact that in some places it can indeed be @{text Null}.
\<close>

datatype capability =
    Call
  | Reg
  | Del
  | Entry
  | Write
  | Log
  | Send

text \<open>
  In general, in the following we strive to make all encoding functions injective without any
  preconditions. All the necessary invariants are built into the type definitions.

  Capability representation would be its assigned number.
\<close>

definition cap_type_rep :: "capability \<Rightarrow> byte" where
  "cap_type_rep c \<equiv> case c of
      Call  \<Rightarrow> 0x03
    | Reg   \<Rightarrow> 0x04
    | Del   \<Rightarrow> 0x05
    | Entry \<Rightarrow> 0x06
    | Write \<Rightarrow> 0x07
    | Log   \<Rightarrow> 0x08
    | Send  \<Rightarrow> 0x09"

adhoc_overloading rep cap_type_rep

text \<open>
  Capability representation range from @{text 3} to @{text 9} since @{text Null} is not included
  and @{text 2} does not exist.
\<close>

lemma cap_type_rep_rng[simp]: "\<lfloor>c\<rfloor> \<in> {0x03..0x09}" for c :: capability
  unfolding cap_type_rep_def by (simp split:capability.split)

text \<open>Capability representation is injective.\<close>

lemma cap_type_rep_inj[dest]: "\<lfloor>c\<^sub>1\<rfloor> = \<lfloor>c\<^sub>2\<rfloor> \<Longrightarrow> c\<^sub>1 = c\<^sub>2" for c\<^sub>1 c\<^sub>2 :: capability
  unfolding cap_type_rep_def
  by (simp split:capability.splits)

text \<open>@{text 4} bits is sufficient to store a capability number.\<close>

lemma width_cap_type: "width \<lfloor>c\<rfloor> \<le> 4" for c :: capability
proof (rule ccontr, drule not_le_imp_less)
  assume "4 < width \<lfloor>c\<rfloor>"
  moreover hence "\<lfloor>c\<rfloor> !! (width \<lfloor>c\<rfloor> - 1)" using nth_width_msb by force
  ultimately obtain n where "\<lfloor>c\<rfloor> !! n" and "n \<ge> 4" by (metis le_step_down_nat nat_less_le)
  thus False unfolding cap_type_rep_def by (simp split:capability.splits)
qed

text \<open>So, any number greater than or equal to @{text 4} will be enough.\<close>

lemma width_cap_type'[simp]: "4 \<le> n \<Longrightarrow> width \<lfloor>c\<rfloor> \<le> n" for c :: capability
  using width_cap_type[of c] by simp

text \<open>Capability representation can't be zero.\<close>

lemma cap_type_nonzero[simp]: "\<lfloor>c\<rfloor> \<noteq> 0" for c :: capability
  unfolding cap_type_rep_def by (simp split:capability.splits)

subsubsection \<open>Capability index\<close>

text \<open>Introduce capability index type that is a natural number in range from 0 to 254.\<close>

typedef capability_index = "{i :: nat. i < 2 ^ LENGTH(byte) - 1}"
  morphisms cap_index_rep' cap_index
  by (intro exI[of _ "0"], simp)

adhoc_overloading rep cap_index_rep'

adhoc_overloading abs cap_index

text \<open>
  Capability index representation is a byte. Zero byte is reserved, so capability index
  representation starts with 1.
\<close>

definition "cap_index_rep i \<equiv> of_nat (\<lfloor>i\<rfloor> + 1) :: byte" for i :: capability_index

adhoc_overloading rep cap_index_rep

text \<open>
  A single byte is sufficient to store the least number of bits of capability index representation.
\<close>

lemma width_cap_index: "width \<lfloor>i\<rfloor> \<le> LENGTH(byte)" for i :: capability_index by simp

lemma width_cap_index'[simp]: "LENGTH(byte) \<le> n \<Longrightarrow> width \<lfloor>i\<rfloor> \<le> n"
  for i :: capability_index by simp

text \<open>Capability index representation can't be zero byte.\<close>

lemma cap_index_nonzero[simp]: "\<lfloor>i\<rfloor> \<noteq> 0x00" for i :: capability_index
  unfolding cap_index_rep_def using cap_index_rep'[of i] of_nat_neq_0[of "Suc \<lfloor>i\<rfloor>"]
  by force

text \<open>Capability index representation is injective.\<close>

lemma cap_index_inj[dest]: "(\<lfloor>i\<^sub>1\<rfloor> :: byte) = \<lfloor>i\<^sub>2\<rfloor> \<Longrightarrow> i\<^sub>1 = i\<^sub>2" for i\<^sub>1 i\<^sub>2 :: capability_index
  unfolding cap_index_rep_def
  using cap_index_rep'[of i\<^sub>1] cap_index_rep'[of i\<^sub>2] word_of_nat_inj[of "\<lfloor>i\<^sub>1\<rfloor>" "\<lfloor>i\<^sub>2\<rfloor>"]
        cap_index_rep'_inject
  by force

text \<open>Representation function is invertible.\<close>

lemmas cap_index_invertible[intro] = invertible.intro[OF injI, OF cap_index_inj]

interpretation cap_index_inv: invertible cap_index_rep ..

adhoc_overloading abs cap_index_inv.inv

subsubsection \<open>Capability offset\<close>

text \<open>The following datatype specifies data offsets for addresses in the procedure heap.\<close>

type_synonym capability_offset = byte

datatype data_offset =
  Addr
  | Index
  | Ncaps capability
  | Cap capability capability_index capability_offset


text \<open>
  Machine word representation of data offsets. Using these offsets the following data can be
  obtained:
  \begin{itemize}
    \item @{text Addr}: procedure Ethereum address;
    \item @{text Index}: procedure index;
    \item @{text "Ncaps ty"}: the number of capabilities of type @{text "ty"};
    \item @{text "Cap ty i off"}: capability of type @{text "ty"}, with index @{text "ty"} and
          offset @{text "off"} into that capability.
  \end{itemize}
\<close>

definition data_offset_rep :: "data_offset \<Rightarrow> word32" where
 "data_offset_rep off \<equiv> case off of
     Addr         \<Rightarrow> 0x00  \<Join>\<^sub>2 0x00  \<Join>\<^sub>1  0x00
   | Index        \<Rightarrow> 0x00  \<Join>\<^sub>2 0x00  \<Join>\<^sub>1  0x01
   | Ncaps ty     \<Rightarrow> \<lfloor>ty\<rfloor>  \<Join>\<^sub>2 0x00  \<Join>\<^sub>1  0x00
   | Cap ty i off \<Rightarrow> \<lfloor>ty\<rfloor>  \<Join>\<^sub>2 \<lfloor>i\<rfloor>   \<Join>\<^sub>1  off"

adhoc_overloading rep data_offset_rep

text \<open>Data offset representation is injective.\<close>

lemma data_offset_inj[dest]:
  "\<lfloor>d\<^sub>1\<rfloor> = \<lfloor>d\<^sub>2\<rfloor> \<Longrightarrow> d\<^sub>1 = d\<^sub>2" for d\<^sub>1 d\<^sub>2 :: data_offset
  unfolding data_offset_rep_def
  by (auto split:data_offset.splits)

text \<open>Least number of bytes to hold the current value of a data offset is @{text 3}.\<close>

lemma width_data_offset: "width \<lfloor>d\<rfloor> \<le> 3 * LENGTH(byte)" for d :: data_offset
  unfolding data_offset_rep_def
  by (simp split:data_offset.splits)

lemma width_data_offset'[simp]: "3 * LENGTH(byte) \<le> n \<Longrightarrow> width \<lfloor>d\<rfloor> \<le> n" for d :: data_offset
  using width_data_offset[of d] by simp

subsubsection \<open>Kernel storage address\<close>

text \<open>
  Type definition for procedure indices. A procedure index is represented as a natural number that
  is smaller then @{text "2\<^sup>1\<^sup>9\<^sup>2 - 1"}. It can be zero here, to simplify its future use as an array
  index, but its low-level representation will start from @{text 1}.
\<close>
typedef key_index = "{i :: nat. i < 2 ^ LENGTH(key) - 1}" morphisms key_index_rep' key_index
  by (rule exI[of _ "0"], simp)

adhoc_overloading rep key_index_rep'

adhoc_overloading abs key_index

text \<open>Introduce address datatype that describes possible addresses in the kernel storage.\<close>

datatype address =
   Heap_proc key data_offset
  | Nprocs
  | Proc_key key_index
  | Kernel
  | Curr_proc
  | Entry_proc

text \<open>Low-level representation of a procedure index is a machine word that starts from @{text 1}.\<close>

definition "key_index_rep i \<equiv> of_nat (\<lfloor>i\<rfloor> + 1) :: key" for i :: key_index

adhoc_overloading rep key_index_rep

text \<open>Proof that low-level representation can't be @{text 0}.\<close>

lemma key_index_nonzero[simp]: "\<lfloor>i\<rfloor> \<noteq> (0 :: key)" for i :: key_index
  unfolding key_index_rep_def using key_index_rep'[of i]
  by (intro of_nat_neq_0, simp_all)

text \<open>Low-level representation is injective.\<close>

lemma key_index_inj[dest]: "(\<lfloor>i\<^sub>1\<rfloor> :: key) = \<lfloor>i\<^sub>2\<rfloor> \<Longrightarrow> i\<^sub>1 = i\<^sub>2" for i :: key_index
  unfolding key_index_rep_def using key_index_rep'[of i\<^sub>1] key_index_rep'[of i\<^sub>2]
  by (simp add:key_index_rep'_inject of_nat_inj)

text \<open>Address prefix for all addresses that belong to the kernel storage.\<close>

abbreviation "kern_prefix \<equiv> 0xffffffff"

text \<open>
  Machine word representation of the kernel storage layout, which consists of the following
  addresses:
  \begin{itemize}
    \item @{text "Heap_proc k offs"}: procedure heap of key @{text k} and data offset @{text offs};
    \item @{text Nprocs}: number of procedures;
    \item @{text "Proc_key i"}: a procedure with index @{text i} in the procedure list;
    \item @{text Kernel}: kernel Ethereum address;
    \item @{text Curr_proc}: current procedure;
    \item @{text Entry_proc}: entry procedure.
  \end{itemize}
\<close>

definition addr_rep :: "address \<Rightarrow> word32" where
  "addr_rep a \<equiv> case a of
    Heap_proc k offs \<Rightarrow> kern_prefix \<Join>\<^sub>1 0x00 \<^sub>5\<diamond> k          \<Join>\<^sub>3 \<lfloor>offs\<rfloor>
  | Nprocs           \<Rightarrow> kern_prefix \<Join>\<^sub>1 0x01 \<^sub>5\<diamond> (0 :: key) \<Join>\<^sub>3 0x000000
  | Proc_key i       \<Rightarrow> kern_prefix \<Join>\<^sub>1 0x01 \<^sub>5\<diamond> \<lfloor>i\<rfloor>        \<Join>\<^sub>3 0x000000
  | Kernel           \<Rightarrow> kern_prefix \<Join>\<^sub>1 0x02 \<^sub>5\<diamond> (0 :: key) \<Join>\<^sub>3 0x000000
  | Curr_proc        \<Rightarrow> kern_prefix \<Join>\<^sub>1 0x03 \<^sub>5\<diamond> (0 :: key) \<Join>\<^sub>3 0x000000
  | Entry_proc       \<Rightarrow> kern_prefix \<Join>\<^sub>1 0x04 \<^sub>5\<diamond> (0 :: key) \<Join>\<^sub>3 0x000000"

adhoc_overloading rep addr_rep

text \<open>Kernel storage address representation is injective.\<close>

lemma addr_inj[dest]: "\<lfloor>a\<^sub>1\<rfloor> = \<lfloor>a\<^sub>2\<rfloor> \<Longrightarrow> a\<^sub>1 = a\<^sub>2" for a\<^sub>1 a\<^sub>2 :: address
  unfolding addr_rep_def
  by (split address.splits) (force split:address.splits)+

text \<open>Representation function is invertible.\<close>

lemmas addr_invertible[intro] = invertible.intro[OF injI, OF addr_inj]

interpretation addr_inv: invertible addr_rep ..

adhoc_overloading abs addr_inv.inv

text \<open>Lowest address of the kernel storage (0xffffffff0000...).\<close>

abbreviation "prefix_bound \<equiv> rpad (size kern_prefix) (ucast kern_prefix :: word32)"

lemma prefix_bound: "unat prefix_bound < 2 ^ LENGTH(word32)" unfolding rpad_def by simp

lemma prefix_bound'[simplified, simp]: "x \<le> unat prefix_bound \<Longrightarrow> x < 2 ^ LENGTH(word32)"
  using prefix_bound by simp

text \<open>All addresses in the kernel storage are indeed start with the kernel prefix (0xffffffff).\<close>

lemma addr_prefix[simp, intro]: "limited_and prefix_bound \<lfloor>a\<rfloor>" for a :: address
  unfolding limited_and_def addr_rep_def
  by (subst word_bw_comms) (auto split:address.split simp del:ucast_bintr)

subsection \<open>Capability formats\<close>

text \<open>
  We define capability format generally as a @{text locale}. It has two parameters: first one is a
  @{text "subset"} function (denoted as @{text "\<subseteq>\<^sub>c"}), and second one is a @{text "set_of"} function,
  which maps a capability to its high-level representation that is expressed as a set.
  We have an assumption that  @{text "Capability A"} is a subset of @{text "Capability B"} if and
  only if their high-level representations are also subsets of each other.
  We call it the well-definedness assumption (denoted as wd) and using it we can prove abstractly
  that such generic capability format satisfies the properties of reflexivity and transitivity.

  Then using this locale we can prove that capability formats of all available system calls
  satisfy the properties of reflexivity and transitivity simply by formalizing corresponding
  @{text "subset"} and @{text "set_of"} functions and then proving the well-definedness assumption.
  This process is called locale interpretation.
\<close>

no_notation abs ("\<lceil>_\<rceil>")

locale cap_sub =
  fixes set_of :: "'a \<Rightarrow> 'b set" ("\<lceil>_\<rceil>")
  fixes sub :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_/ \<subseteq>\<^sub>c _)" [51, 51] 50)
  assumes wd:"a \<subseteq>\<^sub>c b = (\<lceil>a\<rceil> \<subseteq> \<lceil>b\<rceil>)" begin

lemma sub_refl: "a \<subseteq>\<^sub>c a" using wd by auto

lemma sub_trans: "\<lbrakk>a \<subseteq>\<^sub>c b; b \<subseteq>\<^sub>c c\<rbrakk> \<Longrightarrow> a \<subseteq>\<^sub>c c" using wd by blast
end

notation abs ("\<lceil>_\<rceil>")

consts sub :: "'a \<Rightarrow> 'a \<Rightarrow> bool" ("(_/ \<subseteq>\<^sub>c _)" [51, 51] 50)

subsubsection \<open>Call, Register and Delete capabilities\<close>

text \<open>
  Call, Register and Delete capabilities have the same format, so we combine them together here.
  The capability format defines a range of procedure keys that the capability allows one
  to call. This is defined as a base procedure key and a prefix.

  Prefix is defined as a natural number, whose length is bounded by a maximum length of a procedure
  key.
\<close>

typedef prefix_size = "{n :: nat. n \<le> LENGTH(key)}"
  morphisms prefix_size_rep' prefix_size
  by auto

adhoc_overloading rep prefix_size_rep'

text \<open>Low-level representation of a prefix is a 8-bit machine word (or simply a byte).\<close>

definition "prefix_size_rep s \<equiv> of_nat \<lfloor>s\<rfloor> :: byte" for s :: prefix_size

adhoc_overloading rep prefix_size_rep

text \<open>Prefix representation is injective.\<close>

lemma prefix_size_inj[dest]: "(\<lfloor>s\<^sub>1\<rfloor> :: byte) = \<lfloor>s\<^sub>2\<rfloor> \<Longrightarrow> s\<^sub>1 = s\<^sub>2" for s\<^sub>1 s\<^sub>2 :: prefix_size
  unfolding prefix_size_rep_def using prefix_size_rep'[of s\<^sub>1] prefix_size_rep'[of s\<^sub>2]
  by (simp add:prefix_size_rep'_inject of_nat_inj)

text \<open>
  Any number that is greater or equal to a maximum length of a procedure key is greater or equal
  to any procedure index.
\<close>

lemma prefix_size_rep_less[simp]: "LENGTH(key) \<le> n \<Longrightarrow> \<lfloor>s\<rfloor> \<le> (n :: nat)" for s :: prefix_size
  using prefix_size_rep'[of s] by simp

text \<open>
  Capabilities that have the same format based on prefixes we call "prefixed". Type of prefixed
  capabilities is defined as a direct product of prefixes and procedure keys.
\<close>

type_synonym prefixed_capability = "prefix_size \<times> key"

text \<open>
  High-level representation of a prefixed capability is a set of all procedure keys whose first
  @{text s} number of bits (specified by the prefix) are the same as the first @{text s} number of
  bits of the base procedure key @{text k}.
\<close>

definition
  "set_of_pref_cap sk \<equiv> let (s, k) = sk in {k' :: key. take \<lfloor>s\<rfloor> (to_bl k') = take \<lfloor>s\<rfloor> (to_bl k)}"
  for sk :: prefixed_capability

adhoc_overloading abs set_of_pref_cap

text \<open>
  A prefixed capability A is a subset of a prefixed capability B if:
  \begin{itemize}
    \item the prefix size of A is equal to or greater than the prefix size of B;
    \item the first s bits (specified by the prefix size of B) of the base procedure of A is equal
          to the first s bits of the base procedure of B.
  \end{itemize}
\<close>

definition "pref_cap_sub A B \<equiv>
  let (s\<^sub>A, k\<^sub>A) = A; (s\<^sub>B, k\<^sub>B) = B in
  (\<lfloor>s\<^sub>A\<rfloor> :: nat) \<ge> \<lfloor>s\<^sub>B\<rfloor> \<and> take \<lfloor>s\<^sub>B\<rfloor> (to_bl k\<^sub>A) = take \<lfloor>s\<^sub>B\<rfloor> (to_bl k\<^sub>B)"
  for A B :: prefixed_capability

adhoc_overloading sub pref_cap_sub

text \<open>
  Auxiliary lemma: if first @{text n} elements of lists @{text a} and @{text b} are equal, and the
  number @{text i} is smaller than @{text n}, then the @{text ith} elements of both lists are
  also equal.
\<close>

lemma nth_take_i[dest]: "\<lbrakk>take n a = take n b; i < n\<rbrakk> \<Longrightarrow> a ! i = b ! i"
  by (metis nth_take)

lemma take_less_diff:
  fixes l' l'' :: "'a list"
  assumes ex:"\<And> u :: 'a. \<exists> u'. u' \<noteq> u"
  assumes "n < m"
  assumes "length l' = length l''"
  assumes "n \<le> length l'"
  assumes "m \<le> length l'"
  obtains l where
      "length l = length l'"
  and "take n l = take n l'"
  and "take m l \<noteq> take m l''"
proof-
  let ?x = "l'' ! n"
  from ex obtain y where neq:"y \<noteq> ?x" by auto
  let ?l = "take n l' @ y # drop (n + 1) l'"
  from assms have 0:"n = length (take n l') + 0" by simp
  from assms have "take n ?l = take n l'" by simp
  moreover from assms and neq have "take m ?l \<noteq> take m l''"
    using 0 nth_take_i nth_append_length
    by (metis add.right_neutral)
  moreover have "length ?l = length l'" using assms by auto
  ultimately show ?thesis using that by blast
qed

text \<open>Prove the well-definedness assumption for the prefixed capability format.\<close>

lemma pref_cap_sub_iff[iff]: "a \<subseteq>\<^sub>c b = (\<lceil>a\<rceil> \<subseteq> \<lceil>b\<rceil>)" for a b :: prefixed_capability
proof
  show "a \<subseteq>\<^sub>c b \<Longrightarrow> \<lceil>a\<rceil> \<subseteq> \<lceil>b\<rceil>"
    unfolding pref_cap_sub_def set_of_pref_cap_def
    by (force intro:nth_take_lemma)
  {
    fix n m :: prefix_size
    fix x y :: key
    assume "\<lfloor>n\<rfloor> < (\<lfloor>m\<rfloor> :: nat)"
    then obtain z where
      "length z = size x"
      "take \<lfloor>n\<rfloor> z = take \<lfloor>n\<rfloor> (to_bl x)" and "take \<lfloor>m\<rfloor> z \<noteq> take \<lfloor>m\<rfloor> (to_bl y)"
      using take_less_diff[of "\<lfloor>n\<rfloor>" "\<lfloor>m\<rfloor>" "to_bl x" "to_bl y"]
      by auto
    moreover hence "to_bl (of_bl z :: key) = z" by (intro word_bl.Abs_inverse[of z], simp)
    ultimately
    have "\<exists> u :: key.
           take \<lfloor>n\<rfloor> (to_bl u) = take \<lfloor>n\<rfloor> (to_bl x) \<and> take \<lfloor>m\<rfloor> (to_bl u) \<noteq> take \<lfloor>m\<rfloor> (to_bl y)"
      by metis
  }
  thus "\<lceil>a\<rceil> \<subseteq> \<lceil>b\<rceil> \<Longrightarrow> a \<subseteq>\<^sub>c b"
    unfolding pref_cap_sub_def set_of_pref_cap_def subset_eq
    apply (auto split:prod.split)
    by (erule contrapos_pp[of "\<forall> x. _ x"], simp)
qed

lemmas pref_cap_subsets[intro] = cap_sub.intro[OF pref_cap_sub_iff]

text \<open>
  Locale interpretation to prove the reflexivity and transitivity properties of a subset function
  of the prefixed capability format.
\<close>

interpretation pref_cap_sub: cap_sub set_of_pref_cap pref_cap_sub ..

text \<open>
  Low-level 32-byte machine word representation of the prefixed capability format:
  \begin{itemize}
    \item first byte is the prefix;
    \item next seven bytes are undefined;
    \item 24 bytes of the base procedure key.
  \end{itemize}
\<close>

definition "pref_cap_rep sk r \<equiv>
  let (s, k) = sk in \<lfloor>s\<rfloor> \<^sub>1\<diamond> k OR r \<restriction> {LENGTH(key)..<LENGTH(word32) - LENGTH(byte)}"
  for sk :: prefixed_capability

adhoc_overloading rep pref_cap_rep

text \<open>Low-level representation is injective.\<close>

lemma pref_cap_rep_inj_helper_inj[dest]: "\<lfloor>s\<^sub>1\<rfloor> \<^sub>1\<diamond> k\<^sub>1 = \<lfloor>s\<^sub>2\<rfloor> \<^sub>1\<diamond> k\<^sub>2 \<Longrightarrow> s\<^sub>1 = s\<^sub>2 \<and> k\<^sub>1 = k\<^sub>2"
  for s\<^sub>1 s\<^sub>2 :: prefix_size and k\<^sub>1 k\<^sub>2 :: key
  by auto

lemma pref_cap_rep_inj_helper_zero[simplified, simp]:
  "n \<in> {LENGTH(key)..<LENGTH(word32) - LENGTH(byte)} \<Longrightarrow> \<not> (\<lfloor>s\<rfloor> \<^sub>1\<diamond> k) !! n"
  for s :: prefix_size and k :: key
  by simp

lemma pref_cap_rep_inj[dest]: "\<lfloor>c\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>c\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> c\<^sub>1 = c\<^sub>2" for c\<^sub>1 c\<^sub>2 :: prefixed_capability
  unfolding pref_cap_rep_def
  by (auto split:prod.splits)

text \<open>Representation function is invertible.\<close>

lemmas pref_cap_invertible[intro] = invertible2.intro[OF inj2I, OF pref_cap_rep_inj]

interpretation pref_cap_inv: invertible2 pref_cap_rep ..

adhoc_overloading abs pref_cap_inv.inv2

subsubsection \<open>Write capability\<close>

text \<open>
  The write capability format includes 2 values: the first is the base address where we can write
  to storage. The second is the number of additional addresses we can write to.

  Note that write capability must not allow to write to the kernel storage.
\<close>

typedef write_capability = "{(a :: word32, n). n < unat prefix_bound - unat a}"
  morphisms write_cap_rep' write_cap
  unfolding rpad_def
  by (intro exI[of _ "(0, 0)"], simp)

adhoc_overloading rep write_cap_rep'

text \<open>A write capability is correctly bounded by the lowest kernel storage address.\<close>

lemma write_cap_additional_bound[simplified, simp]:
  "snd \<lfloor>w\<rfloor> < unat prefix_bound" for w :: write_capability
  using write_cap_rep'[of w]
  by (auto split:prod.split)

lemma write_cap_additional_bound'[simplified, simp]:
  "unat prefix_bound \<le> n \<Longrightarrow> \<lfloor>w\<rfloor> = (a, b) \<Longrightarrow> b < n"
  using write_cap_additional_bound[of w] by simp

lemma write_cap_bound: "unat (fst \<lfloor>w\<rfloor>) + snd \<lfloor>w\<rfloor> < unat prefix_bound"
  using write_cap_rep'[of w]
  by (simp split:prod.splits)

lemma write_cap_bound'[simplified, simp]: "\<lfloor>w\<rfloor> = (a, b) \<Longrightarrow> unat a + b < unat prefix_bound"
  using write_cap_bound[of w] by simp

text \<open>
  There is no possible overflow in adding the number of additional addresses to the base write
  address.
\<close>

lemma write_cap_no_overflow: "fst \<lfloor>w\<rfloor> \<le> fst \<lfloor>w\<rfloor> + of_nat (snd \<lfloor>w\<rfloor>)" for w :: write_capability
  by (simp add:word_le_nat_alt unat_of_nat_eq less_imp_le)

lemma write_cap_no_overflow'[simp]: "\<lfloor>w\<rfloor> = (a, b) \<Longrightarrow> a \<le> a + of_nat b"
  for w :: write_capability
  using write_cap_no_overflow[of w] by simp

text \<open>
  Auxiliary lemma: the @{text ith} element of the kernel address prefix is binary @{text 1} if and
  only if @{text i} is smaller then the size of the prefix, otherwise it is @{text 0}.
\<close>

lemma nth_kern_prefix: "kern_prefix !! i = (i < size kern_prefix)"
proof-
  fix i
  {
    fix c :: nat
    assume "i < c"
    then consider "i = c - 1" | "i < c - 1 \<and> c \<ge> 1"
      by fastforce
  } note elim = this
  have "i < size kern_prefix \<Longrightarrow> kern_prefix !! i"
    by (subst test_bit_bl, (erule elim, simp_all)+)
  moreover have "i \<ge> size kern_prefix \<Longrightarrow> \<not> kern_prefix !! i" by simp
  ultimately show "kern_prefix !! i = (i < size kern_prefix)" by auto
qed

text \<open>
  The @{text ith} bit of the lowest kernel address is @{text 1} if and only if @{text i} is smaller
  or equal to the size of the kernel prefix, otherwise it is @{text 0}.
\<close>

lemma nth_prefix_bound[iff]:
  "prefix_bound !! i = (i \<in> {LENGTH(word32) - size (kern_prefix)..<LENGTH(word32)})"
  (is "_ = (i \<in> {?l..<?r})")
proof-
  have 0:"is_up (ucast :: 32 word \<Rightarrow> word32)" by simp
  have 1:"width (ucast kern_prefix :: word32) \<le> size kern_prefix"
    using width_ucast[of kern_prefix, OF 0] by (simp del:width_iff)
  fix i
  show "prefix_bound !! i = (i \<in> {?l..<?r})"
    using rpad_high
      [of "(ucast)\<^bsub>(len TYPE(word32))\<^esub> kern_prefix" "size (kern_prefix)" i, OF 1, simplified]
      rpad_low
      [of "(ucast)\<^bsub>(len TYPE(word32))\<^esub> kern_prefix" "size (kern_prefix)" i, OF 1, simplified]
      nth_kern_prefix[of "i - ?l", simplified] nth_ucast[of kern_prefix i, simplified]
      test_bit_size[of prefix_bound i, simplified]
  by (simp (no_asm_simp)) linarith
qed

text \<open>Addresses from write capabilities can not contain the prefix of the kernel storage.\<close>

lemma write_cap_high[dest]:
  "unat a < unat prefix_bound \<Longrightarrow>
   \<exists> i \<in> {LENGTH(word32) - size (kern_prefix)..<LENGTH(word32)}. \<not> a !! i"
  (is "_ \<Longrightarrow> \<exists> i \<in> {?l..<?r}. _")
  for a :: word32
proof (rule ccontr, simp del:word_size len_word ucast_bintr)
  {
    fix i
    have "(ucast kern_prefix :: word32) !! i = (i < size kern_prefix)"
      using nth_kern_prefix[of i] nth_ucast[of kern_prefix i] by auto
    moreover assume "i + ?l < ?r \<Longrightarrow> a !! (i + ?l)"
    ultimately have "(a >> ?l) !! i = (ucast kern_prefix :: word32) !! i"
      using nth_shiftr[of a ?l i] by fastforce
  }
  moreover assume "\<forall>i\<in>{?l..<?r}. a !! i"
  ultimately have "a >> ?l = ucast kern_prefix" unfolding word_eq_iff using nth_ucast by auto
  moreover have "unat (a >> ?l) = unat a div 2 ^ ?l" using shiftr_div_2n' by blast
  moreover have "unat (ucast kern_prefix :: word32) = unat kern_prefix"
    by (rule unat_ucast_upcast, simp)
  ultimately have "unat a div 2 ^ ?l = unat kern_prefix" by simp
  hence "unat a \<ge> unat kern_prefix * 2 ^ ?l" by simp
  hence "unat a \<ge> unat prefix_bound" unfolding rpad_def by simp
  also assume "unat a < unat prefix_bound"
  finally show False ..
qed

text \<open>
  High-level representation of a write capability is a set of all addresses to which the capability
  allows to write.
\<close>

definition "set_of_write_cap w \<equiv> let (a, n) = \<lfloor>w\<rfloor> in {a .. a + of_nat n}" for w :: write_capability

adhoc_overloading abs set_of_write_cap

text \<open>
  A write capability A is a subset of a write capability B if:
  \begin{itemize}
    \item the lowest writable address (which is the base address) of B is less than or equal to
          the lowest writable address of A;
    \item the highest writable address (which is base address plus the number of additional keys)
          of A is less than or equal to the highest writable address of B.
  \end{itemize}
\<close>

definition "write_cap_sub A B \<equiv>
  let (a\<^sub>A, n\<^sub>A) = \<lfloor>A\<rfloor> in let (a\<^sub>B, n\<^sub>B) = \<lfloor>B\<rfloor> in a\<^sub>B \<le> a\<^sub>A \<and> a\<^sub>A + of_nat n\<^sub>A \<le> a\<^sub>B + of_nat n\<^sub>B"
  for A B :: write_capability

adhoc_overloading sub write_cap_sub

text \<open>Prove the well-definedness assumption for the write capability format.\<close>

lemma write_cap_sub_iff[iff]: "a \<subseteq>\<^sub>c b = (\<lceil>a\<rceil> \<subseteq> \<lceil>b\<rceil>)" for a b :: write_capability
  unfolding write_cap_sub_def set_of_write_cap_def
  by (auto split:prod.splits)

lemmas write_cap_subsets[intro] = cap_sub.intro[OF write_cap_sub_iff]

text \<open>
  Locale interpretation to prove the reflexivity and transitivity properties of a subset function
  of the write capability format.
\<close>

interpretation write_cap_sub: cap_sub set_of_write_cap write_cap_sub ..

text \<open>
  Low-level representation of the write capability format is a 32-byte machine word list of two
  elements:
  \begin{itemize}
    \item the base address;
    \item the number of additional addresses (also as a machine word).
  \end{itemize}
\<close>

definition "write_cap_rep w \<equiv> let (a, n) = \<lfloor>w\<rfloor> in (a, of_nat n :: word32)"

adhoc_overloading rep write_cap_rep

text \<open>Low-level representation is injective.\<close>

lemma write_cap_inj[dest]: "(\<lfloor>w\<^sub>1\<rfloor> :: word32 \<times> word32) = \<lfloor>w\<^sub>2\<rfloor> \<Longrightarrow> w\<^sub>1 = w\<^sub>2"
  for w\<^sub>1 w\<^sub>2 :: write_capability
  unfolding write_cap_rep_def
  by (auto
      split:prod.splits iff:write_cap_rep'_inject[symmetric]
      intro!:word_of_nat_inj simp add:rpad_def)

text \<open>Representation function is invertible.\<close>

lemmas write_cap_invertible[intro] = invertible.intro[OF injI, OF write_cap_inj]

interpretation write_cap_inv: invertible write_cap_rep ..

adhoc_overloading abs write_cap_inv.inv

text \<open>
  An address from the high-level representation of the write capability must be below the lowest
  kernel storage address.
\<close>

lemma write_cap_prefix[dest]: "a \<in> \<lceil>w\<rceil> \<Longrightarrow> \<not> limited_and prefix_bound a" for w :: write_capability
proof
  assume "a \<in> \<lceil>w\<rceil>"
  hence "unat a < unat prefix_bound"
    unfolding set_of_write_cap_def
    apply (simp split:prod.splits)
    using write_cap_bound'[of w] word_less_nat_alt word_of_nat_less by fastforce
  then obtain n where "n\<in>{LENGTH(256 word) - size kern_prefix..<LENGTH(256 word)}" and "\<not> a !! n"
    using write_cap_high[of a] by auto
  moreover assume "limited_and prefix_bound a"
  ultimately show False
    unfolding limited_and_def word_eq_iff
    by (subst (asm) nth_prefix_bound, auto)
qed

text \<open>
  An address from the high-level representation is different from any address from the kernel
  storage.
\<close>

lemma write_cap_safe[simp]: "a \<in> \<lceil>w\<rceil> \<Longrightarrow> a \<noteq> \<lfloor>a'\<rfloor>" for w :: write_capability and a' :: address
  by auto

declare
  write_cap_additional_bound'[simp del] write_cap_bound'[simp del] write_cap_no_overflow'[simp del]

subsubsection \<open>Log capability\<close>

text \<open>
  The log capability format includes between 0 and 4 values for log topics and 1 value that
  specifies the number of enforced topics. We model it as a 32-byte machine word list whose length
  is between 0 and 4.
\<close>

typedef log_capability = "{ws :: word32 list. length ws \<le> 4}"
  morphisms log_cap_rep' log_capability
  by (intro exI[of _ "[]"], simp)

adhoc_overloading rep log_cap_rep'

text \<open>
  High-level representation of a log capability is a set of all possible log capabilities whose
  list prefix in the same and equals to the given log capability.
\<close>

definition "set_of_log_cap l \<equiv> {xs . prefix \<lfloor>l\<rfloor> xs}" for l :: log_capability

adhoc_overloading abs set_of_log_cap

text \<open>
  A log capability A is a subset of a log capability B if for each log topic of B the topic
  is either undefined or equal to that of A. But here we specify that A is a subset of B  if B is a
  list prefix for A. Below we prove that this conditions are equivalent.
\<close>

definition "log_cap_sub A B \<equiv> prefix \<lfloor>B\<rfloor> \<lfloor>A\<rfloor>" for A B :: log_capability

adhoc_overloading sub log_cap_sub

text \<open>Prove the well-definedness assumption for the log capability format.\<close>

lemma log_cap_sub_iff[iff]: "a \<subseteq>\<^sub>c b = (\<lceil>a\<rceil> \<subseteq> \<lceil>b\<rceil>)" for a b :: log_capability
  unfolding log_cap_sub_def set_of_log_cap_def
  by force

lemmas log_cap_subsets[intro] = cap_sub.intro[OF log_cap_sub_iff]

text \<open>
  Locale interpretation to prove the reflexivity and transitivity properties of a subset function
  of the log capability format.
\<close>

interpretation log_cap_sub: cap_sub set_of_log_cap log_cap_sub ..

text \<open>Proof that that the log capability subset is defined according to the specification.\<close>

lemma "a \<subseteq>\<^sub>c b = (\<forall>i < length \<lfloor>b\<rfloor> . \<lfloor>a\<rfloor> ! i = \<lfloor>b\<rfloor> ! i \<and> i < length \<lfloor>a\<rfloor>)"
  (is "_ = ?R") for a b :: log_capability
  unfolding log_cap_sub_def prefix_def
proof
  let ?L = "\<exists>zs. \<lfloor>a\<rfloor> = \<lfloor>b\<rfloor> @ zs"
  {
    assume ?L
    moreover hence "length \<lfloor>b\<rfloor> \<le> length \<lfloor>a\<rfloor>" by auto
    ultimately show "?L \<Longrightarrow> ?R"
      by (auto simp add:nth_append)
  next
    assume ?R
    moreover hence len:"length \<lfloor>b\<rfloor> \<le> length \<lfloor>a\<rfloor>"
      using le_def by blast
    moreover from \<open>?R\<close> have "\<lfloor>a\<rfloor> = take (length \<lfloor>b\<rfloor>) \<lfloor>a\<rfloor> @ drop (length \<lfloor>b\<rfloor>) \<lfloor>a\<rfloor> "
      by simp
    moreover from \<open>?R\<close> len have "take (length \<lfloor>b\<rfloor>) \<lfloor>a\<rfloor> = \<lfloor>b\<rfloor>"
      by (metis nth_take_lemma order_refl take_all)
    ultimately show "?R \<Longrightarrow> ?L" by (intro exI[of _ "drop (length \<lfloor>b\<rfloor>) \<lfloor>a\<rfloor>"], arith)
  }
qed


text \<open>
  Low-level representation of the log capability format is a 32-byte machine word list that includes
  between 1 and 5 values. First value is the number of enforced topics and the rest are possible
  values for log topics.
\<close>

definition "log_cap_rep l \<equiv> (of_nat (length \<lfloor>l\<rfloor>) :: word32) # \<lfloor>l\<rfloor>"

no_adhoc_overloading rep log_cap_rep'

adhoc_overloading rep log_cap_rep

text \<open>Low-level representation is injective.\<close>

lemma log_cap_rep_inj[dest]: "(\<lfloor>l\<^sub>1\<rfloor> :: word32 list) = \<lfloor>l\<^sub>2\<rfloor> \<Longrightarrow> l\<^sub>1 = l\<^sub>2" for l\<^sub>1 l\<^sub>2 :: log_capability
  unfolding log_cap_rep_def using log_cap_rep'_inject by auto

text \<open>Representation function is invertible.\<close>

lemmas log_cap_rep_invertible[intro] = invertible.intro[OF injI, OF log_cap_rep_inj]

interpretation log_cap_inv: invertible log_cap_rep ..

adhoc_overloading abs log_cap_inv.inv

text \<open>
  Length of a low-level representation is correct: it is the length of the topics list plus 1 for
  storing the number of topics.
\<close>

lemma log_cap_rep_length[simp]: "length \<lfloor>l\<rfloor> = length (log_cap_rep' l) + 1"
  unfolding log_cap_rep_def by simp

subsubsection \<open>External call capability\<close>

text \<open>
  We model the external call capability format using a record with two fields: @{text "allow_addr"}
  and @{text "may_send"}, with the following semantic:
  \begin{itemize}
    \item if the field  @{text "allow_addr"} has value, then only the Ethereum address specified
          by it can be called, otherwise any address can be called. This models the @{text CallAny}
          flag and the @{text EthAddress} together;
    \item if the value of the field  @{text "may_send"} is true, the any quantity of Ether can be
          sent, otherwise no Ether can be sent. It models the @{text SendValue} flag.
  \end{itemize}
\<close>

type_synonym ethereum_address = "160 word" \<comment> \<open>20 bytes\<close>

record external_call_capability =
  allow_addr :: "ethereum_address option"
  may_send   :: bool

text \<open>
  High-level representation of an external call capability is a set of all possible pairs of account
  addresses and Ether amount that can be sent using this capability.
\<close>

definition "set_of_ext_cap e \<equiv>
  {(a, v) . case_option True ((=) a) (allow_addr e) \<and> (\<not> may_send e \<longrightarrow> v = (0 :: word32)) }"

adhoc_overloading abs set_of_ext_cap

text \<open>
  Auxiliary abbreviation: @{text "allow_any e"} returns @{text True} if the field @{text allow_addr}
  of the capability @{text e} does not contain any value, and @{text False} otherwise.
\<close>

abbreviation "allow_any e \<equiv> Option.is_none (allow_addr e)"

text \<open>
  Auxiliary abbreviation: @{text "the_addr e"} returns the value of the field @{text allow_addr}
  of the capability @{text e}. It can be used only if @{text "allow_any e"} is @{text False}.
\<close>

abbreviation "the_addr e \<equiv> the (allow_addr e)"

text \<open>
  An external call capability A is a subset of an external call capability B if and only if:
  \begin{itemize}
    \item if A allows to call any Ethereum address, then B also must allow to call any address;
    \item if A allows to call only specified Ethereum address, then B either must allow to call any
          address, or it must allow to only call the same address as A;
    \item if A may send Ether, then B also must be able to send Ether.
  \end{itemize}
\<close>

definition "ext_cap_sub A B \<equiv>
    (allow_any A \<longrightarrow> allow_any B)
  \<and> ((\<not> allow_any A \<longrightarrow> allow_any B) \<or> (the_addr A = the_addr B))
  \<and> (may_send A \<longrightarrow> may_send B)"
  for A B :: external_call_capability

adhoc_overloading sub ext_cap_sub

text \<open>Prove the well-definedness assumption for the external call capability format.\<close>

lemma ext_cap_sub_iff[iff]: "a \<subseteq>\<^sub>c b = (\<lceil>a\<rceil> \<subseteq> \<lceil>b\<rceil>)" for a b :: external_call_capability
proof-
  {
    fix v' :: word32
    have "\<exists> v. v \<noteq> v'" by (intro exI[of _ "v' - 1"], simp)
  } note [intro] = this
  {
    fix a' :: ethereum_address
    have "\<exists> a. a \<noteq> a'" by (intro exI[of _ "a' - 1"], simp)
  } note [intro] = this
  show ?thesis
  unfolding set_of_ext_cap_def ext_cap_sub_def
  by (cases "allow_addr a";
      cases "allow_addr b";
      cases "may_send a";
      cases "may_send b",
      auto iff:subset_iff)
qed

lemmas ext_cap_subsets[intro] = cap_sub.intro[OF ext_cap_sub_iff]

text \<open>
  Locale interpretation to prove the reflexivity and transitivity properties of a subset function
  of the external call capability format.
\<close>

interpretation ext_cap_sub: cap_sub set_of_ext_cap ext_cap_sub ..

text \<open>Helper functions to define low-level representation.\<close>

definition "ext_cap_val e \<equiv>
  (of_bl ([allow_any e, may_send e]
          @ replicate 6 False) :: byte) \<^sub>1\<diamond> case_option 0 id (allow_addr e)"

definition "ext_cap_frame e \<equiv>
  {if allow_any e then 0 else LENGTH(ethereum_address)..<LENGTH(word32) - LENGTH(byte)}"

text \<open>
  Low-level 32-byte machine word representation of the external call capability format:
  \begin{itemize}
    \item first bit is the CallAny flag;
    \item second bit is the SendValue flag;
    \item 6 undefined bits;
    \item 11 undefined bytes;
    \item 20 bytes of the Ethereum address.
  \end{itemize}
\<close>

definition "ext_cap_rep e r \<equiv>  ext_cap_val e OR r \<restriction> ext_cap_frame e"
  for e :: external_call_capability

adhoc_overloading rep ext_cap_rep

text \<open>Low-level representation is injective.\<close>

lemma ext_cap_rep_helper_inj[dest]: "ext_cap_val e\<^sub>1 = ext_cap_val e\<^sub>2 \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
  for e\<^sub>1 e\<^sub>2 :: external_call_capability
  unfolding ext_cap_val_def
  by (cases "allow_any e\<^sub>1"; cases "allow_any e\<^sub>2")
     (auto simp del:of_bl_True of_bl_False dest:word_bl.Abs_eqD split:option.splits)

lemma ext_cap_rep_helper_zero[simp]: "n \<in> ext_cap_frame e \<Longrightarrow> \<not> ext_cap_val e !! n"
  unfolding ext_cap_frame_def ext_cap_val_def
  by (auto simp del:of_bl_True split:option.split)

lemma ext_cap_rep_inj[dest]: "\<lfloor>e\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>e\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> e\<^sub>1 = e\<^sub>2" for e\<^sub>1 e\<^sub>2 :: external_call_capability
proof (erule rev_mp; cases "allow_any e\<^sub>1"; cases "allow_any e\<^sub>2")
  let ?goal = "\<lfloor>e\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>e\<^sub>2\<rfloor> r\<^sub>2 \<longrightarrow> e\<^sub>1 = e\<^sub>2"
  {
    {
      fix P e
      have "allow_any e \<Longrightarrow> (\<And>s. P \<lparr> allow_addr = None, may_send = s \<rparr>) \<Longrightarrow> P e"
        by (cases e, simp add:Option.is_none_def)
    } note[elim!] = this
    note [dest] =
      restrict_inj2[of "\<lambda> s (_ :: unit). ext_cap_val \<lparr> allow_addr = None, may_send = s \<rparr>"]
    assume "allow_any e\<^sub>1" and "allow_any e\<^sub>2"
    thus ?goal unfolding ext_cap_rep_def by (auto simp add:ext_cap_frame_def)
  next
    {
      fix P e
      have "\<not> allow_any e \<Longrightarrow> (\<And>a s. P \<lparr> allow_addr = Some a, may_send = s \<rparr>) \<Longrightarrow> P e"
        by (cases e, auto simp add:Option.is_none_def)
    } note [elim!] = this
    note [dest] = restrict_inj2[of "\<lambda> a s. ext_cap_val \<lparr> allow_addr = Some a, may_send = s \<rparr>"]
    assume "\<not> allow_any e\<^sub>1" and "\<not> allow_any e\<^sub>2"
    thus ?goal unfolding ext_cap_rep_def by (auto simp add:ext_cap_frame_def)
  next
    let ?neq = "allow_any e\<^sub>1 \<noteq> allow_any e\<^sub>2"
    {
      presume ?neq
      moreover hence "msb (ext_cap_val e\<^sub>1) \<noteq> msb (ext_cap_val e\<^sub>2)"
        unfolding ext_cap_val_def msb_nth
        by (auto simp del:of_bl_True of_bl_False simp add:pad_join_high iff:test_bit_of_bl)
      ultimately show ?goal
        unfolding ext_cap_rep_def ext_cap_frame_def word_eq_iff msb_nth word_or_nth nth_restrict
        by simp  (meson less_irrefl numeral_less_iff semiring_norm(76) semiring_norm(81))
      thus ?goal .
    next
      assume "allow_any e\<^sub>1" and "\<not> allow_any e\<^sub>2"
      thus ?neq by simp
    next
      assume "\<not> allow_any e\<^sub>1" and "allow_any e\<^sub>2"
      thus ?neq by simp
    }
  }
qed

text \<open>Representation function is invertible.\<close>

lemmas ext_cap_invertible[intro] = invertible2.intro[OF inj2I, OF ext_cap_rep_inj]

interpretation ext_cap_inv: invertible2 ext_cap_rep ..

adhoc_overloading abs ext_cap_inv.inv2

section \<open>Kernel state\<close>

text \<open>This section contains definition of the kernel state.\<close>

subsection \<open>Procedure data\<close>

text \<open>
  Introduce @{text "'a capability_list"} type that is a list of capabilities of a specific type
  @{text "'a"}, whose length is smaller than 255.
\<close>

typedef 'a capability_list = "{l :: 'a list. length l < 2 ^ LENGTH(byte) - 1}"
  morphisms cap_list_rep cap_list
  by (intro exI[of _ "[]"], simp)

adhoc_overloading rep cap_list_rep

text \<open>
  We model a procedure using a record with the following fields:
  \begin{itemize}
    \item @{text eth_addr} field stores the Ethereum address of the procedure;
    \item @{text entry_cap} field is @{text True} if the procedure is the entry procedure, and
          @{text False} otherwise;
    \item other fields are lists of capabilities of corresponding types assigned to the procedure.
  \end{itemize}
\<close>

record procedure =
  eth_addr   :: ethereum_address
  call_caps  :: "prefixed_capability capability_list"
  reg_caps   :: "prefixed_capability capability_list"
  del_caps   :: "prefixed_capability capability_list"
  entry_cap  :: bool
  write_caps :: "write_capability capability_list"
  log_caps   :: "log_capability capability_list"
  ext_caps   :: "external_call_capability capability_list"

lemmas alist_simps = size_alist_def alist.Alist_inverse alist.impl_of_inverse

declare alist_simps[simp]

text \<open>
  Low-level representation of the capability as it is stored in the kernel storage: given the
  procedure, the capability type, index and offset, it checks that all parameters are valid and
  correct and returns the machine word representation of the capability.
\<close>

definition "caps_rep (k :: key) p r ty (i :: capability_index) (off :: capability_offset) \<equiv>
  let addr = \<lfloor>Heap_proc k (Cap ty i off)\<rfloor> in
  case ty of
    Call  \<Rightarrow> if \<lfloor>i\<rfloor> < length \<lfloor>call_caps p\<rfloor> \<and> off = 0
             then \<lfloor>\<lfloor>call_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> (r addr)
             else r addr

  | Reg   \<Rightarrow> if \<lfloor>i\<rfloor> < length \<lfloor>reg_caps p\<rfloor> \<and> off = 0
             then \<lfloor>\<lfloor>reg_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> (r addr)
             else r addr
  | Del   \<Rightarrow> if \<lfloor>i\<rfloor> < length \<lfloor>del_caps p\<rfloor> \<and> off = 0
             then \<lfloor>\<lfloor>del_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> (r addr)
             else r addr
  | Entry \<Rightarrow> r addr
  | Write \<Rightarrow> if \<lfloor>i\<rfloor> < length \<lfloor>write_caps p\<rfloor>
             then
               if off = 0x00      then fst (\<lfloor>\<lfloor>write_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> :: _ \<times> word32)
               else if off = 0x01 then snd \<lfloor>\<lfloor>write_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor>
               else                    r addr
             else                      r addr
  | Log   \<Rightarrow> if \<lfloor>i\<rfloor> < length \<lfloor>log_caps p\<rfloor>
             then
               if unat off < length \<lfloor>\<lfloor>log_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> then \<lfloor>\<lfloor>log_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> ! unat off
               else                                          r addr
             else                                            r addr
  | Send  \<Rightarrow> if \<lfloor>i\<rfloor> < length \<lfloor>ext_caps p\<rfloor> \<and> off = 0
             then \<lfloor>\<lfloor>ext_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> (r addr)
             else r addr"

text \<open>Capability representation is injective.\<close>

lemma caps_rep_inj[dest]:
  assumes "caps_rep k\<^sub>1 p\<^sub>1 r\<^sub>1 = caps_rep k\<^sub>2 p\<^sub>2 r\<^sub>2"
  shows   "length \<lfloor>call_caps p\<^sub>1\<rfloor> = length \<lfloor>call_caps p\<^sub>2\<rfloor>   \<Longrightarrow> call_caps p\<^sub>1 = call_caps p\<^sub>2"
    and   "length \<lfloor>reg_caps p\<^sub>1\<rfloor> = length \<lfloor>reg_caps p\<^sub>2\<rfloor>     \<Longrightarrow> reg_caps p\<^sub>1 = reg_caps p\<^sub>2"
    and   "length \<lfloor>del_caps p\<^sub>1\<rfloor> = length \<lfloor>del_caps p\<^sub>2\<rfloor>     \<Longrightarrow> del_caps p\<^sub>1 = del_caps p\<^sub>2"
    and   "length \<lfloor>write_caps p\<^sub>1\<rfloor> = length \<lfloor>write_caps p\<^sub>2\<rfloor> \<Longrightarrow> write_caps p\<^sub>1 = write_caps p\<^sub>2"
    and   "length \<lfloor>log_caps p\<^sub>1\<rfloor> = length \<lfloor>log_caps p\<^sub>2\<rfloor>     \<Longrightarrow> log_caps p\<^sub>1 = log_caps p\<^sub>2"
    and   "length \<lfloor>ext_caps p\<^sub>1\<rfloor> = length \<lfloor>ext_caps p\<^sub>2\<rfloor>     \<Longrightarrow> ext_caps p\<^sub>1 = ext_caps p\<^sub>2"
proof-
  from assms have eq:"\<And> ty i off. caps_rep k\<^sub>1 p\<^sub>1 r\<^sub>1 ty i off = caps_rep k\<^sub>2 p\<^sub>2 r\<^sub>2 ty i off"
    by simp
  note Let_def[simp] if_splits[split] nth_equalityI[intro] cap_list_rep_inject[symmetric, iff]
  {
    fix i :: nat
    let ?addr\<^sub>1 = "\<lfloor>Heap_proc k\<^sub>1 (Cap Call \<lceil>i\<rceil> 0)\<rfloor>"
    and ?addr\<^sub>2 = "\<lfloor>Heap_proc k\<^sub>2 (Cap Call \<lceil>i\<rceil> 0)\<rfloor>"
    assume idx:"i < length \<lfloor>call_caps p\<^sub>1\<rfloor>"
    hence 0:"i \<in>  {i. i < 2 ^ LENGTH(8 word) - 1}"
      using cap_list_rep[of "call_caps p\<^sub>1"] by simp
    assume "length \<lfloor>call_caps p\<^sub>1\<rfloor> = length \<lfloor>call_caps p\<^sub>2\<rfloor>"
    with idx eq[of Call "\<lceil>i\<rceil>" 0]
    have "\<lfloor>\<lfloor>call_caps p\<^sub>1\<rfloor> ! i\<rfloor> (r\<^sub>1 ?addr\<^sub>1) = \<lfloor>\<lfloor>call_caps p\<^sub>2\<rfloor> ! i\<rfloor> (r\<^sub>2 ?addr\<^sub>2)"
      unfolding caps_rep_def by (simp add:cap_index_inverse[OF 0])
  }
  thus "length \<lfloor>call_caps p\<^sub>1\<rfloor> = length \<lfloor>call_caps p\<^sub>2\<rfloor> \<Longrightarrow> call_caps p\<^sub>1 = call_caps p\<^sub>2"
    by force

  {
    fix i :: nat
    let ?addr\<^sub>1 = "\<lfloor>Heap_proc k\<^sub>1 (Cap Reg \<lceil>i\<rceil> 0)\<rfloor>"
    and ?addr\<^sub>2 = "\<lfloor>Heap_proc k\<^sub>2 (Cap Reg \<lceil>i\<rceil> 0)\<rfloor>"
    assume idx:"i < length \<lfloor>reg_caps p\<^sub>1\<rfloor>"
    hence 0:"i \<in>  {i. i < 2 ^ LENGTH(8 word) - 1}"
      using capability_list.cap_list_rep[of "reg_caps p\<^sub>1"] by simp
    assume "length \<lfloor>reg_caps p\<^sub>1\<rfloor> = length \<lfloor>reg_caps p\<^sub>2\<rfloor>"
    with idx eq[of Reg "\<lceil>i\<rceil>" 0]
    have "\<lfloor>\<lfloor>reg_caps p\<^sub>1\<rfloor> ! i\<rfloor> (r\<^sub>1 ?addr\<^sub>1) = \<lfloor>\<lfloor>reg_caps p\<^sub>2\<rfloor> ! i\<rfloor> (r\<^sub>2 ?addr\<^sub>2)"
      unfolding caps_rep_def by (simp add:cap_index_inverse[OF 0])
  }
  thus "length \<lfloor>reg_caps p\<^sub>1\<rfloor> = length \<lfloor>reg_caps p\<^sub>2\<rfloor> \<Longrightarrow> reg_caps p\<^sub>1 = reg_caps p\<^sub>2"
    by force

  {
    fix i :: nat
    let ?addr\<^sub>1 = "\<lfloor>Heap_proc k\<^sub>1 (Cap Del \<lceil>i\<rceil> 0)\<rfloor>"
    and ?addr\<^sub>2 = "\<lfloor>Heap_proc k\<^sub>2 (Cap Del \<lceil>i\<rceil> 0)\<rfloor>"
    assume idx:"i < length \<lfloor>del_caps p\<^sub>1\<rfloor>"
    hence 0:"i \<in>  {i. i < 2 ^ LENGTH(8 word) - 1}"
      using cap_list_rep[of "del_caps p\<^sub>1"] by simp
    assume "length \<lfloor>del_caps p\<^sub>1\<rfloor> = length \<lfloor>del_caps p\<^sub>2\<rfloor>"
    with idx eq[of Del "\<lceil>i\<rceil>" 0]
    have "\<lfloor>\<lfloor>del_caps p\<^sub>1\<rfloor> ! i\<rfloor> (r\<^sub>1 ?addr\<^sub>1) = \<lfloor>\<lfloor>del_caps p\<^sub>2\<rfloor> ! i\<rfloor> (r\<^sub>2 ?addr\<^sub>2)"
      unfolding caps_rep_def by (simp add:cap_index_inverse[OF 0])
  }
  thus "length \<lfloor>del_caps p\<^sub>1\<rfloor> = length \<lfloor>del_caps p\<^sub>2\<rfloor> \<Longrightarrow> del_caps p\<^sub>1 = del_caps p\<^sub>2"
    by force

  {
    fix i :: nat
    let ?addr\<^sub>1 = "\<lfloor>Heap_proc k\<^sub>1 (Cap Send \<lceil>i\<rceil> 0)\<rfloor>"
    and ?addr\<^sub>2 = "\<lfloor>Heap_proc k\<^sub>2 (Cap Send \<lceil>i\<rceil> 0)\<rfloor>"
    assume idx:"i < length \<lfloor>ext_caps p\<^sub>1\<rfloor>"
    hence 0:"i \<in>  {i. i < 2 ^ LENGTH(8 word) - 1}"
      using capability_list.cap_list_rep[of "ext_caps p\<^sub>1"] by simp
    assume "length \<lfloor>ext_caps p\<^sub>1\<rfloor> = length \<lfloor>ext_caps p\<^sub>2\<rfloor>"
    with idx eq[of Send "\<lceil>i\<rceil>" 0]
    have "\<lfloor>\<lfloor>ext_caps p\<^sub>1\<rfloor> ! i\<rfloor> (r\<^sub>1 ?addr\<^sub>1) = \<lfloor>\<lfloor>ext_caps p\<^sub>2\<rfloor> ! i\<rfloor> (r\<^sub>2 ?addr\<^sub>2)"
      unfolding caps_rep_def by (simp add:cap_index_inverse[OF 0])
  }
  thus "length \<lfloor>ext_caps p\<^sub>1\<rfloor> = length \<lfloor>ext_caps p\<^sub>2\<rfloor> \<Longrightarrow> ext_caps p\<^sub>1 = ext_caps p\<^sub>2"
    by force

  {
    fix i :: nat
    let ?addr\<^sub>1 = "\<lfloor>Heap_proc k\<^sub>1 (Cap Write \<lceil>i\<rceil> 0)\<rfloor>"
    and ?addr\<^sub>2 = "\<lfloor>Heap_proc k\<^sub>2 (Cap Write \<lceil>i\<rceil> 0)\<rfloor>"
    assume idx:"i < length \<lfloor>write_caps p\<^sub>1\<rfloor>"
    hence 0:"i \<in>  {i. i < 2 ^ LENGTH(8 word) - 1}"
      using capability_list.cap_list_rep[of "write_caps p\<^sub>1"] by simp
    assume "length \<lfloor>write_caps p\<^sub>1\<rfloor> = length \<lfloor>write_caps p\<^sub>2\<rfloor>"
    with idx eq[of Write "\<lceil>i\<rceil>" "0x00"] eq[of Write "\<lceil>i\<rceil>" "0x01"]
    have "(\<lfloor>\<lfloor>write_caps p\<^sub>1\<rfloor> ! i\<rfloor> :: word32 \<times> word32) = \<lfloor>\<lfloor>write_caps p\<^sub>2\<rfloor> ! i\<rfloor>"
      unfolding caps_rep_def by (simp add:cap_index_inverse[OF 0] prod_eqI)
  }
  thus "length \<lfloor>write_caps p\<^sub>1\<rfloor> = length \<lfloor>write_caps p\<^sub>2\<rfloor> \<Longrightarrow> write_caps p\<^sub>1 = write_caps p\<^sub>2"
    by force

  {
    fix i :: nat
    let ?addr\<^sub>1 = "\<lfloor>Heap_proc k\<^sub>1 (Cap Log \<lceil>i\<rceil> 0)\<rfloor>"
    and ?addr\<^sub>2 = "\<lfloor>Heap_proc k\<^sub>2 (Cap Log \<lceil>i\<rceil> 0)\<rfloor>"
    assume idx:"i < length \<lfloor>log_caps p\<^sub>1\<rfloor>"
    hence 0:"i \<in>  {i. i < 2 ^ LENGTH(8 word) - 1}"
      using capability_list.cap_list_rep[of "log_caps p\<^sub>1"] by simp
    {
      fix l
      from log_cap_rep'[of l]
      have "unat (of_nat (length (log_cap_rep' l)) :: word32) = length (log_cap_rep' l)"
        by (simp add:unat_of_nat_eq)
    }
    moreover assume len:"length \<lfloor>log_caps p\<^sub>1\<rfloor> = length \<lfloor>log_caps p\<^sub>2\<rfloor>"
    ultimately have rep_len:"length \<lfloor>\<lfloor>log_caps p\<^sub>1\<rfloor> ! i\<rfloor> = length \<lfloor>\<lfloor>log_caps p\<^sub>2\<rfloor> ! i\<rfloor>"
      using idx eq[of Log "\<lceil>i\<rceil>" 0]
      unfolding caps_rep_def log_cap_rep_def
      by (auto simp add:cap_index_inverse[OF 0], metis)
    {
      fix off
      assume off:"off < length \<lfloor>\<lfloor>log_caps p\<^sub>1\<rfloor> ! i\<rfloor>"
      hence "unat (of_nat off :: byte) = off"
        using log_cap_rep'[of "\<lfloor>log_caps p\<^sub>1\<rfloor> ! i"] by (simp add:unat_of_nat_eq)
      with idx off eq[of Log "\<lceil>i\<rceil>" "of_nat off"] len rep_len
      have "\<lfloor>\<lfloor>log_caps p\<^sub>1\<rfloor> ! i\<rfloor> ! off = \<lfloor>\<lfloor>log_caps p\<^sub>2\<rfloor> ! i\<rfloor> ! off"
        unfolding caps_rep_def
        by (auto simp add:cap_index_inverse[OF 0])
    }
    with len rep_len have "\<lfloor>\<lfloor>log_caps p\<^sub>1\<rfloor> ! i\<rfloor> = \<lfloor>\<lfloor>log_caps p\<^sub>2\<rfloor> ! i\<rfloor>" by auto
  }
  thus "length \<lfloor>log_caps p\<^sub>1\<rfloor> = length \<lfloor>log_caps p\<^sub>2\<rfloor> \<Longrightarrow> log_caps p\<^sub>1 = log_caps p\<^sub>2"
    by force
qed

text \<open>
  Low-level representation of the procedure as it is stored in the kernel storage: given the
  procedure and the data offset it returns the machine word representation of the data
  that can be found by that offset.
\<close>

definition "proc_rep k (i :: key_index) (p :: procedure) r (off :: data_offset) \<equiv>
  let addr = \<lfloor>off\<rfloor> in
  let ncaps = \<lambda> n. ucast (of_nat n :: byte) OR r addr \<restriction> {LENGTH(byte)..<LENGTH(word32)} in
  case off of
    Addr         \<Rightarrow> ucast (eth_addr p) OR r addr \<restriction> {LENGTH(ethereum_address) ..<LENGTH(word32)}
  | Index        \<Rightarrow> ucast \<lfloor>i\<rfloor> OR r addr \<restriction> {LENGTH(key) ..<LENGTH(word32)}
  | Ncaps Call   \<Rightarrow> ncaps (length \<lfloor>call_caps p\<rfloor>)
  | Ncaps Reg    \<Rightarrow> ncaps (length \<lfloor>reg_caps p\<rfloor>)
  | Ncaps Del    \<Rightarrow> ncaps (length \<lfloor>del_caps p\<rfloor>)
  | Ncaps Entry  \<Rightarrow> ncaps (of_bool (entry_cap p))
  | Ncaps Write  \<Rightarrow> ncaps (length \<lfloor>write_caps p\<rfloor>)
  | Ncaps Log    \<Rightarrow> ncaps (length \<lfloor>log_caps p\<rfloor>)
  | Ncaps Send   \<Rightarrow> ncaps (length \<lfloor>ext_caps p\<rfloor>)
  | Cap ty i off \<Rightarrow> caps_rep k p r ty i off"

text \<open>Low-level representation is injective.\<close>

lemma restrict_ucast_inj[simplified, dest!]:
  "\<lbrakk>ucast x\<^sub>1 OR y\<^sub>1 \<restriction> {l ..<LENGTH(word32)} = ucast x\<^sub>2 OR y\<^sub>2 \<restriction> {l ..<LENGTH(word32)};
   l = LENGTH('b); LENGTH('b) < LENGTH(word32)\<rbrakk> \<Longrightarrow> x\<^sub>1 = x\<^sub>2"
  for x\<^sub>1 x\<^sub>2 :: "'b::len word" and y\<^sub>1 y\<^sub>2 :: word32
    by (auto dest!:restrict_inj2[of "\<lambda> x (_ :: unit). ucast x"] intro:ucast_up_inj)

lemma proc_rep_inj[dest]:
  assumes "proc_rep k\<^sub>1 i\<^sub>1 p\<^sub>1 r\<^sub>1 = proc_rep k\<^sub>2 i\<^sub>2 p\<^sub>2 r\<^sub>2"
  shows   "p\<^sub>1 = p\<^sub>2" and "i\<^sub>1 = i\<^sub>2"
proof (rule procedure.equality)
  from assms have eq:"\<And> off. proc_rep k\<^sub>1 i\<^sub>1 p\<^sub>1 r\<^sub>1 off = proc_rep k\<^sub>2 i\<^sub>2 p\<^sub>2 r\<^sub>2 off" by simp

  from eq[of Addr] show "eth_addr p\<^sub>1 = eth_addr p\<^sub>2"
    unfolding proc_rep_def by auto
  from eq[of Index] show "i\<^sub>1 = i\<^sub>2" unfolding proc_rep_def by auto

  {
    fix l :: "'b capability_list"
    from cap_list_rep[of l]
    have "unat (of_nat (length \<lfloor>l\<rfloor>) :: byte) = length \<lfloor>l\<rfloor>" by (simp add:unat_of_nat_eq)
  }
  hence [dest]:"\<And> l\<^sub>1 :: 'b capability_list. \<And> l\<^sub>2 :: 'b capability_list.
           (of_nat (length \<lfloor>l\<^sub>1\<rfloor>) :: byte) = of_nat (length \<lfloor>l\<^sub>2\<rfloor>) \<Longrightarrow> length \<lfloor>l\<^sub>1\<rfloor> = length \<lfloor>l\<^sub>2\<rfloor>"
    by metis

  from eq[of "Cap _ _ _"] have caps:"caps_rep k\<^sub>1 p\<^sub>1 r\<^sub>1 = caps_rep k\<^sub>2 p\<^sub>2 r\<^sub>2"
    unfolding proc_rep_def by force

  from eq[of "Ncaps Call"] have "length \<lfloor>call_caps p\<^sub>1\<rfloor> = length \<lfloor>call_caps p\<^sub>2\<rfloor>"
    unfolding proc_rep_def by auto
  with caps show "call_caps p\<^sub>1 = call_caps p\<^sub>2" ..

  from eq[of "Ncaps Reg"] have "length \<lfloor>reg_caps p\<^sub>1\<rfloor> = length \<lfloor>reg_caps p\<^sub>2\<rfloor>"
    unfolding proc_rep_def by auto
  with caps show "reg_caps p\<^sub>1 = reg_caps p\<^sub>2" ..

  from eq[of "Ncaps Del"] have "length \<lfloor>del_caps p\<^sub>1\<rfloor> = length \<lfloor>del_caps p\<^sub>2\<rfloor>"
    unfolding proc_rep_def by auto
  with caps show "del_caps p\<^sub>1 = del_caps p\<^sub>2" ..

  from eq[of "Ncaps Write"] have "length \<lfloor>write_caps p\<^sub>1\<rfloor> = length \<lfloor>write_caps p\<^sub>2\<rfloor>"
    unfolding proc_rep_def by auto
  with caps show "write_caps p\<^sub>1 = write_caps p\<^sub>2" ..

  from eq[of "Ncaps Log"] have "length \<lfloor>log_caps p\<^sub>1\<rfloor> = length \<lfloor>log_caps p\<^sub>2\<rfloor>"
    unfolding proc_rep_def by auto
  with caps show "log_caps p\<^sub>1 = log_caps p\<^sub>2" ..

  from eq[of "Ncaps Send"] have "length \<lfloor>ext_caps p\<^sub>1\<rfloor> = length \<lfloor>ext_caps p\<^sub>2\<rfloor>"
    unfolding proc_rep_def by auto
  with caps show "ext_caps p\<^sub>1 = ext_caps p\<^sub>2" ..

  from eq[of "Ncaps Entry"] show "entry_cap p\<^sub>1 = entry_cap p\<^sub>2"
    unfolding proc_rep_def by (auto del:iffI) (simp split:if_splits add:of_bool_def)
qed simp

subsection \<open>Kernel storage layout\<close>

text \<open>Maximum number of procedures registered in the kernel is @{text "2\<^sup>1\<^sup>9\<^sup>2 - 1"}.\<close>

abbreviation "max_nprocs \<equiv> 2 ^ LENGTH(key) - 1 :: nat"

text \<open>
  Introduce @{text procedure_list} type that is an association list of elements (a list in which
  each list element comprises a key and a value, and all keys are distinct), where element key is
  a procedure key and element value is a procedure itself.
\<close>

typedef procedure_list = "{l :: (key, procedure) alist. size l \<le> max_nprocs}"
  morphisms proc_list_rep proc_list
  by (intro exI[of _ "Alist []"], simp)

adhoc_overloading rep proc_list_rep

adhoc_overloading rep DAList.impl_of

adhoc_overloading abs proc_list

text \<open>
  We model the kernel storage as a record with three fields:
  \begin{itemize}
    \item @{text curr_proc} field stores the Ethereum address of the current procedure;
    \item @{text entry_proc} field stores the Ethereum address of the entry procedure;
    \item @{text proc_list} field stores the list of all registered procedures (with their data).
  \end{itemize}
\<close>

record kernel =
  curr_proc  :: key
  entry_proc :: key
  proc_list  :: procedure_list

text \<open>
  Here we introduce some useful abbreviations and definitions that will simplify the high-level
  expression of the kernel state properties.

  @{text nprocs} returns the number of the procedures registered in the kernel. @{text \<sigma>} is a
  parameter that refers to the state of the kernel storage.
\<close>

abbreviation "nprocs \<sigma> \<equiv> size \<lfloor>proc_list \<sigma>\<rfloor>"

text \<open>Function that returns set of all current procedure indexes.\<close>

definition "proc_ids \<sigma> \<equiv> {0..<nprocs \<sigma>}"

text \<open>
  @{text procs} returns map of procedure keys and corresponding procedures. This is an
  alternative representation of an association list @{text procedure_list} described above.
  Note that not all keys contain procedures.
\<close>

abbreviation "procs \<sigma> \<equiv> DAList.lookup \<lfloor>proc_list \<sigma>\<rfloor>"

text \<open>
  Auxiliary function that returns true if and only if a procedure with the key @{text k} is
  registered in the state @{text \<sigma>}.
 \<close>

definition "has_key k \<sigma> \<equiv> k \<in> dom (procs \<sigma>)"

text \<open>
  @{text proc} returns the procedure by its key. Can be used only if @{text "has_key k \<sigma> = True"}.
\<close>

definition "proc \<sigma> k \<equiv> the (procs \<sigma> k)"

abbreviation "curr_proc' \<sigma> \<equiv> proc \<sigma> (curr_proc \<sigma>)"

text \<open>@{text proc_key} returns the procedure key by its index in the procedure list.\<close>

abbreviation "proc_key \<sigma> i \<equiv> fst (\<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! i)"

text \<open>@{text proc_id} returns the procedure index in the procedure list by its key.\<close>

definition "proc_id \<sigma> k \<equiv> \<lceil>length (takeWhile ((\<noteq>) k \<circ> fst) \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor>)\<rceil> :: key_index"

text \<open>
  @{text proc_id} always returns the procedure index that exists in the current state. Given that
  index the correct corresponding procedure can be found in the procedure list.
\<close>

lemma proc_id_alt[simp]:
  "has_key k \<sigma> \<Longrightarrow> \<lfloor>proc_id \<sigma> k\<rfloor> \<in> proc_ids \<sigma>"
  "has_key k \<sigma> \<Longrightarrow> \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! \<lfloor>proc_id \<sigma> k\<rfloor> = (k, proc \<sigma> k)"
proof-
  assume "has_key k \<sigma>"
  hence 0:"(k, proc \<sigma> k) \<in> set \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor>"
    unfolding has_key_def proc_def DAList.lookup_def
    by auto
  hence "length (takeWhile ((\<noteq>) k \<circ> fst) \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor>) \<in> proc_ids \<sigma>"
    unfolding has_key_def proc_id_def proc_ids_def
    using length_takeWhile_less[of "\<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> :: (key \<times> procedure) list" "(\<noteq>) k \<circ> fst"]
    by force
  moreover hence [simp]:"\<lfloor>\<lceil>length (takeWhile ((\<noteq>) k \<circ> fst) \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor>)\<rceil> :: key_index\<rfloor> =
                         length (takeWhile ((\<noteq>) k \<circ> fst) \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor>)"
    unfolding proc_ids_def
    using key_index_inverse proc_list_rep[of "proc_list \<sigma>"]
    by auto
  ultimately show 1:"\<lfloor>proc_id \<sigma> k\<rfloor> \<in> proc_ids \<sigma>" unfolding proc_ids_def proc_id_def by simp

  from 0 have "\<exists>! i. i < length \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> \<and> \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! i = (k, proc \<sigma> k)"
    using distinct_map by (auto intro!:distinct_Ex1)
  moreover
  {
    fix p i j
    assume 0:"i < length \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor>" and 1:"j < length \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor>"
    moreover assume "\<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! i = (k, p)" and "fst (\<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! j) = k"
    ultimately have "snd (\<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! j) = p"
      using impl_of_distinct nth_mem distinct_map[of fst] unfolding inj_on_def
      by (metis fst_conv snd_conv)
  }
  ultimately have "\<forall> i < length \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor>.
                     fst (\<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! i) = k \<longrightarrow> snd (\<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! i) = proc \<sigma> k"
    by auto
  with 1 show "\<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! \<lfloor>proc_id \<sigma> k\<rfloor> = (k, proc \<sigma> k)"
    unfolding proc_id_def proc_def proc_ids_def DAList.lookup_def
    using nth_length_takeWhile[of "(\<noteq>) k \<circ> fst" "\<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> :: (key \<times> procedure) list"]
    by (auto intro:prod_eqI)
qed

text \<open>Low-level representation of the kernel storage is a 256 x 256 bits key-value store.\<close>

definition "kernel_rep (\<sigma> :: kernel) r a \<equiv>
  case \<lceil>a\<rceil> of
    None              \<Rightarrow> r a
  | Some addr         \<Rightarrow> (case addr of
      Nprocs          \<Rightarrow> ucast (of_nat (nprocs \<sigma>) :: key) OR r a \<restriction> {LENGTH(key) ..<LENGTH(word32)}
    | Proc_key i      \<Rightarrow> ucast (proc_key \<sigma> \<lfloor>i\<rfloor>) OR r a \<restriction> {LENGTH(key) ..<LENGTH(word32)}
    | Kernel          \<Rightarrow> 0
    | Curr_proc       \<Rightarrow> ucast (curr_proc \<sigma>) OR r a \<restriction> {LENGTH(key) ..<LENGTH(word32)}
    | Entry_proc      \<Rightarrow> ucast (entry_proc \<sigma>) OR r a \<restriction> {LENGTH(key) ..<LENGTH(word32)}
    | Heap_proc k off \<Rightarrow> if has_key k \<sigma>
                         then proc_rep k (proc_id \<sigma> k) (proc \<sigma> k) r off
                         else r a)"

adhoc_overloading rep kernel_rep

text \<open>
  If the number of procedures in two kernel states is the same, procedure keys that can be found
  by the same index in two corresponding procedure lists are the same, and for each such procedure
  key its data is also the same in both states, then procedure lists in both states are equal.
\<close>

lemma proc_list_eqI[intro]:
  assumes "nprocs \<sigma>\<^sub>1 = nprocs \<sigma>\<^sub>2"
      and "\<And> i. i < nprocs \<sigma>\<^sub>1 \<Longrightarrow> proc_key \<sigma>\<^sub>1 i = proc_key \<sigma>\<^sub>2 i"
      and "\<And> k. \<lbrakk>has_key k \<sigma>\<^sub>1; has_key k \<sigma>\<^sub>2\<rbrakk> \<Longrightarrow> proc \<sigma>\<^sub>1 k = proc \<sigma>\<^sub>2 k"
    shows "proc_list \<sigma>\<^sub>1 = proc_list \<sigma>\<^sub>2"
  unfolding has_key_def DAList.lookup_def proc_def
proof-
  from assms have "\<forall> i < nprocs \<sigma>\<^sub>1.
                    snd (\<lfloor>\<lfloor>proc_list \<sigma>\<^sub>1\<rfloor>\<rfloor> ! i) = snd (\<lfloor>\<lfloor>proc_list \<sigma>\<^sub>2\<rfloor>\<rfloor> ! i)"
    unfolding has_key_def DAList.lookup_def proc_def
    apply (auto iff:fun_eq_iff)
    using
      Some_eq_map_of_iff[of "\<lfloor>\<lfloor>proc_list \<sigma>\<^sub>1\<rfloor>\<rfloor>"] Some_eq_map_of_iff[of "\<lfloor>\<lfloor>proc_list \<sigma>\<^sub>2\<rfloor>\<rfloor>"]
      nth_mem[of _ "\<lfloor>\<lfloor>proc_list \<sigma>\<^sub>1\<rfloor>\<rfloor>"]          nth_mem[of _ "\<lfloor>\<lfloor>proc_list \<sigma>\<^sub>2\<rfloor>\<rfloor>"]
      impl_of_distinct[of "\<lfloor>proc_list \<sigma>\<^sub>1\<rfloor>"]     impl_of_distinct[of "\<lfloor>proc_list \<sigma>\<^sub>2\<rfloor>"]
    by (metis domIff option.sel option.simps(3) surjective_pairing)
  with assms show ?thesis
    by (auto intro!:nth_equalityI prod_eqI
             iff:proc_list_rep_inject[symmetric] impl_of_inject[symmetric] fun_eq_iff)
qed

text \<open>Low-level representation of the kernel storage is injective.\<close>

lemma kernel_rep_inj[dest]: "\<lfloor>\<sigma>\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>\<sigma>\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2" for \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: kernel
proof (rule kernel.equality)
  assume "\<lfloor>\<sigma>\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>\<sigma>\<^sub>2\<rfloor> r\<^sub>2"
  hence eq:"\<And> a. \<lfloor>\<sigma>\<^sub>1\<rfloor> r\<^sub>1 a = \<lfloor>\<sigma>\<^sub>2\<rfloor> r\<^sub>2 a" by simp

  from eq[of "\<lfloor>Curr_proc\<rfloor>"] show "curr_proc \<sigma>\<^sub>1 = curr_proc \<sigma>\<^sub>2"
    unfolding kernel_rep_def by auto

  from eq[of "\<lfloor>Entry_proc\<rfloor>"] show "entry_proc \<sigma>\<^sub>1 = entry_proc \<sigma>\<^sub>2"
    unfolding kernel_rep_def by auto

  from eq[of "\<lfloor>Nprocs\<rfloor>"] have "nprocs \<sigma>\<^sub>1 = nprocs \<sigma>\<^sub>2"
    unfolding kernel_rep_def
    using proc_list_rep[of "proc_list \<sigma>\<^sub>1"] proc_list_rep[of "proc_list \<sigma>\<^sub>2"]
    by (auto iff:of_nat_inj[symmetric])
  moreover {
    fix i
    assume "i < nprocs \<sigma>\<^sub>1"
    with eq[of "\<lfloor>Proc_key \<lceil>i\<rceil>\<rfloor>"] have "proc_key \<sigma>\<^sub>1 i = proc_key \<sigma>\<^sub>2 i"
      unfolding kernel_rep_def
      using proc_list_rep[of "proc_list \<sigma>\<^sub>1"]
      by (auto simp add:key_index_inject simp add: key_index_inverse)
  }
  moreover {
    fix k
    assume "has_key k \<sigma>\<^sub>1" and " has_key k \<sigma>\<^sub>2"
    with eq[of "\<lfloor>Heap_proc k _\<rfloor>"] have "proc \<sigma>\<^sub>1 k = proc \<sigma>\<^sub>2 k"
      unfolding kernel_rep_def
      by (auto iff:fun_eq_iff[symmetric])
  }
  ultimately show "proc_list \<sigma>\<^sub>1 = proc_list \<sigma>\<^sub>2" ..
qed simp

text \<open>Representation function is invertible.\<close>

lemmas kernel_invertible[intro] = invertible2.intro[OF inj2I, OF kernel_rep_inj]

interpretation kernel_inv: invertible2 kernel_rep ..

adhoc_overloading abs kernel_inv.inv2

lemma kernel_update_neq[simp]: "\<not> limited_and prefix_bound a \<Longrightarrow> \<lfloor>\<sigma>\<rfloor> r a = r a"
proof-
  assume "\<not> limited_and prefix_bound a"
  hence "(\<lceil>a\<rceil> :: address option) = None"
    using addr_prefix by - (rule ccontr, auto)
  thus ?thesis unfolding kernel_rep_def by auto
qed

section \<open>Call formats\<close>

text \<open>Here we describe formats of all available system calls.\<close>

primrec split :: "'a::len word list \<Rightarrow> 'b::len word list list" where
  "split []       = []" |
  "split (x # xs) = word_rsplit x # split xs"

lemma cat_split: "map word_rcat (split x) = x"
  unfolding split_def
  by (induct x, simp_all add:word_rcat_rsplit)

lemma split_inj[dest]: "split x = split y \<Longrightarrow> x = y"
  by (frule arg_cong[where f="map word_rcat"]) (subst (asm) cat_split)+

lemma split_distrib[simp]:"split (a @ b) = split a @ split b" by (induct a, simp_all)

lemma split_length_indep[dest]: "length a = length b \<Longrightarrow> length (split a) = length (split b)"
proof (induct a arbitrary:b, simp)
  case (Cons x xs)
  from Cons(1)[of "tl b"] Cons(2) show ?case by (cases b, simp_all)
qed

lemma split_concat_length_indep[dest]:
  "length a = length b \<Longrightarrow>
   length (concat (split a :: 'b::len word list list)) =
   length (concat (split b :: 'b::len word list list))"
  for a b :: "'a::len word list"
proof (induct a arbitrary:b, simp)
  case (Cons x xs)
  from Cons(1)[of "tl b"] Cons(2) show ?case by (cases b, simp_all add:word_rsplit_len_indep)
qed

lemma split_lengths:
  "i \<in> set (split (a :: 'a::len word list) :: 'b::len word list list)
   \<Longrightarrow> length i = (LENGTH('a) + LENGTH('b) - 1) div LENGTH('b)"
  by (induct a, auto simp add:length_word_rsplit_exp_size')

lemma sum_list_mul[simp]:"\<forall> x \<in> set l. f x = n \<Longrightarrow> sum_list (map f l) = n * length l"
  by (induct l, simp_all)

lemma length_split[simp]: "length (split a) = length a" by (induct a, simp_all)

lemma length_concat_split[simp]:
  "length (concat (split (a :: 'a::len word list) :: 'b::len word list list)) =
   (LENGTH('a) + LENGTH('b) - 1) div LENGTH('b) * length a"
  using split_lengths[of _ a]
  by (auto simp add:length_concat, subst sum_list_mul, auto)

function (sequential, domintros) cat :: "'a::len word list \<Rightarrow> 'b::len word list" where
  "cat [] = []" |
  "cat l  =
    (let d = LENGTH('b) div LENGTH('a) in word_rcat (take d l) # cat (drop d l))"
  using list.exhaust by auto

fun group_by' :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "group_by' g _ _ []             = [rev g]" |
  "group_by' g 0 n (x # xs)       = rev g # group_by' [x] (n - 1) n xs" |
  "group_by' g (Suc m) n (x # xs) = group_by' (x # g) m n xs"

lemma concat_group_by': "concat (group_by' g m n l) = rev g @ l"
  by (induct rule:group_by'.induct[of _ g _ _ l], simp_all)

lemma group_by'_lengths:
  "\<lbrakk>0 < n; length g + m = n; m \<le> length l; n dvd length g + length l\<rbrakk>
   \<Longrightarrow> \<forall> x \<in> set (group_by' g m n l). length x = n"
proof (induct rule:group_by'.induct[of _ g m n l])
  case (1 g m n)
  thus ?case by simp
next
  case (2 g n x xs)
  from 2(2) have p0:"length [x] + (n - 1) = n" by simp
  from 2(2-5) have p1:"n - 1 \<le> length xs"
    by (simp add: diff_add_inverse dvd_imp_le le_diff_conv less_eq_dvd_minus)
  from 2(3,5) have p2:"n dvd length [x] + length xs" using dvd_add_triv_left_iff by fastforce
  from 2(3) 2(1)[OF 2(2) p0 p1 p2] show ?case by simp
next
  case (3 g m n x xs)
  from 3(3) have p0:"length (x # g) + m = n" by simp
  from 3(4) have p1:"m \<le> length xs" by simp
  from 3(5) have p2:"n dvd length (x # g) + length xs" by simp
  from 3(1)[OF 3(2) p0 p1 p2] show ?case by simp
qed

definition "group_by n l \<equiv> if l = [] then [] else group_by' [] n n l"

lemma concat_group_by[simp]: "concat (group_by n l) = l"
  unfolding group_by_def using concat_group_by'[of "[]" n n l] by simp

lemma group_by_lengths[intro]: "\<lbrakk>0 < n; n dvd length l; x \<in> set (group_by n l)\<rbrakk> \<Longrightarrow> length x = n"
  unfolding group_by_def using group_by'_lengths[of n "[]" n l]
  by (auto dest:dvd_imp_le split:if_splits)

lemma cat_induct[consumes 2]:
  assumes major0:"0 < n" and major1:"n dvd length l"
      and base: "P []"
      and induct:"\<And> l. P (drop n l) \<Longrightarrow> P l"
    shows "P l"
proof-
  obtain u where
    "l = concat u" and
    "\<forall> x \<in> set u. length x = n" and
    "concat (tl u) = drop n l"
  proof-
    have p0:"l = concat (group_by n l)" by simp
    from major0 and major1 have p1:"\<forall>x \<in> set (group_by n l). length x = n" by auto
    from p0 p1 have p2:"concat (tl (group_by n l)) = drop n l" by (cases "group_by n l", simp_all)
    from that[of "group_by n l"] p0 p1 p2 show ?thesis .
  qed
  thus ?thesis proof (induct u arbitrary:l)
    case Nil
    with base show ?case by simp
  next
    case (Cons u us)
    let ?l = "concat us"
    from Cons(3) have 0:"\<forall>x\<in>set us. length x = n" by simp
    from Cons(3) have 1:"concat (tl us) = drop n ?l" by (cases us, simp_all)
    from Cons(2,3) have "concat us = drop n l" by simp
    with Cons(1)[of ?l, simplified, OF 0 1] induct[of l] show ?case by simp
  qed
qed

lemma cat_domintros_2:
  "cat_dom TYPE('b::len) (drop (LENGTH('b) div LENGTH('a)) l) \<Longrightarrow> cat_dom TYPE('b) l"
  for l :: "'a::len word list"
  by (cases l, auto intro:cat.domintros)

lemmas cat_domintros = cat.domintros(1) cat_domintros_2

lemma cat_dom_divides[intro]:
  "\<lbrakk>0 < LENGTH('b::len) div LENGTH('a); (LENGTH('b) div LENGTH('a)) dvd length l\<rbrakk>
   \<Longrightarrow> cat_dom (TYPE ('b)) l"
  for l :: "'a::len word list"
  by (induct l rule:cat_induct, auto intro:cat_domintros)

lemma concat_split:
  "LENGTH('b) dvd LENGTH('a) \<Longrightarrow> cat (concat (split a) :: 'b::len word list) = a"
  (is "?dvd \<Longrightarrow> cat (?concat a) = a")
  for a :: "'a::len word list"
proof -
  assume ?dvd
  moreover hence "(LENGTH('a) div LENGTH('b)) dvd length (?concat a)"
    by (simp, metis dvd_div_mult_self dvd_mult2 dvd_refl given_quot_alt len_gt_0)
  ultimately have dom:"cat_dom TYPE('a) (?concat a)" using div_positive dvd_imp_le by blast
  thus ?thesis proof (induction a)
    case Nil
    note [simp] = cat.psimps(1)[OF cat.domintros(1)] cat.psimps(2)
    thus ?case by simp
  next
    case (Cons x xs)
    from \<open>?dvd\<close> have x:"length (word_rsplit x) > 0"
      using length_word_rsplit_lt_size by fastforce
    then obtain y ys where y:"?concat (x # xs) = y # ys"
      apply (auto iff:neq_Nil_conv)
      using x list_exhaust_size_gt0 by auto
    with Cons(2) have 0:"cat_dom TYPE('a) (y # ys)" by simp
    note [simp] = cat.psimps(2)[OF 0]
    from \<open>?dvd\<close> have len:"length (word_rsplit x :: 'b word list) = LENGTH('a) div LENGTH('b)"
      by (metis dvd_div_mult_self length_word_rsplit_even_size word_size)
    from \<open>?dvd\<close> len x have dom0:"0 < LENGTH('a) div LENGTH('b)" by auto
    from \<open>?dvd\<close> have
      dom1:"LENGTH('a) div LENGTH('b) dvd
       (LENGTH('a) + LENGTH('b) - 1) div LENGTH('b) * length xs"
      by (metis dvd_def len length_word_rsplit_exp_size' word_size)
    from cat_dom_divides[of "?concat xs", OF dom0] dom1
    have dom:"cat_dom TYPE('a) (?concat xs)" by simp
    from Cons(1)[OF dom] show ?case unfolding y by (simp, fold y, simp add:len word_rcat_rsplit)
  qed
qed

lemma concat_split':"cat (concat (split a :: byte list list)) = a" for a :: "word32 list"
  by (auto intro:concat_split)

subsection \<open>Deterministic inverse function\<close>

definition "maybe_inv2_tf z f l \<equiv>
  if \<exists> n. takefill z n l \<in> range2 f
  then Some (the_inv2 f (takefill z (SOME n. takefill z n l \<in> range2 f) l))
  else None"

lemma takefill_implies_prefix:
  assumes "x = takefill u n y"
  obtains (Prefix) "prefix x y" | (Postfix) "prefix y x"
proof (cases "length x \<le> length y")
  case True
  with assms have "prefix x y" unfolding takefill_alt by (simp add: take_is_prefix)
  with that show ?thesis by simp
next
  case False
  with assms have "prefix y x" unfolding takefill_alt by simp
  with that show ?thesis by simp
qed

lemma takefill_prefix_inj:
  "\<lbrakk>\<And> x y. \<lbrakk>P x; P y; prefix x y\<rbrakk> \<Longrightarrow> x = y; P x; P y; x = takefill u n y\<rbrakk> \<Longrightarrow> x = y"
  by (elim takefill_implies_prefix) auto

definition "inj2_tf f \<equiv> \<forall> x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2. prefix (f x\<^sub>1 y\<^sub>1) (f x\<^sub>2 y\<^sub>2) \<longrightarrow> x\<^sub>1 = x\<^sub>2"

lemma inj2_tfI: "(\<And> x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2. prefix (f x\<^sub>1 y\<^sub>1) (f x\<^sub>2 y\<^sub>2) \<Longrightarrow> x\<^sub>1 = x\<^sub>2) \<Longrightarrow> inj2_tf f"
  unfolding inj2_tf_def
  by blast

lemma exI2[intro]: "P x y \<Longrightarrow> \<exists> x y. P x y" by auto

lemma maybe_inv2_tf_inj[intro]:
  "\<lbrakk>inj2_tf f; \<And> x y y'. length (f x y) = length (f x y')\<rbrakk> \<Longrightarrow> maybe_inv2_tf z f (f x y) = Some x"
  unfolding maybe_inv2_tf_def range2_def the_inv2_def inj2_tf_def
  apply (auto split:if_splits)
   apply (subst some1_equality[rotated], erule exI2)
     apply (metis length_takefill takefill_implies_prefix)
  apply (smt length_takefill takefill_implies_prefix the_equality)
  by (meson takefill_same)

lemma maybe_inv2_tf_inj':
  "\<lbrakk>inj2_tf f; \<And> x y y'. length (f x y) = length (f x y')\<rbrakk> \<Longrightarrow>
    maybe_inv2_tf z f v = Some x \<Longrightarrow> \<exists> y n. f x y = takefill z n v"
  unfolding maybe_inv2_tf_def range2_def the_inv2_def inj2_tf_def
  apply (simp split:if_splits)
  apply (subst (asm) some1_equality[rotated], erule exI2)
   apply (metis length_takefill nat_less_le not_less take_prefix take_takefill)
  by (smt prefix_order.eq_iff the1_equality)

locale invertible2_tf =
  fixes rep :: "'a \<Rightarrow> 'c \<Rightarrow> 'c::zero list" ("\<lfloor>_\<rfloor>")
  assumes inj:"inj2_tf rep"
      and len_inv:"\<And> x y y'. length (rep x y) = length (rep x y')"
begin
definition inv2_tf :: "'c list \<Rightarrow> 'a option" where "inv2_tf \<equiv> maybe_inv2_tf 0 rep"

lemmas inv2_tf_inj[folded inv2_tf_def, simp] = maybe_inv2_tf_inj[where z=0, OF inj len_inv]

lemmas inv2_tf_inj'[folded inv2_tf_def, dest] = maybe_inv2_tf_inj'[where z=0, OF inj len_inv]
end

subsection \<open>Register system call\<close>

text \<open>
  Definition of well-formedness for capability @{text l} (represented as a 32-byte machine word
  list) of type @{text c}. @{text l} must be correctly formatted to be correctly decoded into
  the more high-level representation.
\<close>

definition "wf_cap c l \<equiv>
  case (c, l) of
    (Entry, [])       \<Rightarrow> True
  | (_,     [])       \<Rightarrow> True \<comment> \<open>A hole representing a copy of the parent capability\<close>
  | (Call,  [c])      \<Rightarrow> (\<lceil>c\<rceil> :: prefixed_capability option) \<noteq> None
  | (Reg,   [c])      \<Rightarrow> (\<lceil>c\<rceil> :: prefixed_capability option) \<noteq> None
  | (Del,   [c])      \<Rightarrow> (\<lceil>c\<rceil> :: prefixed_capability option) \<noteq> None
  | (Write, [c1, c2]) \<Rightarrow> (\<lceil>(c1, c2)\<rceil> :: write_capability option) \<noteq> None
  | (Log,   c)        \<Rightarrow> (\<lceil>c\<rceil> :: log_capability option) \<noteq> None
  | (Send,  [c])      \<Rightarrow> (\<lceil>c\<rceil> :: external_call_capability option) \<noteq> None
  | _                 \<Rightarrow> False"

text \<open>
  If some capability @{text l} of the type @{text c} is well-formed, then the length of l
  (word list) is smaller or equal to 5.
\<close>

lemma length_wf_cap[dest]: "wf_cap c l \<Longrightarrow> length l \<le> 5" (is "?wf \<Longrightarrow> _")
proof-
  have [dest]: "\<lceil>h # t\<rceil> = Some y \<Longrightarrow> length t \<le> 4" for h t and y :: log_capability
  using log_cap_inv.inv_inj'[of "h # t" y] log_cap_rep_length[of y] log_cap_rep'[of y] by simp
  assume ?wf thus ?thesis unfolding wf_cap_def by (auto split:capability.splits list.splits)
qed

text \<open>
  Capabilities @{text l\<^sub>1} and @{text l\<^sub>2} of the type @{text c} are the same if their high-level
  representation are the same.
\<close>

definition "same_cap c l\<^sub>1 l\<^sub>2 \<equiv>
  case (c, l\<^sub>1, l\<^sub>2) of
    (Entry, [],   [])              \<Rightarrow> True
  | (_,     [],   [])              \<Rightarrow> True \<comment> \<open>The same parent capability\<close>
  | (Call,  [c\<^sub>1], [c\<^sub>2])            \<Rightarrow> the \<lceil>c\<^sub>1\<rceil> = (the \<lceil>c\<^sub>2\<rceil> :: prefixed_capability)
  | (Reg,   [c\<^sub>1], [c\<^sub>2])            \<Rightarrow> the \<lceil>c\<^sub>1\<rceil> = (the \<lceil>c\<^sub>2\<rceil> :: prefixed_capability)
  | (Del,   [c\<^sub>1], [c\<^sub>2])            \<Rightarrow> the \<lceil>c\<^sub>1\<rceil> = (the \<lceil>c\<^sub>2\<rceil> :: prefixed_capability)
  | (Write, [c1\<^sub>1, c2\<^sub>1], [c1\<^sub>2, c2\<^sub>2]) \<Rightarrow> the \<lceil>(c1\<^sub>1, c2\<^sub>1)\<rceil> = (the \<lceil>(c1\<^sub>2, c2\<^sub>2)\<rceil> :: write_capability)
  | (Log,   c\<^sub>1,   c\<^sub>2)              \<Rightarrow> length c\<^sub>1 = length c\<^sub>2 \<and>
                                     the \<lceil>c\<^sub>1\<rceil> = (the \<lceil>c\<^sub>2\<rceil> :: log_capability)
  | (Send,  [c\<^sub>1], [c\<^sub>2])            \<Rightarrow> the \<lceil>c\<^sub>1\<rceil> = (the \<lceil>c\<^sub>2\<rceil> :: external_call_capability)
  |  _                             \<Rightarrow> False"

text \<open>
  Some capability formats have undefined bits or bytes. Here we define function that takes
  capability @{text l} of the type @{text c} and writes it over some 32-byte machine word list
  @{text r} in such a way that these undefined parts will contain corresponding parts from
  @{text r}.
\<close>

text \<open>
  Some capability formats have undefined bits or bytes. Here we define function that takes
  capability @{text l} of the type @{text c} and writes it over some 32-byte machine word list
  @{text r} in such a way that these undefined parts will contain corresponding parts from
  @{text r}.
\<close>

definition "overwrite_cap c l r \<equiv>
  case (c, l) of
    (Entry, [])         \<Rightarrow> []
  | (_,     [])         \<Rightarrow> [] \<comment> \<open>Parent capabilty\<close>
  | (Call,  [c])        \<Rightarrow> [\<lfloor>the \<lceil>c\<rceil> :: prefixed_capability\<rfloor> (r ! 0)]
  | (Reg,   [c])        \<Rightarrow> [\<lfloor>the \<lceil>c\<rceil> :: prefixed_capability\<rfloor> (r ! 0)]
  | (Del,   [c])        \<Rightarrow> [\<lfloor>the \<lceil>c\<rceil> :: prefixed_capability\<rfloor> (r ! 0)]
  | (Write, [c1, c2])   \<Rightarrow> let (c1, c2) = \<lfloor>the \<lceil>(c1, c2)\<rceil> :: write_capability\<rfloor> in [c1, c2]
                           \<comment> \<open>for mere consistency, no actual need in this,
                               can be just [c1, c2]\<close>
  | (Log,   c)          \<Rightarrow> \<lfloor>the \<lceil>c\<rceil> :: log_capability\<rfloor>
  | (Send,  [c])        \<Rightarrow> [\<lfloor>the \<lceil>c\<rceil> :: external_call_capability\<rfloor> (r ! 0)]"

text \<open>
  If some capability @{text l} of the type @{text c} is well-wormed, then the result of its writing
  over a 32-byte machine word list @{text r} will also be well-formed.
\<close>

abbreviation "zero_fill l \<equiv> replicate (length l) 0"

text \<open>
  Writing two equal capabilities over 32-byte machine word list filled with zeroes will produce the
  same result.
\<close>

lemma same_cap_inj[dest]:
  "same_cap c l\<^sub>1 l\<^sub>2 \<Longrightarrow> overwrite_cap c l\<^sub>1 (zero_fill l\<^sub>1) = overwrite_cap c l\<^sub>2 (zero_fill l\<^sub>2)"
  unfolding same_cap_def overwrite_cap_def
  by (simp split:capability.splits) (auto split:capability.splits list.splits)+

text \<open>
  If the result of writing capability @{text l\<^sub>1} over @{text r\<^sub>1} is equal to the result of writing
  @{text l\<^sub>2} over @{text r\<^sub>2}, and both these capabilities are well-formed, then they are the same.
\<close>

text \<open>
  If the result of writing capability @{text l\<^sub>1} over @{text r\<^sub>1} is equal to the result of writing
  @{text l\<^sub>2} over @{text r\<^sub>2}, and both these capabilities are well-formed, then they are the same.
\<close>

lemma overwrite_cap_inj[dest]:
  "\<lbrakk>overwrite_cap c l\<^sub>1 r\<^sub>1 = overwrite_cap c l\<^sub>2 r\<^sub>2; wf_cap c l\<^sub>1; wf_cap c l\<^sub>2\<rbrakk> \<Longrightarrow> same_cap c l\<^sub>1 l\<^sub>2"
  unfolding wf_cap_def overwrite_cap_def same_cap_def
  by (simp split:capability.splits; cases l\<^sub>1; cases l\<^sub>2)
    (auto split:capability.splits list.splits simp add:write_cap_inv.inv_inj' log_cap_inv.inv_inj')

text \<open>Writing well-formed capability over some machine word list some does not change its length.\<close>

text \<open>Writing well-formed capability over some machine word list some does not change its length.\<close>

lemma length_overwrite_cap[simp]: "wf_cap c l \<Longrightarrow> length (overwrite_cap c l r) = length l"
  unfolding wf_cap_def overwrite_cap_def
  apply (auto split:capability.splits list.split prod.split)
  using log_cap_rep_length[of "the \<lceil>l\<rceil>"] by (simp add:log_cap_inv.inv_inj')

text \<open>
  Introduce type the described capability data as sent in the Register Procedure system call.
  It is represented as a list of elements, each of which contains some capability type, capability
  index, and well-formed capability itself.
\<close>

text \<open>
  Introduce type the described capability data as sent in the Register Procedure system call.
  It is represented as a list of elements, each of which contains some capability type, capability
  index, and well-formed capability itself.
\<close>

typedef capability_data =
  "{ l :: ((capability \<times> capability_index) \<times> word32 list) list.
       \<forall> ((c, _), l) \<in> set l. wf_cap c l \<and> l = overwrite_cap c l (zero_fill l) }"
  morphisms cap_data_rep' cap_data
  by (intro exI[of _ "[]"], simp)

adhoc_overloading rep cap_data_rep'

adhoc_overloading abs cap_data

text \<open>
  Data format of the Register Procedure system call is modeled as a record with three fields:
  \begin{itemize}
    \item @{text proc_key}: procedure key;
    \item @{text eth_addr}: procedure Ethereum address;
    \item @{text cap_data}: a series of capabilities, and each one is in the format specified above.
  \end{itemize}
\<close>

record register_call_data =
  proc_key :: key
  eth_addr :: ethereum_address
  cap_data :: capability_data

no_adhoc_overloading rep cap_index_rep

no_adhoc_overloading abs cap_index_inv.inv

text \<open>
  Redefine low-level representation of capability index. Previously it started with 1, but in the
  call data format it should start with 0.
\<close>

definition "cap_index_rep0 i \<equiv> of_nat \<lfloor>i\<rfloor> :: byte" for i :: capability_index

adhoc_overloading rep cap_index_rep0

text \<open>
  A single byte is sufficient to store the least number of bits of capability index representation.
\<close>

lemma width_cap_index0: "width \<lfloor>i\<rfloor> \<le> LENGTH(byte)" for i :: capability_index by simp

lemma width_cap_index0'[simp]: "LENGTH(byte) \<le> n \<Longrightarrow> width \<lfloor>i\<rfloor> \<le> n"
  for i :: capability_index by simp

text \<open>Capability index representation is injective.\<close>

lemma cap_index_inj0[simp]: "(\<lfloor>i\<^sub>1\<rfloor> :: byte) = \<lfloor>i\<^sub>2\<rfloor> \<Longrightarrow> i\<^sub>1 = i\<^sub>2" for i\<^sub>1 i\<^sub>2 :: capability_index
  unfolding cap_index_rep0_def
  using cap_index_rep'[of i\<^sub>1] cap_index_rep'[of i\<^sub>2] word_of_nat_inj[of "\<lfloor>i\<^sub>1\<rfloor>" "\<lfloor>i\<^sub>2\<rfloor>"]
        cap_index_rep'_inject
  by force

text \<open>Representation function is invertible.\<close>

lemmas cap_index0_invertible[intro] = invertible.intro[OF injI, OF cap_index_inj0]

interpretation cap_index_inv0: invertible cap_index_rep0 ..

adhoc_overloading abs cap_index_inv0.inv

text \<open>
  Low-level representation of a single element from the capability data list. It starts with the
  number of 32-byte machine words associated with the capability, which is 3 + the length of the
  capability, and stored in a byte aligned right in the 32 bytes. Then there is the type of the
  capability and the index into the capability list of this type for the current procedure,
  both of which are also represented as bytes aligned right in the 32 bytes. And finally there is
  the capability itself as a 32-byte machine word list.
\<close>

abbreviation "cap_data_rep_single r (c :: capability) (i :: capability_index) l j \<equiv>
  [ucast (of_nat (3 + length l) :: byte) OR (r ! j) \<restriction> {LENGTH(byte) ..<LENGTH(word32)},
   ucast \<lfloor>c\<rfloor> OR (r ! (j + 1)) \<restriction> {LENGTH(byte) ..<LENGTH(word32)},
   ucast \<lfloor>i\<rfloor> OR (r ! (j + 2)) \<restriction> {LENGTH(byte) ..<LENGTH(word32)}]
  @ overwrite_cap c l (drop (j + 3) r)"

text \<open>
  Auxiliary function that will be applied to each element from the capability data list to get its
  low-level representation.
\<close>

definition "cap_data_rep0 r \<equiv>
  \<lambda> ((c, i), l) (j, d). (j + 3 + length l, cap_data_rep_single r c i l j # d)"

text \<open>
  Length of each element from the capability data list is correctly stored in the element itself
  in its head (since the element is also a list).
\<close>

lemma length_cap_data_rep0:
  fixes d :: capability_data
  assumes "cap_data_rep0 r ((c, i), l) acc = (j, x # xs)" and "((c, i), l) \<in> set \<lfloor>d\<rfloor>"
  shows   "length x = unat (hd x AND mask LENGTH(byte))"
proof-
  from assms(2) have "wf_cap c l" using cap_data_rep'[of d] by auto
  with assms(1) show ?thesis
    unfolding cap_data_rep0_def
    by (force split:prod.splits simp add:unat_ucast_upcast unat_of_nat_eq)
qed

lemma length_cap_data_rep0':
  "\<lbrakk>[l] = snd (cap_data_rep0 r x acc); x \<in> set \<lfloor>d\<rfloor>\<rbrakk> \<Longrightarrow>
     length l = unat (hd l AND mask LENGTH(byte))"
  (is "\<lbrakk>?l; ?in_set\<rbrakk> \<Longrightarrow> _")
  for d :: capability_data
proof-
  assume ?l and ?in_set
  obtain c i l' j
    where "cap_data_rep0 r ((c, i), l') acc = (j, l # [])"
      and "((c, i), l') \<in> set \<lfloor>d\<rfloor>"
  proof (cases "cap_data_rep0 r x acc", cases x, cases "fst x")
    fix c i l' j ci ls
    assume "cap_data_rep0 r x acc = (j, ls)" and "x = (ci, l')" and "fst x = (c, i)"
    with that[of c i l' j] \<open>?in_set\<close> \<open>?l\<close> show ?thesis by simp
  qed
  thus ?thesis using length_cap_data_rep0 by simp
qed

text \<open>
  Low-level representation of the capability data list is achieved by applying the
  @{text "cap_data_rep0"} function to each element of the list.
\<close>

definition "cap_data_rep (d :: capability_data) r \<equiv> fold (cap_data_rep0 r) \<lfloor>d\<rfloor>"

lemma cap_data_rep'_tail: "\<lfloor>d\<rfloor> = x # xs \<Longrightarrow> xs = \<lfloor>\<lceil>xs\<rceil>\<rfloor>" for d :: capability_data
  using cap_data_rep'[of d]
  by (auto intro:cap_data_inverse[symmetric])

lemma length_snd_fold_cap_data_rep0:
  "length (snd (fold (cap_data_rep0 r) xs i)) = length xs + length (snd i)"
  unfolding cap_data_rep0_def by (induction xs arbitrary: i, simp_all split:prod.split)

lemma length_snd_cap_data_rep[simp]:
  "length (snd (cap_data_rep d r i)) = length \<lfloor>d\<rfloor> + length (snd i)"
  unfolding cap_data_rep_def by (simp add:length_snd_fold_cap_data_rep0)

text \<open>
  First we prove injectivity of "extended" capability data representation, i.e. for capability
  data represented as a list of separate lists (of 32-byte words), each corresponding to a
  low-level representation of one capability. The outer list is paired with the total length of
  the representations. This directly corresponds
  to the result of @{const "cap_data_rep"}. However, to obtain the actual representation,
  we later take only the list of lists out from this result (no total length),
  then reverse and concatenate it.
  So this lemma is not enough to show the overall injectivity of the representation, but
  in the following we reduce overall injectivity to this intermediate result. We do this by
  proving that the total length is unambiguously recoverable from the resulting lists and that
  the resulting list of lists can be recovered from the concatenated list due to the lengths
  encoded in the initial 32-byte words.
\<close>

lemma cap_data_rep_inj[dest]:
  "\<lbrakk>cap_data_rep d\<^sub>1 r\<^sub>1 i\<^sub>1 = cap_data_rep d\<^sub>2 r\<^sub>2 i\<^sub>2; length (snd i\<^sub>1) = length (snd i\<^sub>2)\<rbrakk> \<Longrightarrow> d\<^sub>1 = d\<^sub>2"
  (is "\<lbrakk>?eq_rep d\<^sub>1 i\<^sub>1 d\<^sub>2 i\<^sub>2; ?eq_length i\<^sub>1 i\<^sub>2\<rbrakk> \<Longrightarrow> _")
proof (induction "\<lfloor>d\<^sub>1\<rfloor>" arbitrary:d\<^sub>1 d\<^sub>2 i\<^sub>1 i\<^sub>2)
  case Nil
  moreover hence "length (snd (cap_data_rep d\<^sub>1 r\<^sub>1 i\<^sub>1)) = length (snd i\<^sub>1)" by (simp (no_asm))
  ultimately have "\<lfloor>d\<^sub>1\<rfloor> = \<lfloor>d\<^sub>2\<rfloor>" by simp
  thus ?case by (simp add:cap_data_rep'_inject)
next
  {
    fix xs j\<^sub>1 j\<^sub>2 l\<^sub>1 l\<^sub>2
    have "fold (cap_data_rep0 r\<^sub>1) xs (j\<^sub>1, l\<^sub>1) = fold (cap_data_rep0 r\<^sub>2) xs (j\<^sub>2, l\<^sub>2) \<Longrightarrow> l\<^sub>1 = l\<^sub>2"
      unfolding cap_data_rep0_def
      by (induction xs arbitrary: j\<^sub>1 j\<^sub>2 l\<^sub>1 l\<^sub>2, auto split:prod.splits)
  } note inj = this
  case (Cons x xs)
  hence "length \<lfloor>d\<^sub>2\<rfloor> = length \<lfloor>d\<^sub>1\<rfloor>" by (metis add_right_cancel length_snd_cap_data_rep)
  with \<open>x # xs = \<lfloor>d\<^sub>1\<rfloor>\<close> obtain y ys where "\<lfloor>d\<^sub>2\<rfloor> = y # ys" by (metis length_Suc_conv)
  from \<open>x # xs = \<lfloor>d\<^sub>1\<rfloor>\<close> have d\<^sub>1:"\<lfloor>d\<^sub>1\<rfloor> = x # xs" ..
  note d\<^sub>2 = \<open>\<lfloor>d\<^sub>2\<rfloor> = y # ys\<close>
  from \<open>?eq_rep d\<^sub>1 i\<^sub>1 d\<^sub>2 i\<^sub>2\<close> obtain i\<^sub>1' and i\<^sub>2'
    where "cap_data_rep \<lceil>xs\<rceil> r\<^sub>1 i\<^sub>1' = cap_data_rep \<lceil>ys\<rceil> r\<^sub>2 i\<^sub>2'"
      and "length (snd i\<^sub>1') = length (snd i\<^sub>1) + 1"
      and "length (snd i\<^sub>2') = length (snd i\<^sub>2) + 1"
    unfolding cap_data_rep_def cap_data_rep0_def
    using cap_data_rep'_tail[OF d\<^sub>2] cap_data_rep'_tail[OF d\<^sub>1]
    by (auto simp add:d\<^sub>1 d\<^sub>2 split:prod.split)
  with \<open>?eq_rep d\<^sub>1 i\<^sub>1 d\<^sub>2 i\<^sub>2\<close> \<open>?eq_length i\<^sub>1 i\<^sub>2\<close> have tls:"xs = ys"
    using cap_data_rep'_tail[OF d\<^sub>1] cap_data_rep'_tail[OF d\<^sub>2]
    by (auto dest:Cons.hyps(1)[OF cap_data_rep'_tail[OF d\<^sub>1]])
  with \<open>?eq_rep d\<^sub>1 i\<^sub>1 d\<^sub>2 i\<^sub>2\<close> d\<^sub>1 d\<^sub>2 have "snd (cap_data_rep0 r\<^sub>1 x i\<^sub>1) = snd (cap_data_rep0 r\<^sub>2 y i\<^sub>2)"
    unfolding cap_data_rep_def
    by auto (metis inj prod.collapse)
  moreover have "wf_cap (fst (fst x)) (snd x)" and  "wf_cap (fst (fst y)) (snd y)"
    using cap_data_rep'[of d\<^sub>1] d\<^sub>1 cap_data_rep'[of d\<^sub>2]  d\<^sub>2
    by auto
  ultimately have "x = y" unfolding cap_data_rep0_def
    apply (auto split:prod.splits
        del:cap_type_rep_inj overwrite_cap_inj
        dest!:cap_type_rep_inj overwrite_cap_inj)
    using cap_data_rep'[of d\<^sub>1] d\<^sub>1 cap_data_rep'[of d\<^sub>2] d\<^sub>2
    by auto
  with tls d\<^sub>1 d\<^sub>2 have "\<lfloor>d\<^sub>1\<rfloor> = \<lfloor>d\<^sub>2\<rfloor>" by simp
  thus ?case by (simp add:cap_data_rep'_inject)
qed

text \<open>
  Helper lemma for induction base proofs. Since @{prop "concat a = []"} implies
  @{prop "\<forall> x \<in> set a. x = []"}, to obtain @{prop "a = []"} we need this lemma.
\<close>

lemma cap_data_rep_lengths:
  "list_all ((\<noteq>) []) l \<Longrightarrow> list_all ((\<noteq>) []) (snd (cap_data_rep d r (i, l)))"
proof (induction "\<lfloor>d\<rfloor>" arbitrary:d i l)
  case Nil
  thus ?case unfolding cap_data_rep_def by simp
next
  case (Cons x xs)
  then obtain i' l' where "cap_data_rep0 r x (i, l) = (i', l')" and "list_all ((\<noteq>) []) l'"
    unfolding cap_data_rep0_def by (induction x) auto
  with Cons show ?case
    using cap_data_rep'_tail[of d, OF Cons.hyps(2)[symmetric]] Cons.hyps(1)[of "\<lceil>xs\<rceil>" l' i']
    unfolding cap_data_rep_def
    by (rewrite in \<open>_ # _ = \<lfloor>d\<rfloor>\<close> in asm eq_commute) auto
qed

text \<open>
  Now proving that the total length is unambiguously recoverable from the length of
  the resulting lists (and the initial total length in the general case).
\<close>

lemma cap_data_rep_index[simp]:
  assumes "sum_list (map length l) \<le> i"
  shows   "fst (cap_data_rep d r (i, l)) =
           sum_list (map length (snd (cap_data_rep d r (i, l)))) + (i - sum_list (map length l))"
  using assms
proof (induction "\<lfloor>d\<rfloor>" arbitrary:d i l)
  case Nil
  thus ?case unfolding cap_data_rep_def by auto
next
  case (Cons x xs)
  from Cons(2) have wf:"wf_cap (fst (fst x)) (snd x)"
    using cap_data_rep'[of d] list.set_intros(1)[of x xs]
    by (induction x) auto
  hence 0:"length (overwrite_cap (fst (fst x)) (snd x) (drop (i + 3) r)) = length (snd x)" by simp
  let "?i'" = "fst (cap_data_rep0 r x (i, l))"
    and "?l'" = "snd (cap_data_rep0 r x (i, l))"
  from 0 have "sum_list (map length ?l') = sum_list (map length l) + length (snd x) + 3"
    unfolding cap_data_rep0_def by (auto split:prod.splits)
  hence 1:"?i' = sum_list (map length ?l') + (i - sum_list (map length l))"
    unfolding cap_data_rep0_def using Cons(3) by (simp split:prod.splits)
  from Cons(3) have 2:"sum_list (map length ?l') \<le> ?i'"
    unfolding cap_data_rep0_def using wf by (auto split:prod.splits)
  from Cons(1)[of "\<lceil>xs\<rceil>" ?l' ?i', OF _ 2] cap_data_rep'_tail[OF Cons(2)[symmetric]]
  show ?case unfolding cap_data_rep_def by ((subst Cons(2)[symmetric])+, simp) (insert 1, simp)
qed

lemma cap_data_rep_dest:
  assumes "snd (cap_data_rep d r (i, [])) \<noteq> []"
  obtains i' where
    "snd (cap_data_rep d r (i, l)) =
     hd (snd (cap_data_rep0 r (last \<lfloor>d\<rfloor>) (i', []))) # snd (cap_data_rep \<lceil>butlast \<lfloor>d\<rfloor>\<rceil> r (i, l))"
  using assms(1)
proof (induction "\<lfloor>d\<rfloor>" arbitrary:d i l ?thesis)
  case Nil
  thus ?case unfolding cap_data_rep_def by simp
next
  case nonemp:(Cons x xs)
  show ?case proof (cases xs)
    case Nil
    from nonemp(1,3,4) show ?thesis
      unfolding cap_data_rep_def cap_data_rep0_def using cap_data_inverse
      by (simp add:nonemp(2)[symmetric] Nil split:prod.splits)
  next
    case (Cons x' xs')
    let ?l' = "snd (cap_data_rep0 r x (i, l))"
      and ?i' = "fst (cap_data_rep0 r x (i, l))"
    from cap_data_rep'_tail[OF nonemp(2)[symmetric]] have xs:"\<lfloor>\<lceil>xs\<rceil>\<rfloor> = xs" ..
    let ?repx' = "cap_data_rep0 r x' (?i', [])"
    have lenx':"length (snd ?repx') > 0" unfolding cap_data_rep0_def by (simp split:prod.split)
    from cap_data_rep'_tail[of "\<lceil>xs\<rceil>"] xs Cons have xs':"\<lfloor>\<lceil>xs'\<rceil>\<rfloor> = xs'" by simp
    from xs' have "\<And> i l. length l \<le> length (snd (cap_data_rep \<lceil>xs'\<rceil> r (i, l)))"
    proof (induction xs')
      case Nil
      thus ?case by simp
    next
      case (Cons y ys)
      let ?i' = "fst (cap_data_rep0 r y (i, l))"
        and ?l' = "snd (cap_data_rep0 r y (i, l))"
      note 0 = cap_data_rep'_tail[OF Cons(2), symmetric]
      with Cons(1)[OF 0, of ?l' ?i'] Cons(2)
      show ?case unfolding cap_data_rep_def cap_data_rep0_def by (simp split:prod.splits)
    qed
    from this[of "snd ?repx'" "fst ?repx'"] xs xs' Cons lenx'
    have 0:"snd (cap_data_rep \<lceil>x' # xs'\<rceil> r (?i', [])) \<noteq> []" unfolding cap_data_rep_def by auto
    from nonemp(2) Cons last_ConsR[of xs x] have 1:"last xs = last \<lfloor>d\<rfloor>" by simp
    from cap_data_inverse[of "butlast xs"] cap_data_rep'[of "\<lceil>xs\<rceil>"] xs
    have 2:"\<lfloor>\<lceil>butlast xs\<rceil>\<rfloor> = butlast xs" by (auto split:prod.splits dest!:in_set_butlastD)
    from cap_data_inverse[of "butlast \<lfloor>d\<rfloor>"] cap_data_rep'[of "d"]
    have 3:"\<lfloor>\<lceil>butlast \<lfloor>d\<rfloor>\<rceil>\<rfloor> = butlast \<lfloor>d\<rfloor>" by (auto split:prod.splits dest!:in_set_butlastD)
    from Cons have 4:"butlast \<lfloor>d\<rfloor> = x # butlast xs" by (rewrite nonemp(2)[symmetric], simp)
    from nonemp(1)[of "\<lceil>xs\<rceil>" ?i' ?l', OF xs[symmetric]] 0 Cons obtain i'' where
      "snd (cap_data_rep \<lceil>xs\<rceil> r (?i', ?l')) =
         hd (snd (cap_data_rep0 r (last xs) (i'', []))) #
           snd (cap_data_rep \<lceil>butlast xs\<rceil> r (?i', ?l'))"
      using xs
      by auto
    with nonemp(3) xs show ?thesis unfolding cap_data_rep_def
      by (rewrite in asm nonemp(2)[symmetric]) (rewrite in asm 3, simp add: 1 2 4)
  qed
qed

text \<open>
  Now we need to prove that the list of lists resulting from @{const "cap_data_rep"} can be
  recovered from its reversed and concatenated representation. This is quite hard to do directly,
  so we introduce an intermediate definition @{text "cap_data_rep1"}, prove the
  bijective correspondence between it and @{const "cap_data_rep"}, then prove injectivity for
  concatenation of @{text "cap_data_rep1"} and use it to prove that the initial list of lists
  is recoverable.
\<close>

definition "cap_data_rep1 r \<equiv>
  \<lambda> ((c, i), l) (j, d). (j + 3 + length l, d @ [cap_data_rep_single r c i l j])"

lemma cap_data_rep1_fold_pull[simp]:
  "snd (fold (cap_data_rep1 r) d (i, x # xs)) = x # snd (fold (cap_data_rep1 r) d (i, xs))"
proof (induction d arbitrary:xs i)
  case Nil
  thus ?case by simp
next
  case (Cons d ds)
  obtain xs' i' where
    "cap_data_rep1 r d (i, x # xs) = (i', x # xs @ xs')" and
    "cap_data_rep1 r d (i, xs) = (i', xs @ xs')"
    unfolding cap_data_rep1_def by (induction d) auto
  with Cons(1)[of i' "xs @ xs'"] show ?case by simp
qed

text \<open>
 Proving bijective correspondence between @{const "cap_data_rep"} and @{const "cap_data_rep1"}.
\<close>

lemma cap_data_rep_rel:
  "rev (snd (cap_data_rep d r (i, l))) = rev l @ snd (fold (cap_data_rep1 r) \<lfloor>d\<rfloor> (i, []))"
proof (induction "\<lfloor>d\<rfloor>" arbitrary: d i l)
  case Nil
  thus ?case unfolding cap_data_rep_def by simp
next
  case (Cons x xs)
  from cap_data_rep'_tail[OF Cons(2)[symmetric]] have xs:"\<lfloor>\<lceil>xs\<rceil>\<rfloor> = xs" ..
  let ?i' = "fst (cap_data_rep0 r x (i, l))"
    and ?l' = "snd (cap_data_rep0 r x (i, l))"
  obtain i'' x' where 0:"cap_data_rep1 r x (i, []) = (i'', x' # [])"
    unfolding cap_data_rep1_def by (induction x) auto
  hence 1:"rev (snd (cap_data_rep0 r x (i, []))) = [x']"
    unfolding cap_data_rep0_def cap_data_rep1_def by (induction x) auto
  have [simp]: "fst (cap_data_rep0 r x (i, [])) = fst (cap_data_rep1 r x (i, []))"
    unfolding cap_data_rep0_def cap_data_rep1_def by (induction x) auto
  have [simp]:
    "cap_data_rep0 r x (i, l) =
    (fst (cap_data_rep0 r x (i, [])), snd (cap_data_rep0 r x (i, [])) @ l)"
    unfolding cap_data_rep0_def by (simp split:prod.split)
  from Cons(1)[of "\<lceil>xs\<rceil>" ?i' ?l', OF xs[symmetric]] xs
  show ?case unfolding cap_data_rep_def by (simp add: Cons(2)[symmetric] 0 1)
qed

text \<open>
  Prove that we can recover result of @{const "cap_data_rep1"} from its concatenation.
\<close>

lemma concat_cap_data_rep_inj_snd[dest]:
  fixes d\<^sub>1' d\<^sub>2' :: capability_data
  assumes "concat (snd (fold (cap_data_rep1 r\<^sub>1) d\<^sub>1 (i\<^sub>1, []))) =
           concat (snd (fold (cap_data_rep1 r\<^sub>2) d\<^sub>2 (i\<^sub>2, [])))"
  assumes "d\<^sub>1 = \<lfloor>d\<^sub>1'\<rfloor>" and "d\<^sub>2 = \<lfloor>d\<^sub>2'\<rfloor>"
  shows   "snd (fold (cap_data_rep1 r\<^sub>1) d\<^sub>1 (i\<^sub>1, [])) =
           snd (fold (cap_data_rep1 r\<^sub>2) d\<^sub>2 (i\<^sub>2, []))"
  using assms
proof (induction d\<^sub>1 arbitrary: d\<^sub>1' d\<^sub>2 d\<^sub>2' i\<^sub>1 i\<^sub>2)
  case Nil
  from Nil(3) have 0: "snd (fold (cap_data_rep1 r\<^sub>2) d\<^sub>2 (i\<^sub>2, [])) =
                       rev (snd (cap_data_rep d\<^sub>2' r\<^sub>2 (i\<^sub>2, [])))"
    by (subst rev_is_rev_conv[symmetric], simp add:cap_data_rep_rel)
  from Nil(3) have 1:"d\<^sub>2 \<noteq> [] \<Longrightarrow> set (snd (cap_data_rep d\<^sub>2' r\<^sub>2 (i\<^sub>2, []))) \<noteq> {}"
    using length_snd_cap_data_rep[of d\<^sub>2' r\<^sub>2 "(i\<^sub>2, [])"] by force
  from Nil[simplified] have "d\<^sub>2 \<noteq> [] \<Longrightarrow> False"
    using cap_data_rep_lengths[of "[]" d\<^sub>2' r\<^sub>2 i\<^sub>2, simplified, unfolded list_all_def]
    by (subst (asm) 0) (subst (asm) set_rev, frule 1, metis equals0I)
  thus ?case by (cases d\<^sub>2, simp_all)
next
  case (Cons x xs)
  obtain i\<^sub>1' l\<^sub>1' where
    0:"cap_data_rep1 r\<^sub>1 x (i\<^sub>1, []) = (i\<^sub>1', l\<^sub>1' # [])" and
    1:"l\<^sub>1' \<noteq> []" and
    2:"[l\<^sub>1'] = snd (cap_data_rep1 r\<^sub>1 x (i\<^sub>1, []))"
    unfolding cap_data_rep1_def by (induction x) auto
  have
    l:"concat (snd (fold (cap_data_rep1 r\<^sub>1) (x # xs) (i\<^sub>1, []))) =
       l\<^sub>1' @ concat (snd (fold (cap_data_rep1 r\<^sub>1) xs (i\<^sub>1', [])))"
    by (simp add:0)
  from Cons(2) have "snd (fold (cap_data_rep1 r\<^sub>2) d\<^sub>2 (i\<^sub>2, [])) \<noteq> []" by (auto simp add:0 1)
  hence "d\<^sub>2 \<noteq> []" by auto
  then obtain y ys where 3:"d\<^sub>2 = y # ys" by (cases d\<^sub>2, auto)
  obtain i\<^sub>2' l\<^sub>2' where
    4:"cap_data_rep1 r\<^sub>2 y (i\<^sub>2, []) = (i\<^sub>2', l\<^sub>2' # [])" and
    5:"l\<^sub>2' \<noteq> []" and
    6:"[l\<^sub>2'] = snd (cap_data_rep1 r\<^sub>2 y (i\<^sub>2, []))"
    unfolding cap_data_rep1_def by (induction y) auto
  have
    r:"concat (snd (fold (cap_data_rep1 r\<^sub>2) d\<^sub>2 (i\<^sub>2, []))) =
       l\<^sub>2' @ concat (snd (fold (cap_data_rep1 r\<^sub>2) ys (i\<^sub>2', [])))"
    by (simp add: 3 4)

  from 2 have 7:"[l\<^sub>1'] = snd (cap_data_rep0 r\<^sub>1 x (i\<^sub>1, []))"
    unfolding cap_data_rep0_def cap_data_rep1_def by (cases x) auto
  from Cons(3) have 8:"x \<in> set \<lfloor>d\<^sub>1'\<rfloor>" using list.set_intros(1)[of x xs] by simp
  note 9 = length_cap_data_rep0'[OF 7 8]
  from 6 have 10:"[l\<^sub>2'] = snd (cap_data_rep0 r\<^sub>2 y (i\<^sub>2, []))"
    unfolding cap_data_rep0_def cap_data_rep1_def by (cases y) auto
  from Cons(4) 3 have 11:"y \<in> set \<lfloor>d\<^sub>2'\<rfloor>" using list.set_intros(1)[of y ys] by simp
  note 12 = length_cap_data_rep0'[OF 10 11]
  from Cons(2) l r 1 5 9 12 have 13:"l\<^sub>1' = l\<^sub>2'" by (metis append_eq_append_conv hd_append2)
  with Cons(2) l r
  have 14:"concat (snd (fold (cap_data_rep1 r\<^sub>1) xs (i\<^sub>1', []))) =
           concat (snd (fold (cap_data_rep1 r\<^sub>2) ys (i\<^sub>2', [])))"
    by simp

  note xs = cap_data_rep'_tail[OF Cons(3)[symmetric]]
  from cap_data_rep'_tail[of d\<^sub>2'] Cons(4) 3 have ys:"ys = \<lfloor>\<lceil>ys\<rceil>\<rfloor>" by blast
  note 15 = Cons(1)[OF 14 xs ys]

  from 0 3 4 13 15 show ?case by simp
qed

text \<open>Final injectivity proof for capability data representation:\<close>

lemma concat_cap_data_rep_inj[simplified, dest]:
  "(concat \<circ> rev \<circ> snd) (cap_data_rep d\<^sub>1 r\<^sub>1 (i, [])) =
   (concat \<circ> rev \<circ> snd) (cap_data_rep d\<^sub>2 r\<^sub>2 (i, [])) \<Longrightarrow>
   cap_data_rep d\<^sub>1 r\<^sub>1 (i, []) = cap_data_rep d\<^sub>2 r\<^sub>2 (i, [])"
  (is "?prem \<Longrightarrow> _")
proof
  assume ?prem
  hence
    "concat (snd (fold (cap_data_rep1 r\<^sub>1) \<lfloor>d\<^sub>1\<rfloor> (i, []))) =
     concat (snd (fold (cap_data_rep1 r\<^sub>2) \<lfloor>d\<^sub>2\<rfloor> (i, [])))"
    by (simp add:cap_data_rep_rel)
  hence "snd (fold (cap_data_rep1 r\<^sub>1) \<lfloor>d\<^sub>1\<rfloor> (i, [])) = snd (fold (cap_data_rep1 r\<^sub>2) \<lfloor>d\<^sub>2\<rfloor> (i, []))"
    by auto
  thus "snd (cap_data_rep d\<^sub>1 r\<^sub>1 (i, [])) = snd (cap_data_rep d\<^sub>2 r\<^sub>2 (i, []))"
    by (simp add:cap_data_rep_rel[where l="[]", simplified, symmetric])
  thus "fst (cap_data_rep d\<^sub>1 r\<^sub>1 (i, [])) = fst (cap_data_rep d\<^sub>2 r\<^sub>2 (i, []))"
    by simp
qed

definition "reg_call_rep (d :: register_call_data) r \<equiv>
    [ucast (proc_key d) OR (r ! 0) \<restriction> {LENGTH(key) ..<LENGTH(word32)},
     ucast (eth_addr d) OR (r ! 1) \<restriction> {LENGTH(ethereum_address) ..<LENGTH(word32)}] @
     ((concat \<circ> rev \<circ> snd) (cap_data_rep (cap_data d) r (2, [])))"

adhoc_overloading rep reg_call_rep

lemma reg_call_rep_inj[dest]: "\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>d\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> d\<^sub>1 = d\<^sub>2" for d\<^sub>1 d\<^sub>2 :: register_call_data
proof (rule register_call_data.equality)
  assume eq:"\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>d\<^sub>2\<rfloor> r\<^sub>2"

  from eq show "proc_key d\<^sub>1 = proc_key d\<^sub>2" unfolding reg_call_rep_def by auto
  from eq show "eth_addr d\<^sub>1 = eth_addr d\<^sub>2" unfolding reg_call_rep_def by auto

  from eq show "cap_data d\<^sub>1 = cap_data d\<^sub>2" unfolding reg_call_rep_def by auto
qed simp

lemmas reg_call_invertible[intro] = invertible2.intro[OF inj2I, OF reg_call_rep_inj]

interpretation reg_call_inv: invertible2 reg_call_rep ..

adhoc_overloading abs reg_call_inv.inv2

subsection \<open>Procedure call system call\<close>

type_synonym procedure_call_data = "(key \<times> byte list)"

definition "proc_call_rep (cd :: procedure_call_data) (r :: byte list) \<equiv>
  let (k, d) = cd;
       r' = word_rcat (take (LENGTH(word32) div LENGTH(byte)) r) :: word32 in
  word_rsplit (ucast k OR r' \<restriction> {LENGTH(key) ..<LENGTH(word32)}) @ d"

adhoc_overloading rep proc_call_rep

lemma word_rsplit_inj[dest]: "word_rsplit a = word_rsplit b \<Longrightarrow> a = b" for a::"'a::len word"
  by (auto dest:arg_cong[where f="word_rcat :: _ \<Rightarrow> 'a word"] simp add:word_rcat_rsplit)

lemma proc_call_rep_inj[dest]: "\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>d\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> d\<^sub>1 = d\<^sub>2" for d\<^sub>1 d\<^sub>2 :: procedure_call_data
proof-
  let "?key_rep k r" =
    "word_rsplit (ucast (k :: key) OR (r :: word32) \<restriction> {LENGTH(key) ..<LENGTH(word32)})
     :: byte list"
  assume "\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>d\<^sub>2\<rfloor> r\<^sub>2"
  moreover then obtain k\<^sub>1 d\<^sub>1' and r\<^sub>1' :: word32 and k\<^sub>2 d\<^sub>2' and r\<^sub>2' :: word32 where
    "\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1 = ?key_rep k\<^sub>1 r\<^sub>1' @ d\<^sub>1'" "\<lfloor>d\<^sub>2\<rfloor> r\<^sub>2 = ?key_rep k\<^sub>2 r\<^sub>2' @ d\<^sub>2'" and
    d\<^sub>1:"(k\<^sub>1, d\<^sub>1') = d\<^sub>1" and d\<^sub>2:"(k\<^sub>2, d\<^sub>2') = d\<^sub>2"
    unfolding proc_call_rep_def
    by (simp add: Let_def split:prod.splits, metis)
  moreover have "length (?key_rep k\<^sub>1 r\<^sub>1') = length (?key_rep k\<^sub>2 r\<^sub>2')"
    by (rule word_rsplit_len_indep)
  ultimately have "?key_rep k\<^sub>1 r\<^sub>1' = ?key_rep k\<^sub>2 r\<^sub>2'" and "d\<^sub>1' = d\<^sub>2'" by auto
  with d\<^sub>1 and d\<^sub>2 show ?thesis by auto
qed

lemmas proc_call_invertible[intro] = invertible2.intro[OF inj2I, OF proc_call_rep_inj]

interpretation proc_call_inv: invertible2 proc_call_rep ..

adhoc_overloading abs proc_call_inv.inv2

subsection \<open>External call system call\<close>

record external_call_data =
  addr   :: ethereum_address
  amount :: word32
  data   :: "byte list"

definition "ext_call_rep (d :: external_call_data) (r :: byte list) \<equiv>
  let r' = word_rcat (take (LENGTH(word32) div LENGTH(byte)) r) :: word32 in
  concat (split
    [ucast (addr d) OR r' \<restriction> {LENGTH(ethereum_address) ..<LENGTH(word32)},
     amount d])
  @ data d"

adhoc_overloading rep ext_call_rep

declare length_split[simp del] length_concat_split[simp del]

lemma ext_call_rep_inj[dest]: "\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>d\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> d\<^sub>1 = d\<^sub>2" for d\<^sub>1 d\<^sub>2 :: external_call_data
proof (rule external_call_data.equality)
  {
    fix a\<^sub>1 b\<^sub>1 a\<^sub>2 b\<^sub>2 :: word32 and d\<^sub>1 d\<^sub>2 :: "byte list"
    assume "concat (split [a\<^sub>1, b\<^sub>1]) @ d\<^sub>1 = concat (split [a\<^sub>2, b\<^sub>2]) @ d\<^sub>2"
    hence "a\<^sub>1 = a\<^sub>2" and "b\<^sub>1 = b\<^sub>2" by (auto simp add:word_rsplit_len_indep)
  } note dest[dest] = this
  assume eq:"\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>d\<^sub>2\<rfloor> r\<^sub>2"

  from eq show "addr d\<^sub>1 = addr d\<^sub>2" unfolding ext_call_rep_def
    by (auto simp del:concat.simps split.simps)
  from eq show "amount d\<^sub>1 = amount d\<^sub>2" unfolding ext_call_rep_def by (auto simp only:Let_def)
  from eq show "data d\<^sub>1 = data d\<^sub>2" unfolding ext_call_rep_def
    by (auto simp add:word_rsplit_len_indep)
qed simp

lemmas external_call_invertible[intro] = invertible2.intro[OF inj2I, OF ext_call_rep_inj]

interpretation ext_call_inv: invertible2 ext_call_rep ..

adhoc_overloading abs ext_call_inv.inv2

subsection \<open>Log system call\<close>

type_synonym log_topics = log_capability

type_synonym log_call_data = "log_topics \<times> byte list"

definition "log_call_rep td r \<equiv>
  let (t, d) = td;
      n = length \<lfloor>t\<rfloor>;
      c = LENGTH(word32) div LENGTH(byte);
      r' = word_rcat (take c (drop (c * (n + 1)) r)) :: word32 in
  concat (split (\<lfloor>t\<rfloor> @ [r'])) @ d"
  for td :: log_call_data

adhoc_overloading rep log_call_rep

lemma log_call_rep_inj[dest]: "\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>d\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> d\<^sub>1 = d\<^sub>2" for d\<^sub>1 d\<^sub>2 :: log_call_data
proof
  {
    fix a b :: "word32 list" and d\<^sub>1 d\<^sub>2
    assume "(concat (split a) :: byte list) @ d\<^sub>1 = concat (split b) @ d\<^sub>2"
      and "length a = length b"
    hence "a = b"
      by (intro split_inj, intro concat_injective, auto)
        (subst (asm) append_eq_append_conv, auto elim:in_set_zipE simp add:split_lengths)
  } note [dest] = this

  assume eq:"\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>d\<^sub>2\<rfloor> r\<^sub>2"
  moreover hence "length \<lfloor>fst d\<^sub>1\<rfloor> = length \<lfloor>fst d\<^sub>2\<rfloor>" unfolding log_call_rep_def log_cap_rep_def
    using log_cap_rep'[of "fst d\<^sub>1"] log_cap_rep'[of "fst d\<^sub>2"]
    by (auto split:prod.splits simp add:word_rsplit_len_indep of_nat_inj)
  ultimately show "fst d\<^sub>1 = fst d\<^sub>2" unfolding log_call_rep_def by (auto split:prod.splits)

  with eq show "snd d\<^sub>1 = snd d\<^sub>2" unfolding log_call_rep_def
    by (auto split:prod.splits simp add:word_rsplit_len_indep)
qed

lemmas log_call_invertible[intro] = invertible2.intro[OF inj2I, OF log_call_rep_inj]

interpretation log_call_inv: invertible2 log_call_rep ..

adhoc_overloading abs log_call_inv.inv2

subsection \<open>Delete and Set entry system calls\<close>

type_synonym delete_call_data = key

type_synonym set_entry_call_data = key

definition "proc_key_call_rep k r = [ucast k OR r \<restriction> {LENGTH(key) ..<LENGTH(word32)}]"
  for k :: key and r :: word32

adhoc_overloading rep proc_key_call_rep

lemma proc_key_call_rep_inj0[dest]: "\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>d\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> d\<^sub>1 = d\<^sub>2" for d\<^sub>1 d\<^sub>2 :: key
  unfolding proc_key_call_rep_def by auto

lemma proc_key_call_rep_length[simp]: "length (\<lfloor>d\<rfloor> r) = 1" for d :: key
  unfolding proc_key_call_rep_def by simp

lemma proc_key_call_rep_inj[dest]: "prefix (\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1) (\<lfloor>d\<^sub>2\<rfloor> r\<^sub>2) \<Longrightarrow> d\<^sub>1 = d\<^sub>2" for d\<^sub>1 d\<^sub>2 :: key
  unfolding prefix_def using proc_key_call_rep_length
  by (subst (asm) append_Nil2[symmetric]) (subst (asm) append_eq_append_conv, auto)

lemma proc_key_call_rep_indep: "length (\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1) = length (\<lfloor>d\<^sub>2\<rfloor> r\<^sub>2)" for d\<^sub>1 d\<^sub>2 :: key by simp

lemmas proc_key_call_invertible[intro] =
  invertible2_tf.intro[OF inj2_tfI, OF proc_key_call_rep_inj proc_key_call_rep_indep]

interpretation proc_key_call_inv: invertible2_tf proc_key_call_rep ..

adhoc_overloading abs proc_key_call_inv.inv2_tf

subsection \<open>Write system call\<close>

type_synonym write_call_data = "word32 \<times> word32"

definition "write_call_rep w _ \<equiv> let (a, v) = w in [a, v]" for w :: write_call_data

adhoc_overloading rep write_call_rep

lemma write_call_rep_inj[dest]: "prefix (\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1) (\<lfloor>d\<^sub>2\<rfloor> r\<^sub>2) \<Longrightarrow> d\<^sub>1 = d\<^sub>2" for d\<^sub>1 d\<^sub>2 :: write_call_data
  unfolding write_call_rep_def by (simp split:prod.splits)

lemma write_call_rep_indep: "length (\<lfloor>d\<^sub>1\<rfloor> r\<^sub>1) = length (\<lfloor>d\<^sub>2\<rfloor> r\<^sub>2)" for d\<^sub>1 d\<^sub>2 :: write_call_data
  unfolding write_call_rep_def by (simp split:prod.split)

lemmas write_call_invertible[intro] =
  invertible2_tf.intro[OF inj2_tfI, OF write_call_rep_inj write_call_rep_indep]

interpretation write_call_inv: invertible2_tf write_call_rep ..

adhoc_overloading abs write_call_inv.inv2_tf

section \<open>System calls\<close>

datatype result =
    Success storage
  | Revert

abbreviation "SYSCALL_NOEXIST \<equiv> 0xaa"

abbreviation "SYSCALL_BADCAP \<equiv> 0x33"

abbreviation "SYSCALL_FAIL \<equiv> 0x66"

subsection \<open>Register system call\<close>

abbreviation "REG_TOOMANYCAPS \<equiv> 0x77"

definition "valid_code (_ :: ethereum_address) = undefined"

definition "caps t d \<equiv>
  let caps = filter ((=) t \<circ> fst \<circ> fst) \<lfloor>cap_data d\<rfloor> in
  if length caps < 2 ^ LENGTH(byte) - 1
  then Some (map (apfst snd) caps)
  else None"

lemma wf_caps: "caps t d = Some c \<Longrightarrow> \<forall> (_, l) \<in> set c. wf_cap t l"
  unfolding caps_def using cap_data_rep'[of "cap_data d"]
  by (auto split:prod.splits if_splits simp add:Let_def)

definition "sub_caps t cs p =
   list_all
     (\<lambda> (i :: capability_index, l) \<Rightarrow>
      (case (t, l) of
        (Call,  [])       \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>call_caps p\<rfloor>
      | (Call,  [c])      \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>call_caps p\<rfloor> \<and>
                             the (\<lceil>c\<rceil> :: prefixed_capability option) \<subseteq>\<^sub>c \<lfloor>call_caps p\<rfloor> ! \<lfloor>i\<rfloor>
      | (Reg,   [])       \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>reg_caps p\<rfloor>
      | (Reg,   [c])      \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>reg_caps p\<rfloor> \<and>
                             the (\<lceil>c\<rceil> :: prefixed_capability option) \<subseteq>\<^sub>c \<lfloor>reg_caps p\<rfloor> ! \<lfloor>i\<rfloor>
      | (Del,   [])       \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>del_caps p\<rfloor>
      | (Del,   [c])      \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>del_caps p\<rfloor> \<and>
                             the (\<lceil>c\<rceil> :: prefixed_capability option) \<subseteq>\<^sub>c \<lfloor>del_caps p\<rfloor> ! \<lfloor>i\<rfloor>
      | (Entry, [])       \<Rightarrow> entry_cap p
      | (Write, [])       \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>write_caps p\<rfloor>
      | (Write, [c1, c2]) \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>write_caps p\<rfloor> \<and>
                             the (\<lceil>(c1, c2)\<rceil> :: write_capability option) \<subseteq>\<^sub>c \<lfloor>write_caps p\<rfloor> ! \<lfloor>i\<rfloor>
      | (Log,   [])       \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>log_caps p\<rfloor>
      | (Log,   c)        \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>log_caps p\<rfloor> \<and>
                             the (\<lceil>c\<rceil> :: log_capability option) \<subseteq>\<^sub>c \<lfloor>log_caps p\<rfloor> ! \<lfloor>i\<rfloor>
      | (Send,  [])       \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>ext_caps p\<rfloor>
      | (Send,  [c])      \<Rightarrow> \<lfloor>i\<rfloor> < length \<lfloor>ext_caps p\<rfloor> \<and>
                             the (\<lceil>c\<rceil> :: external_call_capability option) \<subseteq>\<^sub>c \<lfloor>ext_caps p\<rfloor> ! \<lfloor>i\<rfloor>))
     cs"

definition "fill_caps t cs p \<equiv>
  map
   (\<lambda> (i :: capability_index, l) \<Rightarrow>
     if l = [] then
       case t of
         Call  \<Rightarrow> (i, [\<lfloor>\<lfloor>call_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> (0 :: word32)])
       | Reg   \<Rightarrow> (i, [\<lfloor>\<lfloor>reg_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> (0 :: word32)])
       | Del   \<Rightarrow> (i, [\<lfloor>\<lfloor>del_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> (0 :: word32)])
       | Entry \<Rightarrow> (i, [])
       | Write \<Rightarrow> (i, let (a, s) = \<lfloor>\<lfloor>write_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> in [a, s])
       | Log   \<Rightarrow> (i, \<lfloor>\<lfloor>log_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor>)
       | Send  \<Rightarrow> (i, [\<lfloor>\<lfloor>ext_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rfloor> (0 :: word32)])
     else         (i, l))
   cs"

definition register :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "register i d s \<equiv>
     let \<sigma> = the \<lceil>s\<rceil>;
         p = curr_proc' \<sigma> in
     if \<not> LENGTH(word32) div LENGTH(byte) dvd length d then
                                                      (Revert, [])
     else case \<lceil>cat d\<rceil> of
       None                                      \<Rightarrow>   (Revert, [])
                                  \<comment> \<open>Malformed call data, currently the error code is not defined\<close>
     | Some d                                    \<Rightarrow>
       if max_nprocs = nprocs \<sigma>                  then (Revert, [SYSCALL_FAIL])
                                                             \<comment> \<open>Too many procs: Unrealistic,
                                                                  but needed for formal
                                                                  correctness\<close>
       else if has_key (proc_key d) \<sigma>            then (Revert, [SYSCALL_FAIL])
                                                                   \<comment> \<open>Proc key exists,
                                                                        specific error code not
                                                                        defined\<close>
       else if length \<lfloor>reg_caps p\<rfloor> \<le> \<lfloor>i\<rfloor>         then (Revert, [SYSCALL_BADCAP])
                                                                                 \<comment> \<open>No such cap\<close>
       else if proc_key d \<notin> \<lceil>\<lfloor>reg_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rceil>  then (Revert, [SYSCALL_BADCAP])
       else if \<not> valid_code (eth_addr d)         then (Revert, [SYSCALL_FAIL]) \<comment> \<open>Code invalid\<close>
       else (case (caps Call d,
                  caps Reg d,
                  caps Del d,
                  caps Entry d,
                  caps Write d,
                  caps Log d,
                  caps Send d) of
       (Some calls, Some regs, Some dels, Some ents, Some wrts, Some logs, Some exts) \<Rightarrow>
         if sub_caps Call  calls p \<and>
            sub_caps Reg   regs  p \<and>
            sub_caps Del   dels  p \<and>
            sub_caps Entry ents  p \<and>
            sub_caps Write wrts  p \<and>
            sub_caps Log   logs  p \<and>
            sub_caps Send  exts  p               then
           let calls = fill_caps Call  calls p;
               regs  = fill_caps Reg   regs  p;
               dels  = fill_caps Del   dels  p;
               ents  = fill_caps Entry ents  p;
               wrts  = fill_caps Write wrts  p;
               logs  = fill_caps Log   logs  p;
               exts  = fill_caps Send  exts  p  in
           let p' =
              \<lparr> procedure.eth_addr   = eth_addr d,
                call_caps  = cap_list (map (the \<circ> abs \<circ> hd \<circ> snd) calls),
                reg_caps   = cap_list (map (the \<circ> abs \<circ> hd \<circ> snd) regs),
                del_caps   = cap_list (map (the \<circ> abs \<circ> hd \<circ> snd) dels),
                entry_cap  = ents \<noteq> [],
                write_caps = cap_list (map (\<lambda> (_, [a, s]) \<Rightarrow> the \<lceil>(a, s)\<rceil>) wrts),
                log_caps   = cap_list (map (the \<circ> abs \<circ> snd) logs),
                ext_caps   = cap_list (map (the \<circ> abs \<circ> hd \<circ> snd) exts) \<rparr>;
               procs = \<lceil>DAList.update (proc_key d) p' \<lfloor>proc_list \<sigma>\<rfloor>\<rceil>;
               \<sigma>' = \<sigma> \<lparr> proc_list := procs \<rparr> in
                                                      (Success (\<lfloor>\<sigma>'\<rfloor> s), [])
         else                                         (Revert, [SYSCALL_BADCAP])
                                                      \<comment> \<open>No cap inclusion\<close>
      | _                                        \<Rightarrow>   (Revert, [SYSCALL_FAIL, REG_TOOMANYCAPS]))"

subsection \<open>Delete system call\<close>

abbreviation "DEL_NOPROC \<equiv> 0x33"

definition delete :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "delete i d s \<equiv>
     let \<sigma> = the \<lceil>s\<rceil>;
         p = curr_proc' \<sigma> in
     if \<not> LENGTH(word32) div LENGTH(byte) dvd length d then
                                                      (Revert, [])
     else case \<lceil>cat d\<rceil> of
       None                                      \<Rightarrow>   (Revert, [])
                                  \<comment> \<open>Malformed call data, currently the error code is not defined\<close>
     | Some k                                    \<Rightarrow>
       if \<not> has_key k \<sigma>                          then (Revert, [SYSCALL_FAIL, DEL_NOPROC])
       else if length \<lfloor>del_caps p\<rfloor> \<le> \<lfloor>i\<rfloor>         then (Revert, [SYSCALL_BADCAP])
                                                                               \<comment> \<open>No such cap\<close>
       else if k \<notin> \<lceil>\<lfloor>del_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rceil>           then (Revert, [SYSCALL_BADCAP])
       else
         let procs = \<lceil>DAList.delete k \<lfloor>proc_list \<sigma>\<rfloor>\<rceil>;
             \<sigma>' = \<sigma> \<lparr> proc_list := procs \<rparr> in
                                                      (Success (\<lfloor>\<sigma>'\<rfloor> s), [])"

subsection \<open>Write system call\<close>

definition write_addr :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "write_addr i d s \<equiv>
     let \<sigma> = the \<lceil>s\<rceil>;
         p = curr_proc' \<sigma> in
     if \<not> LENGTH(word32) div LENGTH(byte) dvd length d then
                                                      (Revert, [])
     else case \<lceil>cat d\<rceil> of
       None                                      \<Rightarrow>   (Revert, [])
                                  \<comment> \<open>Malformed call data, currently the error code is not defined\<close>
     | Some (a, v)                               \<Rightarrow>
       if length \<lfloor>write_caps p\<rfloor> \<le> \<lfloor>i\<rfloor>            then (Revert, [SYSCALL_BADCAP])
                                                                               \<comment> \<open>No such cap\<close>
       else if a \<notin> \<lceil>\<lfloor>write_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rceil>         then (Revert, [SYSCALL_BADCAP])
       else
                                                      (Success (s (a := v)), [])"

subsection \<open>Set entry system call\<close>

definition set_entry :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "set_entry i d s \<equiv>
     let \<sigma> = the \<lceil>s\<rceil>;
         p = curr_proc' \<sigma> in
     if \<not> LENGTH(word32) div LENGTH(byte) dvd length d then
                                                      (Revert, [])
     else case \<lceil>cat d\<rceil> of
       None                                      \<Rightarrow>   (Revert, [])
                                  \<comment> \<open>Malformed call data, currently the error code is not defined\<close>
     | Some k                                    \<Rightarrow>
       if \<not> has_key k \<sigma>                          then (Revert, [SYSCALL_FAIL])
                                                                   \<comment> \<open>No such proc key,
                                                                        specific error code not
                                                                        defined\<close>
       else if \<not> entry_cap p                     then (Revert, [SYSCALL_BADCAP])
       else
         let \<sigma>' = \<sigma> \<lparr> entry_proc := k \<rparr> in
                                                      (Success (\<lfloor>\<sigma>'\<rfloor> s), [])"

subsection \<open>Log system call\<close>

type_synonym log = "(ethereum_address \<times> log_topics \<times> byte list) list"

definition log ::
  "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> (result \<times> byte list) \<times> log" where
  "log i d s \<equiv>
     let \<sigma> = the \<lceil>s\<rceil>;
         p = curr_proc' \<sigma> in
     let nolog = \<lambda> r. (r, []) in
     case \<lceil>d\<rceil> of
       None                                      \<Rightarrow>     nolog (Revert, [])
                                  \<comment> \<open>Malformed call data, currently the error code is not defined\<close>
     | Some (ts, l)                              \<Rightarrow>
       if length \<lfloor>log_caps p\<rfloor> \<le> \<lfloor>i\<rfloor>                then nolog (Revert, [SYSCALL_BADCAP])
                                                                               \<comment> \<open>No such cap\<close>
       else if \<lfloor>ts\<rfloor> \<notin> \<lceil>\<lfloor>log_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rceil>          then nolog (Revert, [SYSCALL_BADCAP])
       else
         let log = [(procedure.eth_addr (curr_proc' \<sigma>), ts, l)] in
                                                              ((Success s, []), log)"
subsection \<open>Call system call\<close>

abbreviation "SYSCALL_NOGAS \<equiv> 0x44"

abbreviation "SYSCALL_REVERT \<equiv> 0x55"

abbreviation "CALL_NOPROC \<equiv> 0x33"

definition exec_call :: "[key, byte list, storage] \<Rightarrow> result option \<times> byte list"
  where "exec_call k d s \<equiv> undefined"

definition call :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "call i d s \<equiv>
     let \<sigma> = the \<lceil>s\<rceil>;
         p = curr_proc' \<sigma> in
     case \<lceil>d\<rceil> of
       None                                      \<Rightarrow>   (Revert, [])
                                  \<comment> \<open>Malformed call data, currently the error code is not defined\<close>
     | Some (k, a)                               \<Rightarrow>
       if \<not> has_key k \<sigma>                          then (Revert, [SYSCALL_FAIL, CALL_NOPROC])
       else if length \<lfloor>call_caps p\<rfloor> \<le> \<lfloor>i\<rfloor>        then (Revert, [SYSCALL_BADCAP])
                                                                               \<comment> \<open>No such cap\<close>
       else if k \<notin> \<lceil>\<lfloor>call_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rceil>          then (Revert, [SYSCALL_BADCAP])
       else
         (case exec_call k a s of
           (None,             _)                 \<Rightarrow>   (Revert, [SYSCALL_NOGAS])
         | (Some (Success s), r)                 \<Rightarrow>   (Success s, r)
         | (Some Revert,      r)                 \<Rightarrow>   (Revert, SYSCALL_REVERT # r))"

subsection \<open>External system call\<close>

definition exec_ext ::
  "[ethereum_address, word32, byte list, storage] \<Rightarrow> result option \<times> byte list"
  where "exec_ext a v d s \<equiv> undefined"

definition external :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "external i d s \<equiv>
     let \<sigma> = the \<lceil>s\<rceil>;
         p = curr_proc' \<sigma> in
     case \<lceil>d\<rceil> of
       None                                      \<Rightarrow>   (Revert, [])
                                  \<comment> \<open>Malformed call data, currently the error code is not defined\<close>
     | Some d                                    \<Rightarrow>
       let a = addr d; g = amount d in
       if length \<lfloor>ext_caps p\<rfloor> \<le> \<lfloor>i\<rfloor>              then (Revert, [SYSCALL_BADCAP])
                                                                               \<comment> \<open>No such cap\<close>
       else if (a, g) \<notin> \<lceil>\<lfloor>ext_caps p\<rfloor> ! \<lfloor>i\<rfloor>\<rceil>      then (Revert, [SYSCALL_BADCAP])
       else
         (case exec_ext a g (data d) s of
           (None,             _)                 \<Rightarrow>   (Revert, [SYSCALL_NOGAS])
         | (Some (Success s), r)                 \<Rightarrow>   (Success s, r)
         | (Some Revert,      r)                 \<Rightarrow>   (Revert, SYSCALL_REVERT # r))"

definition "cap_type_opt_rep c \<equiv> case c of Some c \<Rightarrow> \<lfloor>c\<rfloor> | None \<Rightarrow> 0x00"
  for c :: "capability option"

adhoc_overloading rep cap_type_opt_rep

lemma cap_type_opt_rep_inj[intro]: "inj cap_type_opt_rep" unfolding cap_type_opt_rep_def inj_def
  by (auto split:option.split)

lemmas cap_type_opt_invertible[intro] = invertible.intro[OF cap_type_opt_rep_inj]

interpretation cap_type_opt_inv: invertible cap_type_opt_rep ..

adhoc_overloading abs cap_type_opt_inv.inv

definition execute :: "byte list \<Rightarrow> storage \<Rightarrow> (result \<times> byte list) \<times> log" where
  "execute c s \<equiv> case takefill 0x00 2 c of ct # ci # c \<Rightarrow>
    let nolog = \<lambda> r. (r, []) in
    (case \<lceil>ct\<rceil> of
      None           \<Rightarrow> nolog (Revert, [SYSCALL_NOEXIST])
    | Some None      \<Rightarrow> nolog (Success s, [])
    | Some (Some ct) \<Rightarrow> (case \<lceil>ci\<rceil> of
       None          \<Rightarrow> nolog (Revert, [SYSCALL_BADCAP]) \<comment> \<open>Capability index out of bounds\<close>
     | Some ci       \<Rightarrow> (case ct of
         Call        \<Rightarrow> nolog (call ci c s)
       | Reg         \<Rightarrow> nolog (register ci c s)
       | Del         \<Rightarrow> nolog (delete ci c s)
       | Entry       \<Rightarrow> nolog (set_entry ci c s)
       | Write       \<Rightarrow> nolog (write_addr ci c s)
       | Log         \<Rightarrow> log ci c s
       | Send        \<Rightarrow> nolog (external ci c s))))"

section \<open>Initialization\<close>

definition "empty_kernel \<equiv>
          \<lparr>  curr_proc  = 0,
             entry_proc = 0,
             proc_list = \<lceil>Alist []\<rceil> \<rparr>"

definition "filled_caps t cs =
   list_all
     (\<lambda> (_, l) \<Rightarrow>
      (case (t, l) of
        (Entry, []) \<Rightarrow> True
      | (_,     []) \<Rightarrow> False
      | (_,      _) \<Rightarrow> True))
     cs"

definition init :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "init i d s \<equiv>
     let \<sigma> = empty_kernel in
     if \<not> LENGTH(word32) div LENGTH(byte) dvd length d then
                                                      (Revert, [])
     else case \<lceil>cat d\<rceil> of
       None                                      \<Rightarrow>   (Revert, [])
                                  \<comment> \<open>Malformed call data, currently the error code is not defined\<close>
     | Some d                                    \<Rightarrow>
       if \<not> valid_code (eth_addr d)              then (Revert, [SYSCALL_FAIL]) \<comment> \<open>Code invalid\<close>
       else (case (caps Call d,
                  caps Reg d,
                  caps Del d,
                  caps Entry d,
                  caps Write d,
                  caps Log d,
                  caps Send d) of
       (Some calls, Some regs, Some dels, Some ents, Some wrts, Some logs, Some exts) \<Rightarrow>
         if filled_caps Call  calls \<and>
            filled_caps Reg   regs  \<and>
            filled_caps Del   dels  \<and>
            filled_caps Entry ents  \<and>
            filled_caps Write wrts  \<and>
            filled_caps Log   logs  \<and>
            filled_caps Send  exts               then
           let p' =
              \<lparr> procedure.eth_addr   = eth_addr d,
                call_caps  = cap_list (map (the \<circ> abs \<circ> hd \<circ> snd) calls),
                reg_caps   = cap_list (map (the \<circ> abs \<circ> hd \<circ> snd) regs),
                del_caps   = cap_list (map (the \<circ> abs \<circ> hd \<circ> snd) dels),
                entry_cap  = ents \<noteq> [],
                write_caps = cap_list (map (\<lambda> (_, [a, s]) \<Rightarrow> the \<lceil>(a, s)\<rceil>) wrts),
                log_caps   = cap_list (map (the \<circ> abs \<circ> snd) logs),
                ext_caps   = cap_list (map (the \<circ> abs \<circ> hd \<circ> snd) exts) \<rparr>;
               procs = \<lceil>DAList.update (proc_key d) p' \<lfloor>proc_list \<sigma>\<rfloor>\<rceil>;
               \<sigma>' = \<sigma> \<lparr> proc_list := procs, entry_proc := proc_key d \<rparr> in
                                                      (Success (\<lfloor>\<sigma>'\<rfloor> s), [])
         else                                         (Revert, [SYSCALL_BADCAP])
                                                      \<comment> \<open>Some parent caps were specified\<close>
      | _                                        \<Rightarrow>   (Revert, [SYSCALL_FAIL, REG_TOOMANYCAPS]))"

end
