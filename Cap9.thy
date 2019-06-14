section \<open>Preliminaries\<close>

theory Cap9
imports
  "HOL-Word.Word"
  "HOL-Library.Adhoc_Overloading"
  "HOL-Library.DAList"
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

text \<open>
  Procedure keys are represented as 24-byte (192 bits) machine words.
\<close>

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

lemmas inv_inj'[folded inv_def, simp] = maybe_inv_inj'[OF inj]
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
  fixes rep :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" ("\<lfloor>_\<rfloor>")
  assumes inj:"inj2 rep"
begin
definition inv2 :: "'c \<Rightarrow> 'a option" where "inv2 \<equiv> maybe_inv2 rep"

lemmas inv2_inj[folded inv2_def, simp] = maybe_inv2_inj[OF inj]

lemmas inv2_inj'[folded inv_def, simp] = maybe_inv2_inj'[OF inj]
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
  Capability representation would be its assigned number.

  In general, in the following we strive to make all encoding functions injective without any
  preconditions. All the necessary invariants are built into the type definitions.
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

lemma cap_type_rep_inj[simp]: "\<lfloor>c\<^sub>1\<rfloor> = \<lfloor>c\<^sub>2\<rfloor> \<Longrightarrow> c\<^sub>1 = c\<^sub>2" for c\<^sub>1 c\<^sub>2 :: capability
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

lemma cap_index_inj[simp]: "(\<lfloor>i\<^sub>1\<rfloor> :: byte) = \<lfloor>i\<^sub>2\<rfloor> \<Longrightarrow> i\<^sub>1 = i\<^sub>2" for i\<^sub>1 i\<^sub>2 :: capability_index
  unfolding cap_index_rep_def
  using cap_index_rep'[of i\<^sub>1] cap_index_rep'[of i\<^sub>2] word_of_nat_inj[of "\<lfloor>i\<^sub>1\<rfloor>" "\<lfloor>i\<^sub>2\<rfloor>"]
        cap_index_rep'_inject
  by force

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

lemma data_offset_inj[simp]:
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

definition "key_index_rep i \<equiv> of_nat (\<lfloor>i\<rfloor> + 1) :: key" for i :: key_index

adhoc_overloading rep key_index_rep

lemma key_index_nonzero[simp]: "\<lfloor>i\<rfloor> \<noteq> (0 :: key)" for i :: key_index
  unfolding key_index_rep_def using key_index_rep'[of i]
  by (intro of_nat_neq_0, simp_all)

lemma key_index_inj[simp]: "(\<lfloor>i\<^sub>1\<rfloor> :: key) = \<lfloor>i\<^sub>2\<rfloor> \<Longrightarrow> i\<^sub>1 = i\<^sub>2" for i :: key_index
  unfolding key_index_rep_def using key_index_rep'[of i\<^sub>1] key_index_rep'[of i\<^sub>2]
  by (simp add:key_index_rep'_inject of_nat_inj)

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

lemma addr_inj[simp]: "\<lfloor>a\<^sub>1\<rfloor> = \<lfloor>a\<^sub>2\<rfloor> \<Longrightarrow> a\<^sub>1 = a\<^sub>2" for a\<^sub>1 a\<^sub>2 :: address
  unfolding addr_rep_def
  by (split address.splits) (force split:address.splits)+

lemmas addr_invertible[intro] = invertible.intro[OF injI, OF addr_inj]

interpretation addr_inv: invertible addr_rep ..

adhoc_overloading abs addr_inv.inv

abbreviation "prefix_bound \<equiv> rpad (size kern_prefix) (ucast kern_prefix :: word32)"

lemma prefix_bound: "unat prefix_bound < 2 ^ LENGTH(word32)" unfolding rpad_def by simp

lemma prefix_bound'[simplified, simp]: "x \<le> unat prefix_bound \<Longrightarrow> x < 2 ^ LENGTH(word32)"
  using prefix_bound by simp

lemma addr_prefix[simp, intro]: "limited_and prefix_bound \<lfloor>a\<rfloor>" for a :: address
  unfolding limited_and_def addr_rep_def
  by (subst word_bw_comms) (auto split:address.split simp del:ucast_bintr)

subsection \<open>Capability formats\<close>

text \<open>
  We define capability format generally as a @{text locale}. It has two parameters: first one is a
  @{text "subset"} function (denoted as @{text "\<subseteq>\<^sub>c"}), and second one is a @{text "set_of"} function, which maps
  a capability to its high-level representation that is expressed as a set.
  We have an assumption that  @{text "Capability A"} is a subset of @{text "Capability B"} if and
  only if their high-level representations are also subsets of each other.
  We call it the well-definedness assumption (denoted as wd) and using it we can prove abstractly
  that such generic capability format satisfies the properties of reflexivity and transitivity.

  Then sing this locale we can prove that capability formats of all available system calls
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

lemma prefix_size_inj[simp]: "(\<lfloor>s\<^sub>1\<rfloor> :: byte) = \<lfloor>s\<^sub>2\<rfloor> \<Longrightarrow> s\<^sub>1 = s\<^sub>2" for s\<^sub>1 s\<^sub>2 :: prefix_size
  unfolding prefix_size_rep_def using prefix_size_rep'[of s\<^sub>1] prefix_size_rep'[of s\<^sub>2]
  by (simp add:prefix_size_rep'_inject of_nat_inj)

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

lemma pref_cap_rep_inj_helper_inj[simp]: "\<lfloor>s\<^sub>1\<rfloor> \<^sub>1\<diamond> k\<^sub>1 = \<lfloor>s\<^sub>2\<rfloor> \<^sub>1\<diamond> k\<^sub>2 \<Longrightarrow> s\<^sub>1 = s\<^sub>2 \<and> k\<^sub>1 = k\<^sub>2"
  for s\<^sub>1 s\<^sub>2 :: prefix_size and k\<^sub>1 k\<^sub>2 :: key
  by auto

lemma pref_cap_rep_inj_helper_zero[simplified, simp]:
  "n \<in> {LENGTH(key)..<LENGTH(word32) - LENGTH(byte)} \<Longrightarrow> \<not> (\<lfloor>s\<rfloor> \<^sub>1\<diamond> k) !! n"
  for s :: prefix_size and k :: key
  by simp

lemma pref_cap_rep_inj[simp]: "\<lfloor>c\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>c\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> c\<^sub>1 = c\<^sub>2" for c\<^sub>1 c\<^sub>2 :: prefixed_capability
  unfolding pref_cap_rep_def
  by (auto split:prod.splits)

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

lemma write_cap_inj[simp]: "(\<lfloor>w\<^sub>1\<rfloor> :: word32 \<times> word32) = \<lfloor>w\<^sub>2\<rfloor> \<Longrightarrow> w\<^sub>1 = w\<^sub>2"
  for w\<^sub>1 w\<^sub>2 :: write_capability
  unfolding write_cap_rep_def
  by (auto
      split:prod.splits iff:write_cap_rep'_inject[symmetric]
      intro!:word_of_nat_inj simp add:rpad_def)

lemmas write_cap_invertible[intro] = invertible.intro[OF injI, OF write_cap_inj]

interpretation write_cap_inv: invertible write_cap_rep ..

adhoc_overloading abs write_cap_inv.inv

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

lemma write_cap_safe[simp]: "a \<in> \<lceil>w\<rceil> \<Longrightarrow> a \<noteq> \<lfloor>a'\<rfloor>" for w :: write_capability and a' :: address
  by auto

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

lemma log_cap_rep_inj[simp]: "(\<lfloor>l\<^sub>1\<rfloor> :: word32 list) = \<lfloor>l\<^sub>2\<rfloor> \<Longrightarrow> l\<^sub>1 = l\<^sub>2" for l\<^sub>1 l\<^sub>2 :: log_capability
  unfolding log_cap_rep_def using log_cap_rep'_inject by auto

lemmas log_cap_rep_invertible[intro] = invertible.intro[OF injI, OF log_cap_rep_inj]

interpretation log_cap_inv: invertible log_cap_rep ..

adhoc_overloading abs log_cap_inv.inv

lemma log_cap_rep_length[simp]: "length \<lfloor>l\<rfloor> = length (log_cap_rep' l) + 1"
  unfolding log_cap_rep_def by simp

subsubsection \<open>External call capability\<close>

text \<open>
  We model the external call capability format using a record with two fields: @{text "allow_addr"}
  and @{text "may_send"}, with the following semantic:
  \begin{itemize}
    \item if the field  @{text "allow_addr"} has value, then only the Ethereum  address specified
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
  High-level representation of a external call capability is a set of all possible pairs of account
  addresses and Ether amount that can be sent using this capability.
\<close>

definition "set_of_ext_cap e \<equiv>
  {(a, v) . case_option True ((=) a) (allow_addr e) \<and> (\<not> may_send e \<longrightarrow> v = (0 :: word32)) }"

adhoc_overloading abs set_of_ext_cap

text \<open>
  An external call capability A is a subset of an external call capability B if and only if:
  \begin{itemize}
    \item if A allows to call any Ethereum address, then B also must allow to call any address;
    \item if A allows to call only specified Ethereum address, then B either must allow to call any
          address, or it must allow to only call the same address as A;
    \item if A may send Ether, then B also must be able to send Ether.
  \end{itemize}
\<close>

abbreviation "allow_any e \<equiv> Option.is_none (allow_addr e)"

abbreviation "the_addr e \<equiv> the (allow_addr e)"

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

lemma ext_cap_rep_inj[simp]: "\<lfloor>e\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>e\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> e\<^sub>1 = e\<^sub>2" for e\<^sub>1 e\<^sub>2 :: external_call_capability
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

lemmas ext_cap_invertible[intro] = invertible2.intro[OF inj2I, OF ext_cap_rep_inj]

interpretation ext_cap_inv: invertible2 ext_cap_rep ..

adhoc_overloading abs ext_cap_inv.inv2

section \<open>Kernel state\<close>

subsection \<open>Procedure data\<close>

typedef 'a capability_list = "{l :: 'a list. length l < 2 ^ LENGTH(byte) - 1}"
  morphisms cap_list_rep cap_list
  by (intro exI[of _ "[]"], simp)

adhoc_overloading rep cap_list_rep

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
      using capability_list.cap_list_rep[of "call_caps p\<^sub>1"] by simp
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
      using capability_list.cap_list_rep[of "del_caps p\<^sub>1"] by simp
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

text \<open>Maximum number of procedures registered in the kernel:\<close>
abbreviation "max_nprocs \<equiv> 2 ^ LENGTH(key) - 1 :: nat"

typedef procedure_list = "{l :: (key, procedure) alist. size l \<le> max_nprocs}"
  morphisms proc_list_rep proc_list
  by (intro exI[of _ "Alist []"], simp)

adhoc_overloading rep proc_list_rep

adhoc_overloading rep DAList.impl_of

record kernel =
  curr_proc  :: ethereum_address
  entry_proc :: ethereum_address
  proc_list  :: procedure_list

text \<open>
  Here we introduce some useful abbreviations that will simplify the expression of the kernel
  state properties.
\<close>

text \<open>Number of the procedures:\<close>
abbreviation "nprocs \<sigma> \<equiv> size \<lfloor>proc_list \<sigma>\<rfloor>"

text \<open>Set of procedure indexes:\<close>
definition "proc_ids \<sigma> \<equiv> {0..<nprocs \<sigma>}"

abbreviation "procs \<sigma> \<equiv> DAList.lookup \<lfloor>proc_list \<sigma>\<rfloor>"

definition "has_key k \<sigma> \<equiv> k \<in> dom (procs \<sigma>)"

text \<open>Procedure by its key:\<close>

definition "proc \<sigma> k \<equiv> the (procs \<sigma> k)"

abbreviation "proc_key \<sigma> i \<equiv> fst (\<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! i)"

text \<open>Index of procedure:\<close>

definition "proc_id \<sigma> k \<equiv> \<lceil>length (takeWhile ((\<noteq>) k \<circ> fst) \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor>)\<rceil> :: key_index"

lemma proc_id_alt[simp]:
  "has_key k \<sigma> \<Longrightarrow> \<lfloor>proc_id \<sigma> k\<rfloor> \<in> proc_ids \<sigma>"
  "has_key k \<sigma> \<Longrightarrow> \<lfloor>\<lfloor>proc_list \<sigma>\<rfloor>\<rfloor> ! \<lfloor>proc_id \<sigma> k\<rfloor> = (k, proc \<sigma> k)"
proof-
  assume "has_key k \<sigma>"
  hence 0:"(k, proc \<sigma> k) \<in> set \<lfloor>\<lfloor>kernel.proc_list \<sigma>\<rfloor>\<rfloor>"
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

definition "kernel_rep (\<sigma> :: kernel) r a \<equiv>
  case \<lceil>a\<rceil> of
    None              \<Rightarrow> r a
  | Some addr         \<Rightarrow> (case addr of
      Nprocs          \<Rightarrow> ucast (of_nat (nprocs \<sigma>) :: key) OR r a \<restriction> {LENGTH(key) ..<LENGTH(word32)}
    | Proc_key i      \<Rightarrow> ucast (proc_key \<sigma> \<lfloor>i\<rfloor>) OR r a \<restriction> {LENGTH(key) ..<LENGTH(word32)}
    | Kernel          \<Rightarrow> 0
    | Curr_proc       \<Rightarrow> ucast (curr_proc \<sigma>) OR r a \<restriction> {LENGTH(ethereum_address) ..<LENGTH(word32)}
    | Entry_proc      \<Rightarrow> ucast (entry_proc \<sigma>) OR r a \<restriction> {LENGTH(ethereum_address) ..<LENGTH(word32)}
    | Heap_proc k off \<Rightarrow> if has_key k \<sigma>
                         then proc_rep k (proc_id \<sigma> k) (proc \<sigma> k) r off
                         else r a)"

adhoc_overloading rep kernel_rep

lemma proc_list_eqI[intro]:
  assumes "nprocs \<sigma>\<^sub>1 = nprocs \<sigma>\<^sub>2"
      and "\<And> i. i < nprocs \<sigma>\<^sub>1 \<Longrightarrow> proc_key \<sigma>\<^sub>1 i = proc_key \<sigma>\<^sub>2 i"
      and "\<And> k. \<lbrakk>has_key k \<sigma>\<^sub>1; has_key k \<sigma>\<^sub>2\<rbrakk> \<Longrightarrow> proc \<sigma>\<^sub>1 k = proc \<sigma>\<^sub>2 k"
    shows "proc_list \<sigma>\<^sub>1 = proc_list \<sigma>\<^sub>2"
  unfolding has_key_def DAList.lookup_def proc_def
proof-
  from assms have "\<forall> i < nprocs \<sigma>\<^sub>1.
                    snd (\<lfloor>\<lfloor>kernel.proc_list \<sigma>\<^sub>1\<rfloor>\<rfloor> ! i) = snd (\<lfloor>\<lfloor>kernel.proc_list \<sigma>\<^sub>2\<rfloor>\<rfloor> ! i)"
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

lemma kernel_rep_inj[simp]: "\<lfloor>\<sigma>\<^sub>1\<rfloor> r\<^sub>1 = \<lfloor>\<sigma>\<^sub>2\<rfloor> r\<^sub>2 \<Longrightarrow> \<sigma>\<^sub>1 = \<sigma>\<^sub>2" for \<sigma>\<^sub>1 \<sigma>\<^sub>2 :: kernel
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

lemmas kernel_invertible[intro] = invertible2.intro[OF inj2I, OF kernel_rep_inj]

interpretation kernel_inv: invertible2 kernel_rep ..

adhoc_overloading abs kernel_inv.inv2

lemma kernel_update_neq[simp]: "\<not> limited_and prefix_bound a \<Longrightarrow> \<lfloor>\<sigma>\<rfloor> r a = r a"
proof-
  assume "\<not> limited_and prefix_bound a"
  hence "(\<lceil>a\<rceil> :: address option) = None"
    using addr_prefix by - (rule ccontr, auto dest:addr_inv.inv_inj')
  thus ?thesis unfolding kernel_rep_def by auto
qed

section \<open>Call formats\<close>

primrec split :: "'a::len word list \<Rightarrow> 'b::len word list list" where
  "split []       = []" |
  "split (x # xs) = word_rsplit x # split xs"

lemma cat_split[simp]: "map word_rcat (split x) = x"
  unfolding split_def
  by (induct x, simp_all add:word_rcat_rsplit)

lemma split_inj[simp]: "split x = split y \<Longrightarrow> x = y"
  by (frule arg_cong[where f="map word_rcat"]) (subst (asm) cat_split)+

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
  fixes rep :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::zero list" ("\<lfloor>_\<rfloor>")
  assumes inj:"inj2_tf rep"
      and len_inv:"\<And> x y y'. length (rep x y) = length (rep x y')"
begin
definition inv2_tf :: "'c list \<Rightarrow> 'a option" where "inv2_tf \<equiv> maybe_inv2_tf 0 rep"

lemmas inv2_tf_inj[folded inv2_tf_def, simp] = maybe_inv2_tf_inj[where z=0, OF inj len_inv]

lemmas inv2_tf_inj'[folded inv2_tf_def, simp] = maybe_inv2_tf_inj'[where z=0, OF inj len_inv]
end

subsection \<open>Register system call\<close>

definition "wf_cap c l \<equiv>
  case (c, l) of
    (Call,  [c])      \<Rightarrow> (\<lceil>c\<rceil> :: prefixed_capability option) \<noteq> None
  | (Reg,   [c])      \<Rightarrow> (\<lceil>c\<rceil> :: prefixed_capability option) \<noteq> None
  | (Del,   [c])      \<Rightarrow> (\<lceil>c\<rceil> :: prefixed_capability option) \<noteq> None
  | (Entry, [])       \<Rightarrow> True
  | (Write, [c1, c2]) \<Rightarrow> (\<lceil>(c1, c2)\<rceil> :: write_capability option) \<noteq> None
  | (Log,   c)        \<Rightarrow> (\<lceil>c\<rceil> :: log_capability option) \<noteq> None
  | (Send,  [c])      \<Rightarrow> (\<lceil>c\<rceil> :: external_call_capability option) \<noteq> None
  | _                 \<Rightarrow> False"

definition "overwrite_cap c l r \<equiv>
  case (c, l) of
    (Call,  [c])        \<Rightarrow> [\<lfloor>the \<lceil>c\<rceil> :: prefixed_capability\<rfloor> (r ! 0)]
  | (Reg,   [c])        \<Rightarrow> [\<lfloor>the \<lceil>c\<rceil> :: prefixed_capability\<rfloor> (r ! 0)]
  | (Del,   [c])        \<Rightarrow> [\<lfloor>the \<lceil>c\<rceil> :: prefixed_capability\<rfloor> (r ! 0)]
  | (Entry, [])         \<Rightarrow> []
  | (Write, [c1, c2])   \<Rightarrow> let (c1, c2) = \<lfloor>the \<lceil>(c1, c2)\<rceil> :: write_capability\<rfloor> in [c1, c2]
                           \<comment> \<open>for mere consistency, no actual need in this,
                               can be just [c1, c2]\<close>
  | (Log,   c)          \<Rightarrow> \<lfloor>the \<lceil>c\<rceil> :: log_capability\<rfloor>
  | (Send,  [c])        \<Rightarrow> [\<lfloor>the \<lceil>c\<rceil> :: external_call_capability\<rfloor> (r ! 0)]"

typedef capability_data =
  "{ l :: ((capability \<times> capability_index) \<times> word32 list) list.
       \<forall> ((c, _), l) \<in> set l. wf_cap c l }"
  morphisms cap_data_rep cap_data
  by (intro exI[of _ "[]"], simp)

adhoc_overloading rep cap_data_rep

record reg_call =
  proc_key :: key
  eth_addr :: ethereum_address
  cap_data :: capability_data

no_adhoc_overloading rep cap_index_rep

no_adhoc_overloading abs cap_index_inv.inv

definition "cap_index_rep0 i \<equiv> of_nat \<lfloor>i\<rfloor> :: byte" for i :: capability_index

adhoc_overloading rep cap_index_rep0

lemma width_cap_index0: "width \<lfloor>i\<rfloor> \<le> LENGTH(byte)" for i :: capability_index by simp

lemma width_cap_index0'[simp]: "LENGTH(byte) \<le> n \<Longrightarrow> width \<lfloor>i\<rfloor> \<le> n"
  for i :: capability_index by simp

lemma cap_index_inj0[simp]: "(\<lfloor>i\<^sub>1\<rfloor> :: byte) = \<lfloor>i\<^sub>2\<rfloor> \<Longrightarrow> i\<^sub>1 = i\<^sub>2" for i\<^sub>1 i\<^sub>2 :: capability_index
  unfolding cap_index_rep0_def
  using cap_index_rep'[of i\<^sub>1] cap_index_rep'[of i\<^sub>2] word_of_nat_inj[of "\<lfloor>i\<^sub>1\<rfloor>" "\<lfloor>i\<^sub>2\<rfloor>"]
        cap_index_rep'_inject
  by force

lemmas cap_index0_invertible[intro] = invertible.intro[OF injI, OF cap_index_inj0]

interpretation cap_index_inv0: invertible cap_index_rep0 ..

adhoc_overloading abs cap_index_inv0.inv

definition "reg_call_rep d r \<equiv>
    [ucast (proc_key d) OR (r ! 0) \<restriction> {LENGTH(key) ..<LENGTH(word32)},
     ucast (eth_addr d) OR (r ! 1) \<restriction> {LENGTH(key) ..<LENGTH(word32)}] @
     snd
      (fold
        (\<lambda> ((c, i), l) (j, d).
          (j + 3 + length l,
           d @
           [ucast (of_nat (3 + length l) :: byte) OR (r ! j) \<restriction> {LENGTH(byte) ..<LENGTH(word32)},
            ucast \<lfloor>c\<rfloor> OR (r ! (j + 1)) \<restriction> {LENGTH(byte) ..<LENGTH(word32)},
            ucast \<lfloor>i\<rfloor> OR (r ! (j + 2)) \<restriction> {LENGTH(byte) ..<LENGTH(word32)}]
           @ overwrite_cap c l (drop (j + 3) r)))
        \<lfloor>cap_data d\<rfloor>
        (2, []))"

datatype result =
    Success storage
  | Revert

abbreviation "SYSCALL_NOEXIST \<equiv> 0xaa"

abbreviation "SYSCALL_BADCAP \<equiv> 0x33"

definition "cap_type_opt_rep c \<equiv> case c of Some c \<Rightarrow> \<lfloor>c\<rfloor> | None \<Rightarrow> 0x00"
  for c :: "capability option"

adhoc_overloading rep cap_type_opt_rep

lemma cap_type_opt_rep_inj[intro]: "inj cap_type_opt_rep" unfolding cap_type_opt_rep_def inj_def
  by (auto split:option.split)

lemmas cap_type_opt_invertible[intro] = invertible.intro[OF cap_type_opt_rep_inj]

interpretation cap_type_opt_inv: invertible cap_type_opt_rep ..

adhoc_overloading abs cap_type_opt_inv.inv

definition call :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "call _ _ s \<equiv> (Success s, [])"

definition register :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "register _ _ s \<equiv> (Success s, [])"

definition delete :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "delete _ _ s \<equiv> (Success s, [])"

definition set_entry :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "set_entry _ _ s \<equiv> (Success s, [])"

definition write_addr :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "write_addr _ _ s \<equiv> (Success s, [])"

definition log :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "log _ _ s \<equiv> (Success s, [])"

definition external :: "capability_index \<Rightarrow> byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "external _ _ s \<equiv> (Success s, [])"

definition execute :: "byte list \<Rightarrow> storage \<Rightarrow> result \<times> byte list" where
  "execute c s \<equiv> case takefill 0x00 2 c of ct # ci # c \<Rightarrow>
    (case \<lceil>ct\<rceil> of
      None           \<Rightarrow> (Revert, [SYSCALL_NOEXIST])
    | Some None      \<Rightarrow> (Success s, [])
    | Some (Some ct) \<Rightarrow> (case \<lceil>ci\<rceil> of
       None          \<Rightarrow> (Revert, [SYSCALL_BADCAP]) \<comment> \<open>Capability index out of bounds\<close>
     | Some ci       \<Rightarrow> (case ct of
         Call        \<Rightarrow> call ci c s
       | Reg         \<Rightarrow> register ci c s
       | Del         \<Rightarrow> delete ci c s
       | Entry       \<Rightarrow> set_entry ci c s
       | Write       \<Rightarrow> write_addr ci c s
       | Log         \<Rightarrow> log ci c s
       | Send        \<Rightarrow> external ci c s)))"

(*
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
qed*)
end
