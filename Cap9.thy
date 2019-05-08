section \<open>Preliminaries\<close>

theory Cap9
imports
  "HOL-Word.Word"
begin

text \<open>We start with some types and definitions that will be used later.\<close>

subsection \<open>Procedure keys\<close>

text \<open>
  Procedure keys are represented as 24-byte (192 bits) machine words.
  Keys will be used both in the abstract and concrete state.
\<close>

type_synonym word24 = "192 word"
type_synonym key = word24

text \<open>
  We make some assumptions about the set of all procedures that can be registered in the system:
  \begin{enumerate}
  \item there is a hash function that maps the set of all procedures to the set of all keys;
  \item this function is injective on the set;
  \item number of all procedures is smaller or equal to the number of all keys.
  \end{enumerate}
  We accomplish it by using Isar type classes:
\<close>

class proc_class =
  fixes key :: "'a \<Rightarrow> key"
  assumes "CARD ('a) \<le> CARD (key)"
  assumes "inj key"

text \<open>
  To insure we don't introduce contradictions with these assumptions we build a sample model
  of the set of all procedures. To do this we proceed with some additional definitions.
\<close>

text \<open>Byte is 8-bit machine word:\<close>
type_synonym byte = "8 word"

subsection \<open>Hash function\<close>

text \<open>
  This is a hash function that takes an arbitrary list of bytes and returns its 24-byte hash.
  It is used to obtain procedure keys.
\<close>

fun hash_rec :: "nat \<Rightarrow> byte list \<Rightarrow> key" where
  "hash_rec n []             = 0" |
  "hash_rec 0 [e]            = ucast e << 191" |
  "hash_rec (Suc n) [e]      = ucast e << n" |
  "hash_rec 0 (e # es)       = (ucast e << 191) XOR hash_rec 191 es" |
  "hash_rec (Suc n) (e # es) = (ucast e << n) XOR hash_rec n es"

definition "some_hash \<equiv> hash_rec 0"

text \<open>
  This is an auxiliary function that takes some hash as an input and if there is some byte list
  (called "element"), whose hash matches the input, then the function will return it.
  Otherwise, the function returns an empty set:
\<close>

definition "choose_proc k \<equiv>
  if k = 0                     then {[]}
  else if \<exists> p. some_hash p = k then {SOME p. some_hash p = k}
  else                              {}"

lemma choose_proc[simp]: "x \<in> choose_proc k \<Longrightarrow> some_hash x = k"
  unfolding choose_proc_def
  by (auto simp add: some_hash_def split: if_splits intro: someI)

text \<open>Each key has only one corresponding procedure:\<close>

lemma[simp]: "\<lbrakk>x \<in> choose_proc k; y \<in> choose_proc k\<rbrakk> \<Longrightarrow> x = y"
  unfolding choose_proc_def
  by (simp split: if_splits)

subsection \<open>Procedures\<close>

text \<open>@{text Procs} is a set of all possible procedures, hash of which will be a
      valid procedure key:\<close>
definition "Procs \<equiv> \<Union>k. choose_proc k"

text \<open>
  Here we introduce a new type called @{text proc} which will be used to represent procedures in the
  abstract state. Type @{text proc} is identified with the @{const Procs} set:
\<close>

typedef proc = Procs
  unfolding Procs_def choose_proc_def
  by (rule exI[of _ "[]"], auto)

subsubsection \<open>Injectivity of the hash function\<close>

text \<open>Hash function is injective on the domain of all procedures:\<close>

lemma some_hash_inj: "inj_on some_hash Procs"
  unfolding inj_on_def Procs_def
  by auto

subsubsection \<open>Number of all procedures\<close>

text \<open>Here we introduce maximum number of procedure keys:\<close>

abbreviation "max_nkeys \<equiv>  2 ^ 192 :: nat"

text \<open>Number of all procedures must be equal or smaller then the maximum number of procedure keys:\<close>

lemma card_procs: "card Procs \<le> max_nkeys"
  unfolding Procs_def
proof (subst card_UN_disjoint)
  show  "finite (UNIV :: key set)"
    and "\<forall>i\<in>UNIV. finite (choose_proc i)"
    unfolding choose_proc_def some_hash_def
    by (simp_all split: if_splits)
  show "\<forall>i\<in>UNIV. \<forall>j\<in>UNIV. i \<noteq> j \<longrightarrow> choose_proc i \<inter> choose_proc j = {}"
    by (auto, ((drule choose_proc)+, simp))
  show "(\<Sum>i\<in>UNIV. card (choose_proc i)) \<le> max_nkeys"
    using sum_bounded_above[of "UNIV :: key set" "\<lambda> i. card (choose_proc i)", where K = 1]
    unfolding choose_proc_def card_word
    by auto
qed

subsection \<open>Sample set of procedures\<close>

text \<open>
  Here we show that there is a sample set of all procedures that satisfies all assumptions:
\<close>

instantiation proc :: proc_class
begin
definition "key \<equiv> some_hash \<circ> Rep_proc"

instance proof
  show "CARD(proc) \<le> CARD(key)"
    using card_procs
          card_word[where 'a = 192]
          type_definition.card[OF proc.type_definition_proc]
    by auto
  show "inj (key :: proc \<Rightarrow> _)"
    using some_hash_inj proc.Rep_proc proc.Rep_proc_inject
    unfolding inj_def key_proc_def inj_on_def
    by force
qed
end

section \<open>Abstract state\<close>

text \<open>
  Abstract state is implemented as a record with a single component labeled "procs".
  This component is a mapping from the set of procedure keys to the
  direct product of procedure indexes and procedure data.
\<close>

record ('p :: proc_class) abs =
  procs    :: "key \<rightharpoonup> nat \<times> 'p"

subsection \<open>Abbreviations\<close>

text \<open>
  Here we introduce some useful abbreviations that will simplify the expression of the abstract
  state properties.
\<close>

text \<open>Number of the procedures in the abstract state:\<close>
abbreviation "nprocs \<S> \<equiv> card (dom (procs \<S>))"

text \<open>List of procedures keys:\<close>
abbreviation "proc_keys \<S> \<equiv> dom (procs \<S>)"

text \<open>Pair with the procedure index and procedure itself for a given key:\<close>
abbreviation "proc \<S> k \<equiv> the (procs \<S> k)"

text \<open>Procedure index for a given key:\<close>
abbreviation "proc_id \<S> k \<equiv> fst (proc \<S> k)"

text \<open>Procedure itself for a given key:\<close>
abbreviation "proc_bdy \<S> k \<equiv> snd (proc \<S> k)"

text \<open>Maximum number of procedures in the abstract state:\<close>
abbreviation "max_nprocs_nat \<equiv> 2 ^ 24 - 1 :: nat"

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

definition "procs_rng_wf \<S> \<equiv>
  (\<forall> k \<in> proc_keys \<S>. proc_id \<S> k \<in> {1 .. nprocs \<S>} \<and> key (proc_bdy \<S> k) = k) \<and>
   nprocs \<S> \<le> max_nprocs_nat"

text \<open>Procedure indexes must be injective:\<close>
definition "procs_map_wf \<S> \<equiv> inj_on (proc_id \<S>) (proc_keys \<S>)"

text \<open>Abstract state is well-formed if the previous two properties are satisfied:\<close>

definition abs_wf :: "'p :: proc_class abs \<Rightarrow> bool" ("\<turnstile>_" [60]) where
  "\<turnstile>\<S> \<equiv>
     procs_rng_wf \<S>
   \<and> procs_map_wf \<S>"

lemmas procs_rng_wf = abs_wf_def procs_rng_wf_def

lemmas procs_map_wf = abs_wf_def procs_map_wf_def

section \<open>Storage state\<close>

text \<open>32-byte machine words that are used to model keys and values of the storage:\<close>

type_synonym word32 = "256 word" (* 32 bytes *)

text \<open>
  Storage is a function that takes a 32-byte word (key) and returns another
  32-byte word (value):
\<close>
type_synonym storage = "word32 \<Rightarrow> word32"

text \<open>Storage key that corresponds to the number of procedures in the list:\<close>
abbreviation "nprocs_key \<equiv> 0xffffffff01 << (27 * 8) :: word32"

text \<open>Storage key that corresponds to the procedure key with index i:\<close>
abbreviation "key_addr_of_id i \<equiv> nprocs_key OR of_nat i"

text \<open>Procedure index that corresponds to some procedure key address:\<close>
abbreviation "id_of_key_addr a \<equiv> unat (nprocs_key XOR a)"

text \<open>Maximum number of procedures in the kernel, but in the form of a 32-byte machine word:\<close>
abbreviation "max_nprocs_word \<equiv> 2 ^ 24 - 1 :: word32"

text \<open>Declare some lemmas as simplification rules:\<close>
declare unat_word_ariths[simp] word_size[simp]

subsection \<open>Lemmas\<close>

subsubsection \<open>Auxiliary lemmas about procedure key addresses\<close>

text \<open>Valid procedure id has all zeros in its higher bits.\<close>
lemma proc_id_high_zeros[simp]:
  "n \<le> max_nprocs_word \<Longrightarrow> \<forall>i\<in>{24..<256}. \<not> n !! i" (is "?nbound \<Longrightarrow> \<forall>_ \<in> ?high. _")
proof
  fix i
  assume 0:"i \<in> ?high"
  from 0 have "2 ^ 24 \<le> (2 :: nat) ^ i" by (simp add: numerals(2))
  moreover from 0 have "0 < (2 :: word32) ^ i"  by (subst word_2p_lem; simp)
  ultimately have "2 ^ 24 \<le> (2 :: word32) ^ i"
    unfolding word_le_def
    by (subst (asm) of_nat_le_iff[symmetric], simp add:uint_2p)
  thus "?nbound \<Longrightarrow> \<not> n !! i"
    unfolding not_def
    by (intro impI) (frule bang_is_le, unat_arith)
qed

text \<open>Address of the \# of procedures has all zeros in its lower bits.\<close>
lemma nprocs_key_low_zeros[simp]: "\<forall>i\<in>{0..< 24}. \<not> nprocs_key !! i"
  by (subst nth_shiftl, auto)

text \<open>
  Elimination (generalized split) rule for 32-byte words:
  a property holds on all bits if and only if it holds on the higher and lower bits.\<close>
lemma low_high_split:
   "(\<forall>n. P ((x :: word32) !! n)) =
    ((\<forall>n\<in>{0..<24}. P (x !! n)) \<and> (\<forall>n\<in> {24..<256}. P (x !! n)) \<and> P False)"
  (is "?left = ?right")
proof (intro iffI)
  have "\<not> x !! size x" using test_bit_size[of x "size x"] by blast
  hence "?left \<Longrightarrow> P False" by (metis (full_types))
  thus "?left \<Longrightarrow> ?right" by auto

  show "?right \<Longrightarrow> ?left" using test_bit_size[of x] by force
qed

text \<open>Computing procedure key address by its id is an invertible operation.\<close>
lemma id_of_key_addr_inv[simp]:
   "i \<le> max_nprocs_nat \<Longrightarrow> id_of_key_addr (key_addr_of_id i) = i" (is "?ibound \<Longrightarrow> ?rev")
proof-
  assume 0:"?ibound"
  hence 1:"unat (of_nat i :: word32) = i"
    by (simp add: le_unat_uoi[where z=max_nprocs_word])
  hence "of_nat i \<le> max_nprocs_word"
    using 0
    by (simp add: word_le_nat_alt)
  hence "nprocs_key XOR nprocs_key OR (of_nat i) = of_nat i"
    using nprocs_key_low_zeros proc_id_high_zeros
    by (auto simp add: word_eq_iff word_ops_nth_size)
  thus "?rev"
    using 1
    by simp
qed

section \<open>Correspondence between abstract and storage states\<close>

text \<open>Number of procedures is stored by the corresponding address (@{const nprocs_key}).\<close>
definition "models_nprocs S \<S> \<equiv> unat (S nprocs_key) = nprocs \<S>"

text \<open>Each procedure key @{text k} is stored by the corresponding address
      (@{term "key_addr_of_id k"}).\<close>
definition "models_proc_keys S \<S> \<equiv>
  \<forall> k \<in> proc_keys \<S>. S (key_addr_of_id (proc_id \<S> k)) = ucast k"

text \<open>A storage corresponds to the abstract state
     if and only if the above properties are satisfied.\<close>
definition models :: "storage \<Rightarrow> ('p :: proc_class) abs \<Rightarrow> bool" ("_ \<tturnstile> _" [65]) where
  "S \<tturnstile> \<S> \<equiv>
    models_nprocs S \<S>
  \<and> models_proc_keys S \<S>"

lemmas models_nprocs = models_def models_nprocs_def

lemmas models_proc_keys = models_def models_proc_keys_def

text \<open>In the following we aim to proof the existence of a storage corresponding to any
      well-formed abstract state (so that any well-formed abstract state can be encoded
      and stored). Later we still need to prove that the encoding is unambiguous.
\<close>

subsection \<open>Auxiliary definitions and lemmas\<close>

text \<open>An empty storage.\<close>
definition "zero_con (_ :: word32) \<equiv> 0 :: word32"

text \<open>The set of all procedure key addresses.\<close>
definition "proc_key_addrs \<S> \<equiv> { key_addr_of_id (proc_id \<S> k) | k. k \<in> proc_keys \<S> }"

text \<open>Procedure id can be converted to a 32-byte word without overflow.\<close>
lemma proc_id_inv[simp]:
  "\<lbrakk>\<turnstile> \<S>; k \<in> proc_keys \<S>\<rbrakk> \<Longrightarrow> unat (of_nat (proc_id \<S> k) :: word32) = proc_id \<S> k"
  unfolding procs_rng_wf
  by (force intro:le_unat_uoi[where z=max_nprocs_word])

text \<open>Moreover, any procedure id is non-zero and bounded by the maximum available id
      (@{const max_nprocs_word}).\<close>
lemma proc_id_bounded[intro]:
  "\<lbrakk>\<turnstile> \<S>; k \<in> proc_keys \<S>\<rbrakk> \<Longrightarrow>
    (0 :: word32) < of_nat (proc_id \<S> k) \<and> of_nat (proc_id \<S> k) \<le> max_nprocs_word"
  by (simp add:word_le_nat_alt word_less_nat_alt, force simp add:procs_rng_wf)

text \<open>Since it's non-zero, any procedure id has a non-zero bit in its lower part.\<close>
lemma proc_id_low_one:
  "0 < n \<and> n \<le> max_nprocs_word \<Longrightarrow> \<exists>i\<in>{0..<24}. n !! i" (is "?nbound \<Longrightarrow> _")
proof-
  assume 0:"?nbound"
  hence "\<not> ?thesis \<Longrightarrow> n = 0" by (auto simp add:inc_le intro!:word_eqI)
  moreover from 0 have "n \<noteq> 0" by auto
  ultimately show ?thesis by auto
qed

text \<open>And procedure key address is different from the address of the \# of procedures
      (@{const nprocs_key}).\<close>
lemma proc_key_addr_neq_nprocs_key:
  "0 < n \<and> n \<le> max_nprocs_word \<Longrightarrow> nprocs_key OR n \<noteq> nprocs_key" (is "?nbound \<Longrightarrow> _")
proof-
  assume 0:"?nbound"
  hence "\<exists> i\<in>{0..<24}.(nprocs_key !! i \<or> n  !! i) \<noteq> nprocs_key !! i"
    using nprocs_key_low_zeros proc_id_low_one
    by fast
  thus ?thesis by (force simp add:word_eq_iff word_ao_nth)
qed

text \<open>Thus @{const nprocs_key} doesn't belong to the set of procedure key addresses.\<close>
lemma nprocs_key_notin_proc_key_addrs: "\<turnstile> \<S> \<Longrightarrow> nprocs_key \<notin> proc_key_addrs \<S>"
  using proc_id_bounded proc_key_addr_neq_nprocs_key
  unfolding proc_key_addrs_def
  by auto

text \<open>The function mapping procedure id to the corresponding procedure key
      (in some abstract state):\<close>
definition "proc_key_of_id \<S> \<equiv> the_inv_into (proc_keys \<S>) (proc_id \<S>)"

text \<open>Invertibility of computing procedure id (by its key) in any abstract state:\<close>
lemma proc_key_of_id_inv[simp]: "\<lbrakk>\<turnstile>\<S>; k \<in> proc_keys \<S>\<rbrakk> \<Longrightarrow> proc_key_of_id \<S> (proc_id \<S> k) = k"
  unfolding procs_map_wf proc_key_of_id_def
  using the_inv_into_f_f by fastforce

text \<open>For any valid procedure id in any well-formed abstract state there is a procedure key that
     corresponds to the id (this is not so trivial as we keep the reverse mapping in
     the abstract state, the proof is implicitly based on the pigeonhole principle).\<close>
lemma proc_key_exists: "\<lbrakk>\<turnstile>\<S>; i\<in>{1..nprocs \<S>}\<rbrakk> \<Longrightarrow> \<exists>k\<in>proc_keys \<S>. proc_id \<S> k = i"
proof (rule ccontr, subst (asm) bex_simps(8))
  let ?rng = "{1 .. nprocs \<S>}"
  let ?prj = "proc_id \<S> ` proc_keys \<S>"
  assume "\<forall>k\<in>proc_keys \<S>. proc_id \<S> k \<noteq> i"
  hence 0:"i \<notin> ?prj"
    by auto
  assume "\<turnstile> \<S>"
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

text \<open>The function @{const proc_key_of_id} gives valid procedure ids.\<close>
lemma proc_key_of_id_in_keys: "\<lbrakk>\<turnstile>\<S>; i\<in>{1..nprocs \<S>}\<rbrakk> \<Longrightarrow> proc_key_of_id \<S> i \<in> proc_keys \<S>"
  using proc_key_exists the_inv_into_into[of "proc_id \<S>" "proc_keys \<S>" i]
  unfolding proc_key_of_id_def procs_map_wf
  by fast

subsection \<open>Any well-formed abstract state can be stored\<close>

text \<open>A mapping of addresses with specified (defined) values:\<close>
definition
  "con_wit_map \<S> :: _ \<rightharpoonup> word32 \<equiv>
        [nprocs_key \<mapsto> of_nat (nprocs \<S>)]
     ++ (Some \<circ> ucast \<circ> proc_key_of_id \<S> \<circ> id_of_key_addr) |` proc_key_addrs \<S>"

text \<open>A sample storage extending the above mapping with default zero values:\<close>
definition "con_wit \<S> \<equiv> override_on zero_con (the \<circ> con_wit_map \<S>) (dom (con_wit_map \<S>))"

lemmas con_wit = con_wit_def con_wit_map_def comp_def

lemma restrict_subst[simp]: "k \<in> S \<Longrightarrow> (f |` { g k | k. k \<in> S}) (g k) = f (g k)"
  unfolding restrict_map_def
  by auto

text \<open>Existence of a storage corresponding to any well-formed abstract state:\<close>
theorem models_nonvac: "\<turnstile> \<S> \<Longrightarrow> \<exists> S. S \<tturnstile> \<S>"
  unfolding models_nprocs models_proc_keys
proof (intro exI[of _ "con_wit \<S>"] conjI)
  assume wf:"\<turnstile>\<S>"
  thus "unat (con_wit \<S> nprocs_key) = nprocs \<S>"
    unfolding con_wit
    using nprocs_key_notin_proc_key_addrs le_unat_uoi[where z=max_nprocs_word]
    by (subst override_on_apply_in, simp)
      (subst map_add_dom_app_simps(3), auto simp add:procs_rng_wf)
  from wf have "\<And> k. k \<in> proc_keys \<S> \<Longrightarrow>
                     proc_key_of_id \<S> (id_of_key_addr (key_addr_of_id (proc_id \<S> k))) = k"
    by (subst id_of_key_addr_inv)
      (auto simp add:procs_rng_wf, force)
  thus "\<forall>k\<in>proc_keys \<S>. con_wit \<S> (key_addr_of_id (proc_id \<S> k)) = ucast k"
    unfolding con_wit proc_key_addrs_def
    by (intro ballI, subst override_on_apply_in, (auto)[1])
       (subst map_add_find_right, subst restrict_subst, auto)
qed

(*TODO: 
        Prove the encoding is unambiguous i.e.
        the same storage cannot model two distinct abstract states.
*)

section \<open>Well-formedness of a storage state\<close>
text \<open>
  We need a decoding function on storage states. However, not every storage state can be
  decoded into an abstract state. So we introduce a minimal well-formedness predicate on 
  storage states.
\<close>

text \<open>Number of procedures is bounded, otherwise procedure key addresses can become invalid and we
      cannot read the procedure keys from the storage.\<close>
definition "nprocs_wf S \<equiv> unat (S nprocs_key) \<le> max_nprocs_nat"

text \<open>Well-formedness of procedure keys:
      \begin{enumerate}
      \item procedure keys should fit into 24-byte words;
      \item they should represent some existing procedures
            (currently this essentially a temorary work-around
             and is understood in a very abstract sense
             (Hilbert epsilon operator is used to ``retrieve'' procedures),
             really we need to formalize how the procedures themselves are stored);
      \item the same procedure key should not be stored by two distinct procedure key addresses.
      \end{enumerate}\<close>
definition "proc_keys_wf (dummy :: 'a itself) (S :: storage) \<equiv>
    (\<forall>k\<in>{S (key_addr_of_id i) | i. i\<in>{1..unat (S nprocs_key)}}. ucast (ucast k :: key) = k)
  \<and> (\<forall>i\<in>{1..unat (S nprocs_key)}. \<exists>p :: ('a :: proc_class). ucast (key p) = S (key_addr_of_id i))
  \<and> inj_on (S \<circ> key_addr_of_id) {1..unat (S nprocs_key)}"

text \<open>Well-formedness of a storage state: the two above requirements should hold.\<close>
definition con_wf ("\<TTurnstile>\<^bsub>_\<^esub>_" [60])  where
  "\<TTurnstile>\<^bsub>(d :: ('a :: proc_class) itself)\<^esub> S \<equiv>
    nprocs_wf S
  \<and> proc_keys_wf d S"

notation (input) con_wf ("\<TTurnstile>\<^sub>__" [60])

lemmas nprocs_wf = con_wf_def nprocs_wf_def

lemmas proc_keys_wf = con_wf_def proc_keys_wf_def

text \<open>We proceed with the proof that any storage state corresponding (in the @{text \<tturnstile>} sense) to
      a well-formed abstract state is well-formed.\<close>

subsection \<open>Auxiliary lemmas\<close>

text \<open>Any property on procedure ids can be reformulated on the corresponding procedure keys
      according to a well-formed abstract state (elimination rule for procedure ids).\<close>
lemma elim_proc_id:
  assumes "i \<in> {1..unat (S nprocs_key)}"
  assumes "\<turnstile> \<S>"
  assumes "S \<tturnstile> \<S>"
  obtains k where "k \<in> proc_keys \<S> \<and> i = proc_id \<S> k"
  using assms proc_key_exists
  unfolding models_nprocs
  by metis

lemmas key_upcast =
  ucast_down_ucast_id
  [where ?'b=256 and ?'a=192,
   simplified is_down_def target_size_def source_size_def]
  down_ucast_inj
  [where ?'b=256 and ?'a=192,
   simplified is_down_def target_size_def source_size_def]

subsection \<open>Storage corresponding to a well-formed state is well-formed\<close>
theorem model_wf:"\<lbrakk>\<turnstile>(\<S> :: ('p :: proc_class) abs); S \<tturnstile> \<S>\<rbrakk> \<Longrightarrow> \<TTurnstile>\<^bsub>TYPE ('p)\<^esub>S"
  unfolding proc_keys_wf
proof (intro conjI ballI)
  assume wf:"\<turnstile> \<S>" and models:"S \<tturnstile> \<S>"
  thus "nprocs_wf S"
    unfolding procs_rng_wf models_nprocs nprocs_wf_def by simp
  show "inj_on (S \<circ> key_addr_of_id) {1..unat (S nprocs_key)}"
    unfolding inj_on_def
  proof (intro ballI impI)
    fix x y
    assume "x\<in>{1..unat (S nprocs_key)}" and "y\<in>{1..unat (S nprocs_key)}"
    from wf models and this
    show "(S \<circ> key_addr_of_id) x = (S \<circ> key_addr_of_id) y \<Longrightarrow> x = y"
      using key_upcast
      by (elim elim_proc_id[where \<S>=\<S>]) (auto simp add:models_proc_keys)
  qed
  fix i
  assume "i\<in>{1..unat (S nprocs_key)}"
  thus "\<exists>p :: 'p. ucast (key p) = S (key_addr_of_id i)"
    using wf models
    by (intro exI[of _ "proc_bdy \<S> (proc_key_of_id \<S> i)"], elim elim_proc_id)
      (simp+, simp add:models_proc_keys procs_rng_wf)
next
  fix k
  assume wf:"\<turnstile> \<S>" and models:"S \<tturnstile> \<S>"
  assume "k\<in>{S (key_addr_of_id i) | i. i\<in>{1..unat (S nprocs_key)}}"
  thus "ucast (ucast k :: key) = k"
  proof (simp only:Setcompr_eq_image image_iff, elim bexE)
    fix x
    assume "x \<in> {1..unat (S nprocs_key)}" and "k = S (key_addr_of_id x)"
    thus "ucast (ucast k :: key) = k"
      using wf models key_upcast
      by (elim elim_proc_id[where \<S>=\<S>])
        (auto simp add:models_proc_keys)
  qed
qed

section \<open>Decoding of storage\<close>

text \<open>Auxiliary abbreviations\<close>

abbreviation "proc_pair S i \<equiv> (ucast (S (key_addr_of_id i)) :: key, (i, SOME p. True))"

abbreviation "proc_list S \<equiv> [proc_pair S i. i \<leftarrow> [1..<Suc (unat (S nprocs_key))]]"

text \<open>The decoding function:\<close>
definition abs ("\<lbrace>_\<rbrace>") where "\<lbrace>S\<rbrace> = \<lparr> procs = map_of (proc_list S) \<rparr>"

lemma inj_on_fst: "inj_on f A \<Longrightarrow> inj_on (\<lambda> x. (f x, y x)) A"
  unfolding inj_on_def by simp

(*
theorem models_abs: "\<TTurnstile>\<^sub>p S \<Longrightarrow> S \<tturnstile> \<lbrace>S\<rbrace>"
  unfolding models_nprocs models_proc_keys
proof (intro conjI ballI)
  assume wf:"\<TTurnstile>\<^sub>p S"
  hence key_inj:"inj_on (\<lambda>i. ucast (S (key_addr_of_id i)) :: key) {1..unat (S nprocs_key)}"
    unfolding inj_on_def proc_keys_wf
    by (auto simp only:comp_apply Ball_def mem_Collect_eq) metis
  hence fst_inj:"inj_on fst (set (proc_list S))"
    unfolding inj_on_def set_map set_upt Ball_def image_iff
    by simp
  moreover have dist:"distinct (proc_list S)"
    by (simp add:distinct_map inj_on_def)
  ultimately show "unat (S nprocs_key) = nprocs \<lbrace>S\<rbrace>"
    unfolding abs_def
    by (simp only:abs.simps dom_map_of_conv_image_fst distinct_card[OF dist] card_image[OF fst_inj]
                  length_map length_upt)
  fix k
  assume "k\<in>proc_keys \<lbrace>S\<rbrace>"
  hence "map_of (proc_list S) k = Some (proc \<lbrace>S\<rbrace> k)"
    using key_inj fst_inj
    apply (intro  map_of_is_SomeI)
     apply (auto simp only:distinct_map, simp)
     apply (simp only:inj_on_fst set_upt atLeastLessThanSuc_atLeastAtMost)

  show "S (key_addr_of_id (proc_id \<lbrace>S\<rbrace> k)) = ucast k"
    unfolding abs_def
    apply (simp only:abs.simps)
    apply (cases "map_of (proc_list S) k")
    apply (subst map_of_eq_Some_iff)
qed
*)

section \<open>System calls\<close>

text \<open>
  This section will contain specifications of the system calls, but for now there are only some
  early experiments.
\<close>

abbreviation higher32 where "higher32 k n \<equiv> n >> ((32 - k) * 8)"

definition is_kernel_storage_key :: "word32 \<Rightarrow> bool"
  where "is_kernel_storage_key w \<equiv> higher32 4 w = 0xffffffff"

subsection \<open>Register Procedure\<close>

(*
24 bytes aligned right in the 32 bytes
*)
definition n_of_procedures :: "storage \<Rightarrow> word32"
  where "n_of_procedures s = s nprocs_key"

(*
When a procedure is added to the kernel:
  1. TODO: The procedure data is added to the procedure heap.
  2. The procedure key is appended to the end of the array.
  3. If the length value is equal to the maximum procedure index value, abort.
  4. The length value (the first value) is incremented by one.
  5. TODO: The procedure index value (in procedure metadata) is set to the new length value.
*)
definition add_proc :: "key \<Rightarrow> storage \<Rightarrow> storage option"
  where
    "add_proc p s \<equiv>
      if n_of_procedures s < max_nprocs_word
      then
        Some (s
              (nprocs_key := n_of_procedures s + 1,
               nprocs_key OR (n_of_procedures s + 1) := ucast p))
      else
        None"

lemma
  assumes "n_of_procedures s < max_nprocs_word"
  shows   "case (add_proc p s) of
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
  ultimately have "nprocs_key OR n_of_procedures s + 1 \<noteq> nprocs_key"
    using proc_key_addr_neq_nprocs_key by auto
  thus ?thesis
    unfolding add_proc_def
    using assms
    by (simp add:n_of_procedures_def)
qed

section \<open>Tests\<close>

text \<open>
  These are tests that we use to quickly check that the implemented functions and lemmas are
  correct, before conducting full-scale proofs.
\<close>

lemma "(0xFF :: word32) = (255 :: word32)" by auto
value "is_kernel_storage_key 0xffffffff00000000000000000000000000000000000000000000000000000000"
value "(0b1011 :: word32) >> 2 = 0x02"
value "0b1111 :: (2 word)"
value "ucast (0b1010 :: 4 word) = (0b101010 :: 6 word)"
value "case (add_proc 5 (\<lambda>x.0)) of (Some s) \<Rightarrow> s nprocs_key"
value "case (add_proc 5 (\<lambda>x.0)) of (Some s) \<Rightarrow> s (nprocs_key OR 1)"
value "case (add_proc 5 (\<lambda>x.0)) of (Some s) \<Rightarrow> s (nprocs_key OR 2)"
end
