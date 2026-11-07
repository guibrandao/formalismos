theory Multisets
  imports Partial_Orders
begin

section \<open>Natural numbers extended with infinity\<close>

text\<open> \<open>\<nat>\<^sub>\<infinity>\<close> consists of the natural numbers \<open>Fin n\<close> together with a new element \<open>\<infinity>\<close>.\<close>

datatype nat_inf = Fin nat | Infty (\<open>\<infinity>\<close>)

text\<open>Register \<open>Fin\<close> as a coercion: a \<open>nat\<close> used where a \<open>nat_inf\<close> is expected is
  automatically wrapped in \<open>Fin\<close>.\<close>

declare [[coercion_enabled, coercion Fin]]

subsection \<open>The natural ordering\<close>

text\<open>The ordering on \<open>\<nat>\<close> is extended so that \<open>\<infinity>\<close> is the maximal element.\<close>

instantiation nat_inf :: ord
begin

fun less_eq_nat_inf :: "nat_inf \<Rightarrow> nat_inf \<Rightarrow> bool" where
  "Fin m \<le> Fin n \<longleftrightarrow> m \<le> n"
| "Fin m \<le> \<infinity> \<longleftrightarrow> True"
| "\<infinity> \<le> Fin n \<longleftrightarrow> False"
| "\<infinity> \<le> \<infinity> \<longleftrightarrow> True"

fun less_nat_inf :: "nat_inf \<Rightarrow> nat_inf \<Rightarrow> bool" where
  "Fin m < Fin n \<longleftrightarrow> m < n"
| "Fin m < \<infinity> \<longleftrightarrow> True"
| "\<infinity> < _ \<longleftrightarrow> False"

instance ..

end

lemma infinity_maximal: "x \<le> \<infinity>"
  by (cases x) simp_all

lemma fin_less_infinity: "(n::nat) < \<infinity>"
  by simp

subsection \<open>Minimum and maximum\<close>

text\<open>Minimum (\<open>\<and>\<close> in the book) and maximum (\<open>\<or>\<close> in the book) are HOL's \<open>min\<close> and
  \<open>max\<close> for the ordering above.\<close>

lemma min_fin: "min (Fin m) (Fin n) = Fin (min m n)"
  unfolding min_def by simp

lemma min_infinity: "min x \<infinity> = x" "min \<infinity> x = x"
  unfolding min_def by (cases x; simp)+

lemma max_fin: "max (Fin m) (Fin n) = Fin (max m n)"
  unfolding max_def by simp

lemma max_infinity: "max x \<infinity> = \<infinity>" "max \<infinity> x = \<infinity>"
  unfolding max_def by (cases x; simp)+

subsection \<open>Addition\<close>

instantiation nat_inf :: plus
begin

fun plus_nat_inf :: "nat_inf \<Rightarrow> nat_inf \<Rightarrow> nat_inf" where
  "Fin m + Fin n = Fin (m + n)"
| "Fin m + \<infinity> = \<infinity>"
| "\<infinity> + _ = \<infinity>"

instance ..

end

lemma plus_infinity: "x + \<infinity> = \<infinity>" "\<infinity> + x = \<infinity>"
  by (cases x; simp)+

text\<open>With \<open>0 = Fin 0\<close>, \<open>\<nat>\<^sub>\<infinity>\<close> is a commutative monoid, so finite sums \<open>\<Sum>\<close> are available.\<close>

instantiation nat_inf :: comm_monoid_add
begin

definition zero_nat_inf :: nat_inf where
  "0 = Fin 0"

instance
proof
  fix a b c :: nat_inf
  show "a + b + c = a + (b + c)"
    by (cases a; cases b; cases c) simp_all
  show "a + b = b + a"
    by (cases a; cases b) simp_all
  show "0 + a = a"
    unfolding zero_nat_inf_def by (cases a) simp_all
qed

end

lemma sum_eq_infinity:
  assumes "finite S"
  shows "(\<Sum>x\<in>S. f x) = \<infinity> \<longleftrightarrow> (\<exists>x\<in>S. f x = \<infinity>)"
  using assms
proof (induction S rule: finite_induct)
  case empty
  then show ?case by (simp add: zero_nat_inf_def)
next
  case (insert y S)
  then show ?case
    by (cases "f y"; cases "\<Sum>x\<in>S. f x") simp_all
qed

subsection \<open>Cutoff subtraction\<close>


instantiation nat_inf :: minus
begin

fun minus_nat_inf :: "nat_inf \<Rightarrow> nat_inf \<Rightarrow> nat_inf" where
  "Fin m - Fin n = Fin (m - n)"
| "Fin m - \<infinity> = Fin 0"
| "\<infinity> - Fin n = \<infinity>"
| "\<infinity> - \<infinity> = \<infinity>"

instance ..

end

lemma cutoff_sub_fin: "Fin m - Fin n = (if m \<ge> n then Fin (m - n) else Fin 0)"
  by simp

section \<open>Multisets\<close>

text\<open>A multiset over \<open>A\<close> is a function \<open>M :: A \<Rightarrow> \<nat>\<^sub>\<infinity>\<close>; \<open>M x\<close> is the multiplicity of \<open>x\<close> in \<open>M\<close>.\<close>

type_synonym 'a multiset = "'a \<Rightarrow> nat_inf"


definition msize :: "'a multiset \<Rightarrow> nat_inf" where
  "msize M = (if finite {a. M a \<noteq> 0} then \<Sum>a\<in>{a. M a \<noteq> 0}. M a else \<infinity>)"

text\<open>A multiset \<open>F\<close> over \<open>A\<close> is \<^emph>\<open>finite\<close> if \<open>\<Sum>a\<in>A. F(a) < \<infinity>\<close>.\<close>

definition finite_multiset :: "'a multiset \<Rightarrow> bool" where
  "finite_multiset F \<longleftrightarrow> msize F < \<infinity>"

text\<open>A multiset \<open>S\<close> over \<open>A\<close> is a \<^emph>\<open>set\<close> if \<open>\<forall>a \<in> A. S(a) \<in> {0, \<infinity>}\<close>.\<close>

definition is_set :: "'a multiset \<Rightarrow> bool" where
  "is_set S \<longleftrightarrow> (\<forall>a. S a \<in> {0, \<infinity>})"

text\<open>\<open>a\<close> belongs to a multiset \<open>M\<close> iff \<open>M(a) \<noteq> 0\<close>\<close>

definition member_mul :: "'a \<Rightarrow> 'a multiset \<Rightarrow> bool" (infix \<open>\<^bold>\<in>\<close> 100)
where
  "a \<^bold>\<in> M \<longleftrightarrow> (M a > 0)"

definition multisets :: "'a set \<Rightarrow> 'a multiset set" (\<open>\<M>'(_')\<close>) where
  "\<M>(A) = {M. {a. M a \<noteq> 0} \<subseteq> A}"

definition finite_multisets :: "'a set \<Rightarrow> 'a multiset set" (\<open>\<F>\<M>'(_')\<close>) where
  "\<F>\<M>(A) = {F \<in> multisets A. finite_multiset F}"

definition sets :: "'a set \<Rightarrow> 'a multiset set" (\<open>\<S>'(_')\<close>) where
  "\<S>(A) = {S \<in> multisets A. is_set S}"

text\<open>The book writes \<open>[a]\<close> for the finite multiset with exactly one occurrence of \<open>a\<close> and
  \<open>{a}\<close> for the set with infinitely many occurrences of \<open>a\<close>. Since \<open>[_]\<close> and \<open>{_}\<close> are
  already HOL's list and set syntax, we write \<open>[#a#]\<close> and \<open>{#a#}\<close>.\<close>

definition fmsingleton :: "'a \<Rightarrow> 'a multiset" where
  "fmsingleton a = (\<lambda>x. if x = a then Fin 1 else 0)"

definition ssingleton :: "'a \<Rightarrow> 'a multiset"  where
  "ssingleton a = (\<lambda>x. if x = a then \<infinity> else 0)"


subsection \<open>Operations on multisets\<close>

text\<open>The binary operations intersection, union, sum and difference are defined pointwise
  by \<open>(M \<otimes> N)(a) = M(a) \<^emph> N(a)\<close>, where \<open>\<^emph>\<close> is \<open>min\<close>, \<open>max\<close>, \<open>+\<close> and cutoff \<open>-\<close>, respectively.\<close>

definition munion :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" (infixl \<open>\<^bold>\<union>\<close> 65) where
  "M \<^bold>\<union> N = (\<lambda>a. max (M a) (N a))"

lemma munion_in_multisets: "M \<in> \<M>(A) \<Longrightarrow> N \<in> \<M>(A) \<Longrightarrow> M \<^bold>\<union> N \<in> \<M>(A)"
  by (auto simp: multisets_def munion_def max_def)

definition minter :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" (infixl \<open>\<^bold>\<inter>\<close> 70) where
  "M \<^bold>\<inter> N = (\<lambda>a. min (M a) (N a))"

lemma minter_in_multisets: "M \<in> \<M>(A) \<Longrightarrow> N \<in> \<M>(A) \<Longrightarrow> M \<^bold>\<inter> N \<in> \<M>(A)"
  by (auto simp: multisets_def minter_def min_def)

definition msum :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" (infixl \<open>\<oplus>\<close> 65) where
  "M \<oplus> N = (\<lambda>a. M a + N a)"

lemma msum_in_multisets: "M \<in> \<M>(A) \<Longrightarrow> N \<in> \<M>(A) \<Longrightarrow> M \<oplus> N \<in> \<M>(A)"
  by (simp add: multisets_def msum_def subset_iff) (metis add_0)

text\<open>Finite multisets can be written by enumeration, \<open>\<lbrakk>a, a, b\<rbrakk> = \<lbrakk>a\<rbrakk> \<oplus> \<lbrakk>a\<rbrakk> \<oplus> \<lbrakk>b\<rbrakk>\<close>, in the same
  way as HOL's \<open>{a, a, b}\<close> for sets and \<open>[a, a, b]\<close> for lists.\<close>

syntax
  "_fmset" :: "args \<Rightarrow> 'a multiset" (\<open>\<lbrakk>(_)\<rbrakk>\<close>)
syntax_consts
  "_fmset" \<rightleftharpoons> fmsingleton msum
translations
  "\<lbrakk>x, xs\<rbrakk>" \<rightleftharpoons> "CONST msum \<lbrakk>x\<rbrakk> \<lbrakk>xs\<rbrakk>"
  "\<lbrakk>x\<rbrakk>" \<rightleftharpoons> "CONST fmsingleton x"

lemma "a \<noteq> b \<Longrightarrow> \<lbrakk>a, a, b\<rbrakk> a = Fin 2 \<and> \<lbrakk>a, a, b\<rbrakk> b = Fin 1"
  by (simp add: msum_def fmsingleton_def zero_nat_inf_def)

text\<open>Similarly, sets are written \<open>\<lbrace>a, b\<rbrace> = \<lbrace>a\<rbrace> \<^bold>\<union> \<lbrace>b\<rbrace>\<close>. Repetitions do not matter, since
  \<open>max \<infinity> \<infinity> = \<infinity>\<close>.\<close>

no_notation ssingleton (\<open>\<lbrace>_\<rbrace>\<close>)

syntax
  "_sset" :: "args \<Rightarrow> 'a multiset" (\<open>\<lbrace>(_)\<rbrace>\<close>)
syntax_consts
  "_sset" \<rightleftharpoons> ssingleton munion
translations
  "\<lbrace>x, xs\<rbrace>" \<rightleftharpoons> "CONST munion \<lbrace>x\<rbrace> \<lbrace>xs\<rbrace>"
  "\<lbrace>x\<rbrace>" \<rightleftharpoons> "CONST ssingleton x"

lemma set_idem: "\<lbrace>a, a\<rbrace> = \<lbrace>a\<rbrace>"
  by (auto simp: fun_eq_iff munion_def ssingleton_def max_infinity max_fin zero_nat_inf_def)

lemma fmsingleton_in_finite_multisets: "\<lbrakk>a\<rbrakk> \<in> finite_multisets {a}"
proof -
  have "{x. \<lbrakk>a\<rbrakk> x \<noteq> 0} = {a}"
    by (auto simp: fmsingleton_def zero_nat_inf_def)
  then show ?thesis
    by (simp add: finite_multisets_def multisets_def finite_multiset_def msize_def
        fmsingleton_def)
qed

lemma ssingleton_in_sets: "\<lbrace>a\<rbrace> \<in> sets {a}"
  by (auto simp: sets_def multisets_def is_set_def ssingleton_def)

text\<open>The singleton set \<open>\<lbrace>a\<rbrace>\<close> has exactly the same members as the usual set \<open>{a}\<close>.\<close>

lemma ssingleton_iff_singleton: "x \<^bold>\<in> \<lbrace>a\<rbrace> \<longleftrightarrow> x \<in> {a}"
  by (simp add: member_mul_def ssingleton_def zero_nat_inf_def)

definition mdiff :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" (infixl \<open>\<setminus>\<close> 65) where
  "M \<setminus> N = (\<lambda>a. M a - N a)"

lemma zero_minus_nat_inf: "0 - x = (0::nat_inf)"
  by (cases x) (simp_all add: zero_nat_inf_def)

lemma mdiff_in_multisets: "M \<in> \<M>(A) \<Longrightarrow> M \<setminus> N \<in> \<M>(A)"
  by (auto simp: multisets_def mdiff_def zero_minus_nat_inf)

subsection \<open>Sets as multisets\<close>

text\<open>A set \<open>S \<in> \<S>(A)\<close> is determined by its members, so \<open>\<S>(A)\<close> corresponds one-to-one to
  the subsets of \<open>A\<close>: a HOL set \<open>B\<close> becomes the multiset with value \<open>\<infinity>\<close> on \<open>B\<close> and \<open>0\<close> elsewhere.\<close>

definition set_of :: "'a multiset \<Rightarrow> 'a set" where
  "set_of S = {a. a \<^bold>\<in> S}"

definition of_set :: "'a set \<Rightarrow> 'a multiset" where
  "of_set B = (\<lambda>a. if a \<in> B then \<infinity> else 0)"

lemma of_set_in_sets: "B \<subseteq> A \<Longrightarrow> of_set B \<in> \<S>(A)"
  by (auto simp: sets_def multisets_def is_set_def of_set_def)

lemma set_of_subset: "S \<in> \<S>(A) \<Longrightarrow> set_of S \<subseteq> A"
  by (auto simp: sets_def multisets_def set_of_def member_mul_def zero_nat_inf_def)

lemma set_of_of_set: "set_of (of_set B) = B"
  by (simp add: set_of_def of_set_def member_mul_def zero_nat_inf_def)

lemma of_set_set_of:
  assumes "S \<in> \<S>(A)"
  shows "of_set (set_of S) = S"
proof
  fix x
  from assms have "S x = 0 \<or> S x = \<infinity>"
    by (simp add: sets_def is_set_def)
  then show "of_set (set_of S) x = S x"
    by (auto simp: of_set_def set_of_def member_mul_def zero_nat_inf_def)
qed

text\<open>Hence \<open>set_of\<close> is a bijection between \<open>\<S>(A)\<close> and the subsets of \<open>A\<close>.\<close>

lemma bij_betw_sets_Pow: "bij_betw set_of (\<S>(A)) (Pow A)"
  by (rule bij_betw_byWitness[where f' = of_set])
    (auto simp: of_set_set_of set_of_of_set of_set_in_sets dest!: set_of_subset)

text\<open>Under this correspondence, the enumerated sets \<open>\<lbrace>a, b, \<dots>\<rbrace>\<close> are exactly HOL's \<open>{a, b, \<dots>}\<close>.\<close>

lemma ssingleton_eq_of_set: "\<lbrace>a\<rbrace> = of_set {a}"
  by (simp add: fun_eq_iff ssingleton_def of_set_def)

lemma munion_of_set: "munion (of_set A) (of_set B) = of_set (A \<union> B)"
  by (auto simp: fun_eq_iff munion_def of_set_def max_infinity max_fin zero_nat_inf_def)

lemma "\<lbrace>a, b, c\<rbrace> = of_set {a, b, c}"
  by (simp add: ssingleton_eq_of_set munion_of_set insert_commute)

lemma "set_of \<lbrace>a, b, c\<rbrace> = {a, b, c}"
  by (simp add: ssingleton_eq_of_set munion_of_set set_of_of_set insert_commute)

subsection \<open>The multiset extension of an ordering\<close>

text\<open>The empty multiset and the submultiset relation, defined pointwise.\<close>

definition mempty :: "'a multiset" (\<open>\<emptyset>\<close>) where
  "\<emptyset> = (\<lambda>a. 0)"

definition msubseteq :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" (infix \<open>\<^bold>\<subseteq>\<close> 50) where
  "M \<^bold>\<subseteq> N \<longleftrightarrow> (\<forall>a. M a \<le> N a)"

text\<open>Definition 2.3.10\<close>

definition mul_ext :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a multiset rel"  where
  "mul_ext A r = {(M\<^sub>1, M\<^sub>2). M\<^sub>1 \<in> \<F>\<M>(A) \<and> M\<^sub>2 \<in> \<F>\<M>(A) \<and>
     (\<exists>X \<in> \<F>\<M>(A). \<exists>Y \<in> \<F>\<M>(A).
        \<emptyset> \<noteq> X \<and> X \<^bold>\<subseteq> M\<^sub>1 \<and> M\<^sub>2 = (M\<^sub>1 \<setminus> X) \<oplus> Y \<and> (\<forall>y. y \<^bold>\<in> Y \<longrightarrow> (\<exists>x. x \<^bold>\<in> X \<and> x \<succ>\<^sub>r y)))}"

lemma "a \<in> A \<Longrightarrow> (\<lbrakk>a\<rbrakk>, \<emptyset>) \<in> mul_ext A r"
proof -
  assume a: "a \<in> A"
  have fm: "\<lbrakk>a\<rbrakk> \<in> \<F>\<M>(A)" "\<emptyset> \<in> \<F>\<M>(A)"
    using a
    by (auto simp: finite_multisets_def multisets_def finite_multiset_def msize_def
        fmsingleton_def mempty_def zero_nat_inf_def)
  have "\<exists>X \<in> \<F>\<M>(A). \<exists>Y \<in> \<F>\<M>(A).
      \<emptyset> \<noteq> X \<and> X \<^bold>\<subseteq> \<lbrakk>a\<rbrakk> \<and> \<emptyset> = (\<lbrakk>a\<rbrakk> \<setminus> X) \<oplus> Y \<and> (\<forall>y. y \<^bold>\<in> Y \<longrightarrow> (\<exists>x. x \<^bold>\<in> X \<and> x \<succ>\<^sub>r y))"
  proof (rule bexI[of _ "\<lbrakk>a\<rbrakk>"], rule bexI[of _ \<emptyset>])
    have "\<lbrakk>a\<rbrakk> \<setminus> \<lbrakk>a\<rbrakk> \<oplus> \<emptyset> = \<emptyset>"
      by (simp add: fun_eq_iff mdiff_def msum_def mempty_def fmsingleton_def zero_nat_inf_def)
    moreover have "\<emptyset> \<noteq> \<lbrakk>a\<rbrakk>"
      by (auto simp: fun_eq_iff mempty_def fmsingleton_def zero_nat_inf_def)
    moreover have "\<lbrakk>a\<rbrakk> \<^bold>\<subseteq> \<lbrakk>a\<rbrakk>"
      by (simp add: msubseteq_def fmsingleton_def zero_nat_inf_def)
    moreover have "\<forall>y. \<not> y \<^bold>\<in> (\<emptyset> :: 'a multiset)"
      by (simp add: member_mul_def mempty_def zero_nat_inf_def)
    ultimately show "\<emptyset> \<noteq> \<lbrakk>a\<rbrakk> \<and> \<lbrakk>a\<rbrakk> \<^bold>\<subseteq> \<lbrakk>a\<rbrakk> \<and> \<emptyset> = (\<lbrakk>a\<rbrakk> \<setminus> \<lbrakk>a\<rbrakk>) \<oplus> \<emptyset> \<and>
        (\<forall>y. y \<^bold>\<in> \<emptyset> \<longrightarrow> (\<exists>x. x \<^bold>\<in> \<lbrakk>a\<rbrakk> \<and> x \<succ>\<^sub>r y))"
      by simp
  qed (fact fm)+
  with fm show ?thesis
    unfolding mul_ext_def by simp
qed

subsection \<open>The multiset extension of a partial ordering is a partial ordering\<close>

text\<open>A finite multiset has finite support and no infinite multiplicities.\<close>

lemma less_infinity_iff: "x < \<infinity> \<longleftrightarrow> x \<noteq> \<infinity>"
  by (cases x) simp_all

lemma finite_multiset_iff:
  "finite_multiset F \<longleftrightarrow> finite {a. F a \<noteq> 0} \<and> (\<forall>a. F a \<noteq> \<infinity>)"
  unfolding finite_multiset_def msize_def less_infinity_iff
  by (auto simp: sum_eq_infinity zero_nat_inf_def) (metis nat_inf.distinct(2))

lemma finite_multisets_iff:
  "M \<in> finite_multisets A \<longleftrightarrow>
     {a. M a \<noteq> 0} \<subseteq> A \<and> finite {a. M a \<noteq> 0} \<and> (\<forall>a. M a \<noteq> \<infinity>)"
  by (simp add: finite_multisets_def multisets_def finite_multiset_iff)

lemma finite_multisets_Fin: "M \<in> finite_multisets A \<Longrightarrow> \<exists>n. M a = Fin n"
  by (cases "M a") (auto simp: finite_multisets_iff)

lemma member_mul_iff: "member_mul a M \<longleftrightarrow> M a \<noteq> 0"
  by (cases "M a") (auto simp: member_mul_def zero_nat_inf_def)

text\<open>Irreflexivity. If \<open>M = (M \<setminus> X) \<oplus> Y\<close> with \<open>X \<^bold>\<subseteq> M\<close>, then \<open>X = Y\<close>; but a nonempty finite
  \<open>X\<close> cannot have every element dominated by another element of \<open>X\<close>.\<close>

lemma msum_mdiff_same:
  assumes "M \<in> finite_multisets A" "X \<in> finite_multisets A" "Y \<in> finite_multisets A"
    and "msubseteq X M" and "M = msum (mdiff M X) Y"
  shows "X = Y"
proof
  fix a
  obtain m x y where "M a = Fin m" "X a = Fin x" "Y a = Fin y"
    using assms(1-3) finite_multisets_Fin by metis
  moreover have "M a = (M a - X a) + Y a"
    using assms(5) by (metis msum_def mdiff_def)
  moreover have "X a \<le> M a"
    using assms(4) by (simp add: msubseteq_def)
  ultimately show "X a = Y a"
    by auto
qed

lemma partial_ordering_maximal:
  assumes "partial_ordering r" "finite S" "S \<noteq> {}"
  shows "\<exists>z\<in>S. \<forall>y\<in>S. (y, z) \<notin> r"
proof -
  let ?r = "r \<inter> S \<times> S"
  have "trans ?r"
    using assms(1) unfolding partial_ordering_def trans_def by blast
  then have "trancl ?r = ?r"
    by (rule trancl_id)
  moreover have "(x, x) \<notin> ?r" for x
    using assms(1) by (auto simp: partial_ordering_def irrefl_def)
  ultimately have "acyclic ?r"
    unfolding acyclic_def by simp
  moreover have "finite ?r"
    using assms(2) by blast
  ultimately have "wf ?r"
    by (blast intro: finite_acyclic_wf)
  moreover obtain s where "s \<in> S"
    using assms(3) by blast
  ultimately obtain z where "z \<in> S" "\<And>y. (y, z) \<in> ?r \<Longrightarrow> y \<notin> S"
    by (metis wfE_min)
  then show ?thesis
    by blast
qed

lemma mul_ext_irreflexive:
  assumes "partial_ordering r"
  shows "irrefl (mul_ext A r)"
  unfolding irrefl_def
proof (intro allI notI)
  fix M
  assume "(M, M) \<in> mul_ext A r"
  then obtain X Y where
    M: "M \<in> finite_multisets A" and X: "X \<in> finite_multisets A"
    and Y: "Y \<in> finite_multisets A" and ne: "mempty \<noteq> X"
    and sub: "msubseteq X M" and eq: "M = msum (mdiff M X) Y"
    and dom: "\<forall>y. member_mul y Y \<longrightarrow> (\<exists>x. member_mul x X \<and> (x, y) \<in> r)"
    unfolding mul_ext_def by blast
  have XY: "X = Y"
    using M X Y sub eq by (rule msum_mdiff_same)
  let ?S = "{a. X a \<noteq> 0}"
  have "finite ?S"
    using X by (simp add: finite_multisets_iff)
  moreover have "?S \<noteq> {}"
    using ne by (auto simp: mempty_def fun_eq_iff)
  ultimately obtain z where z: "z \<in> ?S" and max: "\<forall>y\<in>?S. (y, z) \<notin> r"
    using assms partial_ordering_maximal by blast
  from z dom XY obtain x where "X x \<noteq> 0" "(x, z) \<in> r"
    by (auto simp: member_mul_iff)
  with max show False
    by blast
qed

text\<open>Transitivity. If \<open>M\<^sub>2\<close> arises from \<open>M\<^sub>1\<close> by replacing \<open>X\<^sub>1\<close> with \<open>Y\<^sub>1\<close>, and \<open>M\<^sub>3\<close> from \<open>M\<^sub>2\<close>
  by replacing \<open>X\<^sub>2\<close> with \<open>Y\<^sub>2\<close>, then \<open>M\<^sub>3\<close> arises from \<open>M\<^sub>1\<close> by replacing
  \<open>X = X\<^sub>1 \<oplus> (X\<^sub>2 \<setminus> Y\<^sub>1)\<close> with \<open>Y = (Y\<^sub>1 \<setminus> X\<^sub>2) \<oplus> Y\<^sub>2\<close>.\<close>

lemma plus_eq_zero_nat_inf: "p + q = (0::nat_inf) \<longleftrightarrow> p = 0 \<and> q = 0"
  by (cases p; cases q) (simp_all add: zero_nat_inf_def)

lemma minus_zero_nat_inf: "p - 0 = (p::nat_inf)"
  by (cases p) (simp_all add: zero_nat_inf_def)

lemma msum_finite_multisets:
  assumes "M \<in> finite_multisets A" "N \<in> finite_multisets A"
  shows "msum M N \<in> finite_multisets A"
proof -
  have sub: "{a. msum M N a \<noteq> 0} \<subseteq> {a. M a \<noteq> 0} \<union> {a. N a \<noteq> 0}"
    by (auto simp: msum_def plus_eq_zero_nat_inf)
  have "msum M N a \<noteq> \<infinity>" for a
    using finite_multisets_Fin[OF assms(1), of a] finite_multisets_Fin[OF assms(2), of a]
    by (auto simp: msum_def)
  then show ?thesis
    using assms sub finite_subset[OF sub] by (auto simp: finite_multisets_iff)
qed

lemma mdiff_finite_multisets:
  assumes "M \<in> finite_multisets A"
  shows "mdiff M N \<in> finite_multisets A"
proof -
  have sub: "{a. mdiff M N a \<noteq> 0} \<subseteq> {a. M a \<noteq> 0}"
    by (auto simp: mdiff_def zero_minus_nat_inf)
  have "mdiff M N a \<noteq> \<infinity>" for a
    using finite_multisets_Fin[OF assms, of a] by (cases "N a") (auto simp: mdiff_def)
  then show ?thesis
    using assms sub finite_subset[OF sub] by (auto simp: finite_multisets_iff)
qed

lemma mul_ext_transitive:
  assumes "partial_ordering r"
  shows "trans (mul_ext A r)"
  unfolding trans_def
proof (intro allI impI)
  fix M\<^sub>1 M\<^sub>2 M\<^sub>3
  assume "(M\<^sub>1, M\<^sub>2) \<in> mul_ext A r" "(M\<^sub>2, M\<^sub>3) \<in> mul_ext A r"
  then obtain X\<^sub>1 Y\<^sub>1 X\<^sub>2 Y\<^sub>2 where
    M\<^sub>1: "M\<^sub>1 \<in> finite_multisets A" and M\<^sub>3: "M\<^sub>3 \<in> finite_multisets A"
    and X\<^sub>1: "X\<^sub>1 \<in> finite_multisets A" and Y\<^sub>1: "Y\<^sub>1 \<in> finite_multisets A"
    and X\<^sub>2: "X\<^sub>2 \<in> finite_multisets A" and Y\<^sub>2: "Y\<^sub>2 \<in> finite_multisets A"
    and ne\<^sub>1: "mempty \<noteq> X\<^sub>1" and sub\<^sub>1: "msubseteq X\<^sub>1 M\<^sub>1" and eq\<^sub>1: "M\<^sub>2 = msum (mdiff M\<^sub>1 X\<^sub>1) Y\<^sub>1"
    and dom\<^sub>1: "\<forall>y. member_mul y Y\<^sub>1 \<longrightarrow> (\<exists>x. member_mul x X\<^sub>1 \<and> (x, y) \<in> r)"
    and sub\<^sub>2: "msubseteq X\<^sub>2 M\<^sub>2" and eq\<^sub>2: "M\<^sub>3 = msum (mdiff M\<^sub>2 X\<^sub>2) Y\<^sub>2"
    and dom\<^sub>2: "\<forall>y. member_mul y Y\<^sub>2 \<longrightarrow> (\<exists>x. member_mul x X\<^sub>2 \<and> (x, y) \<in> r)"
    unfolding mul_ext_def by blast
  define X where "X = msum X\<^sub>1 (mdiff X\<^sub>2 Y\<^sub>1)"
  define Y where "Y = msum (mdiff Y\<^sub>1 X\<^sub>2) Y\<^sub>2"
  have X: "X \<in> finite_multisets A" and Y: "Y \<in> finite_multisets A"
    using X\<^sub>1 X\<^sub>2 Y\<^sub>1 Y\<^sub>2
    by (simp_all add: X_def Y_def msum_finite_multisets mdiff_finite_multisets)
  have point: "X a \<le> M\<^sub>1 a \<and> M\<^sub>3 a = (M\<^sub>1 a - X a) + Y a" for a
  proof -
    obtain m x\<^sub>1 y\<^sub>1 x\<^sub>2 y\<^sub>2 where
      "M\<^sub>1 a = Fin m" "X\<^sub>1 a = Fin x\<^sub>1" "Y\<^sub>1 a = Fin y\<^sub>1" "X\<^sub>2 a = Fin x\<^sub>2" "Y\<^sub>2 a = Fin y\<^sub>2"
      using M\<^sub>1 X\<^sub>1 Y\<^sub>1 X\<^sub>2 Y\<^sub>2 finite_multisets_Fin by metis
    moreover have "M\<^sub>2 a = M\<^sub>1 a - X\<^sub>1 a + Y\<^sub>1 a" "M\<^sub>3 a = M\<^sub>2 a - X\<^sub>2 a + Y\<^sub>2 a"
      using eq\<^sub>1 eq\<^sub>2 by (simp_all add: msum_def mdiff_def)
    moreover have "X\<^sub>1 a \<le> M\<^sub>1 a" "X\<^sub>2 a \<le> M\<^sub>2 a"
      using sub\<^sub>1 sub\<^sub>2 by (simp_all add: msubseteq_def)
    ultimately show ?thesis
      by (simp add: X_def Y_def msum_def mdiff_def) arith
  qed
  then have sub: "msubseteq X M\<^sub>1" and eq: "M\<^sub>3 = msum (mdiff M\<^sub>1 X) Y"
    by (simp_all add: msubseteq_def fun_eq_iff msum_def mdiff_def)
  have ne: "mempty \<noteq> X"
  proof -
    obtain a where "X\<^sub>1 a \<noteq> 0"
      using ne\<^sub>1 by (auto simp: mempty_def fun_eq_iff)
    then have "X a \<noteq> 0"
      by (simp add: X_def msum_def plus_eq_zero_nat_inf)
    then show ?thesis
      by (auto simp: mempty_def)
  qed
  have dom: "\<forall>y. member_mul y Y \<longrightarrow> (\<exists>x. member_mul x X \<and> (x, y) \<in> r)"
  proof (intro allI impI)
    fix y
    assume "member_mul y Y"
    then have "Y\<^sub>1 y - X\<^sub>2 y \<noteq> 0 \<or> Y\<^sub>2 y \<noteq> 0"
      by (simp add: member_mul_iff Y_def msum_def mdiff_def plus_eq_zero_nat_inf)
    then show "\<exists>x. member_mul x X \<and> (x, y) \<in> r"
    proof
      assume "Y\<^sub>1 y - X\<^sub>2 y \<noteq> 0"
      then have "Y\<^sub>1 y \<noteq> 0"
        by (metis zero_minus_nat_inf)
      then obtain x where "X\<^sub>1 x \<noteq> 0" "(x, y) \<in> r"
        using dom\<^sub>1 by (auto simp: member_mul_iff)
      then show ?thesis
        by (auto simp: member_mul_iff X_def msum_def plus_eq_zero_nat_inf)
    next
      assume "Y\<^sub>2 y \<noteq> 0"
      then obtain x where x: "X\<^sub>2 x \<noteq> 0" "(x, y) \<in> r"
        using dom\<^sub>2 by (auto simp: member_mul_iff)
      show ?thesis
      proof (cases "X\<^sub>2 x - Y\<^sub>1 x = 0")
        case True
        then have "Y\<^sub>1 x \<noteq> 0"
          using x(1) by (metis minus_zero_nat_inf)
        then obtain x' where x': "X\<^sub>1 x' \<noteq> 0" "(x', x) \<in> r"
          using dom\<^sub>1 by (auto simp: member_mul_iff)
        have "(x', y) \<in> r"
          by (rule succ_trans[OF assms x'(2) x(2)])
        with x'(1) show ?thesis
          by (auto simp: member_mul_iff X_def msum_def plus_eq_zero_nat_inf)
      next
        case False
        with x(2) show ?thesis
          by (auto simp: member_mul_iff X_def msum_def mdiff_def plus_eq_zero_nat_inf)
      qed
    qed
  qed
  show "(M\<^sub>1, M\<^sub>3) \<in> mul_ext A r"
    unfolding mul_ext_def using M\<^sub>1 M\<^sub>3 X Y ne sub eq dom by blast
qed

text\<open>Hence, if \<open>(A, \<succ>)\<close> is a partial ordering, so is its finite multiset extension
  \<open>(\<F>\<M>(A), \<succ>\<^sub>m\<^sub>u\<^sub>l)\<close>.\<close>

theorem mul_ext_partial_ordering:
  assumes "partial_ordering r"
  shows "partial_ordering (mul_ext A r)"
  using mul_ext_irreflexive[OF assms] mul_ext_transitive[OF assms]
  by (simp add: partial_ordering_def)












end
