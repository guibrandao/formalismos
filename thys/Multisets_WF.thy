theory Multisets_WF
  imports Multisets
begin

text\<open>In this theory we write the multiset operations by name, so the book notation for
  multiset membership, inclusion and the empty multiset is switched off here
  (and switched back on at the end) to avoid clashes with HOL's set notation.\<close>


section \<open>Well-foundedness of the multiset extension\<close>

text\<open>We prove Theorem 2.3.12 directly from the definitions of \<open>Multisets\<close>. The idea is to
  split each step \<open>M\<^sub>1 \<succ>\<^sub>m\<^sub>u\<^sub>l M\<^sub>2\<close> into \<^emph>\<open>one-element steps\<close>, which replace a single
  occurrence of some \<open>a\<close> by finitely many elements smaller than \<open>a\<close>, and to show by
  well-founded induction that every finite multiset is accessible for the one-element steps.\<close>

subsection \<open>Multiplicities as natural numbers\<close>

text\<open>A finite multiset takes only values \<open>Fin n\<close>; \<open>nat_of\<close> reads off \<open>n\<close>. Equations between
  finite multisets then reduce to pointwise equations between natural numbers.\<close>

fun nat_of :: "nat_inf \<Rightarrow> nat" where
  "nat_of (Fin n) = n"
| "nat_of \<infinity> = 0"

lemma nat_of_mempty: "nat_of (mempty x) = 0"
  by (simp add: mempty_def zero_nat_inf_def)

lemma nat_of_fmsingleton: "nat_of (fmsingleton a x) = (if x = a then 1 else 0)"
  by (simp add: fmsingleton_def zero_nat_inf_def)

text\<open>The part of a multiset whose elements satisfy \<open>P\<close>.\<close>

definition mfilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a multiset \<Rightarrow> 'a multiset" where
  "mfilter P M = (\<lambda>x. if P x then M x else 0)"

lemma nat_of_mfilter: "nat_of (mfilter P M x) = (if P x then nat_of (M x) else 0)"
  by (simp add: mfilter_def zero_nat_inf_def)

text\<open>Sum of multisets is associative and commutative, with unit \<open>\<emptyset>\<close>.\<close>

lemma msum_assoc: "msum (msum M N) K = msum M (msum N K)"
  by (simp add: msum_def add.assoc)

lemma msum_commute: "msum M N = msum N M"
  by (simp add: msum_def add.commute)

lemma msum_left_commute: "msum M (msum N K) = msum N (msum M K)"
  by (simp add: msum_def add.left_commute)

lemmas msum_ac = msum_assoc msum_commute msum_left_commute

lemma msum_mempty: "msum M mempty = M"
  by (simp add: msum_def mempty_def)

lemma mempty_msum: "msum mempty M = M"
  by (simp add: msum_def mempty_def)

text\<open>A \<^emph>\<open>one-element step\<close> replaces one occurrence of \<open>a\<close> by a finite multiset \<open>K\<close> of
  elements smaller than \<open>a\<close>. We orient it as \<open>(smaller, bigger)\<close>, as HOL's \<open>wf\<close> expects.\<close>

definition mul_step :: "'a set \<Rightarrow> 'a rel \<Rightarrow> 'a multiset rel" where
  "mul_step A r = {(N, M). \<exists>M\<^sub>0 a K. M\<^sub>0 \<in> finite_multisets A \<and> a \<in> A \<and> K \<in> finite_multisets A \<and>
     M = msum M\<^sub>0 (fmsingleton a) \<and> N = msum M\<^sub>0 K \<and> (\<forall>b. member_mul b K \<longrightarrow> (a, b) \<in> r)}"

lemma mul_stepI:
  assumes "M\<^sub>0 \<in> finite_multisets A" "a \<in> A" "K \<in> finite_multisets A"
    and "\<forall>b. member_mul b K \<longrightarrow> (a, b) \<in> r"
  shows "(msum M\<^sub>0 K, msum M\<^sub>0 (fmsingleton a)) \<in> mul_step A r"
  using assms unfolding mul_step_def by blast

subsection \<open>Well-foundedness of the transitive closure\<close>

text\<open>HOL already provides this: @{thm [source] wf_trancl}.\<close>

lemmas wf_trans_cl = wf_trancl

context
  fixes A :: "'a set"
begin

lemma fm_eqI:
  assumes "M \<in> finite_multisets A" "N \<in> finite_multisets A"
    and "\<And>x. nat_of (M x) = nat_of (N x)"
  shows "M = N"
proof
  fix x
  obtain m n where "M x = Fin m" "N x = Fin n"
    using assms(1,2) finite_multisets_Fin by metis
  then show "M x = N x"
    using assms(3)[of x] by simp
qed

lemma nat_of_msum:
  assumes "M \<in> finite_multisets A" "N \<in> finite_multisets A"
  shows "nat_of (msum M N x) = nat_of (M x) + nat_of (N x)"
proof -
  obtain m n where "M x = Fin m" "N x = Fin n"
    using assms finite_multisets_Fin by metis
  then show ?thesis
    by (simp add: msum_def)
qed

lemma nat_of_mdiff:
  assumes "M \<in> finite_multisets A" "N \<in> finite_multisets A"
  shows "nat_of (mdiff M N x) = nat_of (M x) - nat_of (N x)"
proof -
  obtain m n where "M x = Fin m" "N x = Fin n"
    using assms finite_multisets_Fin by metis
  then show ?thesis
    by (simp add: mdiff_def)
qed

lemma nat_of_zero_iff:
  assumes "M \<in> finite_multisets A"
  shows "M x = 0 \<longleftrightarrow> nat_of (M x) = 0"
proof -
  obtain m where "M x = Fin m"
    using assms finite_multisets_Fin by metis
  then show ?thesis
    by (simp add: zero_nat_inf_def)
qed

lemma member_mul_nat_of:
  assumes "M \<in> finite_multisets A"
  shows "member_mul x M \<longleftrightarrow> 0 < nat_of (M x)"
  using nat_of_zero_iff[OF assms] by (simp add: member_mul_iff)

lemma msubseteq_nat_of:
  assumes "M \<in> finite_multisets A" "N \<in> finite_multisets A"
  shows "msubseteq M N \<longleftrightarrow> (\<forall>x. nat_of (M x) \<le> nat_of (N x))"
proof -
  have "M x \<le> N x \<longleftrightarrow> nat_of (M x) \<le> nat_of (N x)" for x
  proof -
    obtain m n where "M x = Fin m" "N x = Fin n"
      using assms finite_multisets_Fin by metis
    then show ?thesis
      by simp
  qed
  then show ?thesis
    by (simp add: msubseteq_def)
qed

lemma mempty_finite_multisets: "mempty \<in> finite_multisets A"
  by (simp add: finite_multisets_iff mempty_def zero_nat_inf_def)

lemma fmsingleton_finite_multisets: "a \<in> A \<Longrightarrow> fmsingleton a \<in> finite_multisets A"
  by (auto simp: finite_multisets_iff fmsingleton_def zero_nat_inf_def split: if_splits)

lemma mfilter_finite_multisets:
  assumes "M \<in> finite_multisets A"
  shows "mfilter P M \<in> finite_multisets A"
proof -
  have sub: "{x. mfilter P M x \<noteq> 0} \<subseteq> {x. M x \<noteq> 0}"
    by (auto simp: mfilter_def)
  then show ?thesis
    using assms finite_subset[OF sub]
    by (auto simp: finite_multisets_iff mfilter_def zero_nat_inf_def)
qed

subsection \<open>Induction over finite multisets\<close>

text\<open>Every finite multiset is built from \<open>\<emptyset>\<close> by adding one element at a time.\<close>

lemma finite_multisets_induct [consumes 1, case_names empty add]:
  assumes "M \<in> finite_multisets A"
    and P0: "P mempty"
    and Padd: "\<And>M a. M \<in> finite_multisets A \<Longrightarrow> a \<in> A \<Longrightarrow> P M \<Longrightarrow> P (msum M (fmsingleton a))"
  shows "P M"
proof -
  have "\<forall>N. N \<in> finite_multisets A \<longrightarrow> {x. N x \<noteq> 0} \<subseteq> S \<longrightarrow> P N" if "finite S" for S
    using that
  proof (induction S rule: finite_induct)
    case empty
    show ?case
    proof (intro allI impI)
      fix N
      assume "N \<in> finite_multisets A" "{x. N x \<noteq> 0} \<subseteq> {}"
      then have "N = mempty"
        by (auto simp: mempty_def fun_eq_iff)
      then show "P N"
        using P0 by simp
    qed
  next
    case (insert a S)
    have "\<forall>N. N \<in> finite_multisets A \<longrightarrow> {x. N x \<noteq> 0} \<subseteq> insert a S \<longrightarrow>
        nat_of (N a) = n \<longrightarrow> P N" for n
    proof (induction n)
      case 0
      show ?case
      proof (intro allI impI)
        fix N
        assume N: "N \<in> finite_multisets A" "{x. N x \<noteq> 0} \<subseteq> insert a S" "nat_of (N a) = 0"
        then have "{x. N x \<noteq> 0} \<subseteq> S"
          using nat_of_zero_iff[OF N(1), of a] by auto
        then show "P N"
          using insert.IH N(1) by blast
      qed
    next
      case (Suc n)
      show ?case
      proof (intro allI impI)
        fix N
        assume N: "N \<in> finite_multisets A" "{x. N x \<noteq> 0} \<subseteq> insert a S" "nat_of (N a) = Suc n"
        have Na: "N a \<noteq> 0"
          using N(3) nat_of_zero_iff[OF N(1), of a] by simp
        then have a: "a \<in> A"
          using N(1) by (auto simp: finite_multisets_iff)
        define N' where "N' = N(a := Fin n)"
        have sub: "{x. N' x \<noteq> 0} \<subseteq> {x. N x \<noteq> 0}"
          using Na by (auto simp: N'_def)
        then have N': "N' \<in> finite_multisets A"
          using N(1) a finite_subset[OF sub] by (auto simp: finite_multisets_iff N'_def)
        have "{x. N' x \<noteq> 0} \<subseteq> insert a S"
          using sub N(2) by blast
        moreover have "nat_of (N' a) = n"
          by (simp add: N'_def)
        ultimately have "P N'"
          using Suc.IH N' by blast
        moreover have "N = msum N' (fmsingleton a)"
          using N(3)
          by (intro fm_eqI[OF N(1) msum_finite_multisets[OF N' fmsingleton_finite_multisets[OF a]]])
            (simp add: nat_of_msum[OF N' fmsingleton_finite_multisets[OF a]] nat_of_fmsingleton,
             simp add: N'_def)
        ultimately show "P N"
          using Padd[OF N' a] by simp
      qed
    qed
    then show ?case
      by blast
  qed
  moreover have "finite {x. M x \<noteq> 0}"
    using assms(1) by (simp add: finite_multisets_iff)
  ultimately show ?thesis
    using assms(1) by blast
qed

text\<open>Simplification rules that turn equations between finite multisets over \<open>A\<close> into
  arithmetic on multiplicities.\<close>

lemmas fm_simps = nat_of_msum nat_of_mdiff nat_of_mfilter nat_of_fmsingleton nat_of_mempty
  msum_finite_multisets mdiff_finite_multisets mfilter_finite_multisets
  mempty_finite_multisets fmsingleton_finite_multisets

subsection \<open>A step of \<open>\<succ>\<^sub>m\<^sub>u\<^sub>l\<close> is a sequence of one-element steps\<close>

text\<open>Replace the elements of \<open>X\<close> one at a time: the last added element \<open>a\<close> of \<open>X\<close> is
  replaced by the part of \<open>Y\<close> below \<open>a\<close>, and the rest of \<open>Y\<close> is handled by induction.\<close>

lemma mul_step_trancl:
  assumes "X \<in> finite_multisets A" "X \<noteq> mempty"
    and "I \<in> finite_multisets A" "Y \<in> finite_multisets A"
    and "\<forall>y. member_mul y Y \<longrightarrow> (\<exists>x. member_mul x X \<and> (x, y) \<in> r)"
  shows "(msum I Y, msum I X) \<in> (mul_step A r)\<^sup>+"
  using assms
proof (induction X arbitrary: I Y rule: finite_multisets_induct)
  case empty
  then show ?case
    by simp
next
  case (add X a)
  note I = add.prems(2) and Y = add.prems(3) and X = add.hyps(1) and a = add.hyps(2)
  let ?Ya = "mfilter (\<lambda>y. (a, y) \<in> r) Y" and ?Y' = "mfilter (\<lambda>y. (a, y) \<notin> r) Y"
  have Ya: "?Ya \<in> finite_multisets A" and Y': "?Y' \<in> finite_multisets A"
    using Y by (simp_all add: mfilter_finite_multisets)
  have step: "(msum (msum I X) ?Ya, msum I (msum X (fmsingleton a))) \<in> mul_step A r"
    using mul_stepI[OF msum_finite_multisets[OF I X] a Ya]
    by (simp add: msum_assoc member_mul_nat_of[OF Ya] nat_of_mfilter)
  have dom': "\<forall>y. member_mul y ?Y' \<longrightarrow> (\<exists>x. member_mul x X \<and> (x, y) \<in> r)"
  proof (intro allI impI)
    fix y
    assume "member_mul y ?Y'"
    then have y: "(a, y) \<notin> r" "member_mul y Y"
      by (simp_all add: member_mul_nat_of[OF Y'] member_mul_nat_of[OF Y] nat_of_mfilter
          split: if_splits)
    then obtain x where "member_mul x (msum X (fmsingleton a))" "(x, y) \<in> r"
      using add.prems(4) by blast
    then show "\<exists>x. member_mul x X \<and> (x, y) \<in> r"
      using y(1) X a
      by (auto simp: member_mul_nat_of fm_simps split: if_splits)
  qed
  have Ysplit: "msum I Y = msum (msum I ?Ya) ?Y'"
    using I Y by (intro fm_eqI) (simp_all add: fm_simps)
  show ?case
  proof (cases "X = mempty")
    case True
    have "?Y' = mempty"
    proof (rule fm_eqI[OF Y' mempty_finite_multisets])
      fix y
      have "\<not> member_mul y ?Y'"
        using dom' by (simp add: True member_mul_nat_of[OF mempty_finite_multisets] nat_of_mempty)
      then show "nat_of (?Y' y) = nat_of (mempty y)"
        by (simp add: member_mul_nat_of[OF Y'] nat_of_mempty)
    qed
    then have eq: "msum I Y = msum (msum I X) ?Ya"
      by (simp add: Ysplit True msum_mempty mempty_msum)
    show ?thesis
      unfolding eq by (rule r_into_trancl'[OF step])
  next
    case False
    have "(msum (msum I ?Ya) ?Y', msum (msum I ?Ya) X) \<in> (mul_step A r)\<^sup>+"
      using add.IH[OF False msum_finite_multisets[OF I Ya] Y' dom'] .
    moreover have "msum (msum I ?Ya) X = msum (msum I X) ?Ya"
      by (simp add: msum_ac)
    ultimately have "(msum I Y, msum (msum I X) ?Ya) \<in> (mul_step A r)\<^sup>+"
      by (simp only: Ysplit)
    then show ?thesis
      using r_into_trancl'[OF step] by (rule trancl_trans)
  qed
qed
subsection \<open>One-element steps are well-founded\<close>

lemma mul_step_finite_multisets:
  assumes "(N, M) \<in> mul_step A r"
  shows "N \<in> finite_multisets A" "M \<in> finite_multisets A"
  using assms unfolding mul_step_def by (auto simp: fm_simps)

text\<open>If \<open>N\<close> is one step below \<open>M\<^sub>0 \<oplus> \<lbrakk>a\<rbrakk>\<close>, then either the step happens inside \<open>M\<^sub>0\<close>,
  or it is the occurrence of \<open>a\<close> that is replaced.\<close>

lemma mul_step_add_cases:
  assumes "(N, msum M\<^sub>0 (fmsingleton a)) \<in> mul_step A r"
    and M\<^sub>0: "M\<^sub>0 \<in> finite_multisets A" and a: "a \<in> A"
  shows "(\<exists>M. (M, M\<^sub>0) \<in> mul_step A r \<and> N = msum M (fmsingleton a)) \<or>
    (\<exists>K. K \<in> finite_multisets A \<and> (\<forall>b. member_mul b K \<longrightarrow> (a, b) \<in> r) \<and> N = msum M\<^sub>0 K)"
proof -
  obtain M\<^sub>1 a' K where M\<^sub>1: "M\<^sub>1 \<in> finite_multisets A" and a': "a' \<in> A"
    and K: "K \<in> finite_multisets A"
    and eq: "msum M\<^sub>0 (fmsingleton a) = msum M\<^sub>1 (fmsingleton a')" and N: "N = msum M\<^sub>1 K"
    and dom: "\<forall>b. member_mul b K \<longrightarrow> (a', b) \<in> r"
    using assms(1) unfolding mul_step_def by blast
  have pt: "nat_of (M\<^sub>0 x) + (if x = a then 1 else 0) = nat_of (M\<^sub>1 x) + (if x = a' then 1 else 0)"
    for x
    using arg_cong[OF eq, of "\<lambda>M. nat_of (M x)"] M\<^sub>0 a M\<^sub>1 a' by (simp add: fm_simps)
  show ?thesis
  proof (cases "a = a'")
    case True
    have "M\<^sub>0 = M\<^sub>1"
      using pt True by (intro fm_eqI[OF M\<^sub>0 M\<^sub>1]) simp
    then show ?thesis
      using K dom N True by blast
  next
    case False
    let ?K\<^sub>0 = "mdiff M\<^sub>0 (fmsingleton a')"
    have K\<^sub>0: "?K\<^sub>0 \<in> finite_multisets A"
      by (rule mdiff_finite_multisets[OF M\<^sub>0])
    have "nat_of (M\<^sub>0 a') = nat_of (M\<^sub>1 a') + 1"
      using pt[of a'] False by simp
    then have M\<^sub>0_eq: "M\<^sub>0 = msum ?K\<^sub>0 (fmsingleton a')"
      using M\<^sub>0 a' by (intro fm_eqI) (auto simp: fm_simps)
    have a'_in: "nat_of (M\<^sub>0 a') = nat_of (M\<^sub>1 a') + 1"
      using pt[of a'] False by simp
    have "N = msum (msum ?K\<^sub>0 K) (fmsingleton a)"
    proof (rule fm_eqI)
      show "N \<in> finite_multisets A" "msum (msum ?K\<^sub>0 K) (fmsingleton a) \<in> finite_multisets A"
        using M\<^sub>1 K K\<^sub>0 a unfolding N by (simp_all add: fm_simps)
      fix x
      show "nat_of (N x) = nat_of (msum (msum ?K\<^sub>0 K) (fmsingleton a) x)"
        using pt[of x] a'_in False M\<^sub>0 M\<^sub>1 K a a' unfolding N
        by (cases "x = a"; cases "x = a'") (simp_all add: fm_simps)
    qed
    moreover have "(msum ?K\<^sub>0 K, M\<^sub>0) \<in> mul_step A r"
      using mul_stepI[OF K\<^sub>0 a' K dom] M\<^sub>0_eq by simp
    ultimately show ?thesis
      by blast
  qed
qed

text\<open>We show that every finite multiset is \<^emph>\<open>accessible\<close>, i.e. there is no infinite descending
  chain of one-element steps starting from it. First: if \<open>M\<^sub>0\<close> is accessible, all
  one-element steps below \<open>M\<^sub>0\<close> stay accessible after adding \<open>a\<close>, and adding any \<open>b\<close> below \<open>a\<close>
  preserves accessibility, then \<open>M\<^sub>0 \<oplus> \<lbrakk>a\<rbrakk>\<close> is accessible.\<close>

lemma acc_msum_fmsingleton_aux:
  assumes M\<^sub>0: "M\<^sub>0 \<in> Wellfounded.acc (mul_step A r)" "M\<^sub>0 \<in> finite_multisets A" and a: "a \<in> A"
    and H1: "\<forall>M. (M, M\<^sub>0) \<in> mul_step A r \<longrightarrow> msum M (fmsingleton a) \<in> Wellfounded.acc (mul_step A r)"
    and H2: "\<forall>b. (a, b) \<in> r \<longrightarrow> b \<in> A \<longrightarrow> (\<forall>M. M \<in> Wellfounded.acc (mul_step A r) \<longrightarrow>
      M \<in> finite_multisets A \<longrightarrow> msum M (fmsingleton b) \<in> Wellfounded.acc (mul_step A r))"
  shows "msum M\<^sub>0 (fmsingleton a) \<in> Wellfounded.acc (mul_step A r)"
proof -
  have K: "msum M\<^sub>0 K \<in> Wellfounded.acc (mul_step A r)"
    if "K \<in> finite_multisets A" "\<forall>b. member_mul b K \<longrightarrow> (a, b) \<in> r" for K
    using that
  proof (induction K rule: finite_multisets_induct)
    case empty
    then show ?case
      using M\<^sub>0(1) by (simp add: msum_mempty)
  next
    case (add K b)
    have b: "fmsingleton b \<in> finite_multisets A"
      using add.hyps(2) by (rule fmsingleton_finite_multisets)
    have "member_mul b (msum K (fmsingleton b))"
      using add.hyps b by (simp add: member_mul_nat_of fm_simps)
    then have ab: "(a, b) \<in> r"
      using add.prems by blast
    have "\<forall>c. member_mul c K \<longrightarrow> (a, c) \<in> r"
      using add.prems add.hyps b by (auto simp: member_mul_nat_of fm_simps)
    then have "msum M\<^sub>0 K \<in> Wellfounded.acc (mul_step A r)"
      by (rule add.IH)
    then have "msum (msum M\<^sub>0 K) (fmsingleton b) \<in> Wellfounded.acc (mul_step A r)"
      using H2 ab add.hyps(2) msum_finite_multisets[OF M\<^sub>0(2) add.hyps(1)] by blast
    then show ?case
      by (simp add: msum_assoc)
  qed
  show ?thesis
  proof (rule accI)
    fix N
    assume "(N, msum M\<^sub>0 (fmsingleton a)) \<in> mul_step A r"
    then show "N \<in> Wellfounded.acc (mul_step A r)"
      using mul_step_add_cases[OF _ M\<^sub>0(2) a] H1 K by blast
  qed
qed

text\<open>Second, by induction on accessibility of \<open>M\<close>: if adding any \<open>b\<close> below \<open>a\<close> preserves
  accessibility, then so does adding \<open>a\<close>.\<close>

lemma acc_msum_fmsingleton_step:
  assumes H2: "\<forall>b. (a, b) \<in> r \<longrightarrow> b \<in> A \<longrightarrow> (\<forall>M. M \<in> Wellfounded.acc (mul_step A r) \<longrightarrow>
      M \<in> finite_multisets A \<longrightarrow> msum M (fmsingleton b) \<in> Wellfounded.acc (mul_step A r))"
    and a: "a \<in> A" and "M \<in> Wellfounded.acc (mul_step A r)"
  shows "M \<in> finite_multisets A \<longrightarrow> msum M (fmsingleton a) \<in> Wellfounded.acc (mul_step A r)"
  using assms(3)
proof (induction M rule: acc.induct)
  case (accI M)
  note hyps = this
  show ?case
  proof
    assume M: "M \<in> finite_multisets A"
    have "M \<in> Wellfounded.acc (mul_step A r)"
      using hyps(1) by (rule acc.accI)
    moreover have "\<forall>N. (N, M) \<in> mul_step A r \<longrightarrow> msum N (fmsingleton a) \<in> Wellfounded.acc (mul_step A r)"
      using hyps(2) mul_step_finite_multisets(1) by blast
    ultimately show "msum M (fmsingleton a) \<in> Wellfounded.acc (mul_step A r)"
      using acc_msum_fmsingleton_aux[OF _ M a _ H2] by blast
  qed
qed

text\<open>Third, by well-founded induction on \<open>a\<close>: adding any \<open>a \<in> A\<close> preserves accessibility.\<close>

lemma acc_msum_fmsingleton:
  assumes "wf (r\<inverse>)"
  shows "a \<in> A \<longrightarrow> (\<forall>M. M \<in> Wellfounded.acc (mul_step A r) \<longrightarrow> M \<in> finite_multisets A \<longrightarrow>
    msum M (fmsingleton a) \<in> Wellfounded.acc (mul_step A r))"
proof (induction a rule: wf_induct[OF assms])
  case (1 a)
  then have H2: "\<forall>b. (a, b) \<in> r \<longrightarrow> b \<in> A \<longrightarrow> (\<forall>M. M \<in> Wellfounded.acc (mul_step A r) \<longrightarrow>
      M \<in> finite_multisets A \<longrightarrow> msum M (fmsingleton b) \<in> Wellfounded.acc (mul_step A r))"
    by auto
  show ?case
    using acc_msum_fmsingleton_step[OF H2] by blast
qed

lemma mempty_acc: "mempty \<in> Wellfounded.acc (mul_step A r)"
proof (rule accI)
  fix N
  assume "(N, mempty) \<in> mul_step A r"
  then obtain M\<^sub>0 a where M\<^sub>0: "M\<^sub>0 \<in> finite_multisets A" and a: "a \<in> A"
    and eq: "mempty = msum M\<^sub>0 (fmsingleton a)"
    unfolding mul_step_def by blast
  have "nat_of (mempty a) = nat_of (msum M\<^sub>0 (fmsingleton a) a)"
    by (simp only: eq)
  then show "N \<in> Wellfounded.acc (mul_step A r)"
    using M\<^sub>0 a by (simp add: fm_simps)
qed

text\<open>Finally, every multiset is accessible: the finite ones by induction, and the others
  because no step leads to them.\<close>

lemma wf_mul_step:
  assumes "wf (r\<inverse>)"
  shows "wf (mul_step A r)"
proof -
  have "M \<in> Wellfounded.acc (mul_step A r)" if "M \<in> finite_multisets A" for M
    using that
  proof (induction M rule: finite_multisets_induct)
    case empty
    show ?case
      by (rule mempty_acc)
  next
    case (add M a)
    then show ?case
      using acc_msum_fmsingleton[OF assms] by blast
  qed
  moreover have "M \<in> Wellfounded.acc (mul_step A r)" if "M \<notin> finite_multisets A" for M
    using that by (auto intro: accI dest: mul_step_finite_multisets(2))
  ultimately show ?thesis
    by (auto simp: wf_iff_acc)
qed

end

subsection \<open>Theorem 2.3.12\<close>

text\<open>Each step \<open>M\<^sub>1 \<succ>\<^sub>m\<^sub>u\<^sub>l M\<^sub>2\<close> is a sequence of one-element steps from \<open>M\<^sub>1\<close> down to \<open>M\<^sub>2\<close>,
  since \<open>M\<^sub>1 = (M\<^sub>1 \<setminus> X) \<oplus> X\<close> and \<open>M\<^sub>2 = (M\<^sub>1 \<setminus> X) \<oplus> Y\<close>.\<close>

lemma mul_ext_imp_mul_step:
  assumes "(M\<^sub>1, M\<^sub>2) \<in> mul_ext A r"
  shows "(M\<^sub>2, M\<^sub>1) \<in> (mul_step A r)\<^sup>+"
proof -
  obtain X Y where M\<^sub>1: "M\<^sub>1 \<in> finite_multisets A"
    and X: "X \<in> finite_multisets A" and Y: "Y \<in> finite_multisets A"
    and ne: "mempty \<noteq> X" and sub: "msubseteq X M\<^sub>1" and eq: "M\<^sub>2 = msum (mdiff M\<^sub>1 X) Y"
    and dom: "\<forall>y. member_mul y Y \<longrightarrow> (\<exists>x. member_mul x X \<and> (x, y) \<in> r)"
    using assms unfolding mul_ext_def by blast
  have I: "mdiff M\<^sub>1 X \<in> finite_multisets A"
    by (rule mdiff_finite_multisets[OF M\<^sub>1])
  have "M\<^sub>1 = msum (mdiff M\<^sub>1 X) X"
  proof (rule fm_eqI[OF M\<^sub>1 msum_finite_multisets[OF I X]])
    fix x
    have "nat_of (X x) \<le> nat_of (M\<^sub>1 x)"
      using sub msubseteq_nat_of[OF X M\<^sub>1] by blast
    then show "nat_of (M\<^sub>1 x) = nat_of (msum (mdiff M\<^sub>1 X) X x)"
      by (simp add: nat_of_msum[OF I X] nat_of_mdiff[OF M\<^sub>1 X])
  qed
  then show ?thesis
    using mul_step_trancl[OF X _ I Y dom] ne eq by auto
qed

text\<open>Conversely, \<open>a \<succ> b\<close> gives \<open>\<lbrakk>a\<rbrakk> \<succ>\<^sub>m\<^sub>u\<^sub>l \<lbrakk>b\<rbrakk>\<close>, so a descending chain in \<open>A\<close> gives one of singletons.\<close>

lemma fmsingleton_mul_ext:
  assumes "a \<in> A" "b \<in> A" "(a, b) \<in> r"
  shows "(fmsingleton a, fmsingleton b) \<in> mul_ext A r"
proof -
  have fm: "fmsingleton a \<in> finite_multisets A" "fmsingleton b \<in> finite_multisets A"
    using assms(1,2) by (simp_all add: fmsingleton_finite_multisets)
  have "\<exists>X \<in> finite_multisets A. \<exists>Y \<in> finite_multisets A. mempty \<noteq> X \<and>
      msubseteq X (fmsingleton a) \<and> fmsingleton b = msum (mdiff (fmsingleton a) X) Y \<and>
      (\<forall>y. member_mul y Y \<longrightarrow> (\<exists>x. member_mul x X \<and> (x, y) \<in> r))"
  proof (rule bexI[of _ "fmsingleton a"], rule bexI[of _ "fmsingleton b"])
    have "fmsingleton b = msum (mdiff (fmsingleton a) (fmsingleton a)) (fmsingleton b)"
      by (simp add: fun_eq_iff msum_def mdiff_def fmsingleton_def zero_nat_inf_def)
    moreover have "mempty \<noteq> fmsingleton a"
      by (auto simp: fun_eq_iff mempty_def fmsingleton_def zero_nat_inf_def)
    moreover have "msubseteq (fmsingleton a) (fmsingleton a)"
      by (simp add: msubseteq_def fmsingleton_def zero_nat_inf_def)
    moreover have "\<forall>y. member_mul y (fmsingleton b) \<longrightarrow>
        (\<exists>x. member_mul x (fmsingleton a) \<and> (x, y) \<in> r)"
      using assms(3) by (simp add: member_mul_iff fmsingleton_def zero_nat_inf_def)
    ultimately show "mempty \<noteq> fmsingleton a \<and> msubseteq (fmsingleton a) (fmsingleton a) \<and>
        fmsingleton b = msum (mdiff (fmsingleton a) (fmsingleton a)) (fmsingleton b) \<and>
        (\<forall>y. member_mul y (fmsingleton b) \<longrightarrow> (\<exists>x. member_mul x (fmsingleton a) \<and> (x, y) \<in> r))"
      by simp
  qed (fact fm)+
  with fm show ?thesis
    unfolding mul_ext_def by simp
qed

text\<open>Theorem 2.3.12. For an ordering \<open>\<succ>\<close> on \<open>A\<close>, the finite multiset extension is
  well-founded if and only if \<open>\<succ>\<close> is. (The proof does not need \<open>\<succ>\<close> to be a partial ordering.)\<close>

theorem well_founded_mul_ext:
  assumes "r \<subseteq> A \<times> A"
  shows "well_founded (mul_ext A r) \<longleftrightarrow> well_founded r"
proof
  assume "well_founded r"
  then have "wf ((mul_step A r)\<^sup>+)"
    by (simp add: well_founded_iff_wf wf_mul_step wf_trans_cl)
  moreover have "(mul_ext A r)\<inverse> \<subseteq> (mul_step A r)\<^sup>+"
    by (auto intro: mul_ext_imp_mul_step)
  ultimately show "well_founded (mul_ext A r)"
    unfolding well_founded_iff_wf by (rule wf_subset)
next
  assume "well_founded (mul_ext A r)"
  then have "wf (inv_image ((mul_ext A r)\<inverse>) fmsingleton)"
    by (simp add: well_founded_iff_wf)
  moreover have "r\<inverse> \<subseteq> inv_image ((mul_ext A r)\<inverse>) fmsingleton"
    using assms by (auto simp: inv_image_def intro: fmsingleton_mul_ext)
  ultimately show "well_founded r"
    unfolding well_founded_iff_wf by (rule wf_subset)
qed


end
