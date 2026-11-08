theory Parallel_Closed
  imports Confluence
begin

section \<open>Beyond orthogonality\<close>

text \<open>Baader \& Nipkow, Section 6.4: Huet's Parallel Closure Theorem.\<close>

subsection \<open>Parallel closed systems\<close>

text \<open>Definition 6.4.5. Note the orientation: \<open>u\<^sub>2 \<rightrightarrows> u\<^sub>1\<close> for every critical pair
  \<open>\<langle>u\<^sub>1, u\<^sub>2\<rangle> = \<langle>\<theta>r\<^sub>1, (\<theta>l\<^sub>1)[\<theta>r\<^sub>2]\<^sub>p\<rangle>\<close>.\<close>

definition parallel_closed :: "('f, 'v) term rel \<Rightarrow> bool" where
  "parallel_closed R \<longleftrightarrow> (\<forall>(u\<^sub>1, u\<^sub>2) \<in> CP R. (u\<^sub>2, u\<^sub>1) \<in> par_rstep R)"

text \<open>A left-linear system all of whose critical pairs are trivial is called weakly
  orthogonal (remark after Example 6.4.10).\<close>

definition weakly_orthogonal :: "('f, 'v) term rel \<Rightarrow> bool" where
  "weakly_orthogonal R \<longleftrightarrow> left_linear R \<and> (\<forall>(u, v) \<in> CP R. u = v)"

subsection \<open>The overlap of two parallel steps\<close>

text \<open>Definition 6.4.6. For a peak \<open>t\<^sub>0 \<leftleftarrows>\<^sup>P\<^sup>0 s \<rightrightarrows>\<^sup>P\<^sup>1 t\<^sub>1\<close>, the overlap \<open>P\<^sub>0 \<sqinter> P\<^sub>1\<close> consists of the
  redex positions of each step that lie below (or at) a redex position of the other step, and
  the size of the overlap is \<open>|s|\<^sub>P\<^sub>0\<^sub>\<sqinter>\<^sub>P\<^sub>1| := \<Sigma>\<^sub>p\<^sub>\<in>\<^sub>P\<^sub>0\<^sub>\<sqinter>\<^sub>P\<^sub>1 |s|\<^sub>p|\<close>.\<close>

definition overlap :: "pos set \<Rightarrow> pos set \<Rightarrow> pos set" where
  "overlap P\<^sub>0 P\<^sub>1 = {p \<in> P\<^sub>0. \<exists>q \<in> P\<^sub>1. q \<le>\<^sub>p p} \<union> {q \<in> P\<^sub>1. \<exists>p \<in> P\<^sub>0. p \<le>\<^sub>p q}"

definition overlap_size :: "('f, 'v) term \<Rightarrow> pos set \<Rightarrow> pos set \<Rightarrow> nat" where
  "overlap_size s P\<^sub>0 P\<^sub>1 = (\<Sum>p \<in> overlap P\<^sub>0 P\<^sub>1. term_size (s |_ p))"

lemma overlap_sym: "overlap P\<^sub>0 P\<^sub>1 = overlap P\<^sub>1 P\<^sub>0"
  unfolding overlap_def by blast

lemma overlap_size_sym: "overlap_size s P\<^sub>0 P\<^sub>1 = overlap_size s P\<^sub>1 P\<^sub>0"
  unfolding overlap_size_def by (simp add: overlap_sym)

lemma finite_overlap: "P\<^sub>0 \<subseteq> poss s \<Longrightarrow> P\<^sub>1 \<subseteq> poss s \<Longrightarrow> finite (overlap P\<^sub>0 P\<^sub>1)"
  unfolding overlap_def by (auto intro: finite_subset)

lemma term_size_pos: "0 < term_size t"
proof -
  have "[] \<in> poss t" by (cases t) (auto simp: poss.simps(2))
  then have "poss t \<noteq> {}" by blast
  then show ?thesis unfolding term_size_def by (simp add: card_gt_0_iff)
qed

text \<open>The subterms at a parallel set of positions are disjoint parts of the term.\<close>

lemma sum_term_size_parallel:
  assumes "parallel_set P" and "P \<subseteq> poss t"
  shows "(\<Sum>p \<in> P. term_size (t |_ p)) \<le> term_size t"
proof -
  let ?A = "\<lambda>p. (@) p ` poss (t |_ p)"
  have fin: "finite P" using assms(2) by (rule finite_subset) simp
  have card: "card (?A p) = term_size (t |_ p)" for p
    by (simp add: term_size_def card_image inj_on_def)
  have disj: "?A p \<inter> ?A q = {}" if "p \<in> P" "q \<in> P" "p \<noteq> q" for p q
  proof -
    have "p \<parallel> q" using parallel_setD[OF assms(1) that] .
    then show ?thesis
      using prefix_le_cases[of p _ q] unfolding parallel_def by (auto simp: prefix_le_def)
  qed
  have "(\<Union>p \<in> P. ?A p) \<subseteq> poss t" using assms(2) poss_subt_at by blast
  then have "card (\<Union>p \<in> P. ?A p) \<le> term_size t"
    unfolding term_size_def by (intro card_mono) auto
  moreover have "card (\<Union>p \<in> P. ?A p) = (\<Sum>p \<in> P. card (?A p))"
    using fin disj by (intro card_UN_disjoint) auto
  ultimately show ?thesis using card by simp
qed

text \<open>Lemma 6.4.7. The size of the overlap is bounded by the total size of the redexes of
  either step.\<close>

lemma overlap_size_le:
  assumes P0: "parallel_set P\<^sub>0" "P\<^sub>0 \<subseteq> poss s" and P1: "parallel_set P\<^sub>1" "P\<^sub>1 \<subseteq> poss s"
  shows "overlap_size s P\<^sub>0 P\<^sub>1 \<le> (\<Sum>p \<in> P\<^sub>0. term_size (s |_ p))"
proof -
  define Y where "Y p = {y \<in> overlap P\<^sub>0 P\<^sub>1. p \<le>\<^sub>p y}" for p
  have fin0: "finite P\<^sub>0" using P0(2) by (rule finite_subset) simp
  have finY: "finite (Y p)" for p
    using finite_overlap[OF P0(2) P1(2)] unfolding Y_def by simp
  have cover: "overlap P\<^sub>0 P\<^sub>1 = (\<Union>p \<in> P\<^sub>0. Y p)"
    unfolding Y_def overlap_def by (auto intro: prefix_le_refl)
  have disj: "Y p \<inter> Y p' = {}" if "p \<in> P\<^sub>0" "p' \<in> P\<^sub>0" "p \<noteq> p'" for p p'
  proof -
    have "p \<parallel> p'" using parallel_setD[OF P0(1) that] .
    then show ?thesis using prefix_le_cases unfolding Y_def parallel_def by blast
  qed
  have Ypar: "parallel_set (Y p)" if p: "p \<in> P\<^sub>0" for p
    unfolding parallel_set_def
  proof (intro ballI)
    fix y y' assume y: "y \<in> Y p" and y': "y' \<in> Y p"
    have eq: "z = p" if "z \<in> Y p" "z \<in> P\<^sub>0" for z
      using that p P0(1) unfolding Y_def parallel_set_def parallel_def by blast
    have in1: "z \<in> P\<^sub>1" if "z \<in> Y p" "z \<noteq> p" for z
      using that eq unfolding Y_def overlap_def by blast
    have same: "z = z'" if z: "z \<in> Y p" "z = p" and z': "z' \<in> Y p" "z' \<noteq> p" for z z'
    proof -
      have y'1: "z' \<in> P\<^sub>1" "p \<le>\<^sub>p z'" using in1[OF z'] z'(1) unfolding Y_def by auto
      have "p = z'"
      proof (cases "p \<in> P\<^sub>1")
        case True
        then show ?thesis using y'1 P1(1) unfolding parallel_set_def parallel_def by blast
      next
        case False
        then obtain q where q: "q \<in> P\<^sub>1" "q \<le>\<^sub>p p" using z unfolding Y_def overlap_def by blast
        then have "q = z'" using y'1 P1(1) prefix_le_trans
          unfolding parallel_set_def parallel_def by blast
        then show ?thesis using q(2) y'1(2) prefix_le_antisym by blast
      qed
      then show ?thesis using z(2) by simp
    qed
    have "y \<parallel> y' \<or> y = y'" if "y \<noteq> p" "y' \<noteq> p"
      using in1[OF y that(1)] in1[OF y' that(2)] P1(1) unfolding parallel_set_def by blast
    then show "y \<parallel> y' \<or> y = y'" using same[OF y _ y'] same[OF y' _ y] by blast
  qed
  have Ybound: "(\<Sum>y \<in> Y p. term_size (s |_ y)) \<le> term_size (s |_ p)" if p: "p \<in> P\<^sub>0" for p
  proof -
    define X where "X = {x. p @ x \<in> Y p}"
    have Yp: "Y p = (@) p ` X" unfolding X_def Y_def prefix_le_def by auto
    have Ypos: "Y p \<subseteq> poss s"
      using P0(2) P1(2) unfolding Y_def overlap_def by blast
    have X: "parallel_set X" "X \<subseteq> poss (s |_ p)"
      unfolding X_def using parallel_set_below[OF Ypar[OF p]] Ypos P0(2) p poss_subt_at by blast+
    have "(\<Sum>y \<in> Y p. term_size (s |_ y)) = (\<Sum>x \<in> X. term_size (s |_ (p @ x)))"
      unfolding Yp by (simp add: sum.reindex inj_on_def)
    also have "\<dots> = (\<Sum>x \<in> X. term_size (s |_ p |_ x))"
      using Ypos unfolding X_def by (intro sum.cong refl) (auto simp: subt_at_append)
    also have "\<dots> \<le> term_size (s |_ p)" using X by (rule sum_term_size_parallel)
    finally show ?thesis .
  qed
  have "overlap_size s P\<^sub>0 P\<^sub>1 = (\<Sum>p \<in> P\<^sub>0. \<Sum>y \<in> Y p. term_size (s |_ y))"
    unfolding overlap_size_def cover using fin0 finY disj by (intro sum.UNION_disjoint) auto
  also have "\<dots> \<le> (\<Sum>p \<in> P\<^sub>0. term_size (s |_ p))" using Ybound by (intro sum_mono) auto
  finally show ?thesis .
qed

text \<open>If one of the steps contracts the redex at the root, every redex of the other step
  belongs to the overlap.\<close>

lemma overlap_size_root:
  assumes "P\<^sub>1 \<subseteq> poss s"
  shows "(\<Sum>p \<in> P\<^sub>1. term_size (s |_ p)) \<le> overlap_size s {[]} P\<^sub>1"
  unfolding overlap_size_def
  using assms finite_overlap[of "{[]}" s P\<^sub>1] by (intro sum_mono2) (auto simp: overlap_def)

text \<open>Passing to an outermost position does not increase the size of the overlap.\<close>

lemma overlap_size_outermost:
  assumes "P\<^sub>0 \<subseteq> poss s" and "P\<^sub>1 \<subseteq> poss s"
  shows "overlap_size (s |_ q) {p. q @ p \<in> P\<^sub>0} {p. q @ p \<in> P\<^sub>1} \<le> overlap_size s P\<^sub>0 P\<^sub>1"
proof -
  let ?O = "overlap {p. q @ p \<in> P\<^sub>0} {p. q @ p \<in> P\<^sub>1}"
  have sub: "(@) q ` ?O \<subseteq> overlap P\<^sub>0 P\<^sub>1"
  proof (rule image_subsetI)
    fix x assume "x \<in> ?O"
    then consider (a) y where "q @ x \<in> P\<^sub>0" "q @ y \<in> P\<^sub>1" "y \<le>\<^sub>p x"
      | (b) y where "q @ x \<in> P\<^sub>1" "q @ y \<in> P\<^sub>0" "y \<le>\<^sub>p x"
      unfolding overlap_def by blast
    then show "q @ x \<in> overlap P\<^sub>0 P\<^sub>1"
    proof cases
      case a
      then have "q @ y \<le>\<^sub>p q @ x" by (auto simp: prefix_le_def)
      then show ?thesis using a unfolding overlap_def by blast
    next
      case b
      then have "q @ y \<le>\<^sub>p q @ x" by (auto simp: prefix_le_def)
      then show ?thesis using b unfolding overlap_def by blast
    qed
  qed
  have pos: "q @ x \<in> poss s" if "x \<in> ?O" for x
    using that assms unfolding overlap_def by blast
  have "overlap_size (s |_ q) {p. q @ p \<in> P\<^sub>0} {p. q @ p \<in> P\<^sub>1} = (\<Sum>x \<in> ?O. term_size (s |_ (q @ x)))"
    unfolding overlap_size_def using pos by (intro sum.cong refl) (simp add: subt_at_append)
  also have "\<dots> = (\<Sum>y \<in> (@) q ` ?O. term_size (s |_ y))"
    by (simp add: sum.reindex inj_on_def)
  also have "\<dots> \<le> overlap_size s P\<^sub>0 P\<^sub>1"
    unfolding overlap_size_def using sub finite_overlap[OF assms] by (intro sum_mono2) auto
  finally show ?thesis .
qed

subsection \<open>The Parallel Closure Theorem\<close>

context TRS_inf
begin

text \<open>The core of the proof of Theorem 6.4.8: a peak in which one of the steps contracts the
  redex \<open>\<sigma>(l)\<close> at the root, assuming the theorem for all peaks with a smaller overlap.
  If no redex of the other step lies at a non-variable position of \<open>l\<close>, Lemma 6.4.4 applies as in
  the orthogonal case. Otherwise such a redex at \<open>q\<close> forms a critical pair with the root redex;
  contracting it first and using parallel closedness, we obtain a peak
  \<open>t\<^sub>1 \<leftleftarrows>\<^sup>P\<^sup>1\<^sup>-\<^sup>{\<^sup>q\<^sup>} s' \<rightrightarrows> t\<^sub>0\<close> with a smaller overlap.\<close>

lemma parallel_closed_root_peak:
  assumes ll: "left_linear R" and pc: "parallel_closed R"
    and step0: "par_rstep_at R P\<^sub>0 s t\<^sub>0" and step1: "par_rstep_at R P\<^sub>1 s t\<^sub>1" and root: "[] \<in> P\<^sub>0"
    and IH: "\<And>s' P\<^sub>0' P\<^sub>1' t\<^sub>0' t\<^sub>1'. overlap_size s' P\<^sub>0' P\<^sub>1' < overlap_size s P\<^sub>0 P\<^sub>1 \<Longrightarrow>
      par_rstep_at R P\<^sub>0' s' t\<^sub>0' \<Longrightarrow> par_rstep_at R P\<^sub>1' s' t\<^sub>1' \<Longrightarrow>
      \<exists>u. (t\<^sub>0', u) \<in> par_rstep R \<and> (t\<^sub>1', u) \<in> par_rstep R"
  shows "\<exists>u. (t\<^sub>0, u) \<in> par_rstep R \<and> (t\<^sub>1, u) \<in> par_rstep R"
proof -
  from step0 obtain c where P0: "parallel_set P\<^sub>0"
    and redex0: "\<And>p. p \<in> P\<^sub>0 \<Longrightarrow> \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c p = \<sigma> \<cdot> r"
    and t0: "t\<^sub>0 = s\<lbrakk>P\<^sub>0 \<Leftarrow> c\<rbrakk>"
    unfolding par_rstep_at_def by blast
  from step1 obtain c' where P1: "parallel_set P\<^sub>1" "P\<^sub>1 \<subseteq> poss s"
    and redex1: "\<And>p. p \<in> P\<^sub>1 \<Longrightarrow> \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c' p = \<sigma> \<cdot> r"
    and t1: "t\<^sub>1 = s\<lbrakk>P\<^sub>1 \<Leftarrow> c'\<rbrakk>"
    unfolding par_rstep_at_def by blast
  have P0': "P\<^sub>0 = {[]}" using parallel_set_Nil[OF P0 root] .
  obtain l r \<sigma> where R: "(l, r) \<in> R" and seq: "s = \<sigma> \<cdot> l" and c: "c [] = \<sigma> \<cdot> r"
    using redex0[OF root] by auto
  have t0': "t\<^sub>0 = \<sigma> \<cdot> r" using t0 c P0' by (simp add: replace_at_set_singleton)
  have lin: "linear_term l" using ll R unfolding left_linear_def by auto
  show ?thesis
  proof (cases "\<forall>p \<in> P\<^sub>1. p \<in> poss l \<longrightarrow> (\<exists>x. l |_ p = Var x)")
    case True
    text \<open>Case 1: the redexes of the second step lie inside the substitution.\<close>
    then obtain \<tau> where t1': "t\<^sub>1 = \<tau> \<cdot> l" and \<sigma>\<tau>: "\<forall>x \<in> vars l. (\<sigma> x, \<tau> x) \<in> par_rstep R"
      using par_rstep_at_linear[OF lin step1[unfolded seq]] by blast
    have "(t\<^sub>0, \<tau> \<cdot> r) \<in> par_rstep R"
      unfolding t0' using rule_vars[OF R] \<sigma>\<tau> by (intro par_rstep_subst) auto
    moreover have "(t\<^sub>1, \<tau> \<cdot> r) \<in> par_rstep R" unfolding t1' using R by (rule par_rstep_rule)
    ultimately show ?thesis by blast
  next
    case False
    text \<open>Case 2: a redex of the second step at a non-variable position \<open>q\<close> of \<open>l\<close>.\<close>
    then obtain q where q: "q \<in> P\<^sub>1" "q \<in> poss l" and nv: "\<forall>x. l |_ q \<noteq> Var x" by blast
    obtain l' r' \<sigma>' where R': "(l', r') \<in> R" and sq: "s |_ q = \<sigma>' \<cdot> l'" and c'q: "c' q = \<sigma>' \<cdot> r'"
      using redex1[OF q(1)] by blast
    have unif: "\<sigma> \<cdot> (l |_ q) = \<sigma>' \<cdot> l'" using sq seq q(2) by (simp add: subt_at_subst_apply)
    show ?thesis
    proof (cases "q = [] \<and> (l, r) = (l', r')")
      case True
      text \<open>A trivial overlap: both steps contract the same redex.\<close>
      then have l: "\<sigma> \<cdot> l = \<sigma>' \<cdot> l" using unif by simp
      have "\<sigma> \<cdot> r = \<sigma>' \<cdot> r"
        by (intro subst_apply_cong subst_apply_eq_vars[OF l]) (use rule_vars[OF R] in auto)
      moreover have "t\<^sub>1 = \<sigma>' \<cdot> r'"
        using t1 c'q parallel_set_Nil[OF P1(1)] q(1) True by (simp add: replace_at_set_singleton)
      ultimately have "t\<^sub>1 = t\<^sub>0" using t0' True by simp
      then show ?thesis by (intro exI[of _ t\<^sub>0]) simp
    next
      case False
      text \<open>A critical overlap.\<close>
      let ?s' = "s\<lbrakk>q \<leftarrow> c' q\<rbrakk>"
      obtain u\<^sub>1 u\<^sub>2 \<delta> where cp: "(u\<^sub>1, u\<^sub>2) \<in> CP R" and u1: "\<delta> \<cdot> u\<^sub>1 = \<sigma> \<cdot> r"
        and u2: "\<delta> \<cdot> u\<^sub>2 = (\<sigma> \<cdot> l)\<lbrakk>q \<leftarrow> \<sigma>' \<cdot> r'\<rbrakk>"
        using overlap_imp_CP[OF infinite_vars R R' q(2) nv unif] False by blast
      have "(u\<^sub>2, u\<^sub>1) \<in> par_rstep R" using pc cp unfolding parallel_closed_def by blast
      then have "(?s', t\<^sub>0) \<in> par_rstep R"
        using par_rstep_subst_closed[of u\<^sub>2 u\<^sub>1 R \<delta>] u1 u2 t0' seq c'q by simp
      then obtain P' where step': "par_rstep_at R P' ?s' t\<^sub>0" by (rule par_rstepE)
      let ?P1 = "P\<^sub>1 - {q}"
      have qs: "q \<in> poss s" using P1(2) q(1) by blast
      have par: "q \<parallel> p" if "p \<in> ?P1" for p using parallel_setD[OF P1(1) q(1)] that by blast
      have P1': "parallel_set ?P1" "?P1 \<subseteq> poss ?s'"
        using parallel_set_subset[OF P1(1)] P1(2) par qs by (auto intro: parallel_poss_replace_at)
      have sub: "?s' |_ p = s |_ p" if "p \<in> ?P1" for p
        using par[OF that] qs P1(2) that by (intro parallel_subt_at_replace_at) auto
      have "t\<^sub>1 = ?s'\<lbrakk>?P1 \<Leftarrow> c'\<rbrakk>"
      proof -
        have "?s'\<lbrakk>?P1 \<Leftarrow> c'\<rbrakk> = replace_par ?s' ?P1 c'"
          using P1' by (rule replace_at_set_replace_par)
        also have "\<dots> = replace_par s (insert q ?P1) c'"
          using qs par by (intro replace_par_insert) auto
        also have "insert q ?P1 = P\<^sub>1" using q(1) by blast
        finally show ?thesis using t1 P1 by (simp add: replace_at_set_replace_par)
      qed
      moreover have "par_rstep_at R ?P1 ?s' (?s'\<lbrakk>?P1 \<Leftarrow> c'\<rbrakk>)"
        using P1' sub redex1 by (intro par_rstep_atI) auto
      ultimately have step1': "par_rstep_at R ?P1 ?s' t\<^sub>1" by simp
      have "overlap_size ?s' ?P1 P' \<le> (\<Sum>p \<in> ?P1. term_size (?s' |_ p))"
        using step' P1' unfolding par_rstep_at_def by (intro overlap_size_le) auto
      also have "\<dots> = (\<Sum>p \<in> ?P1. term_size (s |_ p))" using sub by simp
      also have "\<dots> < (\<Sum>p \<in> P\<^sub>1. term_size (s |_ p))"
      proof -
        have "finite P\<^sub>1" using P1(2) by (rule finite_subset) simp
        then have "(\<Sum>p \<in> P\<^sub>1. term_size (s |_ p)) = term_size (s |_ q) + (\<Sum>p \<in> ?P1. term_size (s |_ p))"
          using q(1) by (simp add: sum.remove)
        then show ?thesis using term_size_pos[of "s |_ q"] by simp
      qed
      also have "\<dots> \<le> overlap_size s P\<^sub>0 P\<^sub>1" using P1(2) P0' by (simp add: overlap_size_root)
      finally have "overlap_size ?s' ?P1 P' < overlap_size s P\<^sub>0 P\<^sub>1" .
      from IH[OF this step1' step'] show ?thesis by blast
    qed
  qed
qed

text \<open>Theorem 6.4.8 (Parallel Closure Theorem). We show that every peak
  \<open>t\<^sub>0 \<leftleftarrows>\<^sup>P\<^sup>0 s \<rightrightarrows>\<^sup>P\<^sup>1 t\<^sub>1\<close> is joinable by strong induction on the size of the overlap, joining the
  peaks below the outermost positions of \<open>P\<^sub>0 \<union> P\<^sub>1\<close>.\<close>

lemma parallel_closed_peak:
  assumes ll: "left_linear R" and pc: "parallel_closed R"
  shows "par_rstep_at R P\<^sub>0 s t\<^sub>0 \<Longrightarrow> par_rstep_at R P\<^sub>1 s t\<^sub>1 \<Longrightarrow>
    \<exists>u. (t\<^sub>0, u) \<in> par_rstep R \<and> (t\<^sub>1, u) \<in> par_rstep R"
proof (induct "overlap_size s P\<^sub>0 P\<^sub>1" arbitrary: s P\<^sub>0 P\<^sub>1 t\<^sub>0 t\<^sub>1 rule: less_induct)
  case less
  have poss: "P\<^sub>0 \<subseteq> poss s" "P\<^sub>1 \<subseteq> poss s" using less.prems unfolding par_rstep_at_def by blast+
  show ?case
  proof (rule par_peak_outermost[OF less.prems])
    fix q assume q: "q \<in> outermost (P\<^sub>0 \<union> P\<^sub>1)"
    let ?P0 = "{p. q @ p \<in> P\<^sub>0}" and ?P1 = "{p. q @ p \<in> P\<^sub>1}"
    note local = par_rstep_at_outermost[OF less.prems q]
    have le: "overlap_size (s |_ q) ?P0 ?P1 \<le> overlap_size s P\<^sub>0 P\<^sub>1"
      using poss by (rule overlap_size_outermost)
    have IH: "\<exists>u. (t\<^sub>0', u) \<in> par_rstep R \<and> (t\<^sub>1', u) \<in> par_rstep R"
      if "overlap_size s' P\<^sub>0' P\<^sub>1' < overlap_size (s |_ q) ?P0 ?P1"
        and "par_rstep_at R P\<^sub>0' s' t\<^sub>0'" and "par_rstep_at R P\<^sub>1' s' t\<^sub>1'"
      for s' P\<^sub>0' P\<^sub>1' t\<^sub>0' t\<^sub>1'
      using less.hyps[OF order_less_le_trans[OF that(1) le] that(2,3)] .
    have IH': "\<exists>u. (t\<^sub>0', u) \<in> par_rstep R \<and> (t\<^sub>1', u) \<in> par_rstep R"
      if "overlap_size s' P\<^sub>0' P\<^sub>1' < overlap_size (s |_ q) ?P1 ?P0"
        and "par_rstep_at R P\<^sub>0' s' t\<^sub>0'" and "par_rstep_at R P\<^sub>1' s' t\<^sub>1'"
      for s' P\<^sub>0' P\<^sub>1' t\<^sub>0' t\<^sub>1'
      using IH[OF _ that(2,3)] that(1) by (simp add: overlap_size_sym[of "s |_ q" ?P1 ?P0])
    have "q \<in> P\<^sub>0 \<or> q \<in> P\<^sub>1" using q outermost_subset by blast
    then show "\<exists>u. (t\<^sub>0 |_ q, u) \<in> par_rstep R \<and> (t\<^sub>1 |_ q, u) \<in> par_rstep R"
    proof
      assume "q \<in> P\<^sub>0"
      then have "[] \<in> ?P0" by simp
      from parallel_closed_root_peak[OF ll pc local this IH] show ?thesis .
    next
      assume "q \<in> P\<^sub>1"
      then have "[] \<in> ?P1" by simp
      from parallel_closed_root_peak[OF ll pc local(2) local(1) this IH']
      have "\<exists>u. (t\<^sub>1 |_ q, u) \<in> par_rstep R \<and> (t\<^sub>0 |_ q, u) \<in> par_rstep R" .
      then show ?thesis by blast
    qed
  qed
qed

theorem parallel_closure_theorem:
  assumes "left_linear R" and "parallel_closed R"
  shows "\<diamond> (par_rstep R)"
  unfolding diamond_def
proof (intro allI impI, elim conjE)
  fix s t\<^sub>0 t\<^sub>1 assume "(s, t\<^sub>0) \<in> par_rstep R" and "(s, t\<^sub>1) \<in> par_rstep R"
  then obtain P\<^sub>0 P\<^sub>1 where "par_rstep_at R P\<^sub>0 s t\<^sub>0" and "par_rstep_at R P\<^sub>1 s t\<^sub>1"
    by (auto elim!: par_rstepE)
  from parallel_closed_peak[OF assms this]
  show "\<exists>u. (t\<^sub>0, u) \<in> par_rstep R \<and> (t\<^sub>1, u) \<in> par_rstep R" .
qed

text \<open>Corollary 6.4.9.\<close>

corollary left_linear_parallel_closed_imp_confluent:
  assumes "left_linear R" and "parallel_closed R"
  shows is_confluent
  by (rule diamond_between_imp_confluent[OF parallel_closure_theorem[OF assms]
        rstep_subset_par_rstep par_rstep_subset_rtrancl])

text \<open>Orthogonal systems are trivially parallel closed, so Theorem 6.3.10 is a special case.\<close>

lemma orthogonal_imp_parallel_closed: "orthogonal R \<Longrightarrow> parallel_closed R"
  by (simp add: orthogonal_def parallel_closed_def)

text \<open>Weakly orthogonal systems are parallel closed, hence confluent.\<close>

corollary weakly_orthogonal_imp_confluent:
  assumes "weakly_orthogonal R"
  shows is_confluent
proof -
  have "parallel_closed R"
    using assms unfolding weakly_orthogonal_def parallel_closed_def by auto
  then show ?thesis
    using assms left_linear_parallel_closed_imp_confluent
    unfolding weakly_orthogonal_def by blast
qed

end

end
