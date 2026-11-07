theory Unification
  imports Terms
begin

section \<open>Unification\<close>

text \<open>Baader \& Nipkow, Section 4.5. Critical pairs (Chapter 6) are defined through most
  general unifiers, so we need that every solvable unification problem has an mgu
  (Theorem 4.5.8). We prove existence directly, by well-founded induction on the number of
  variables and the size of the problem, following the transformation rules of the
  unification algorithm (Delete, Decompose, Orient, Eliminate), but without defining the
  algorithm itself.\<close>

type_synonym ('f, 'v) equation = "('f, 'v) term \<times> ('f, 'v) term"

text \<open>Definition 4.5.1.\<close>

definition unifiers :: "('f, 'v) equation set \<Rightarrow> ('f, 'v) subst set" where
  "unifiers E = {\<sigma>. \<forall>(s, t) \<in> E. \<sigma> \<cdot> s = \<sigma> \<cdot> t}"

definition unifiable :: "('f, 'v) equation set \<Rightarrow> bool" where
  "unifiable E \<longleftrightarrow> unifiers E \<noteq> {}"

definition is_mgu :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation set \<Rightarrow> bool" where
  "is_mgu \<theta> E \<longleftrightarrow> \<theta> \<in> unifiers E \<and> (\<forall>\<tau> \<in> unifiers E. \<exists>\<delta>. \<tau> = \<delta> \<circ>\<^sub>s \<theta>)"

lemma unifiers_insert:
  "\<sigma> \<in> unifiers (insert (s, t) E) \<longleftrightarrow> \<sigma> \<cdot> s = \<sigma> \<cdot> t \<and> \<sigma> \<in> unifiers E"
  by (auto simp: unifiers_def)

lemma unifiers_Un: "unifiers (E \<union> F) = unifiers E \<inter> unifiers F"
  by (auto simp: unifiers_def)

lemma unifiers_insert_swap: "unifiers (insert (s, t) E) = unifiers (insert (t, s) E)"
  by (auto simp: unifiers_def)

lemma is_mgu_cong: "unifiers E = unifiers F \<Longrightarrow> is_mgu \<theta> E \<longleftrightarrow> is_mgu \<theta> F"
  by (simp add: is_mgu_def)

subsection \<open>The occurs check\<close>

lemma size_subst_apply_var:
  "x \<in> vars t \<Longrightarrow> size (\<sigma> x) \<le> size (\<sigma> \<cdot> t)"
proof (induct t)
  case (Var y)
  then show ?case by simp
next
  case (Fun f ts)
  then obtain t where t: "t \<in> set ts" "x \<in> vars t" by auto
  then have "size (\<sigma> x) \<le> size (\<sigma> \<cdot> t)" using Fun by blast
  also have "\<dots> < size (\<sigma> \<cdot> Fun f ts)"
    by (auto intro!: le_imp_less_Suc size_list_estimation'[OF t(1)])
  finally show ?case by simp
qed

lemma occurs_check:
  assumes "x \<in> vars t" and "t \<noteq> Var x"
  shows "\<sigma> x \<noteq> \<sigma> \<cdot> t"
proof -
  obtain f ts where t: "t = Fun f ts"
    using assms by (cases t) auto
  then obtain u where u: "u \<in> set ts" "x \<in> vars u" using assms(1) by auto
  have "size (\<sigma> x) \<le> size (\<sigma> \<cdot> u)" using u(2) by (rule size_subst_apply_var)
  also have "\<dots> < size (\<sigma> \<cdot> t)"
    unfolding t by (auto intro!: le_imp_less_Suc size_list_estimation'[OF u(1)])
  finally show ?thesis by auto
qed

subsection \<open>Measures on unification problems\<close>

definition eqs_vars :: "('f, 'v) equation list \<Rightarrow> 'v set" where
  "eqs_vars E = (\<Union>(s, t) \<in> set E. vars s \<union> vars t)"

definition eqs_size :: "('f, 'v) equation list \<Rightarrow> nat" where
  "eqs_size E = sum_list (map (\<lambda>(s, t). size s + size t + 1) E)"

lemma finite_eqs_vars [simp]: "finite (eqs_vars E)"
  by (auto simp: eqs_vars_def)

lemma eqs_vars_Nil [simp]: "eqs_vars [] = {}"
  by (simp add: eqs_vars_def)

lemma eqs_size_Nil [simp]: "eqs_size [] = 0"
  by (simp add: eqs_size_def)

lemma eqs_vars_Cons [simp]: "eqs_vars ((s, t) # E) = vars s \<union> vars t \<union> eqs_vars E"
  by (auto simp: eqs_vars_def)

lemma eqs_size_Cons [simp]: "eqs_size ((s, t) # E) = size s + size t + 1 + eqs_size E"
  by (simp add: eqs_size_def)

lemma eqs_vars_append [simp]: "eqs_vars (E @ F) = eqs_vars E \<union> eqs_vars F"
  by (auto simp: eqs_vars_def)

lemma eqs_size_append [simp]: "eqs_size (E @ F) = eqs_size E + eqs_size F"
  by (simp add: eqs_size_def)

lemma eqs_vars_zip:
  "length ss = length ts \<Longrightarrow> eqs_vars (zip ss ts) = (\<Union>s \<in> set ss. vars s) \<union> (\<Union>t \<in> set ts. vars t)"
  by (induct ss ts rule: list_induct2) auto

lemma eqs_size_zip:
  "length ss = length ts \<Longrightarrow> eqs_size (zip ss ts) = sum_list (map size ss) + sum_list (map size ts) + length ss"
  by (induct ss ts rule: list_induct2) (auto simp: eqs_size_def)

lemma unifiers_zip:
  "length ss = length ts \<Longrightarrow>
    unifiers (set (zip ss ts)) = {\<sigma>. map (\<lambda>t. \<sigma> \<cdot> t) ss = map (\<lambda>t. \<sigma> \<cdot> t) ts}"
  by (induct ss ts rule: list_induct2) (auto simp: unifiers_def)

subsection \<open>Existence of most general unifiers\<close>

text \<open>The rule Eliminate: if \<open>x \<notin> Var(u)\<close>, an mgu of \<open>{x \<mapsto> u}(E)\<close> composed with
  \<open>{x \<mapsto> u}\<close> is an mgu of \<open>{x =\<^sup>? u} \<union> E\<close>.\<close>

lemma unifier_eliminate:
  assumes "\<sigma> \<cdot> Var x = \<sigma> \<cdot> u"
  shows "\<sigma> \<circ>\<^sub>s Var(x := u) = \<sigma>"
  using assms by (auto simp: subst_compose_def)

definition subst_eqs :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation list \<Rightarrow> ('f, 'v) equation list" where
  "subst_eqs \<rho> E = map (\<lambda>(s, t). (\<rho> \<cdot> s, \<rho> \<cdot> t)) E"

lemma unifiers_subst_eqs: "\<sigma> \<in> unifiers (set (subst_eqs \<rho> E)) \<longleftrightarrow> \<sigma> \<circ>\<^sub>s \<rho> \<in> unifiers (set E)"
  by (auto simp: unifiers_def subst_eqs_def)

lemma eqs_vars_subst_eqs:
  assumes "x \<notin> vars u"
  shows "eqs_vars (subst_eqs (Var(x := u)) E) \<subseteq> (vars u \<union> eqs_vars E) - {x}"
  using assms by (auto simp: eqs_vars_def subst_eqs_def vars_subst_apply split: if_splits)

lemma is_mgu_eliminate:
  assumes x: "x \<notin> vars u" and mgu: "is_mgu \<theta> (set (subst_eqs (Var(x := u)) E))"
  shows "is_mgu (\<theta> \<circ>\<^sub>s Var(x := u)) (insert (Var x, u) (set E))"
proof -
  let ?\<rho> = "Var(x := u)"
  have \<rho>u: "?\<rho> \<cdot> u = u"
    using x by (auto intro: trans[OF subst_apply_cong subst_apply_Var])
  have "\<theta> \<circ>\<^sub>s ?\<rho> \<in> unifiers (set E)"
    using mgu by (simp add: is_mgu_def unifiers_subst_eqs)
  moreover have "(\<theta> \<circ>\<^sub>s ?\<rho>) \<cdot> Var x = (\<theta> \<circ>\<^sub>s ?\<rho>) \<cdot> u"
    unfolding subst_compose_apply using \<rho>u by simp
  ultimately have "\<theta> \<circ>\<^sub>s ?\<rho> \<in> unifiers (insert (Var x, u) (set E))"
    by (simp add: unifiers_insert)
  moreover have "\<exists>\<delta>. \<tau> = \<delta> \<circ>\<^sub>s (\<theta> \<circ>\<^sub>s ?\<rho>)" if \<tau>: "\<tau> \<in> unifiers (insert (Var x, u) (set E))" for \<tau>
  proof -
    have \<tau>\<rho>: "\<tau> \<circ>\<^sub>s ?\<rho> = \<tau>"
      using \<tau> by (intro unifier_eliminate) (simp add: unifiers_insert)
    then have "\<tau> \<in> unifiers (set (subst_eqs ?\<rho> E))"
      using \<tau> by (simp add: unifiers_subst_eqs unifiers_insert)
    then obtain \<delta> where "\<tau> = \<delta> \<circ>\<^sub>s \<theta>" using mgu by (auto simp: is_mgu_def)
    then have "\<tau> = \<delta> \<circ>\<^sub>s (\<theta> \<circ>\<^sub>s ?\<rho>)"
      using \<tau>\<rho> by (metis subst_compose_assoc)
    then show ?thesis by blast
  qed
  ultimately show ?thesis by (auto simp: is_mgu_def)
qed

lemma mgu_exists_list:
  "unifiers (set E) \<noteq> {} \<Longrightarrow> \<exists>\<theta>. is_mgu \<theta> (set E)"
proof (induct E rule: wf_induct[OF wf_measures[of "[\<lambda>E. card (eqs_vars E), eqs_size]"]])
  case (1 E)
  note IH = 1(1)[rule_format] and unif = 1(2)
  show ?case
  proof (cases E)
    case Nil
    then show ?thesis by (intro exI[of _ Var]) (auto simp: is_mgu_def unifiers_def)
  next
    case (Cons e E')
    obtain s t where e: "e = (s, t)" by (cases e)
    from unif obtain \<sigma> where \<sigma>: "\<sigma> \<in> unifiers (set E)" by blast
    then have \<sigma>st: "\<sigma> \<cdot> s = \<sigma> \<cdot> t" and \<sigma>E': "\<sigma> \<in> unifiers (set E')"
      by (auto simp: Cons e unifiers_insert)
    consider (eq) "s = t"
      | (var) x u where "s = Var x \<and> u = t \<or> t = Var x \<and> u = s" and "u \<noteq> Var x"
      | (func) f ss g ts where "s = Fun f ss" and "t = Fun g ts"
      by (cases s; cases t) auto
    then show ?thesis
    proof cases
      case eq
      have "(E', E) \<in> measures [\<lambda>E. card (eqs_vars E), eqs_size]"
        by (rule measures_lesseq) (auto simp: Cons e intro: card_mono measures_less)
      then obtain \<theta> where "is_mgu \<theta> (set E')" using IH \<sigma>E' by blast
      moreover have "unifiers (set E) = unifiers (set E')"
        using eq by (auto simp: Cons e unifiers_insert)
      ultimately show ?thesis using is_mgu_cong by blast
    next
      case var
      have swap: "unifiers (set E) = unifiers (insert (Var x, u) (set E'))"
        using var(1) by (auto simp: Cons e unifiers_insert_swap)
      have "\<sigma> x = \<sigma> \<cdot> u"
        using \<sigma> var(1) by (auto simp: swap unifiers_insert)
      then have x: "x \<notin> vars u" using occurs_check[OF _ var(2)] by metis
      let ?E'' = "subst_eqs (Var(x := u)) E'"
      have "eqs_vars ?E'' \<subseteq> eqs_vars E - {x}"
        using eqs_vars_subst_eqs[OF x, of E'] var(1) by (auto simp: Cons e)
      moreover have "x \<in> eqs_vars E" using var(1) by (auto simp: Cons e)
      ultimately have "eqs_vars ?E'' \<subset> eqs_vars E" by blast
      then have "(?E'', E) \<in> measures [\<lambda>E. card (eqs_vars E), eqs_size]"
        by (intro measures_less psubset_card_mono) auto
      moreover have "unifiers (set ?E'') \<noteq> {}"
      proof -
        have "\<sigma> \<circ>\<^sub>s Var(x := u) = \<sigma>"
          using \<open>\<sigma> x = \<sigma> \<cdot> u\<close> by (intro unifier_eliminate) simp
        then show ?thesis using \<sigma>E' by (metis empty_iff unifiers_subst_eqs)
      qed
      ultimately obtain \<theta> where "is_mgu \<theta> (set ?E'')" using IH by blast
      then have "is_mgu (\<theta> \<circ>\<^sub>s Var(x := u)) (insert (Var x, u) (set E'))"
        by (rule is_mgu_eliminate[OF x])
      then show ?thesis using is_mgu_cong[OF swap] by blast
    next
      case func
      from \<sigma>st func have fg: "f = g" and len: "length ss = length ts"
        by (auto dest: map_eq_imp_length_eq)
      let ?E'' = "zip ss ts @ E'"
      have "eqs_vars ?E'' = eqs_vars E"
        using len func by (auto simp: Cons e eqs_vars_zip)
      moreover have "eqs_size ?E'' < eqs_size E"
        using len func by (auto simp: Cons e eqs_size_zip size_list_conv_sum_list)
      ultimately have "(?E'', E) \<in> measures [\<lambda>E. card (eqs_vars E), eqs_size]"
        by (intro measures_lesseq measures_less) auto
      moreover have unifs: "unifiers (set ?E'') = unifiers (set E)"
        using len func fg by (auto simp: Cons e unifiers_Un unifiers_zip unifiers_insert)
      moreover have "unifiers (set ?E'') \<noteq> {}" using unifs unif by simp
      ultimately obtain \<theta> where "is_mgu \<theta> (set ?E'')" using IH by blast
      then show ?thesis using is_mgu_cong[OF unifs] by blast
    qed
  qed
qed

text \<open>Theorem 4.5.8 (existence part): every unifiable finite problem has an mgu.\<close>

theorem mgu_exists:
  assumes "finite E" and "unifiable E"
  shows "\<exists>\<theta>. is_mgu \<theta> E"
proof -
  obtain L where "E = set L" using assms(1) finite_list by blast
  then show ?thesis using assms(2) mgu_exists_list unfolding unifiable_def by blast
qed

corollary mgu_exists_pair:
  assumes "\<sigma> \<cdot> s = \<sigma> \<cdot> t"
  shows "\<exists>\<theta>. is_mgu \<theta> {(s, t)} \<and> (\<exists>\<delta>. \<sigma> = \<delta> \<circ>\<^sub>s \<theta>)"
proof -
  have "\<sigma> \<in> unifiers {(s, t)}" using assms by (simp add: unifiers_def)
  then obtain \<theta> where "is_mgu \<theta> {(s, t)}"
    using mgu_exists[of "{(s, t)}"] by (auto simp: unifiable_def)
  then show ?thesis using \<open>\<sigma> \<in> unifiers {(s, t)}\<close> by (auto simp: is_mgu_def)
qed

end
