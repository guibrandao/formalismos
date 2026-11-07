theory Term_Rewriting
  imports Reduction_Systems Terms
begin

section \<open>The reduction relation induced by a set of identities\<close>

text \<open>Baader \& Nipkow, Definition 3.1.8: \<open>s \<rightarrow>\<^sub>E t\<close> iff there are \<open>(l, r) \<in> E\<close>, \<open>p \<in> Pos(s)\<close>
  and \<open>\<sigma>\<close> with \<open>s|\<^sub>p = \<sigma>(l)\<close> and \<open>t = s[\<sigma>(r)]\<^sub>p\<close>.\<close>

definition rstep :: "('f, 'v) identity set \<Rightarrow> ('f, 'v) term rel" where
  "rstep E = {(s, t). \<exists>(l, r) \<in> E. \<exists>p \<in> poss s. \<exists>\<sigma>. s |_ p = \<sigma> \<cdot> l \<and> t = s\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r\<rbrakk>}"

lemma rstepI:
  assumes "(l, r) \<in> E" and "p \<in> poss s" and "s |_ p = \<sigma> \<cdot> l" and "t = s\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r\<rbrakk>"
  shows "(s, t) \<in> rstep E"
  using assms unfolding rstep_def by blast

lemma rstepE:
  assumes "(s, t) \<in> rstep E"
  obtains l r p \<sigma> where "(l, r) \<in> E" and "p \<in> poss s" and "s |_ p = \<sigma> \<cdot> l"
    and "t = s\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r\<rbrakk>"
  using assms unfolding rstep_def by blast

text \<open>Every identity is a (root) reduction step.\<close>

lemma subset_rstep: "E \<subseteq> rstep E"
proof
  fix e assume "e \<in> E"
  then obtain l r where "e = (l, r)" "(l, r) \<in> E" by (cases e) auto
  then show "e \<in> rstep E" by (auto intro: rstepI[where p = "[]" and \<sigma> = Var])
qed

section \<open>Closure properties of relations on terms\<close>

text \<open>Definition 3.1.9. Since our terms are not restricted to a signature, the conditions
  range over all function symbols and argument lists.\<close>

definition closed_subst :: "('f, 'v) term rel \<Rightarrow> bool" where
  "closed_subst r \<longleftrightarrow> (\<forall>s t \<sigma>. (s, t) \<in> r \<longrightarrow> (\<sigma> \<cdot> s, \<sigma> \<cdot> t) \<in> r)"

definition closed_ops :: "('f, 'v) term rel \<Rightarrow> bool" where
  "closed_ops r \<longleftrightarrow>
    (\<forall>f ss ts. list_all2 (\<lambda>s t. (s, t) \<in> r) ss ts \<longrightarrow> (Fun f ss, Fun f ts) \<in> r)"

definition compatible_ops :: "('f, 'v) term rel \<Rightarrow> bool" where
  "compatible_ops r \<longleftrightarrow>
    (\<forall>f us s t vs. (s, t) \<in> r \<longrightarrow> (Fun f (us @ s # vs), Fun f (us @ t # vs)) \<in> r)"

definition compatible_ctxt :: "('f, 'v) term rel \<Rightarrow> bool" where
  "compatible_ctxt r \<longleftrightarrow> (\<forall>s s' t p. (s, s') \<in> r \<longrightarrow> p \<in> poss t \<longrightarrow> (t\<lbrakk>p \<leftarrow> s\<rbrakk>, t\<lbrakk>p \<leftarrow> s'\<rbrakk>) \<in> r)"

lemma closed_substD: "closed_subst r \<Longrightarrow> (s, t) \<in> r \<Longrightarrow> (\<sigma> \<cdot> s, \<sigma> \<cdot> t) \<in> r"
  unfolding closed_subst_def by blast

lemma compatible_opsD:
  "compatible_ops r \<Longrightarrow> (s, t) \<in> r \<Longrightarrow> (Fun f (us @ s # vs), Fun f (us @ t # vs)) \<in> r"
  unfolding compatible_ops_def by blast

lemma compatible_ctxtD:
  "compatible_ctxt r \<Longrightarrow> (s, s') \<in> r \<Longrightarrow> p \<in> poss t \<Longrightarrow> (t\<lbrakk>p \<leftarrow> s\<rbrakk>, t\<lbrakk>p \<leftarrow> s'\<rbrakk>) \<in> r"
  unfolding compatible_ctxt_def by blast

subsection \<open>Lemma 3.1.10\<close>

lemma closed_subst_rstep: "closed_subst (rstep E)"
  unfolding closed_subst_def
proof (intro allI impI)
  fix s t \<tau>
  assume "(s, t) \<in> rstep E"
  then obtain l r p \<sigma> where lr: "(l, r) \<in> E" and p: "p \<in> poss s"
    and s: "s |_ p = \<sigma> \<cdot> l" and t: "t = s\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r\<rbrakk>"
    by (rule rstepE)
  show "(\<tau> \<cdot> s, \<tau> \<cdot> t) \<in> rstep E"
  proof (rule rstepI[OF lr])
    show "p \<in> poss (\<tau> \<cdot> s)" using p by (rule poss_subst_apply)
    show "(\<tau> \<cdot> s) |_ p = (\<tau> \<circ>\<^sub>s \<sigma>) \<cdot> l" using p s by (simp add: subt_at_subst_apply)
    show "\<tau> \<cdot> t = (\<tau> \<cdot> s)\<lbrakk>p \<leftarrow> (\<tau> \<circ>\<^sub>s \<sigma>) \<cdot> r\<rbrakk>" using p t by (simp add: replace_at_subst_apply)
  qed
qed

lemma compatible_ops_rstep: "compatible_ops (rstep E)"
  unfolding compatible_ops_def
proof (intro allI impI)
  fix f us s t vs
  assume "(s, t) \<in> rstep E"
  then obtain l r p \<sigma> where lr: "(l, r) \<in> E" and p: "p \<in> poss s"
    and s: "s |_ p = \<sigma> \<cdot> l" and t: "t = s\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r\<rbrakk>"
    by (rule rstepE)
  show "(Fun f (us @ s # vs), Fun f (us @ t # vs)) \<in> rstep E"
    by (rule rstepI[OF lr, where p = "length us # p"]) (use p s t in auto)
qed

subsection \<open>Lemma 3.1.11\<close>

lemma compatible_ops_iff_ctxt: "compatible_ops r \<longleftrightarrow> compatible_ctxt r"
  for r :: "('f, 'v) term rel"
proof
  assume comp: "compatible_ops r"
  show "compatible_ctxt r"
    unfolding compatible_ctxt_def
  proof (intro allI impI)
    fix s s' t :: "('f, 'v) term" and p
    assume "(s, s') \<in> r" and "p \<in> poss t"
    then show "(t\<lbrakk>p \<leftarrow> s\<rbrakk>, t\<lbrakk>p \<leftarrow> s'\<rbrakk>) \<in> r"
    proof (induct p arbitrary: t)
      case Nil
      then show ?case by simp
    next
      case (Cons i p)
      then obtain f ts where t: "t = Fun f ts" and i: "i < length ts" and p: "p \<in> poss (ts ! i)"
        by (cases t) auto
      have "((ts ! i)\<lbrakk>p \<leftarrow> s\<rbrakk>, (ts ! i)\<lbrakk>p \<leftarrow> s'\<rbrakk>) \<in> r"
        using Cons p by blast
      from compatible_opsD[OF comp this, of f "take i ts" "drop (Suc i) ts"]
      show ?case using i unfolding t by (simp add: upd_conv_take_nth_drop)
    qed
  qed
next
  assume comp: "compatible_ctxt r"
  show "compatible_ops r"
    unfolding compatible_ops_def
  proof (intro allI impI)
    fix f us s t vs
    assume st: "(s, t) \<in> r"
    let ?u = "Fun f (us @ s # vs)"
    have "[length us] \<in> poss ?u" by simp
    from compatible_ctxtD[OF comp st this]
    show "(Fun f (us @ s # vs), Fun f (us @ t # vs)) \<in> r" by simp
  qed
qed

lemma closed_ops_imp_compatible_ops:
  assumes "refl r" and "closed_ops r"
  shows "compatible_ops r"
  unfolding compatible_ops_def
proof (intro allI impI)
  fix f us s t vs
  assume "(s, t) \<in> r"
  with \<open>refl r\<close> have "list_all2 (\<lambda>s t. (s, t) \<in> r) (us @ s # vs) (us @ t # vs)"
    by (auto intro!: list_all2_appendI list_all2_refl dest: reflD)
  with \<open>closed_ops r\<close> show "(Fun f (us @ s # vs), Fun f (us @ t # vs)) \<in> r"
    unfolding closed_ops_def by blast
qed

lemma compatible_ops_imp_closed_ops:
  assumes "refl r" and "trans r" and "compatible_ops r"
  shows "closed_ops r"
  unfolding closed_ops_def
proof (intro allI impI)
  fix f ss ts
  assume "list_all2 (\<lambda>s t. (s, t) \<in> r) ss ts"
  then have "(Fun f (us @ ss), Fun f (us @ ts)) \<in> r" for us
  proof (induct arbitrary: us)
    case Nil
    then show ?case using \<open>refl r\<close> by (simp add: reflD)
  next
    case (Cons s ss t ts)
    have "(Fun f (us @ s # ss), Fun f (us @ t # ss)) \<in> r"
      using Cons(1) \<open>compatible_ops r\<close> by (rule compatible_opsD[rotated])
    moreover have "(Fun f ((us @ [t]) @ ss), Fun f ((us @ [t]) @ ts)) \<in> r"
      by (rule Cons(3))
    ultimately show ?case using \<open>trans r\<close> by (auto dest: transD)
  qed
  from this[of "[]"] show "(Fun f ss, Fun f ts) \<in> r" by simp
qed

lemma refl_trans_compatible_ops_iff_closed_ops:
  assumes "refl r" and "trans r"
  shows "compatible_ops r \<longleftrightarrow> closed_ops r"
  using assms closed_ops_imp_compatible_ops compatible_ops_imp_closed_ops by blast

subsection \<open>Closure properties are preserved by converse, union and closures\<close>

lemma closed_subst_converse: "closed_subst r \<Longrightarrow> closed_subst (r\<inverse>)"
  unfolding closed_subst_def by blast

lemma closed_subst_Un: "closed_subst r \<Longrightarrow> closed_subst s \<Longrightarrow> closed_subst (r \<union> s)"
  unfolding closed_subst_def by blast

lemma closed_subst_rtrancl:
  assumes "closed_subst r"
  shows "closed_subst (r\<^sup>*)"
  unfolding closed_subst_def
proof (intro allI impI)
  fix s t \<sigma>
  assume "(s, t) \<in> r\<^sup>*"
  then show "(\<sigma> \<cdot> s, \<sigma> \<cdot> t) \<in> r\<^sup>*"
    by (induct rule: rtrancl_induct)
      (auto intro: rtrancl_into_rtrancl closed_substD[OF assms])
qed

lemma closed_subst_trancl:
  assumes "closed_subst r"
  shows "closed_subst (r\<^sup>+)"
  unfolding closed_subst_def
proof (intro allI impI)
  fix s t \<sigma>
  assume "(s, t) \<in> r\<^sup>+"
  then show "(\<sigma> \<cdot> s, \<sigma> \<cdot> t) \<in> r\<^sup>+"
    by (induct rule: trancl_induct)
      (auto intro: trancl_into_trancl closed_substD[OF assms])
qed

lemma compatible_ops_converse: "compatible_ops r \<Longrightarrow> compatible_ops (r\<inverse>)"
  unfolding compatible_ops_def by blast

lemma compatible_ops_Un: "compatible_ops r \<Longrightarrow> compatible_ops s \<Longrightarrow> compatible_ops (r \<union> s)"
  unfolding compatible_ops_def by blast

lemma compatible_ops_rtrancl:
  assumes "compatible_ops r"
  shows "compatible_ops (r\<^sup>*)"
  unfolding compatible_ops_def
proof (intro allI impI)
  fix f us s t vs
  assume "(s, t) \<in> r\<^sup>*"
  then show "(Fun f (us @ s # vs), Fun f (us @ t # vs)) \<in> r\<^sup>*"
    by (induct rule: rtrancl_induct)
      (auto intro: rtrancl_into_rtrancl compatible_opsD[OF assms])
qed

lemma compatible_ops_trancl:
  assumes "compatible_ops r"
  shows "compatible_ops (r\<^sup>+)"
  unfolding compatible_ops_def
proof (intro allI impI)
  fix f us s t vs
  assume "(s, t) \<in> r\<^sup>+"
  then show "(Fun f (us @ s # vs), Fun f (us @ t # vs)) \<in> r\<^sup>+"
    by (induct rule: trancl_induct)
      (auto intro: trancl_into_trancl compatible_opsD[OF assms])
qed

subsection \<open>Rewrite relations\<close>

text \<open>Definition 4.2.2: a rewrite relation is compatible with \<open>\<Sigma>\<close>-operations and closed under
  substitutions. By Lemma 3.1.10, \<open>\<rightarrow>\<^sub>E\<close> is one.\<close>

definition rewrite_relation :: "('f, 'v) term rel \<Rightarrow> bool" where
  "rewrite_relation r \<longleftrightarrow> compatible_ops r \<and> closed_subst r"

lemma rewrite_relation_rstep: "rewrite_relation (rstep E)"
  unfolding rewrite_relation_def using compatible_ops_rstep closed_subst_rstep by blast

lemma rewrite_relation_rtrancl: "rewrite_relation r \<Longrightarrow> rewrite_relation (r\<^sup>*)"
  unfolding rewrite_relation_def using compatible_ops_rtrancl closed_subst_rtrancl by blast

lemma rewrite_relation_trancl: "rewrite_relation r \<Longrightarrow> rewrite_relation (r\<^sup>+)"
  unfolding rewrite_relation_def using compatible_ops_trancl closed_subst_trancl by blast

lemma rewrite_relation_conv: "rewrite_relation r \<Longrightarrow> rewrite_relation ((r \<union> r\<inverse>)\<^sup>*)"
  unfolding rewrite_relation_def
  by (intro conjI compatible_ops_rtrancl closed_subst_rtrancl compatible_ops_Un
      closed_subst_Un compatible_ops_converse closed_subst_converse) auto

text \<open>Exercise 4.5: \<open>\<rightarrow>\<^sub>E\<close> is the least rewrite relation containing \<open>E\<close>.\<close>

lemma rstep_least:
  assumes "E \<subseteq> r" and "rewrite_relation r"
  shows "rstep E \<subseteq> r"
proof (rule subrelI)
  fix s t assume "(s, t) \<in> rstep E"
  then obtain l r' p \<sigma> where lr: "(l, r') \<in> E" and p: "p \<in> poss s"
    and s: "s |_ p = \<sigma> \<cdot> l" and t: "t = s\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r'\<rbrakk>"
    by (rule rstepE)
  from assms have ctxt: "compatible_ctxt r" and subst: "closed_subst r"
    unfolding rewrite_relation_def compatible_ops_iff_ctxt by auto
  have "(\<sigma> \<cdot> l, \<sigma> \<cdot> r') \<in> r" using lr assms(1) closed_substD[OF subst] by blast
  from compatible_ctxtD[OF ctxt this p] have "(s\<lbrakk>p \<leftarrow> \<sigma> \<cdot> l\<rbrakk>, t) \<in> r" by (simp add: t)
  then show "(s, t) \<in> r" using p s by (metis replace_at_subt_at)
qed

lemma rstep_least_rewrite_relation:
  "rstep E = \<Inter>{r. E \<subseteq> r \<and> rewrite_relation r}"
proof (rule antisym)
  show "rstep E \<subseteq> \<Inter>{r. E \<subseteq> r \<and> rewrite_relation r}"
    using rstep_least by (intro Inter_greatest) auto
  show "\<Inter>{r. E \<subseteq> r \<and> rewrite_relation r} \<subseteq> rstep E"
    by (rule Inter_lower) (simp add: subset_rstep rewrite_relation_rstep)
qed

section \<open>Theorem 3.1.12\<close>

text \<open>\<open>\<leftrightarrow>\<^sup>*\<^sub>E\<close>, the reflexive, transitive and symmetric closure of \<open>\<rightarrow>\<^sub>E\<close>.\<close>

abbreviation conv :: "('f, 'v) identity set \<Rightarrow> ('f, 'v) term rel" where
  "conv E \<equiv> (rstep E \<union> (rstep E)\<inverse>)\<^sup>*"

lemma rtrancl_subset_refl_trans:
  assumes "refl r" and "trans r" and "s \<subseteq> r"
  shows "s\<^sup>* \<subseteq> r"
proof (rule subrelI)
  fix a b assume "(a, b) \<in> s\<^sup>*"
  then show "(a, b) \<in> r"
    by (induct rule: rtrancl_induct) (use assms in \<open>auto dest: transD reflD\<close>)
qed

theorem conv_equational_closure:
  shows "equiv UNIV (conv E)"
    and "E \<subseteq> conv E"
    and "closed_subst (conv E)"
    and "closed_ops (conv E)"
proof -
  show equiv: "equiv UNIV (conv E)"
    unfolding equiv_def by (auto simp: refl_rtrancl sym_Un_converse intro: sym_rtrancl trans_rtrancl)
  show "E \<subseteq> conv E" using subset_rstep by blast
  have "rewrite_relation (conv E)" by (rule rewrite_relation_conv[OF rewrite_relation_rstep])
  then have subst: "closed_subst (conv E)" and comp: "compatible_ops (conv E)"
    unfolding rewrite_relation_def by auto
  from subst show "closed_subst (conv E)" .
  from comp show "closed_ops (conv E)"
    using equiv compatible_ops_imp_closed_ops unfolding equiv_def by blast
qed

theorem conv_least:
  assumes equiv: "equiv UNIV r" and "E \<subseteq> r" and "closed_subst r" and "closed_ops r"
  shows "conv E \<subseteq> r"
proof -
  from equiv have refl: "refl r" and sym: "sym r" and trans: "trans r"
    unfolding equiv_def by auto
  have "rewrite_relation r"
    using assms refl closed_ops_imp_compatible_ops unfolding rewrite_relation_def by blast
  with \<open>E \<subseteq> r\<close> have "rstep E \<subseteq> r" by (rule rstep_least)
  with sym have "rstep E \<union> (rstep E)\<inverse> \<subseteq> r" by (auto dest: symD)
  with refl trans show ?thesis by (rule rtrancl_subset_refl_trans)
qed

section \<open>Term rewriting systems\<close>

text \<open>Definition 4.2.1: a rewrite rule is an identity \<open>l \<approx> r\<close> whose left-hand side is not a
  variable and \<open>Var(l) \<supseteq> Var(r)\<close>. A term rewriting system is a set of rewrite rules.\<close>

definition rewrite_rule :: "('f, 'v) identity \<Rightarrow> bool" where
  "rewrite_rule \<rho> \<longleftrightarrow> (case \<rho> of (l, r) \<Rightarrow> (\<forall>x. l \<noteq> Var x) \<and> vars r \<subseteq> vars l)"

text \<open>A TRS \<open>R\<close> is an ARS whose reduction is the rewrite relation \<open>\<rightarrow>\<^sub>R\<close>. The sublocale
  declaration makes every notion and result about ARSs (normal forms, confluence,
  termination, Newman's lemma, \dots) available for \<open>\<rightarrow>\<^sub>R\<close>.\<close>

locale TRS =
  fixes R :: "('f, 'v) term rel"
  assumes rewrite_rules: "\<rho> \<in> R \<Longrightarrow> rewrite_rule \<rho>"

sublocale TRS \<subseteq> ARS "rstep R" .

context TRS
begin

text \<open>Isabelle drops the mixfix syntax of a locale's notation when the locale parameter is
  instantiated by a term (here \<open>rstep R\<close>), so we declare the main notations again. They are
  abbreviations, hence they denote exactly the inherited ARS notions.\<close>

abbreviation rew :: "('f, 'v) term rel" (\<open>\<^bold>\<rightarrow>\<close>) where
  "\<^bold>\<rightarrow> \<equiv> rstep R"

abbreviation rew_step :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix \<open>\<rightarrow>\<close> 50) where
  "s \<rightarrow> t \<equiv> (s, t) \<in> \<^bold>\<rightarrow>"

abbreviation rew_rstar :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (\<open>_ \<rightarrow>\<^sup>* _\<close> [51, 51] 50) where
  "s \<rightarrow>\<^sup>* t \<equiv> (s, t) \<in> \<^bold>\<rightarrow>\<^sup>*"

abbreviation rew_rplus :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (\<open>_ \<rightarrow>\<^sup>+ _\<close> [51, 51] 50) where
  "s \<rightarrow>\<^sup>+ t \<equiv> (s, t) \<in> \<^bold>\<rightarrow>\<^sup>+"

abbreviation rew_conv :: "('f, 'v) term rel" (\<open>\<^bold>\<leftrightarrow>\<close>) where
  "\<^bold>\<leftrightarrow> \<equiv> \<^bold>\<rightarrow> \<union> \<^bold>\<rightarrow>\<inverse>"

abbreviation rew_conv_star :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (\<open>_ \<leftrightarrow>\<^sup>* _\<close> [51, 51] 50) where
  "s \<leftrightarrow>\<^sup>* t \<equiv> (s, t) \<in> \<^bold>\<leftrightarrow>\<^sup>*"

abbreviation rew_joinable :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (\<open>_ \<down> _\<close> [60, 60] 60) where
  "s \<down> t \<equiv> joinable s t"

lemma step_iff_rstep: "s \<rightarrow> t \<longleftrightarrow> (s, t) \<in> rstep R"
  by (rule refl)

lemma rewrite_relation_step: "rewrite_relation \<^bold>\<rightarrow>"
  by (rule rewrite_relation_rstep)

lemma rewrite_relation_rstar: "rewrite_relation (\<^bold>\<rightarrow>\<^sup>*)"
  by (rule rewrite_relation_rtrancl[OF rewrite_relation_rstep])

lemma rewrite_relation_rplus: "rewrite_relation (\<^bold>\<rightarrow>\<^sup>+)"
  by (rule rewrite_relation_trancl[OF rewrite_relation_rstep])

lemma rewrite_relation_rconv: "rewrite_relation (\<^bold>\<leftrightarrow>\<^sup>*)"
  by (rule rewrite_relation_conv[OF rewrite_relation_rstep])

text \<open>All ARS results apply to \<open>\<rightarrow>\<^sub>R\<close>; for instance Newman's lemma: a terminating, locally
  confluent TRS is confluent.\<close>

lemma newman: "is_terminating \<Longrightarrow> locally_confluent \<Longrightarrow> is_church_rosser"
  by (rule newman_lemma)

end


end
