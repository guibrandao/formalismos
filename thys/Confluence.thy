theory Confluence
  imports Term_Rewriting Unification Commutation
begin

text \<open>Baader \& Nipkow, Chapter 6 (Confluence), Sections 6.1--6.3.\<close>

section \<open>Strong confluence implies confluence\<close>

text \<open>Lemma 2.7.4 of the book, needed for the Strong Confluence Lemma 6.3.3.\<close>

context ARS
begin

lemma scD:
  assumes SC and "(a, b) \<in> \<^bold>\<rightarrow>" and "(a, c) \<in> \<^bold>\<rightarrow>"
  shows "\<exists>d. (b, d) \<in> \<^bold>\<rightarrow>\<^sup>= \<and> (c, d) \<in> \<^bold>\<rightarrow>\<^sup>*"
  using assms unfolding strongly_confluent_def by (auto simp: rtrancl_converse)

lemma sc_strip:
  assumes SC and "(a, b) \<in> \<^bold>\<rightarrow>" and "(a, c) \<in> \<^bold>\<rightarrow>\<^sup>*"
  shows "\<exists>d. (b, d) \<in> \<^bold>\<rightarrow>\<^sup>* \<and> (c, d) \<in> \<^bold>\<rightarrow>\<^sup>="
  using assms(3)
proof (induct rule: rtrancl_induct)
  case base
  then show ?case using assms(2) by blast
next
  case (step c c')
  then obtain d where bd: "(b, d) \<in> \<^bold>\<rightarrow>\<^sup>*" and cd: "(c, d) \<in> \<^bold>\<rightarrow>\<^sup>=" by blast
  show ?case
  proof (cases "c = d")
    case True
    then show ?thesis using bd step(2) by (metis UnI2 pair_in_Id_conv rtrancl.rtrancl_into_rtrancl)
  next
    case False
    then have "(c, d) \<in> \<^bold>\<rightarrow>" using cd by auto
    from scD[OF assms(1) step(2) this] obtain e
      where "(c', e) \<in> \<^bold>\<rightarrow>\<^sup>=" and "(d, e) \<in> \<^bold>\<rightarrow>\<^sup>*" by blast
    then show ?thesis using bd by (meson rtrancl_trans)
  qed
qed

lemma sc_imp_confluent:
  assumes SC
  shows is_confluent
proof -
  have "\<exists>d. (b, d) \<in> \<^bold>\<rightarrow>\<^sup>* \<and> (c, d) \<in> \<^bold>\<rightarrow>\<^sup>*"
    if "(a, b) \<in> \<^bold>\<rightarrow>\<^sup>*" and "(a, c) \<in> \<^bold>\<rightarrow>\<^sup>*" for a b c
    using that(1)
  proof (induct rule: rtrancl_induct)
    case base
    then show ?case using that(2) by blast
  next
    case (step b b')
    then obtain d where bd: "(b, d) \<in> \<^bold>\<rightarrow>\<^sup>*" and cd: "(c, d) \<in> \<^bold>\<rightarrow>\<^sup>*" by blast
    from sc_strip[OF assms step(2) bd] obtain e
      where "(b', e) \<in> \<^bold>\<rightarrow>\<^sup>*" and "(d, e) \<in> \<^bold>\<rightarrow>\<^sup>=" by blast
    moreover from \<open>(d, e) \<in> \<^bold>\<rightarrow>\<^sup>=\<close> have "(d, e) \<in> \<^bold>\<rightarrow>\<^sup>*" by auto
    ultimately show ?case using cd by (meson rtrancl_trans)
  qed
  then show ?thesis
    unfolding is_confluent_def joinable_def by (auto simp: rtrancl_converse)
qed

end

section \<open>Auxiliary results on rewriting below substitutions and contexts\<close>

lemma closed_ops_rtrancl:
  assumes "compatible_ops r"
  shows "closed_ops (r\<^sup>*)"
  using refl_trans_compatible_ops_iff_closed_ops[of "r\<^sup>*"] compatible_ops_rtrancl[OF assms]
  by (simp add: refl_rtrancl trans_rtrancl)

lemma closed_opsD:
  assumes "closed_ops r" and "length ss = length ts" and "\<And>i. i < length ts \<Longrightarrow> (ss ! i, ts ! i) \<in> r"
  shows "(Fun f ss, Fun f ts) \<in> r"
  using assms unfolding closed_ops_def by (auto simp: list_all2_conv_all_nth)

text \<open>If \<open>\<sigma>(x) \<rightarrow>\<^sup>* \<tau>(x)\<close> for all variables of \<open>t\<close>, then \<open>\<sigma>(t) \<rightarrow>\<^sup>* \<tau>(t)\<close>.\<close>

lemma rtrancl_subst_apply:
  assumes "compatible_ops r" and "\<And>x. x \<in> vars t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> r\<^sup>*"
  shows "(\<sigma> \<cdot> t, \<tau> \<cdot> t) \<in> r\<^sup>*"
  using assms(2)
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  have "(Fun f (map ((\<cdot>) \<sigma>) ts), Fun f (map ((\<cdot>) \<tau>) ts)) \<in> r\<^sup>*"
  proof (rule closed_opsD[OF closed_ops_rtrancl[OF assms(1)]])
    fix i assume "i < length (map ((\<cdot>) \<tau>) ts)"
    then have i: "i < length ts" by simp
    then have "(\<sigma> \<cdot> ts ! i, \<tau> \<cdot> ts ! i) \<in> r\<^sup>*"
      by (intro Fun.hyps[OF nth_mem[OF i]] Fun.prems) (auto intro!: bexI[OF _ nth_mem[OF i]])
    then show "(map ((\<cdot>) \<sigma>) ts ! i, map ((\<cdot>) \<tau>) ts ! i) \<in> r\<^sup>*" using i by simp
  qed simp
  then show ?case by simp
qed

lemma ctxt_closed:
  assumes "compatible_ops r" and "(u, v) \<in> r" and "p \<in> poss s"
  shows "(s\<lbrakk>p \<leftarrow> u\<rbrakk>, s\<lbrakk>p \<leftarrow> v\<rbrakk>) \<in> r"
  using compatible_ctxtD[OF compatible_ops_iff_ctxt[THEN iffD1, OF assms(1)] assms(2,3)] .

lemma ctxt_closed_rtrancl:
  assumes "compatible_ops r" and "(u, v) \<in> r\<^sup>*" and "p \<in> poss s"
  shows "(s\<lbrakk>p \<leftarrow> u\<rbrakk>, s\<lbrakk>p \<leftarrow> v\<rbrakk>) \<in> r\<^sup>*"
  using ctxt_closed[OF compatible_ops_rtrancl[OF assms(1)] assms(2,3)] .

lemma ctxt_closed_reflcl:
  assumes "compatible_ops r" and "(u, v) \<in> r\<^sup>=" and "p \<in> poss s"
  shows "(s\<lbrakk>p \<leftarrow> u\<rbrakk>, s\<lbrakk>p \<leftarrow> v\<rbrakk>) \<in> r\<^sup>="
  using assms ctxt_closed[OF assms(1) _ assms(3)] by auto

text \<open>A position of \<open>\<sigma>(l)\<close> is either a non-variable position of \<open>l\<close> or lies below a
  variable position of \<open>l\<close>.\<close>

lemma poss_subst_apply_cases:
  assumes "p \<in> poss (\<sigma> \<cdot> l)"
  shows "(p \<in> poss l \<and> (\<forall>x. l |_ p \<noteq> Var x)) \<or>
    (\<exists>q1 q2 x. p = q1 @ q2 \<and> q1 \<in> poss l \<and> l |_ q1 = Var x \<and> q2 \<in> poss (\<sigma> x))"
  using assms
proof (induct l arbitrary: p)
  case (Var x)
  then show ?case by (intro disjI2 exI[of _ "[]"] exI[of _ p]) auto
next
  case (Fun f ls)
  show ?case
  proof (cases p)
    case Nil
    then show ?thesis by simp
  next
    case (Cons i p')
    with Fun.prems have i: "i < length ls" and p': "p' \<in> poss (\<sigma> \<cdot> ls ! i)" by auto
    from Fun.hyps[OF nth_mem[OF i] p'] show ?thesis
    proof
      assume "p' \<in> poss (ls ! i) \<and> (\<forall>x. ls ! i |_ p' \<noteq> Var x)"
      then show ?thesis using i Cons by auto
    next
      assume "\<exists>q1 q2 x. p' = q1 @ q2 \<and> q1 \<in> poss (ls ! i) \<and> ls ! i |_ q1 = Var x \<and> q2 \<in> poss (\<sigma> x)"
      then obtain q1 q2 x where "p' = q1 @ q2" "q1 \<in> poss (ls ! i)" "ls ! i |_ q1 = Var x" "q2 \<in> poss (\<sigma> x)"
        by blast
      then show ?thesis using i Cons by (intro disjI2 exI[of _ "i # q1"] exI[of _ q2]) auto
    qed
  qed
qed

text \<open>The non-critical overlap (Case 2.1 of the proof of the Critical Pair Lemma, see
  Exercise 6.8): replacing one occurrence of \<open>\<sigma>(x)\<close> in \<open>\<sigma>(l)\<close> by \<open>\<tau>(x)\<close> can be
  completed to \<open>\<tau>(l)\<close> if \<open>\<sigma>(y) \<rightarrow>\<^sup>* \<tau>(y)\<close> for all variables \<open>y\<close> of \<open>l\<close>.\<close>

lemma replace_at_var_rtrancl:
  assumes r: "compatible_ops r" and "q \<in> poss l" and "l |_ q = Var x"
    and "\<And>y. y \<in> vars l \<Longrightarrow> (\<sigma> y, \<tau> y) \<in> r\<^sup>*"
  shows "((\<sigma> \<cdot> l)\<lbrakk>q \<leftarrow> \<tau> x\<rbrakk>, \<tau> \<cdot> l) \<in> r\<^sup>*"
  using assms(2-)
proof (induct l arbitrary: q)
  case (Var y)
  then show ?case by simp
next
  case (Fun f ls)
  then obtain i q' where q: "q = i # q'" and i: "i < length ls" and q': "q' \<in> poss (ls ! i)"
    by (cases q) auto
  have "(Fun f ((map ((\<cdot>) \<sigma>) ls)[i := (\<sigma> \<cdot> ls ! i)\<lbrakk>q' \<leftarrow> \<tau> x\<rbrakk>]), Fun f (map ((\<cdot>) \<tau>) ls)) \<in> r\<^sup>*"
  proof (rule closed_opsD[OF closed_ops_rtrancl[OF r]])
    fix j assume j: "j < length (map ((\<cdot>) \<tau>) ls)"
    show "((map ((\<cdot>) \<sigma>) ls)[i := (\<sigma> \<cdot> ls ! i)\<lbrakk>q' \<leftarrow> \<tau> x\<rbrakk>] ! j, map ((\<cdot>) \<tau>) ls ! j) \<in> r\<^sup>*"
    proof (cases "j = i")
      case True
      then show ?thesis
        using i q Fun.prems by (auto intro!: Fun.hyps[OF nth_mem[OF i] q'] intro: nth_mem)
    next
      case False
      then show ?thesis
        using j by (auto intro!: rtrancl_subst_apply[OF r] Fun.prems(3) bexI[OF _ nth_mem[of j]])
    qed
  qed simp
  then show ?case using i q by simp
qed

lemma subst_apply_eq_vars:
  assumes "\<sigma> \<cdot> t = \<tau> \<cdot> t" and "x \<in> vars t"
  shows "\<sigma> x = \<tau> x"
  using assms by (induct t) auto

lemma vars_subt_at: "p \<in> poss t \<Longrightarrow> vars (t |_ p) \<subseteq> vars t"
proof (induct p arbitrary: t)
  case (Cons i p)
  then show ?case by (cases t) (fastforce intro: nth_mem)+
qed simp

lemma replace_at_append:
  assumes "p @ q \<in> poss s"
  shows "s\<lbrakk>p @ q \<leftarrow> t\<rbrakk> = s\<lbrakk>p \<leftarrow> (s |_ p)\<lbrakk>q \<leftarrow> t\<rbrakk>\<rbrakk>"
proof -
  have p: "p \<in> poss s" using assms by (rule poss_append_poss)
  then have q: "q \<in> poss (s |_ p)" using assms by (simp add: poss_subt_at)
  have "s\<lbrakk>p @ q \<leftarrow> t\<rbrakk> = s\<lbrakk>p \<leftarrow> s |_ p\<rbrakk>\<lbrakk>p @ q \<leftarrow> t\<rbrakk>" using p by simp
  also have "\<dots> = s\<lbrakk>p \<leftarrow> (s |_ p)\<lbrakk>q \<leftarrow> t\<rbrakk>\<rbrakk>"
    by (rule replace_at_replace_at_append[OF p q])
  finally show ?thesis .
qed

lemma parallel_sym: "p \<parallel> q \<Longrightarrow> q \<parallel> p"
  by (auto simp: parallel_def)

lemma parallel_poss_replace_at:
  assumes "p \<parallel> q" and "p \<in> poss s" and "q \<in> poss s"
  shows "q \<in> poss (s\<lbrakk>p \<leftarrow> t\<rbrakk>)"
  using assms
proof (induct p arbitrary: q s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain j q' where q: "q = j # q'" by (cases q) auto
  from Cons.prems obtain f ss where s: "s = Fun f ss" by (cases s) auto
  show ?case
    using Cons.prems Cons.hyps[of q' "ss ! i"] by (auto simp: q s nth_list_update)
qed

section \<open>The decision problem\<close>

text \<open>Theorem 6.1.1 states that confluence of finite TRSs is undecidable. The proof reduces
  the ground word problem for a set of identities \<open>E\<close> with \<open>Var(l) = Var(r)\<close> to confluence:
  for ground terms \<open>s, t\<close> and a fresh constant \<open>a\<close>, the system
  \<open>R\<^sub>s\<^sub>t = E \<union> E\<inverse> \<union> {a \<rightarrow> s, a \<rightarrow> t}\<close> is confluent iff \<open>s \<approx>\<^sub>E t\<close>. Undecidability itself
  needs a theory of computability; we formalize the reduction, which is the mathematical
  content of the proof.\<close>

subsection \<open>Function symbols and replacing a constant\<close>

fun funs :: "('f, 'v) term \<Rightarrow> 'f set" where
  "funs (Var x) = {}"
| "funs (Fun f ts) = insert f (\<Union>t \<in> set ts. funs t)"

text \<open>\<open>repl a t u\<close> is the book's \<open>u\<^sup>t\<close>: all occurrences of the constant \<open>a\<close> in \<open>u\<close> are replaced
  by \<open>t\<close>.\<close>

fun repl :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "repl a t (Var x) = Var x"
| "repl a t (Fun f us) = (if f = a \<and> us = [] then t else Fun f (map (repl a t) us))"

lemma repl_id: "a \<notin> funs u \<Longrightarrow> repl a t u = u"
  by (induct u) (auto intro: map_idI)

lemma repl_subst_apply:
  "a \<notin> funs l \<Longrightarrow> repl a t (\<sigma> \<cdot> l) = (\<lambda>x. repl a t (\<sigma> x)) \<cdot> l"
  by (induct l) auto

lemma repl_poss:
  assumes "p \<in> poss u"
  shows "p \<in> poss (repl a t u) \<and> (repl a t u) |_ p = repl a t (u |_ p) \<and>
    repl a t (u\<lbrakk>p \<leftarrow> w\<rbrakk>) = (repl a t u)\<lbrakk>p \<leftarrow> repl a t w\<rbrakk>"
  using assms
proof (induct p arbitrary: u)
  case (Cons i p)
  then obtain f us where u: "u = Fun f us" and i: "i < length us" and p: "p \<in> poss (us ! i)"
    by (cases u) auto
  then have "us \<noteq> []" by auto
  then show ?case using Cons.hyps[OF p] u i by (auto simp: map_update)
qed simp

lemma funs_subt_at: "p \<in> poss u \<Longrightarrow> funs (u |_ p) \<subseteq> funs u"
proof (induct p arbitrary: u)
  case (Cons i p)
  then show ?case by (cases u) (fastforce intro: nth_mem)+
qed simp

lemma funs_replace_at: "p \<in> poss u \<Longrightarrow> funs (u\<lbrakk>p \<leftarrow> w\<rbrakk>) \<subseteq> funs u \<union> funs w"
proof (induct p arbitrary: u)
  case (Cons i p)
  then obtain f us where u: "u = Fun f us" and i: "i < length us" and p: "p \<in> poss (us ! i)"
    by (cases u) auto
  show ?case
  proof
    fix g assume "g \<in> funs (u\<lbrakk>i # p \<leftarrow> w\<rbrakk>)"
    then consider "g = f" | v where "v \<in> set (us[i := (us ! i)\<lbrakk>p \<leftarrow> w\<rbrakk>])" "g \<in> funs v"
      by (auto simp: u)
    then show "g \<in> funs u \<union> funs w"
    proof cases
      case 2
      then show ?thesis using Cons.hyps[OF p] i
        by (auto simp: u dest!: set_update_subset_insert[THEN subsetD] intro: nth_mem)
    qed (simp add: u)
  qed
qed simp

lemma funs_subst_apply: "funs (\<sigma> \<cdot> l) = funs l \<union> (\<Union>x \<in> vars l. funs (\<sigma> x))"
  by (induct l) auto

subsection \<open>Rewriting with unions and converses of identities\<close>

lemma rstep_mono: "E \<subseteq> F \<Longrightarrow> rstep E \<subseteq> rstep F"
  unfolding rstep_def by blast

lemma rstep_Un: "rstep (E \<union> F) = rstep E \<union> rstep F"
  unfolding rstep_def by blast

lemma rstep_converse_sub: "(s, t) \<in> rstep E \<Longrightarrow> (t, s) \<in> rstep (E\<inverse>)"
proof -
  assume "(s, t) \<in> rstep E"
  then obtain l r p \<sigma> where lr: "(l, r) \<in> E" and p: "p \<in> poss s" "s |_ p = \<sigma> \<cdot> l"
    and t: "t = s\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r\<rbrakk>" by (rule rstepE)
  have pt: "p \<in> poss t" using poss_replace_at[OF p(1), of "[]"] t by simp
  have "t |_ p = \<sigma> \<cdot> r" using subt_at_replace_at_append[OF p(1), of "[]"] t by simp
  moreover have "s = t\<lbrakk>p \<leftarrow> \<sigma> \<cdot> l\<rbrakk>"
    using replace_at_append_replace_at[of p "[]" s] replace_at_subt_at[OF p(1)] p t by simp
  ultimately show "(t, s) \<in> rstep (E\<inverse>)" using lr pt by (auto intro: rstepI)
qed

lemma rstep_converse: "rstep (E\<inverse>) = (rstep E)\<inverse>"
  using rstep_converse_sub[of _ _ E] rstep_converse_sub[of _ _ "E\<inverse>"] by auto

lemma conv_sym: "(s, t) \<in> conv E \<Longrightarrow> (t, s) \<in> conv E"
proof -
  assume "(s, t) \<in> conv E"
  then have "(t, s) \<in> ((rstep E \<union> (rstep E)\<inverse>)\<inverse>)\<^sup>*" by (simp add: rtrancl_converse)
  moreover have "(rstep E \<union> (rstep E)\<inverse>)\<inverse> = rstep E \<union> (rstep E)\<inverse>" by auto
  ultimately show ?thesis by simp
qed

subsection \<open>The reduction\<close>

theorem confluence_reduction:
  fixes E :: "('f, 'v) term rel" and a :: 'f and s t :: "('f, 'v) term"
  defines "R \<equiv> E \<union> E\<inverse>"
  defines "R\<^sub>s\<^sub>t \<equiv> R \<union> {(Fun a [], s), (Fun a [], t)}"
  assumes vars: "\<And>l r. (l, r) \<in> E \<Longrightarrow> vars l = vars r"
    and fresh: "\<And>l r. (l, r) \<in> E \<Longrightarrow> a \<notin> funs l \<union> funs r"
    and ground: "ground s" "ground t" and fresh_st: "a \<notin> funs s" "a \<notin> funs t"
  shows "ARS.is_confluent (rstep R\<^sub>s\<^sub>t) \<longleftrightarrow> (s, t) \<in> conv E"
proof -
  have RE: "rstep R = rstep E \<union> (rstep E)\<inverse>" by (simp add: R_def rstep_Un rstep_converse)
  have R_sub: "rstep R \<subseteq> rstep R\<^sub>s\<^sub>t" by (rule rstep_mono) (auto simp: R\<^sub>s\<^sub>t_def)
  have varsR: "vars l = vars r" and freshR: "a \<notin> funs l \<union> funs r" if "(l, r) \<in> R" for l r
    using that vars fresh by (auto simp: R_def)
  have a_s: "(Fun a [], s) \<in> rstep R\<^sub>s\<^sub>t"
    by (rule rstepI[where p = "[]" and \<sigma> = Var and l = "Fun a []" and r = s]) (auto simp: R\<^sub>s\<^sub>t_def)
  have a_t: "(Fun a [], t) \<in> rstep R\<^sub>s\<^sub>t"
    by (rule rstepI[where p = "[]" and \<sigma> = Var and l = "Fun a []" and r = t]) (auto simp: R\<^sub>s\<^sub>t_def)
  show ?thesis
  proof
    assume conf: "ARS.is_confluent (rstep R\<^sub>s\<^sub>t)"
    \<comment> \<open>Steps from terms without \<open>a\<close> are \<open>R\<close>-steps and do not introduce \<open>a\<close>.\<close>
    have noa: "(u, v) \<in> rstep R \<and> a \<notin> funs v"
      if uv: "(u, v) \<in> rstep R\<^sub>s\<^sub>t" and ua: "a \<notin> funs u" for u v
    proof -
      obtain l r p \<sigma> where lr: "(l, r) \<in> R\<^sub>s\<^sub>t" and p: "p \<in> poss u" "u |_ p = \<sigma> \<cdot> l"
        and v: "v = u\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r\<rbrakk>" using uv by (rule rstepE)
      have up: "funs (\<sigma> \<cdot> l) \<subseteq> funs u" using funs_subt_at[OF p(1)] p(2) by simp
      have lrR: "(l, r) \<in> R"
        using lr up ua by (auto simp: R\<^sub>s\<^sub>t_def)
      have "funs (\<sigma> \<cdot> r) \<subseteq> funs r \<union> funs u"
        using up varsR[OF lrR] by (auto simp: funs_subst_apply)
      then have "a \<notin> funs v"
        using funs_replace_at[OF p(1), of "\<sigma> \<cdot> r"] v freshR[OF lrR] ua by auto
      moreover have "(u, v) \<in> rstep R" using lrR p v by (auto intro: rstepI)
      ultimately show ?thesis by blast
    qed
    have noa_star: "(u, v) \<in> (rstep R)\<^sup>*"
      if "(u, v) \<in> (rstep R\<^sub>s\<^sub>t)\<^sup>*" and "a \<notin> funs u" for u v
    proof -
      from that have "(u, v) \<in> (rstep R)\<^sup>* \<and> a \<notin> funs v"
        by (induct rule: rtrancl_induct) (auto dest: noa intro: rtrancl_into_rtrancl)
      then show ?thesis by blast
    qed
    have "ARS.joinable (rstep R\<^sub>s\<^sub>t) s t"
      using conf a_s a_t unfolding ARS.is_confluent_def by blast
    then obtain z where "(s, z) \<in> (rstep R\<^sub>s\<^sub>t)\<^sup>*" "(t, z) \<in> (rstep R\<^sub>s\<^sub>t)\<^sup>*"
      unfolding ARS.joinable_def by (auto simp: rtrancl_converse)
    then have "(s, z) \<in> conv E" "(t, z) \<in> conv E"
      using noa_star fresh_st RE by auto
    then show "(s, t) \<in> conv E" using conv_sym by (meson rtrancl_trans)
  next
    assume st: "(s, t) \<in> conv E"
    then have st': "(s, t) \<in> (rstep R)\<^sup>*" "(t, s) \<in> (rstep R)\<^sup>*"
      using conv_sym RE by auto
    let ?r = "repl a t"
    have to_repl: "(u, ?r u) \<in> (rstep R\<^sub>s\<^sub>t)\<^sup>*" for u
    proof (induct u)
      case (Fun f us)
      show ?case
      proof (cases "f = a \<and> us = []")
        case True
        then show ?thesis using a_t by auto
      next
        case False
        then show ?thesis
          using Fun by (auto intro!: closed_opsD[OF closed_ops_rtrancl[OF compatible_ops_rstep]])
      qed
    qed simp
    \<comment> \<open>Every \<open>R\<^sub>s\<^sub>t\<close>-step becomes an \<open>R\<close>-conversion after replacing \<open>a\<close> by \<open>t\<close>.\<close>
    have step: "(?r u, ?r v) \<in> (rstep R)\<^sup>*" if uv: "(u, v) \<in> rstep R\<^sub>s\<^sub>t" for u v
    proof -
      obtain l r p \<sigma> where lr: "(l, r) \<in> R\<^sub>s\<^sub>t" and p: "p \<in> poss u" "u |_ p = \<sigma> \<cdot> l"
        and v: "v = u\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r\<rbrakk>" using uv by (rule rstepE)
      note rp = repl_poss[OF p(1), of a t]
      have "(?r (\<sigma> \<cdot> l), ?r (\<sigma> \<cdot> r)) \<in> (rstep R)\<^sup>*"
      proof (cases "(l, r) \<in> R")
        case True
        then show ?thesis
          using freshR[OF True]
          by (auto simp: repl_subst_apply intro!: rstepI[where p = "[]"])
      next
        case False
        then have "l = Fun a []" "r = s \<or> r = t" using lr by (auto simp: R\<^sub>s\<^sub>t_def)
        then show ?thesis using st' ground fresh_st by (auto simp: repl_id)
      qed
      then have "((?r u)\<lbrakk>p \<leftarrow> ?r (\<sigma> \<cdot> l)\<rbrakk>, (?r u)\<lbrakk>p \<leftarrow> ?r (\<sigma> \<cdot> r)\<rbrakk>) \<in> (rstep R)\<^sup>*"
        using rp by (intro ctxt_closed_rtrancl[OF compatible_ops_rstep]) auto
      moreover have "(?r u)\<lbrakk>p \<leftarrow> ?r (\<sigma> \<cdot> l)\<rbrakk> = ?r u"
        using rp p(2) by (metis replace_at_subt_at)
      ultimately show ?thesis using rp v by simp
    qed
    have sym: "(rstep R)\<inverse> = rstep R"
      by (auto simp: R_def rstep_Un rstep_converse)
    have steps: "(?r u, ?r v) \<in> (rstep R)\<^sup>*" if "(u, v) \<in> (rstep R\<^sub>s\<^sub>t)\<^sup>*" for u v
      using that by (induct rule: rtrancl_induct) (auto dest: step intro: rtrancl_trans)
    have "ARS.joinable (rstep R\<^sub>s\<^sub>t) y\<^sub>1 y\<^sub>2"
      if "(x, y\<^sub>1) \<in> (rstep R\<^sub>s\<^sub>t)\<^sup>*" "(x, y\<^sub>2) \<in> (rstep R\<^sub>s\<^sub>t)\<^sup>*" for x y\<^sub>1 y\<^sub>2
    proof -
      have "(?r x, ?r y\<^sub>1) \<in> (rstep R)\<^sup>*" using steps[OF that(1)] .
      then have "(?r y\<^sub>1, ?r x) \<in> (rstep R)\<^sup>*"
        using sym by (metis rtrancl_converseI)
      moreover have "(?r x, ?r y\<^sub>2) \<in> (rstep R)\<^sup>*" using steps[OF that(2)] .
      ultimately have "(?r y\<^sub>1, ?r y\<^sub>2) \<in> (rstep R\<^sub>s\<^sub>t)\<^sup>*"
        using rtrancl_mono[OF R_sub] by (meson rtrancl_trans subsetD)
      then have "(y\<^sub>1, ?r y\<^sub>2) \<in> (rstep R\<^sub>s\<^sub>t)\<^sup>*" using to_repl by (meson rtrancl_trans)
      then show ?thesis
        unfolding ARS.joinable_def using to_repl[of y\<^sub>2] by (auto simp: rtrancl_converse)
    qed
    then show "ARS.is_confluent (rstep R\<^sub>s\<^sub>t)"
      unfolding ARS.is_confluent_def by (auto simp: rtrancl_converse)
  qed
qed

section \<open>Critical pairs\<close>

subsection \<open>Renamed rules\<close>

text \<open>A variant of a rule is obtained by an invertible renaming of its variables. Rather than
  speaking about bijections on variables, we ask for substitutions in both directions.\<close>

definition variant :: "('f, 'v) identity \<Rightarrow> ('f, 'v) identity \<Rightarrow> bool" where
  "variant \<rho>' \<rho> \<longleftrightarrow> (\<exists>\<pi> \<pi>'. fst \<rho>' = \<pi> \<cdot> fst \<rho> \<and> snd \<rho>' = \<pi> \<cdot> snd \<rho> \<and>
                               fst \<rho> = \<pi>' \<cdot> fst \<rho>' \<and> snd \<rho> = \<pi>' \<cdot> snd \<rho>')"

lemma variant_refl [simp]: "variant \<rho> \<rho>"
  unfolding variant_def by (intro exI[of _ Var]) simp

text \<open>If there are infinitely many variables, every finite set of variables can be renamed
  away from any other finite set.\<close>

lemma fresh_renaming:
  assumes inf: "infinite (UNIV :: 'v set)" and "finite V" and "finite W"
  obtains \<pi> \<pi>' :: "('f, 'v) subst"
  where "\<And>x. x \<in> W \<Longrightarrow> \<pi>' \<cdot> \<pi> x = Var x" and "\<And>x. vars (\<pi> x) \<inter> V = {}"
proof -
  have "infinite (UNIV - V)" using inf assms(2) by (simp add: Diff_infinite_finite)
  then obtain B where B: "finite B" "card B = card W" "B \<subseteq> UNIV - V"
    using infinite_arbitrarily_large by blast
  then obtain g where g: "bij_betw g W B" using finite_same_card_bij[OF assms(3) B(1)] by metis
  define \<pi> :: "('f, 'v) subst" where "\<pi> x = (if x \<in> W then Var (g x) else Var (SOME y. y \<in> B \<or> y \<notin> V))" for x
  define \<pi>' :: "('f, 'v) subst" where "\<pi>' y = Var (the_inv_into W g y)" for y
  have "\<pi>' \<cdot> \<pi> x = Var x" if "x \<in> W" for x
    using that g by (simp add: \<pi>_def \<pi>'_def bij_betw_def the_inv_into_f_f)
  moreover have "vars (\<pi> x) \<inter> V = {}" for x
  proof (cases "x \<in> W")
    case True
    then show ?thesis using g B(3) by (auto simp: \<pi>_def bij_betw_def)
  next
    case False
    obtain y where "y \<notin> V" using ex_new_if_finite[OF inf assms(2)] by blast
    then have "(SOME y. y \<in> B \<or> y \<notin> V) \<notin> V"
      using B(3) by (metis (mono_tags, lifting) DiffD2 someI subsetD)
    then show ?thesis using False by (simp add: \<pi>_def)
  qed
  ultimately show thesis using that by blast
qed

lemma fresh_variant:
  fixes l r :: "('f, 'v) term"
  assumes inf: "infinite (UNIV :: 'v set)" and "finite V"
  obtains l' r' \<pi>' where "variant (l', r') (l, r)" and "vars l' \<inter> V = {}" and "vars r' \<inter> V = {}"
    and "\<pi>' \<cdot> l' = l" and "\<pi>' \<cdot> r' = r"
proof -
  obtain \<pi> \<pi>' :: "('f, 'v) subst"
    where inv: "\<And>x. x \<in> vars l \<union> vars r \<Longrightarrow> \<pi>' \<cdot> \<pi> x = Var x" and fresh: "\<And>x. vars (\<pi> x) \<inter> V = {}"
    by (rule fresh_renaming[OF inf assms(2), of "vars l \<union> vars r"]) auto
  have "\<pi>' \<cdot> (\<pi> \<cdot> t) = t" if "vars t \<subseteq> vars l \<union> vars r" for t
    using that inv by (simp add: subst_compose_apply[symmetric] del: subst_compose_apply)
      (rule trans[OF subst_apply_cong subst_apply_Var], auto simp: subst_compose_def)
  then have l: "\<pi>' \<cdot> (\<pi> \<cdot> l) = l" and r: "\<pi>' \<cdot> (\<pi> \<cdot> r) = r" by auto
  have "variant (\<pi> \<cdot> l, \<pi> \<cdot> r) (l, r)"
    unfolding variant_def by (intro exI[of _ \<pi>] exI[of _ \<pi>']) (simp add: l r)
  moreover have "vars (\<pi> \<cdot> t) \<inter> V = {}" for t
    using fresh by (auto simp: vars_subst_apply)
  ultimately show thesis using that l r by blast
qed

subsection \<open>Definition of critical pairs\<close>

text \<open>Definition 6.2.1. Let \<open>l\<^sub>i \<rightarrow> r\<^sub>i\<close> (\<open>i = 1, 2\<close>) be variable-disjoint variants of rules
  \<open>\<rho>\<^sub>1, \<rho>\<^sub>2 \<in> R\<close>, \<open>p \<in> Pos(l\<^sub>1)\<close> such that \<open>l\<^sub>1|\<^sub>p\<close> is not a variable, and \<open>\<theta>\<close> an mgu of
  \<open>l\<^sub>1|\<^sub>p =\<^sup>? l\<^sub>2\<close>. Then \<open>\<langle>\<theta>r\<^sub>1, (\<theta>l\<^sub>1)[\<theta>r\<^sub>2]\<^sub>p\<rangle>\<close> is a critical pair of \<open>R\<close>. Overlaps of a rule
  with a variant of itself at the root are excluded.\<close>

definition CP :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel" where
  "CP R = {(\<theta> \<cdot> r\<^sub>1, (\<theta> \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<theta> \<cdot> r\<^sub>2\<rbrakk>) | l\<^sub>1 r\<^sub>1 l\<^sub>2 r\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 p \<theta>.
      \<rho>\<^sub>1 \<in> R \<and> \<rho>\<^sub>2 \<in> R \<and> variant (l\<^sub>1, r\<^sub>1) \<rho>\<^sub>1 \<and> variant (l\<^sub>2, r\<^sub>2) \<rho>\<^sub>2 \<and>
      (vars l\<^sub>1 \<union> vars r\<^sub>1) \<inter> (vars l\<^sub>2 \<union> vars r\<^sub>2) = {} \<and>
      p \<in> poss l\<^sub>1 \<and> (\<forall>x. l\<^sub>1 |_ p \<noteq> Var x) \<and> is_mgu \<theta> {(l\<^sub>1 |_ p, l\<^sub>2)} \<and>
      \<not> (p = [] \<and> \<rho>\<^sub>1 = \<rho>\<^sub>2)}"

lemma CPE:
  assumes "(u, v) \<in> CP R"
  obtains l\<^sub>1 r\<^sub>1 l\<^sub>2 r\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 p \<theta> where "\<rho>\<^sub>1 \<in> R" and "\<rho>\<^sub>2 \<in> R"
    and "variant (l\<^sub>1, r\<^sub>1) \<rho>\<^sub>1" and "variant (l\<^sub>2, r\<^sub>2) \<rho>\<^sub>2"
    and "(vars l\<^sub>1 \<union> vars r\<^sub>1) \<inter> (vars l\<^sub>2 \<union> vars r\<^sub>2) = {}"
    and "p \<in> poss l\<^sub>1" and "\<forall>x. l\<^sub>1 |_ p \<noteq> Var x" and "is_mgu \<theta> {(l\<^sub>1 |_ p, l\<^sub>2)}"
    and "\<not> (p = [] \<and> \<rho>\<^sub>1 = \<rho>\<^sub>2)"
    and "u = \<theta> \<cdot> r\<^sub>1" and "v = (\<theta> \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<theta> \<cdot> r\<^sub>2\<rbrakk>"
  using assms unfolding CP_def by blast

lemma CPI:
  assumes "\<rho>\<^sub>1 \<in> R" and "\<rho>\<^sub>2 \<in> R"
    and "variant (l\<^sub>1, r\<^sub>1) \<rho>\<^sub>1" and "variant (l\<^sub>2, r\<^sub>2) \<rho>\<^sub>2"
    and "(vars l\<^sub>1 \<union> vars r\<^sub>1) \<inter> (vars l\<^sub>2 \<union> vars r\<^sub>2) = {}"
    and "p \<in> poss l\<^sub>1" and "\<forall>x. l\<^sub>1 |_ p \<noteq> Var x" and "is_mgu \<theta> {(l\<^sub>1 |_ p, l\<^sub>2)}"
    and "\<not> (p = [] \<and> \<rho>\<^sub>1 = \<rho>\<^sub>2)"
  shows "(\<theta> \<cdot> r\<^sub>1, (\<theta> \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<theta> \<cdot> r\<^sub>2\<rbrakk>) \<in> CP R"
  unfolding CP_def using assms by blast

text \<open>Every overlap is an instance of a critical pair (Case 2.2 of the analysis of forks).\<close>

lemma overlap_imp_CP:
  fixes R :: "('f, 'v) term rel"
  assumes inf: "infinite (UNIV :: 'v set)"
    and R: "(l\<^sub>1, r\<^sub>1) \<in> R" "(l\<^sub>2, r\<^sub>2) \<in> R"
    and p: "p \<in> poss l\<^sub>1" "\<forall>x. l\<^sub>1 |_ p \<noteq> Var x"
    and unif: "\<sigma>\<^sub>1 \<cdot> (l\<^sub>1 |_ p) = \<sigma>\<^sub>2 \<cdot> l\<^sub>2"
    and nontriv: "\<not> (p = [] \<and> (l\<^sub>1, r\<^sub>1) = (l\<^sub>2, r\<^sub>2))"
  shows "\<exists>u v \<delta>. (u, v) \<in> CP R \<and> \<delta> \<cdot> u = \<sigma>\<^sub>1 \<cdot> r\<^sub>1 \<and> \<delta> \<cdot> v = (\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>"
proof -
  let ?V = "vars l\<^sub>1 \<union> vars r\<^sub>1"
  obtain l\<^sub>2' r\<^sub>2' \<pi>' where var: "variant (l\<^sub>2', r\<^sub>2') (l\<^sub>2, r\<^sub>2)"
    and dl: "vars l\<^sub>2' \<inter> ?V = {}" and dr: "vars r\<^sub>2' \<inter> ?V = {}"
    and l2: "\<pi>' \<cdot> l\<^sub>2' = l\<^sub>2" and r2: "\<pi>' \<cdot> r\<^sub>2' = r\<^sub>2"
    using fresh_variant[OF inf, of ?V l\<^sub>2 r\<^sub>2] by auto
  define \<sigma> where "\<sigma> x = (if x \<in> ?V then \<sigma>\<^sub>1 x else \<sigma>\<^sub>2 \<cdot> \<pi>' x)" for x
  have \<sigma>1: "\<sigma> \<cdot> t = \<sigma>\<^sub>1 \<cdot> t" if "vars t \<subseteq> ?V" for t
    using that by (intro subst_apply_cong) (auto simp: \<sigma>_def)
  have \<sigma>2: "\<sigma> \<cdot> t = \<sigma>\<^sub>2 \<cdot> (\<pi>' \<cdot> t)" if "vars t \<inter> ?V = {}" for t
    using that by (simp add: subst_compose_apply[symmetric] del: subst_compose_apply)
      (intro subst_apply_cong, auto simp: \<sigma>_def subst_compose_def)
  have "\<sigma> \<cdot> (l\<^sub>1 |_ p) = \<sigma>\<^sub>1 \<cdot> (l\<^sub>1 |_ p)" using vars_subt_at[OF p(1)] by (intro \<sigma>1) auto
  also have "\<dots> = \<sigma> \<cdot> l\<^sub>2'" using unif \<sigma>2[OF dl] l2 by simp
  finally obtain \<theta> \<delta> where mgu: "is_mgu \<theta> {(l\<^sub>1 |_ p, l\<^sub>2')}" and \<sigma>\<theta>: "\<sigma> = \<delta> \<circ>\<^sub>s \<theta>"
    using mgu_exists_pair by blast
  have "(\<theta> \<cdot> r\<^sub>1, (\<theta> \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<theta> \<cdot> r\<^sub>2'\<rbrakk>) \<in> CP R"
    by (rule CPI[OF R variant_refl var _ p mgu]) (use dl dr nontriv in auto)
  moreover have "\<delta> \<cdot> (\<theta> \<cdot> r\<^sub>1) = \<sigma>\<^sub>1 \<cdot> r\<^sub>1"
    using \<sigma>1[of r\<^sub>1] \<sigma>\<theta> by simp
  moreover have "\<delta> \<cdot> (\<theta> \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<theta> \<cdot> r\<^sub>2'\<rbrakk> = (\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>"
    using \<sigma>1[of l\<^sub>1] \<sigma>2[OF dr] r2 \<sigma>\<theta> p(1)
    by (simp add: replace_at_subst_apply poss_subst_apply)
  ultimately show ?thesis by blast
qed

text \<open>Conversely, every critical pair is the result of a fork.\<close>

lemma CP_fork:
  assumes "(u, v) \<in> CP R"
  shows "\<exists>s. (s, u) \<in> rstep R \<and> (s, v) \<in> rstep R"
proof -
  obtain l\<^sub>1 r\<^sub>1 l\<^sub>2 r\<^sub>2 \<rho>\<^sub>1 \<rho>\<^sub>2 p \<theta> where R: "\<rho>\<^sub>1 \<in> R" "\<rho>\<^sub>2 \<in> R"
    and v1: "variant (l\<^sub>1, r\<^sub>1) \<rho>\<^sub>1" and v2: "variant (l\<^sub>2, r\<^sub>2) \<rho>\<^sub>2"
    and p: "p \<in> poss l\<^sub>1" and mgu: "is_mgu \<theta> {(l\<^sub>1 |_ p, l\<^sub>2)}"
    and u: "u = \<theta> \<cdot> r\<^sub>1" and v: "v = (\<theta> \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<theta> \<cdot> r\<^sub>2\<rbrakk>"
    using CPE[OF assms] by metis
  obtain \<pi>\<^sub>1 where \<pi>1: "l\<^sub>1 = \<pi>\<^sub>1 \<cdot> fst \<rho>\<^sub>1" "r\<^sub>1 = \<pi>\<^sub>1 \<cdot> snd \<rho>\<^sub>1" using v1 by (auto simp: variant_def)
  obtain \<pi>\<^sub>2 where \<pi>2: "l\<^sub>2 = \<pi>\<^sub>2 \<cdot> fst \<rho>\<^sub>2" "r\<^sub>2 = \<pi>\<^sub>2 \<cdot> snd \<rho>\<^sub>2" using v2 by (auto simp: variant_def)
  have "(\<theta> \<cdot> l\<^sub>1, u) \<in> rstep R"
    using R(1) \<pi>1 u by (intro rstepI[where p = "[]" and \<sigma> = "\<theta> \<circ>\<^sub>s \<pi>\<^sub>1"]) (auto simp: prod_eq_iff)
  moreover have "(\<theta> \<cdot> (l\<^sub>1 |_ p)) = \<theta> \<cdot> l\<^sub>2"
    using mgu by (auto simp: is_mgu_def unifiers_def)
  then have "(\<theta> \<cdot> l\<^sub>1, v) \<in> rstep R"
    using R(2) \<pi>2 v p
    by (intro rstepI[where p = p and \<sigma> = "\<theta> \<circ>\<^sub>s \<pi>\<^sub>2" and l = "fst \<rho>\<^sub>2" and r = "snd \<rho>\<^sub>2"])
      (auto simp: poss_subst_apply subt_at_subst_apply)
  ultimately show ?thesis by blast
qed

subsection \<open>The Critical Pair Lemma and Theorem\<close>

context ARS
begin

lemma lc_iff_joinable: "LC \<longleftrightarrow> (\<forall>a b c. (a, b) \<in> \<^bold>\<rightarrow> \<longrightarrow> (a, c) \<in> \<^bold>\<rightarrow> \<longrightarrow> b \<down> c)"
  unfolding locally_confluent_def joinable_def by auto

lemma joinableI: "(a, c) \<in> \<^bold>\<rightarrow>\<^sup>* \<Longrightarrow> (b, c) \<in> \<^bold>\<rightarrow>\<^sup>* \<Longrightarrow> a \<down> b"
  unfolding joinable_def by (auto simp: rtrancl_converse)

lemma joinableE:
  assumes "a \<down> b"
  obtains c where "(a, c) \<in> \<^bold>\<rightarrow>\<^sup>*" and "(b, c) \<in> \<^bold>\<rightarrow>\<^sup>*"
  using assms unfolding joinable_def by (auto simp: rtrancl_converse)

lemma joinable_refl [simp]: "a \<down> a"
  by (rule joinableI) auto

lemma joinable_sym: "a \<down> b \<Longrightarrow> b \<down> a"
  by (metis joinableE joinableI)

end

context TRS
begin

lemma rule_vars: "(l, r) \<in> R \<Longrightarrow> vars r \<subseteq> vars l"
  using rewrite_rules unfolding rewrite_rule_def by fastforce

lemma rule_lhs_not_Var: "(l, r) \<in> R \<Longrightarrow> l \<noteq> Var x"
  using rewrite_rules unfolding rewrite_rule_def by fastforce

text \<open>Joinability is closed under substitutions and contexts.\<close>

lemma joinable_ctxt_subst:
  assumes "joinable u v" and "p \<in> poss s"
  shows "joinable (s\<lbrakk>p \<leftarrow> \<delta> \<cdot> u\<rbrakk>) (s\<lbrakk>p \<leftarrow> \<delta> \<cdot> v\<rbrakk>)"
proof -
  obtain w where "u \<rightarrow>\<^sup>* w" and "v \<rightarrow>\<^sup>* w" using assms(1) by (rule joinableE)
  then have "(\<delta> \<cdot> u, \<delta> \<cdot> w) \<in> \<^bold>\<rightarrow>\<^sup>*" and "(\<delta> \<cdot> v, \<delta> \<cdot> w) \<in> \<^bold>\<rightarrow>\<^sup>*"
    using closed_substD[OF closed_subst_rtrancl[OF closed_subst_rstep]] by blast+
  then show ?thesis
    by (intro joinableI[where c = "s\<lbrakk>p \<leftarrow> \<delta> \<cdot> w\<rbrakk>"] ctxt_closed_rtrancl[OF compatible_ops_rstep _ assms(2)])
qed

end

text \<open>From now on we assume that there are infinitely many variables, so that rules can
  always be renamed apart.\<close>

locale TRS_inf = TRS R for R :: "('f, 'v) term rel" +
  assumes infinite_vars: "infinite (UNIV :: 'v set)"
begin

text \<open>The analysis of a fork whose second redex lies below the first one (Case 2 of the
  proof of the Critical Pair Lemma).\<close>

lemma nested_fork:
  assumes R: "(l\<^sub>1, r\<^sub>1) \<in> R" "(l\<^sub>2, r\<^sub>2) \<in> R"
    and p1: "p\<^sub>1 \<in> poss s" "s |_ p\<^sub>1 = \<sigma>\<^sub>1 \<cdot> l\<^sub>1"
    and p2: "p\<^sub>1 @ p \<in> poss s" "s |_ (p\<^sub>1 @ p) = \<sigma>\<^sub>2 \<cdot> l\<^sub>2"
  shows "joinable (s\<lbrakk>p\<^sub>1 \<leftarrow> \<sigma>\<^sub>1 \<cdot> r\<^sub>1\<rbrakk>) (s\<lbrakk>p\<^sub>1 @ p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>) \<or>
    (\<exists>u v \<delta>. (u, v) \<in> CP R \<and> s\<lbrakk>p\<^sub>1 \<leftarrow> \<sigma>\<^sub>1 \<cdot> r\<^sub>1\<rbrakk> = s\<lbrakk>p\<^sub>1 \<leftarrow> \<delta> \<cdot> u\<rbrakk> \<and>
       s\<lbrakk>p\<^sub>1 @ p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk> = s\<lbrakk>p\<^sub>1 \<leftarrow> \<delta> \<cdot> v\<rbrakk>)"
proof -
  have p: "p \<in> poss (\<sigma>\<^sub>1 \<cdot> l\<^sub>1)" using poss_subt_at[OF p1(1)] p1(2) p2(1) by simp
  have sub: "(\<sigma>\<^sub>1 \<cdot> l\<^sub>1) |_ p = \<sigma>\<^sub>2 \<cdot> l\<^sub>2" using subt_at_append[OF p2(1)] p1(2) p2(2) by simp
  have t2: "s\<lbrakk>p\<^sub>1 @ p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk> = s\<lbrakk>p\<^sub>1 \<leftarrow> (\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>\<rbrakk>"
    using replace_at_append[OF p2(1)] p1(2) by simp
  from poss_subst_apply_cases[OF p] show ?thesis
  proof
    assume crit: "p \<in> poss l\<^sub>1 \<and> (\<forall>x. l\<^sub>1 |_ p \<noteq> Var x)"
    then have unif: "\<sigma>\<^sub>1 \<cdot> (l\<^sub>1 |_ p) = \<sigma>\<^sub>2 \<cdot> l\<^sub>2" using sub subt_at_subst_apply by metis
    show ?thesis
    proof (cases "p = [] \<and> (l\<^sub>1, r\<^sub>1) = (l\<^sub>2, r\<^sub>2)")
      case True
      then have l: "\<sigma>\<^sub>1 \<cdot> l\<^sub>1 = \<sigma>\<^sub>2 \<cdot> l\<^sub>1" using unif by simp
      have "\<sigma>\<^sub>1 \<cdot> r\<^sub>1 = \<sigma>\<^sub>2 \<cdot> r\<^sub>1"
        by (intro subst_apply_cong subst_apply_eq_vars[OF l]) (use rule_vars[OF R(1)] in auto)
      then show ?thesis using True by simp
    next
      case False
      from overlap_imp_CP[OF infinite_vars R crit[THEN conjunct1] crit[THEN conjunct2] unif False]
      show ?thesis using t2 by metis
    qed
  next
    assume "\<exists>q1 q2 x. p = q1 @ q2 \<and> q1 \<in> poss l\<^sub>1 \<and> l\<^sub>1 |_ q1 = Var x \<and> q2 \<in> poss (\<sigma>\<^sub>1 x)"
    then obtain q1 q2 x where p_eq: "p = q1 @ q2" and q1: "q1 \<in> poss l\<^sub>1" "l\<^sub>1 |_ q1 = Var x"
      and q2: "q2 \<in> poss (\<sigma>\<^sub>1 x)" by blast
    define \<tau> where "\<tau> = \<sigma>\<^sub>1(x := (\<sigma>\<^sub>1 x)\<lbrakk>q2 \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>)"
    have sx: "(\<sigma>\<^sub>1 \<cdot> l\<^sub>1) |_ q1 = \<sigma>\<^sub>1 x" using subt_at_subst_apply[OF q1(1)] q1(2) by simp
    have "(\<sigma>\<^sub>1 x) |_ q2 = \<sigma>\<^sub>2 \<cdot> l\<^sub>2" using sub p_eq subt_at_append[of q1 q2 "\<sigma>\<^sub>1 \<cdot> l\<^sub>1"] sx p by simp
    then have "(\<sigma>\<^sub>1 x, \<tau> x) \<in> \<^bold>\<rightarrow>" using R(2) q2 by (auto simp: \<tau>_def intro: rstepI)
    then have steps: "(\<sigma>\<^sub>1 y, \<tau> y) \<in> \<^bold>\<rightarrow>\<^sup>*" for y by (cases "y = x") (auto simp: \<tau>_def)
    have "(\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk> = (\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>q1 \<leftarrow> \<tau> x\<rbrakk>"
      using replace_at_append[of q1 q2 "\<sigma>\<^sub>1 \<cdot> l\<^sub>1"] p p_eq sx by (simp add: \<tau>_def)
    moreover have "((\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>q1 \<leftarrow> \<tau> x\<rbrakk>, \<tau> \<cdot> l\<^sub>1) \<in> \<^bold>\<rightarrow>\<^sup>*"
      by (rule replace_at_var_rtrancl[OF compatible_ops_rstep q1 steps])
    moreover have "(\<tau> \<cdot> l\<^sub>1, \<tau> \<cdot> r\<^sub>1) \<in> \<^bold>\<rightarrow>"
      using R(1) by (intro rstepI[where p = "[]"]) auto
    ultimately have "((\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>, \<tau> \<cdot> r\<^sub>1) \<in> \<^bold>\<rightarrow>\<^sup>*" by auto
    moreover have "(\<sigma>\<^sub>1 \<cdot> r\<^sub>1, \<tau> \<cdot> r\<^sub>1) \<in> \<^bold>\<rightarrow>\<^sup>*"
      by (rule rtrancl_subst_apply[OF compatible_ops_rstep steps])
    ultimately show ?thesis
      unfolding t2 by (intro disjI1 joinableI[where c = "s\<lbrakk>p\<^sub>1 \<leftarrow> \<tau> \<cdot> r\<^sub>1\<rbrakk>"]
          ctxt_closed_rtrancl[OF compatible_ops_rstep _ p1(1)])
  qed
qed

text \<open>Lemma 6.2.3 (Critical Pair Lemma).\<close>

theorem critical_pair_lemma:
  assumes "s \<rightarrow> t\<^sub>1" and "s \<rightarrow> t\<^sub>2"
  shows "joinable t\<^sub>1 t\<^sub>2 \<or>
    (\<exists>p u v \<delta>. ((u, v) \<in> CP R \<or> (v, u) \<in> CP R) \<and> p \<in> poss s \<and>
       t\<^sub>1 = s\<lbrakk>p \<leftarrow> \<delta> \<cdot> u\<rbrakk> \<and> t\<^sub>2 = s\<lbrakk>p \<leftarrow> \<delta> \<cdot> v\<rbrakk>)"
proof -
  obtain l\<^sub>1 r\<^sub>1 p\<^sub>1 \<sigma>\<^sub>1 where R1: "(l\<^sub>1, r\<^sub>1) \<in> R" and p1: "p\<^sub>1 \<in> poss s" "s |_ p\<^sub>1 = \<sigma>\<^sub>1 \<cdot> l\<^sub>1"
    and t1: "t\<^sub>1 = s\<lbrakk>p\<^sub>1 \<leftarrow> \<sigma>\<^sub>1 \<cdot> r\<^sub>1\<rbrakk>" using assms(1) by (rule rstepE)
  obtain l\<^sub>2 r\<^sub>2 p\<^sub>2 \<sigma>\<^sub>2 where R2: "(l\<^sub>2, r\<^sub>2) \<in> R" and p2: "p\<^sub>2 \<in> poss s" "s |_ p\<^sub>2 = \<sigma>\<^sub>2 \<cdot> l\<^sub>2"
    and t2: "t\<^sub>2 = s\<lbrakk>p\<^sub>2 \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>" using assms(2) by (rule rstepE)
  consider (par) "p\<^sub>1 \<parallel> p\<^sub>2" | (below) p where "p\<^sub>2 = p\<^sub>1 @ p" | (above) p where "p\<^sub>1 = p\<^sub>2 @ p"
    unfolding parallel_def prefix_le_def by blast
  then show ?thesis
  proof cases
    case par
    have "(t\<^sub>1, t\<^sub>1\<lbrakk>p\<^sub>2 \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>) \<in> \<^bold>\<rightarrow>"
      unfolding t1 using par p1 p2
      by (intro rstepI[OF R2 parallel_poss_replace_at]) (auto simp: parallel_subt_at_replace_at)
    moreover have "(t\<^sub>2, t\<^sub>2\<lbrakk>p\<^sub>1 \<leftarrow> \<sigma>\<^sub>1 \<cdot> r\<^sub>1\<rbrakk>) \<in> \<^bold>\<rightarrow>"
      unfolding t2 using parallel_sym[OF par] p1 p2
      by (intro rstepI[OF R1 parallel_poss_replace_at]) (auto simp: parallel_subt_at_replace_at)
    moreover have "t\<^sub>1\<lbrakk>p\<^sub>2 \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk> = t\<^sub>2\<lbrakk>p\<^sub>1 \<leftarrow> \<sigma>\<^sub>1 \<cdot> r\<^sub>1\<rbrakk>"
      unfolding t1 t2 using parallel_replace_at_replace_at[OF par p1(1) p2(1)] .
    ultimately show ?thesis by (metis joinableI r_into_rtrancl)
  next
    case below
    from nested_fork[OF R1 R2 p1 p2[unfolded below]] show ?thesis
      unfolding t1 t2 below using p1(1) by blast
  next
    case above
    from nested_fork[OF R2 R1 p2 p1[unfolded above]] show ?thesis
      unfolding t1 t2 above using p2(1) joinable_sym by blast
  qed
qed

text \<open>Theorem 6.2.4 (Critical Pair Theorem).\<close>

theorem critical_pair_theorem:
  "locally_confluent \<longleftrightarrow> (\<forall>(u, v) \<in> CP R. joinable u v)"
proof
  assume LC: locally_confluent
  show "\<forall>(u, v) \<in> CP R. joinable u v"
    using CP_fork LC unfolding lc_iff_joinable by blast
next
  assume CP: "\<forall>(u, v) \<in> CP R. joinable u v"
  show locally_confluent
    unfolding lc_iff_joinable
  proof (intro allI impI)
    fix s t\<^sub>1 t\<^sub>2 assume "s \<rightarrow> t\<^sub>1" and "s \<rightarrow> t\<^sub>2"
    from critical_pair_lemma[OF this] show "joinable t\<^sub>1 t\<^sub>2"
      using CP joinable_ctxt_subst joinable_sym by blast
  qed
qed

text \<open>Corollary 6.2.5.\<close>

corollary terminating_confluent_iff_CP_joinable:
  assumes is_terminating
  shows "is_confluent \<longleftrightarrow> (\<forall>(u, v) \<in> CP R. joinable u v)"
  using confluent_imp_lc newman[OF assms] confluent_iff_CR critical_pair_theorem by blast

text \<open>The content of Corollary 6.2.6: for a terminating TRS, confluence holds iff the two
  sides of every critical pair have the same normal forms. If \<open>R\<close> is finite there are only
  finitely many critical pairs up to renaming, and normal forms are computable, which yields
  the decision procedure.\<close>

lemma nf_rtrancl_eq:
  assumes "a \<rightarrow>\<^sup>* b" and "\<nexists>c. a \<rightarrow> c"
  shows "a = b"
  using assms by (induct rule: converse_rtrancl_induct) auto

corollary terminating_confluent_iff_CP_normal_forms:
  assumes is_terminating
  shows "is_confluent \<longleftrightarrow>
    (\<forall>(u, v) \<in> CP R. \<forall>u' v'. u' \<in> normal_form u \<longrightarrow> v' \<in> normal_form v \<longrightarrow> u' = v')"
proof
  assume conf: is_confluent
  show "\<forall>(u, v) \<in> CP R. \<forall>u' v'. u' \<in> normal_form u \<longrightarrow> v' \<in> normal_form v \<longrightarrow> u' = v'"
  proof (clarify)
    fix u v u' v' assume "(u, v) \<in> CP R" "u' \<in> normal_form u" "v' \<in> normal_form v"
    then obtain s where "s \<rightarrow> u" "s \<rightarrow> v" "u \<rightarrow>\<^sup>* u'" "v \<rightarrow>\<^sup>* v'"
      and nf: "\<nexists>c. u' \<rightarrow> c" "\<nexists>c. v' \<rightarrow> c"
      using CP_fork unfolding normal_form_def by blast
    then have "s \<rightarrow>\<^sup>* u'" "s \<rightarrow>\<^sup>* v'" by auto
    then have "joinable u' v'"
      using conf unfolding is_confluent_def by (auto simp: rtrancl_converse)
    then obtain w where "u' \<rightarrow>\<^sup>* w" "v' \<rightarrow>\<^sup>* w" by (rule joinableE)
    then show "u' = v'" using nf nf_rtrancl_eq by metis
  qed
next
  assume nfs: "\<forall>(u, v) \<in> CP R. \<forall>u' v'. u' \<in> normal_form u \<longrightarrow> v' \<in> normal_form v \<longrightarrow> u' = v'"
  have "joinable u v" if "(u, v) \<in> CP R" for u v
  proof -
    obtain u' v' where "u' \<in> normal_form u" "v' \<in> normal_form v"
      using terminating_is_normalizing[OF assms] unfolding is_normalizing_def by blast
    moreover from this have "u' = v'" using nfs that by blast
    ultimately show ?thesis unfolding normal_form_def by (auto intro: joinableI)
  qed
  then show is_confluent
    using terminating_confluent_iff_CP_joinable[OF assms] by blast
qed

end

section \<open>Orthogonality\<close>

subsection \<open>Linearity\<close>

text \<open>Definition 6.3.1. A term is linear if no variable occurs twice in it.\<close>

fun linear_term :: "('f, 'v) term \<Rightarrow> bool" where
  "linear_term (Var x) = True"
| "linear_term (Fun f ts) \<longleftrightarrow>
    (\<forall>i < length ts. \<forall>j < length ts. i \<noteq> j \<longrightarrow> vars (ts ! i) \<inter> vars (ts ! j) = {}) \<and>
    (\<forall>t \<in> set ts. linear_term t)"

definition left_linear :: "('f, 'v) term rel \<Rightarrow> bool" where
  "left_linear R \<longleftrightarrow> (\<forall>(l, r) \<in> R. linear_term l)"

definition right_linear :: "('f, 'v) term rel \<Rightarrow> bool" where
  "right_linear R \<longleftrightarrow> (\<forall>(l, r) \<in> R. linear_term r)"

definition linear :: "('f, 'v) term rel \<Rightarrow> bool" where
  "linear R \<longleftrightarrow> left_linear R \<and> right_linear R"

text \<open>The defining property of linearity: the only occurrence of \<open>x\<close> in a linear term \<open>l\<close>
  is at \<open>q\<close>, so replacing \<open>\<sigma>(x)\<close> at \<open>q\<close> in \<open>\<sigma>(l)\<close> amounts to changing \<open>\<sigma>\<close> at \<open>x\<close>.\<close>

lemma linear_replace_at_var:
  assumes "linear_term l" and "q \<in> poss l" and "l |_ q = Var x"
  shows "(\<sigma> \<cdot> l)\<lbrakk>q \<leftarrow> t\<rbrakk> = (\<sigma>(x := t)) \<cdot> l"
  using assms
proof (induct l arbitrary: q)
  case (Var y)
  then show ?case by simp
next
  case (Fun f ls)
  then obtain i q' where q: "q = i # q'" and i: "i < length ls" and q': "q' \<in> poss (ls ! i)"
    by (cases q) auto
  have xi: "x \<in> vars (ls ! i)"
    using vars_subt_at[OF q'] Fun.prems(3) q by auto
  have "(map ((\<cdot>) \<sigma>) ls)[i := (\<sigma> \<cdot> ls ! i)\<lbrakk>q' \<leftarrow> t\<rbrakk>] = map ((\<cdot>) (\<sigma>(x := t))) ls"
  proof (rule nth_equalityI)
    fix j assume "j < length ((map ((\<cdot>) \<sigma>) ls)[i := (\<sigma> \<cdot> ls ! i)\<lbrakk>q' \<leftarrow> t\<rbrakk>])"
    then have j: "j < length ls" by simp
    show "(map ((\<cdot>) \<sigma>) ls)[i := (\<sigma> \<cdot> ls ! i)\<lbrakk>q' \<leftarrow> t\<rbrakk>] ! j = map ((\<cdot>) (\<sigma>(x := t))) ls ! j"
    proof (cases "j = i")
      case True
      have "linear_term (ls ! i)" "ls ! i |_ q' = Var x" using Fun.prems q i by auto
      then have "(\<sigma> \<cdot> ls ! i)\<lbrakk>q' \<leftarrow> t\<rbrakk> = \<sigma>(x := t) \<cdot> ls ! i"
        by (intro Fun.hyps[OF nth_mem[OF i] _ q'])
      then show ?thesis using True i by (simp only: nth_list_update_eq length_map nth_map)
    next
      case False
      then have "x \<notin> vars (ls ! j)" using Fun.prems(1) xi i j by auto
      then have "\<sigma>(x := t) \<cdot> ls ! j = \<sigma> \<cdot> ls ! j" by (intro subst_apply_cong) auto
      then show ?thesis using False j by simp
    qed
  qed simp
  then show ?case using q i by (simp only: subst_apply.simps replace_at.simps nth_map)
qed

text \<open>Rewriting below a variable occurring at most once takes at most one step.\<close>

lemma linear_subst_reflcl:
  assumes r: "compatible_ops r" and "linear_term t" and "(\<sigma> x, u) \<in> r"
  shows "(\<sigma> \<cdot> t, (\<sigma>(x := u)) \<cdot> t) \<in> r\<^sup>="
proof (cases "x \<in> vars t")
  case True
  then obtain q where q: "q \<in> poss t" "t |_ q = Var x" by (auto simp: vars_poss)
  then have q': "q \<in> poss (\<sigma> \<cdot> t)" and sub: "(\<sigma> \<cdot> t) |_ q = \<sigma> x"
    by (auto simp: poss_subst_apply subt_at_subst_apply)
  have "((\<sigma> \<cdot> t)\<lbrakk>q \<leftarrow> \<sigma> x\<rbrakk>, (\<sigma> \<cdot> t)\<lbrakk>q \<leftarrow> u\<rbrakk>) \<in> r"
    by (rule ctxt_closed[OF r assms(3) q'])
  then show ?thesis
    using replace_at_subt_at[OF q'] sub linear_replace_at_var[OF assms(2) q] by simp
next
  case False
  then have "(\<sigma>(x := u)) \<cdot> t = \<sigma> \<cdot> t" by (intro subst_apply_cong) auto
  then show ?thesis by simp
qed

subsection \<open>Strong joinability and the Strong Confluence Lemma\<close>

context ARS
begin

text \<open>Definition 6.3.2.\<close>

definition strongly_joinable :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "strongly_joinable s\<^sub>1 s\<^sub>2 \<longleftrightarrow>
    (\<exists>t\<^sub>1. (s\<^sub>1, t\<^sub>1) \<in> \<^bold>\<rightarrow>\<^sup>= \<and> (s\<^sub>2, t\<^sub>1) \<in> \<^bold>\<rightarrow>\<^sup>*) \<and> (\<exists>t\<^sub>2. (s\<^sub>1, t\<^sub>2) \<in> \<^bold>\<rightarrow>\<^sup>* \<and> (s\<^sub>2, t\<^sub>2) \<in> \<^bold>\<rightarrow>\<^sup>=)"

lemma strongly_joinable_sym: "strongly_joinable a b \<Longrightarrow> strongly_joinable b a"
  unfolding strongly_joinable_def by blast

lemma strongly_joinable_refl [simp]: "strongly_joinable a a"
  unfolding strongly_joinable_def by blast

lemma strongly_joinable_common_reduct:
  "(a, c) \<in> \<^bold>\<rightarrow>\<^sup>= \<Longrightarrow> (b, c) \<in> \<^bold>\<rightarrow>\<^sup>= \<Longrightarrow> strongly_joinable a b"
  unfolding strongly_joinable_def by blast

lemma sc_iff_strongly_joinable:
  "SC \<longleftrightarrow> (\<forall>a b c. (a, b) \<in> \<^bold>\<rightarrow> \<longrightarrow> (a, c) \<in> \<^bold>\<rightarrow> \<longrightarrow> strongly_joinable b c)"
  unfolding strongly_joinable_def strongly_confluent_def
  by (auto simp: rtrancl_converse) blast+

end

context TRS
begin

lemma strongly_joinable_ctxt_subst:
  assumes "strongly_joinable u v" and "p \<in> poss s"
  shows "strongly_joinable (s\<lbrakk>p \<leftarrow> \<delta> \<cdot> u\<rbrakk>) (s\<lbrakk>p \<leftarrow> \<delta> \<cdot> v\<rbrakk>)"
proof -
  have refl: "(s\<lbrakk>p \<leftarrow> \<delta> \<cdot> a\<rbrakk>, s\<lbrakk>p \<leftarrow> \<delta> \<cdot> b\<rbrakk>) \<in> \<^bold>\<rightarrow>\<^sup>=" if "(a, b) \<in> \<^bold>\<rightarrow>\<^sup>=" for a b
    using that closed_substD[OF closed_subst_rstep, where \<sigma> = \<delta>]
    by (intro ctxt_closed_reflcl[OF compatible_ops_rstep _ assms(2)]) auto
  have star: "(s\<lbrakk>p \<leftarrow> \<delta> \<cdot> a\<rbrakk>, s\<lbrakk>p \<leftarrow> \<delta> \<cdot> b\<rbrakk>) \<in> \<^bold>\<rightarrow>\<^sup>*" if "(a, b) \<in> \<^bold>\<rightarrow>\<^sup>*" for a b
    using that closed_substD[OF closed_subst_rtrancl[OF closed_subst_rstep], where \<sigma> = \<delta>]
    by (intro ctxt_closed_rtrancl[OF compatible_ops_rstep _ assms(2)]) auto
  show ?thesis using assms(1) refl star unfolding strongly_joinable_def by meson
qed

end

context TRS_inf
begin

lemma nested_fork_linear:
  assumes lin: "linear R" and CP: "\<forall>(u, v) \<in> CP R. strongly_joinable u v"
    and R: "(l\<^sub>1, r\<^sub>1) \<in> R" "(l\<^sub>2, r\<^sub>2) \<in> R"
    and p1: "p\<^sub>1 \<in> poss s" "s |_ p\<^sub>1 = \<sigma>\<^sub>1 \<cdot> l\<^sub>1"
    and p2: "p\<^sub>1 @ p \<in> poss s" "s |_ (p\<^sub>1 @ p) = \<sigma>\<^sub>2 \<cdot> l\<^sub>2"
  shows "strongly_joinable (s\<lbrakk>p\<^sub>1 \<leftarrow> \<sigma>\<^sub>1 \<cdot> r\<^sub>1\<rbrakk>) (s\<lbrakk>p\<^sub>1 @ p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>)"
proof -
  have p: "p \<in> poss (\<sigma>\<^sub>1 \<cdot> l\<^sub>1)" using poss_subt_at[OF p1(1)] p1(2) p2(1) by simp
  have sub: "(\<sigma>\<^sub>1 \<cdot> l\<^sub>1) |_ p = \<sigma>\<^sub>2 \<cdot> l\<^sub>2" using subt_at_append[OF p2(1)] p1(2) p2(2) by simp
  have t2: "s\<lbrakk>p\<^sub>1 @ p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk> = s\<lbrakk>p\<^sub>1 \<leftarrow> (\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>\<rbrakk>"
    using replace_at_append[OF p2(1)] p1(2) by simp
  from poss_subst_apply_cases[OF p] show ?thesis
  proof
    assume crit: "p \<in> poss l\<^sub>1 \<and> (\<forall>x. l\<^sub>1 |_ p \<noteq> Var x)"
    then have unif: "\<sigma>\<^sub>1 \<cdot> (l\<^sub>1 |_ p) = \<sigma>\<^sub>2 \<cdot> l\<^sub>2" using sub subt_at_subst_apply by metis
    show ?thesis
    proof (cases "p = [] \<and> (l\<^sub>1, r\<^sub>1) = (l\<^sub>2, r\<^sub>2)")
      case True
      then have l: "\<sigma>\<^sub>1 \<cdot> l\<^sub>1 = \<sigma>\<^sub>2 \<cdot> l\<^sub>1" using unif by simp
      have "\<sigma>\<^sub>1 \<cdot> r\<^sub>1 = \<sigma>\<^sub>2 \<cdot> r\<^sub>1"
        by (intro subst_apply_cong subst_apply_eq_vars[OF l]) (use rule_vars[OF R(1)] in auto)
      then show ?thesis using True by simp
    next
      case False
      from overlap_imp_CP[OF infinite_vars R crit[THEN conjunct1] crit[THEN conjunct2] unif False]
      obtain u v \<delta> where "(u, v) \<in> CP R" and "\<delta> \<cdot> u = \<sigma>\<^sub>1 \<cdot> r\<^sub>1"
        and "\<delta> \<cdot> v = (\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>" by blast
      then show ?thesis
        using strongly_joinable_ctxt_subst[OF _ p1(1), of u v \<delta>] CP t2 by auto
    qed
  next
    assume "\<exists>q1 q2 x. p = q1 @ q2 \<and> q1 \<in> poss l\<^sub>1 \<and> l\<^sub>1 |_ q1 = Var x \<and> q2 \<in> poss (\<sigma>\<^sub>1 x)"
    then obtain q1 q2 x where p_eq: "p = q1 @ q2" and q1: "q1 \<in> poss l\<^sub>1" "l\<^sub>1 |_ q1 = Var x"
      and q2: "q2 \<in> poss (\<sigma>\<^sub>1 x)" by blast
    define u where "u = (\<sigma>\<^sub>1 x)\<lbrakk>q2 \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>"
    have linl: "linear_term l\<^sub>1" and linr: "linear_term r\<^sub>1"
      using lin R(1) unfolding linear_def left_linear_def right_linear_def by auto
    have sx: "(\<sigma>\<^sub>1 \<cdot> l\<^sub>1) |_ q1 = \<sigma>\<^sub>1 x" using subt_at_subst_apply[OF q1(1)] q1(2) by simp
    have "(\<sigma>\<^sub>1 x) |_ q2 = \<sigma>\<^sub>2 \<cdot> l\<^sub>2" using sub p_eq subt_at_append[of q1 q2 "\<sigma>\<^sub>1 \<cdot> l\<^sub>1"] sx p by simp
    then have step: "(\<sigma>\<^sub>1 x, u) \<in> \<^bold>\<rightarrow>" using R(2) q2 by (auto simp: u_def intro: rstepI)
    have "(\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk> = (\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>q1 \<leftarrow> u\<rbrakk>"
      using replace_at_append[of q1 q2 "\<sigma>\<^sub>1 \<cdot> l\<^sub>1"] p p_eq sx by (simp add: u_def)
    also have "\<dots> = (\<sigma>\<^sub>1(x := u)) \<cdot> l\<^sub>1"
      by (rule linear_replace_at_var[OF linl q1])
    finally have "((\<sigma>\<^sub>1 \<cdot> l\<^sub>1)\<lbrakk>p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>, (\<sigma>\<^sub>1(x := u)) \<cdot> r\<^sub>1) \<in> \<^bold>\<rightarrow>\<^sup>="
      using R(1) by (auto intro: rstepI[where p = "[]"])
    moreover have "(\<sigma>\<^sub>1 \<cdot> r\<^sub>1, (\<sigma>\<^sub>1(x := u)) \<cdot> r\<^sub>1) \<in> \<^bold>\<rightarrow>\<^sup>="
      by (rule linear_subst_reflcl[where \<sigma> = "\<sigma>\<^sub>1" and x = x, OF compatible_ops_rstep linr step])
    ultimately show ?thesis
      unfolding t2
      by (intro strongly_joinable_common_reduct[where c = "s\<lbrakk>p\<^sub>1 \<leftarrow> (\<sigma>\<^sub>1(x := u)) \<cdot> r\<^sub>1\<rbrakk>"]
          ctxt_closed_reflcl[OF compatible_ops_rstep _ p1(1)])
  qed
qed

text \<open>Lemma 6.3.3 (Strong Confluence Lemma).\<close>

theorem strong_confluence_lemma:
  assumes lin: "linear R" and CP: "\<forall>(u, v) \<in> CP R. strongly_joinable u v"
  shows strongly_confluent
  unfolding sc_iff_strongly_joinable
proof (intro allI impI)
  fix s t\<^sub>1 t\<^sub>2 assume "s \<rightarrow> t\<^sub>1" and "s \<rightarrow> t\<^sub>2"
  obtain l\<^sub>1 r\<^sub>1 p\<^sub>1 \<sigma>\<^sub>1 where R1: "(l\<^sub>1, r\<^sub>1) \<in> R" and p1: "p\<^sub>1 \<in> poss s" "s |_ p\<^sub>1 = \<sigma>\<^sub>1 \<cdot> l\<^sub>1"
    and t1: "t\<^sub>1 = s\<lbrakk>p\<^sub>1 \<leftarrow> \<sigma>\<^sub>1 \<cdot> r\<^sub>1\<rbrakk>" using \<open>s \<rightarrow> t\<^sub>1\<close> by (rule rstepE)
  obtain l\<^sub>2 r\<^sub>2 p\<^sub>2 \<sigma>\<^sub>2 where R2: "(l\<^sub>2, r\<^sub>2) \<in> R" and p2: "p\<^sub>2 \<in> poss s" "s |_ p\<^sub>2 = \<sigma>\<^sub>2 \<cdot> l\<^sub>2"
    and t2: "t\<^sub>2 = s\<lbrakk>p\<^sub>2 \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>" using \<open>s \<rightarrow> t\<^sub>2\<close> by (rule rstepE)
  consider (par) "p\<^sub>1 \<parallel> p\<^sub>2" | (below) p where "p\<^sub>2 = p\<^sub>1 @ p" | (above) p where "p\<^sub>1 = p\<^sub>2 @ p"
    unfolding parallel_def prefix_le_def by blast
  then show "strongly_joinable t\<^sub>1 t\<^sub>2"
  proof cases
    case par
    have "(t\<^sub>1, t\<^sub>1\<lbrakk>p\<^sub>2 \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>) \<in> \<^bold>\<rightarrow>"
      unfolding t1 using par p1 p2
      by (intro rstepI[OF R2 parallel_poss_replace_at]) (auto simp: parallel_subt_at_replace_at)
    moreover have "(t\<^sub>2, t\<^sub>2\<lbrakk>p\<^sub>1 \<leftarrow> \<sigma>\<^sub>1 \<cdot> r\<^sub>1\<rbrakk>) \<in> \<^bold>\<rightarrow>"
      unfolding t2 using parallel_sym[OF par] p1 p2
      by (intro rstepI[OF R1 parallel_poss_replace_at]) (auto simp: parallel_subt_at_replace_at)
    moreover have "t\<^sub>1\<lbrakk>p\<^sub>2 \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk> = t\<^sub>2\<lbrakk>p\<^sub>1 \<leftarrow> \<sigma>\<^sub>1 \<cdot> r\<^sub>1\<rbrakk>"
      unfolding t1 t2 using parallel_replace_at_replace_at[OF par p1(1) p2(1)] .
    ultimately show ?thesis by (metis strongly_joinable_common_reduct UnI1)
  next
    case below
    show ?thesis
      using nested_fork_linear[OF lin CP R1 R2 p1 p2[unfolded below]] unfolding t1 t2 below .
  next
    case above
    show ?thesis
      using nested_fork_linear[OF lin CP R2 R1 p2 p1[unfolded above]] strongly_joinable_sym
      unfolding t1 t2 above by blast
  qed
qed

corollary linear_strongly_joinable_CP_imp_confluent:
  assumes "linear R" and "\<forall>(u, v) \<in> CP R. strongly_joinable u v"
  shows is_confluent
  using sc_imp_confluent[OF strong_confluence_lemma[OF assms]] .

end

subsection \<open>Orthogonal systems and parallel reduction\<close>

text \<open>Definition 6.3.6.\<close>

definition orthogonal :: "('f, 'v) term rel \<Rightarrow> bool" where
  "orthogonal R \<longleftrightarrow> left_linear R \<and> CP R = {}"

subsection \<open>Parallel reduction\<close>

text \<open>Definition 6.3.7. A set of positions \<open>P\<close> is parallel if any two distinct positions of \<open>P\<close>
  are parallel.\<close>

definition parallel_set :: "pos set \<Rightarrow> bool" where
  "parallel_set P \<longleftrightarrow> (\<forall>p \<in> P. \<forall>q \<in> P. p \<parallel> q \<or> p = q)"

text \<open>For \<open>P = {p\<^sub>1, \<dots>, p\<^sub>n}\<close> parallel and a term \<open>t\<^sub>p\<close> for each \<open>p \<in> P\<close>, the book writes
  \<open>s[t\<^sub>p]\<^sub>p\<^sub>\<in>\<^sub>P := s[t\<^sub>p\<^sub>1]\<^sub>p\<^sub>1 \<dots> [t\<^sub>p\<^sub>n]\<^sub>p\<^sub>n\<close>. We first define the successive replacement along a list
  of positions, and then take any enumeration of \<open>P\<close> without repetitions. Since the positions
  are parallel, the order of the replacements does not matter (\<open>replace_at_set_any_order\<close> below).\<close>

fun replace_at_list :: "('f, 'v) term \<Rightarrow> (pos \<times> ('f, 'v) term) list \<Rightarrow> ('f, 'v) term" where
  "replace_at_list s [] = s"
| "replace_at_list s ((p, t) # pts) = replace_at_list (s\<lbrakk>p \<leftarrow> t\<rbrakk>) pts"

definition replace_at_set :: "('f, 'v) term \<Rightarrow> pos set \<Rightarrow> (pos \<Rightarrow> ('f, 'v) term) \<Rightarrow> ('f, 'v) term"
  (\<open>_\<lbrakk>_ \<Leftarrow> _\<rbrakk>\<close> [1000, 0, 0] 1000) where
  "s\<lbrakk>P \<Leftarrow> t\<rbrakk> = replace_at_list s (map (\<lambda>p. (p, t p)) (SOME ps. distinct ps \<and> set ps = P))"

text \<open>The parallel reduction step \<open>s \<rightrightarrows>\<^sub>R\<^sup>P s[\<sigma>\<^sub>p(r\<^sub>p)]\<^sub>p\<^sub>\<in>\<^sub>P\<close>, where \<open>P\<close> is a parallel set of positions
  of \<open>s\<close> and, for each \<open>p \<in> P\<close>, \<open>s|\<^sub>p = \<sigma>\<^sub>p(l\<^sub>p)\<close> for a rule \<open>l\<^sub>p \<rightarrow> r\<^sub>p \<in> R\<close>. The function \<open>c\<close> gives
  the contractum \<open>c(p) = \<sigma>\<^sub>p(r\<^sub>p)\<close> at each \<open>p \<in> P\<close>. The relation \<open>\<rightrightarrows>\<^sub>R\<close> omits the annotation \<open>P\<close>.\<close>

definition par_rstep_at :: "('f, 'v) term rel \<Rightarrow> pos set \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
  "par_rstep_at R P s t \<longleftrightarrow> parallel_set P \<and> P \<subseteq> poss s \<and>
    (\<exists>c. (\<forall>p \<in> P. \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c p = \<sigma> \<cdot> r) \<and> t = s\<lbrakk>P \<Leftarrow> c\<rbrakk>)"

definition par_rstep :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel" where
  "par_rstep R = {(s, t). \<exists>P. par_rstep_at R P s t}"

subsubsection \<open>Parallel sets of positions\<close>

lemma parallel_setD: "parallel_set P \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> P \<Longrightarrow> p \<noteq> q \<Longrightarrow> p \<parallel> q"
  unfolding parallel_set_def by blast

lemma parallel_set_subset: "parallel_set P \<Longrightarrow> Q \<subseteq> P \<Longrightarrow> parallel_set Q"
  unfolding parallel_set_def by blast

lemma parallel_set_empty [simp]: "parallel_set {}"
  and parallel_set_singleton [simp]: "parallel_set {p}"
  unfolding parallel_set_def by auto

lemma parallel_append_left [simp]: "q @ p \<parallel> q @ p' \<longleftrightarrow> p \<parallel> p'"
  by (induct q) auto

lemma parallel_append_parallel: "q \<parallel> q' \<Longrightarrow> q @ p \<parallel> q' @ p'"
  unfolding parallel_def prefix_le_def by (metis append_eq_append_conv2)

lemma parallel_set_Nil: "parallel_set P \<Longrightarrow> [] \<in> P \<Longrightarrow> P = {[]}"
  using not_parallel_Nil unfolding parallel_set_def by blast

lemma parallel_set_below:
  assumes "parallel_set P"
  shows "parallel_set {p. q @ p \<in> P}"
  unfolding parallel_set_def
proof (intro ballI)
  fix p p' assume "p \<in> {p. q @ p \<in> P}" and "p' \<in> {p. q @ p \<in> P}"
  then have "q @ p \<parallel> q @ p' \<or> q @ p = q @ p'" using assms unfolding parallel_set_def by blast
  then show "p \<parallel> p' \<or> p = p'" by simp
qed

lemma parallel_not_less: "parallel_set P \<Longrightarrow> p \<in> P \<Longrightarrow> q \<in> P \<Longrightarrow> \<not> p <\<^sub>p q"
  unfolding parallel_set_def parallel_def prefix_less_def by blast

lemma Cons_prefix_less_Cons [simp]: "i # p <\<^sub>p j # q \<longleftrightarrow> i = j \<and> p <\<^sub>p q"
  and prefix_le_Nil [simp]: "p \<le>\<^sub>p [] \<longleftrightarrow> p = []"
  unfolding prefix_less_def prefix_le_def by auto

text \<open>Two prefixes of the same position are comparable.\<close>

lemma prefix_le_cases: "p \<le>\<^sub>p r \<Longrightarrow> q \<le>\<^sub>p r \<Longrightarrow> p \<le>\<^sub>p q \<or> q \<le>\<^sub>p p"
  unfolding prefix_le_def by (metis append_eq_append_conv2)

text \<open>The outermost positions of a set.\<close>

definition outermost :: "pos set \<Rightarrow> pos set" where
  "outermost P = {p \<in> P. \<forall>q \<in> P. \<not> q <\<^sub>p p}"

lemma outermost_subset: "outermost P \<subseteq> P"
  unfolding outermost_def by blast

lemma parallel_set_outermost: "parallel_set (outermost P)"
  unfolding parallel_set_def outermost_def parallel_def prefix_less_def by blast

lemma outermost_exists: "p \<in> P \<Longrightarrow> \<exists>q \<in> outermost P. q \<le>\<^sub>p p"
proof (induct "length p" arbitrary: p rule: less_induct)
  case less
  show ?case
  proof (cases "p \<in> outermost P")
    case False
    then obtain q where q: "q \<in> P" "q <\<^sub>p p" using less.prems unfolding outermost_def by blast
    then have "length q < length p"
      unfolding prefix_less_def prefix_le_def by auto
    then obtain q' where "q' \<in> outermost P" "q' \<le>\<^sub>p q" using less.hyps q(1) by blast
    then show ?thesis using q(2) prefix_le_trans unfolding prefix_less_def by blast
  qed (use prefix_le_refl in blast)
qed

subsubsection \<open>Simultaneous replacement\<close>

text \<open>To reason about \<open>s[t\<^sub>p]\<^sub>p\<^sub>\<in>\<^sub>P\<close> we describe it recursively on \<open>s\<close>.\<close>

function replace_par :: "('f, 'v) term \<Rightarrow> pos set \<Rightarrow> (pos \<Rightarrow> ('f, 'v) term) \<Rightarrow> ('f, 'v) term" where
  "replace_par (Var x) P t = (if [] \<in> P then t [] else Var x)"
| "replace_par (Fun f ss) P t = (if [] \<in> P then t [] else
    Fun f (map (\<lambda>(i, s). replace_par s {p. i # p \<in> P} (\<lambda>p. t (i # p))) (zip [0..<length ss] ss)))"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(s, _, _). size s)")
    (auto dest!: set_zip_rightD intro: le_imp_less_Suc size_list_estimation')

lemma replace_par_root: "[] \<in> P \<Longrightarrow> replace_par s P t = t []"
  by (cases s) auto

lemma replace_par_Var: "[] \<notin> P \<Longrightarrow> replace_par (Var x) P t = Var x"
  by simp

lemma replace_par_Fun:
  "[] \<notin> P \<Longrightarrow> replace_par (Fun f ss) P t =
    Fun f (map (\<lambda>i. replace_par (ss ! i) {p. i # p \<in> P} (\<lambda>p. t (i # p))) [0..<length ss])"
  by (auto intro!: nth_equalityI)

declare replace_par.simps [simp del]

lemma replace_par_empty [simp]: "replace_par s {} t = s"
proof (induct s arbitrary: t)
  case (Fun f ss)
  then show ?case by (auto simp: replace_par_Fun intro!: nth_equalityI)
qed (simp add: replace_par_Var)

lemma replace_par_cong:
  "(\<And>p. p \<in> P \<Longrightarrow> c p = d p) \<Longrightarrow> replace_par s P c = replace_par s P d"
proof (induct s arbitrary: P c d)
  case (Var x)
  then show ?case by (cases "[] \<in> P") (auto simp: replace_par_root replace_par_Var)
next
  case (Fun f ss)
  show ?case
  proof (cases "[] \<in> P")
    case False
    have "replace_par (ss ! i) {p. i # p \<in> P} (\<lambda>p. c (i # p)) =
        replace_par (ss ! i) {p. i # p \<in> P} (\<lambda>p. d (i # p))" if "i < length ss" for i
      by (rule Fun.hyps[OF nth_mem[OF that]]) (simp add: Fun.prems)
    then show ?thesis using False by (simp add: replace_par_Fun)
  qed (simp add: replace_par_root Fun.prems)
qed

lemma replace_par_subt_at:
  assumes "parallel_set P" and "P \<subseteq> poss s" and "q \<in> P"
  shows "replace_par s P c |_ q = c q"
  using assms
proof (induct q arbitrary: s P c)
  case Nil
  then show ?case by (simp add: replace_par_root)
next
  case (Cons i q)
  then obtain f ss where s: "s = Fun f ss" and i: "i < length ss"
    by (cases s) auto
  have "[] \<notin> P" using Cons.prems parallel_set_Nil by blast
  moreover have "parallel_set {p. i # p \<in> P}"
    using parallel_set_below[OF Cons.prems(1), of "[i]"] by simp
  moreover have "{p. i # p \<in> P} \<subseteq> poss (ss ! i)" using Cons.prems(2) s by auto
  ultimately show ?case
    using Cons.prems(3) Cons.hyps[of "{p. i # p \<in> P}" "ss ! i"] s i by (simp add: replace_par_Fun)
qed

lemma replace_par_subt_at_parallel:
  assumes "q \<in> poss s" and "\<forall>p \<in> P. q \<parallel> p"
  shows "replace_par s P c |_ q = s |_ q"
  using assms
proof (induct q arbitrary: s P c)
  case (Cons i q)
  then obtain f ss where s: "s = Fun f ss" and i: "i < length ss" and q: "q \<in> poss (ss ! i)"
    by (cases s) auto
  have "[] \<notin> P" using Cons.prems(2) by auto
  moreover have "\<forall>p \<in> {p. i # p \<in> P}. q \<parallel> p" using Cons.prems(2) by auto
  ultimately show ?case
    using Cons.hyps[OF q, of "{p. i # p \<in> P}"] s i by (simp add: replace_par_Fun)
qed simp

lemma replace_par_poss:
  assumes "q \<in> poss s" and "\<forall>p \<in> P. \<not> p <\<^sub>p q"
  shows "q \<in> poss (replace_par s P c)"
  using assms
proof (induct q arbitrary: s P c)
  case (Cons i q)
  then obtain f ss where s: "s = Fun f ss" and i: "i < length ss" and q: "q \<in> poss (ss ! i)"
    by (cases s) auto
  have "[] \<notin> P" using Cons.prems(2) unfolding prefix_less_def by auto
  moreover have "\<forall>p \<in> {p. i # p \<in> P}. \<not> p <\<^sub>p q" using Cons.prems(2) by auto
  ultimately show ?case
    using Cons.hyps[OF q, of "{p. i # p \<in> P}"] s i by (simp add: replace_par_Fun)
qed simp

lemma replace_par_overwrite:
  assumes "parallel_set Q"
  shows "replace_par (replace_par s Q a) Q b = replace_par s Q b"
  using assms
proof (induct s arbitrary: Q a b)
  case (Var x)
  then show ?case by (cases "[] \<in> Q") (auto simp: replace_par_root replace_par_Var)
next
  case (Fun f ss)
  show ?case
  proof (cases "[] \<in> Q")
    case False
    have "parallel_set {p. i # p \<in> Q}" for i
      using parallel_set_below[OF Fun.prems, of "[i]"] by simp
    then show ?thesis using False Fun.hyps[OF nth_mem] by (auto simp: replace_par_Fun)
  qed (simp add: replace_par_root)
qed

lemma replace_par_id: "replace_par s P (\<lambda>p. s |_ p) = s"
proof (induct s arbitrary: P)
  case (Var x)
  then show ?case by (cases "[] \<in> P") (auto simp: replace_par_root replace_par_Var)
next
  case (Fun f ss)
  then show ?case
    by (cases "[] \<in> P") (auto simp: replace_par_root replace_par_Fun intro!: nth_equalityI)
qed

lemma replace_par_subst:
  assumes "P \<subseteq> poss s"
  shows "\<delta> \<cdot> replace_par s P c = replace_par (\<delta> \<cdot> s) P (\<lambda>p. \<delta> \<cdot> c p)"
  using assms
proof (induct s arbitrary: P c)
  case (Var x)
  then have "P = {} \<or> P = {[]}" by auto
  then show ?case by (auto simp: replace_par_root)
next
  case (Fun f ss)
  show ?case
  proof (cases "[] \<in> P")
    case False
    have "{p. i # p \<in> P} \<subseteq> poss (ss ! i)" if "i < length ss" for i
      using Fun.prems that by auto
    then show ?thesis using False Fun.hyps[OF nth_mem] by (auto simp: replace_par_Fun)
  qed (simp add: replace_par_root)
qed

text \<open>Replacing at all variable positions of \<open>t\<close> in an instance \<open>\<sigma>(t)\<close>.\<close>

definition var_poss :: "('f, 'v) term \<Rightarrow> pos set" where
  "var_poss t = {p \<in> poss t. \<exists>x. t |_ p = Var x}"

lemma var_poss_Var [simp]: "var_poss (Var x) = {[]}"
  by (auto simp: var_poss_def)

lemma var_poss_Fun: "var_poss (Fun f ts) = {i # p | i p. i < length ts \<and> p \<in> var_poss (ts ! i)}"
proof (intro set_eqI iffI)
  fix x assume "x \<in> var_poss (Fun f ts)"
  then show "x \<in> {i # p | i p. i < length ts \<and> p \<in> var_poss (ts ! i)}"
    by (cases x) (auto simp: var_poss_def)
qed (auto simp: var_poss_def)

lemma var_poss_subset: "var_poss t \<subseteq> poss t"
  by (auto simp: var_poss_def)

lemma parallel_set_var_poss: "parallel_set (var_poss t)"
proof (induct t)
  case (Fun f ts)
  show ?case
    unfolding parallel_set_def var_poss_Fun
    using Fun.hyps[OF nth_mem] by (fastforce simp: parallel_set_def)
qed (simp add: parallel_set_def)

lemma replace_par_var_poss: "replace_par (\<sigma> \<cdot> t) (var_poss t) (\<lambda>p. \<tau> \<cdot> (t |_ p)) = \<tau> \<cdot> t"
proof (induct t)
  case (Var x)
  then show ?case by (simp add: replace_par_root)
next
  case (Fun f ts)
  have "{p. i # p \<in> var_poss (Fun f ts)} = var_poss (ts ! i)" if "i < length ts" for i
    using that by (auto simp: var_poss_Fun)
  then show ?case
    using Fun.hyps[OF nth_mem] by (auto simp: replace_par_Fun var_poss_Fun intro!: nth_equalityI)
qed

text \<open>Every position of an instance \<open>\<sigma>(t)\<close> is a position of \<open>t\<close> or lies below a variable
  position of \<open>t\<close>.\<close>

lemma poss_subst_apply_var_poss:
  "p \<in> poss (\<sigma> \<cdot> t) \<Longrightarrow> p \<in> poss t \<or> (\<exists>q \<in> var_poss t. q \<le>\<^sub>p p)"
proof (induct t arbitrary: p)
  case (Fun f ts)
  show ?case
  proof (cases p)
    case (Cons i p')
    with Fun.prems have i: "i < length ts" and p': "p' \<in> poss (\<sigma> \<cdot> ts ! i)" by auto
    from Fun.hyps[OF nth_mem[OF i] p'] show ?thesis
    proof
      assume "\<exists>q \<in> var_poss (ts ! i). q \<le>\<^sub>p p'"
      then obtain q where "q \<in> var_poss (ts ! i)" "q \<le>\<^sub>p p'" by blast
      then have "i # q \<in> var_poss (Fun f ts)" "i # q \<le>\<^sub>p p" using Cons i by (auto simp: var_poss_Fun)
      then show ?thesis by blast
    qed (simp add: Cons i)
  qed simp
qed (auto simp: var_poss_def)

lemma replace_par_nested:
  assumes "parallel_set Q" and "Q \<subseteq> poss s"
  shows "replace_par s {q @ p | q p. q \<in> Q \<and> p \<in> P q} c =
    replace_par s Q (\<lambda>q. replace_par (s |_ q) (P q) (\<lambda>p. c (q @ p)))"
  using assms
proof (induct s arbitrary: Q P c)
  case (Var x)
  then have "Q = {} \<or> Q = {[]}" by auto
  moreover have "{q @ p | q p. q \<in> {[]} \<and> p \<in> P q} = P []" by auto
  ultimately show ?case by (auto simp: replace_par_root)
next
  case (Fun f ss)
  let ?PP = "{q @ p | q p. q \<in> Q \<and> p \<in> P q}"
  show ?case
  proof (cases "[] \<in> Q")
    case True
    then have Q: "Q = {[]}" using Fun.prems(1) parallel_set_Nil by blast
    have "?PP = P []" using Q by auto
    then show ?thesis using Q by (simp add: replace_par_root)
  next
    case False
    have nil: "[] \<notin> ?PP" using False by auto
    have sets: "{p. i # p \<in> ?PP} = {q @ p | q p. q \<in> {q. i # q \<in> Q} \<and> p \<in> P (i # q)}" for i
    proof (intro set_eqI iffI)
      fix x assume "x \<in> {p. i # p \<in> ?PP}"
      then obtain q p where "i # x = q @ p" "q \<in> Q" "p \<in> P q" by blast
      moreover from this have "q \<noteq> []" using False by auto
      ultimately show "x \<in> {q @ p | q p. q \<in> {q. i # q \<in> Q} \<and> p \<in> P (i # q)}"
        by (cases q) auto
    next
      fix x assume "x \<in> {q @ p | q p. q \<in> {q. i # q \<in> Q} \<and> p \<in> P (i # q)}"
      then obtain q p where "x = q @ p" "i # q \<in> Q" "p \<in> P (i # q)" by blast
      moreover have "i # x = (i # q) @ p" using \<open>x = q @ p\<close> by simp
      ultimately show "x \<in> {p. i # p \<in> ?PP}" by blast
    qed
    have "replace_par (ss ! i) {p. i # p \<in> ?PP} (\<lambda>p. c (i # p)) =
        replace_par (ss ! i) {q. i # q \<in> Q}
          (\<lambda>q. replace_par (Fun f ss |_ (i # q)) (P (i # q)) (\<lambda>p. c ((i # q) @ p)))"
      if i: "i < length ss" for i
    proof -
      have "parallel_set {q. i # q \<in> Q}"
        using parallel_set_below[OF Fun.prems(1), of "[i]"] by simp
      moreover have "{q. i # q \<in> Q} \<subseteq> poss (ss ! i)" using Fun.prems(2) by auto
      ultimately show ?thesis
        unfolding sets
        using Fun.hyps[OF nth_mem[OF i], of "{q. i # q \<in> Q}" "\<lambda>q. P (i # q)" "\<lambda>p. c (i # p)"]
        by simp
    qed
    then show ?thesis using False nil by (simp add: replace_par_Fun)
  qed
qed

lemma parallel_set_nested:
  assumes "parallel_set Q" and "\<And>q. q \<in> Q \<Longrightarrow> parallel_set (P q)"
  shows "parallel_set {q @ p | q p. q \<in> Q \<and> p \<in> P q}"
  unfolding parallel_set_def
proof (intro ballI)
  fix x y assume "x \<in> {q @ p | q p. q \<in> Q \<and> p \<in> P q}" and "y \<in> {q @ p | q p. q \<in> Q \<and> p \<in> P q}"
  then obtain q p q' p' where x: "x = q @ p" "q \<in> Q" "p \<in> P q" and y: "y = q' @ p'" "q' \<in> Q" "p' \<in> P q'"
    by blast
  show "x \<parallel> y \<or> x = y"
  proof (cases "q = q'")
    case True
    then show ?thesis using x y assms(2)[of q] unfolding parallel_set_def by auto
  next
    case False
    then show ?thesis using x y assms(1) parallel_append_parallel unfolding parallel_set_def by blast
  qed
qed

lemma poss_nested:
  assumes "Q \<subseteq> poss s" and "\<And>q. q \<in> Q \<Longrightarrow> P q \<subseteq> poss (s |_ q)"
  shows "{q @ p | q p. q \<in> Q \<and> p \<in> P q} \<subseteq> poss s"
  using assms poss_subt_at by blast

text \<open>Relating \<open>s[t\<^sub>p]\<^sub>p\<^sub>\<in>\<^sub>P\<close> to its recursive description.\<close>

lemma replace_par_insert:
  assumes "p \<in> poss s" and "\<forall>q \<in> Q. p \<parallel> q"
  shows "replace_par (s\<lbrakk>p \<leftarrow> t p\<rbrakk>) Q t = replace_par s (insert p Q) t"
  using assms
proof (induct p arbitrary: s Q t)
  case Nil
  then have "Q = {}" by auto
  then show ?case by (simp add: replace_par_root)
next
  case (Cons i p)
  then obtain f ss where s: "s = Fun f ss" and i: "i < length ss" and p: "p \<in> poss (ss ! i)"
    by (cases s) auto
  have Q: "[] \<notin> Q" using Cons.prems(2) by auto
  have IH: "replace_par ((ss ! i)\<lbrakk>p \<leftarrow> t (i # p)\<rbrakk>) {q. i # q \<in> Q} (\<lambda>q. t (i # q)) =
      replace_par (ss ! i) {q. i # q \<in> insert (i # p) Q} (\<lambda>q. t (i # q))"
  proof -
    have "{q. i # q \<in> insert (i # p) Q} = insert p {q. i # q \<in> Q}" by auto
    moreover have "\<forall>q \<in> {q. i # q \<in> Q}. p \<parallel> q" using Cons.prems(2) by auto
    ultimately show ?thesis using Cons.hyps[OF p, of "{q. i # q \<in> Q}" "\<lambda>q. t (i # q)"] by simp
  qed
  show ?case
    unfolding s using Q i IH by (auto simp: replace_par_Fun nth_list_update intro!: nth_equalityI)
qed

lemma replace_at_list_replace_par:
  assumes "distinct ps" and "parallel_set (set ps)" and "set ps \<subseteq> poss s"
  shows "replace_at_list s (map (\<lambda>p. (p, t p)) ps) = replace_par s (set ps) t"
  using assms
proof (induct ps arbitrary: s)
  case (Cons p ps)
  have par: "\<forall>q \<in> set ps. p \<parallel> q"
    using Cons.prems(1,2) by (auto intro: parallel_setD)
  have "set ps \<subseteq> poss (s\<lbrakk>p \<leftarrow> t p\<rbrakk>)"
    using Cons.prems(3) par by (auto intro: parallel_poss_replace_at)
  moreover have "parallel_set (set ps)" using Cons.prems(2) by (auto simp: parallel_set_def)
  ultimately show ?case
    using Cons.hyps[of "s\<lbrakk>p \<leftarrow> t p\<rbrakk>"] Cons.prems(1,3) replace_par_insert[of p s "set ps" t] par
    by simp
qed simp

lemma replace_at_set_replace_par:
  assumes "parallel_set P" and "P \<subseteq> poss s"
  shows "s\<lbrakk>P \<Leftarrow> t\<rbrakk> = replace_par s P t"
proof -
  have "finite P" using assms(2) by (rule finite_subset) simp
  then have "\<exists>ps. distinct ps \<and> set ps = P" by (metis finite_distinct_list)
  then have "distinct (SOME ps. distinct ps \<and> set ps = P) \<and> set (SOME ps. distinct ps \<and> set ps = P) = P"
    by (rule someI_ex)
  then show ?thesis
    unfolding replace_at_set_def using assms replace_at_list_replace_par by metis
qed

text \<open>The order of the replacements in \<open>s[t\<^sub>p]\<^sub>p\<^sub>\<in>\<^sub>P\<close> does not matter.\<close>

lemma replace_at_set_any_order:
  assumes "parallel_set P" and "P \<subseteq> poss s" and "distinct ps" and "set ps = P"
  shows "s\<lbrakk>P \<Leftarrow> t\<rbrakk> = replace_at_list s (map (\<lambda>p. (p, t p)) ps)"
  using assms replace_at_list_replace_par replace_at_set_replace_par by metis

text \<open>Basic properties of \<open>s[t\<^sub>p]\<^sub>p\<^sub>\<in>\<^sub>P\<close>.\<close>

lemma replace_at_set_empty [simp]: "s\<lbrakk>{} \<Leftarrow> t\<rbrakk> = s"
  by (simp add: replace_at_set_replace_par)

lemma replace_at_set_singleton: "p \<in> poss s \<Longrightarrow> s\<lbrakk>{p} \<Leftarrow> t\<rbrakk> = s\<lbrakk>p \<leftarrow> t p\<rbrakk>"
  using replace_at_set_any_order[of "{p}" s "[p]" t] by simp

lemma replace_at_set_cong:
  assumes "parallel_set P" and "P \<subseteq> poss s" and "\<And>p. p \<in> P \<Longrightarrow> c p = d p"
  shows "s\<lbrakk>P \<Leftarrow> c\<rbrakk> = s\<lbrakk>P \<Leftarrow> d\<rbrakk>"
  unfolding replace_at_set_replace_par[OF assms(1,2)] by (rule replace_par_cong) (rule assms(3))

lemma replace_at_set_subt_at:
  assumes "parallel_set P" and "P \<subseteq> poss s" and "q \<in> P"
  shows "s\<lbrakk>P \<Leftarrow> c\<rbrakk> |_ q = c q"
  using assms replace_par_subt_at by (simp add: replace_at_set_replace_par)

lemma poss_replace_at_set:
  assumes "parallel_set P" and "P \<subseteq> poss s" and "q \<in> poss s" and "\<forall>p \<in> P. \<not> p <\<^sub>p q"
  shows "q \<in> poss (s\<lbrakk>P \<Leftarrow> c\<rbrakk>)"
  using assms replace_par_poss by (simp add: replace_at_set_replace_par)

lemma poss_replace_at_set_subset:
  assumes "parallel_set P" and "P \<subseteq> poss s"
  shows "P \<subseteq> poss (s\<lbrakk>P \<Leftarrow> c\<rbrakk>)"
  using assms poss_replace_at_set parallel_not_less by blast

lemma replace_at_set_overwrite:
  assumes "parallel_set P" and "P \<subseteq> poss s"
  shows "s\<lbrakk>P \<Leftarrow> a\<rbrakk>\<lbrakk>P \<Leftarrow> b\<rbrakk> = s\<lbrakk>P \<Leftarrow> b\<rbrakk>"
  using assms poss_replace_at_set_subset[OF assms] replace_par_overwrite
  by (simp add: replace_at_set_replace_par)

lemma replace_at_set_id:
  assumes "parallel_set P" and "P \<subseteq> poss s"
  shows "s\<lbrakk>P \<Leftarrow> \<lambda>p. s |_ p\<rbrakk> = s"
  using assms replace_par_id by (simp add: replace_at_set_replace_par)

lemma subst_replace_at_set:
  assumes "parallel_set P" and "P \<subseteq> poss s"
  shows "\<delta> \<cdot> s\<lbrakk>P \<Leftarrow> c\<rbrakk> = (\<delta> \<cdot> s)\<lbrakk>P \<Leftarrow> \<lambda>p. \<delta> \<cdot> c p\<rbrakk>"
proof -
  have "P \<subseteq> poss (\<delta> \<cdot> s)" using assms(2) poss_subst_apply by blast
  then show ?thesis using assms replace_par_subst by (simp add: replace_at_set_replace_par)
qed

lemma replace_at_set_var_poss: "(\<sigma> \<cdot> t)\<lbrakk>var_poss t \<Leftarrow> \<lambda>p. \<tau> \<cdot> (t |_ p)\<rbrakk> = \<tau> \<cdot> t"
proof -
  have "var_poss t \<subseteq> poss (\<sigma> \<cdot> t)" using var_poss_subset poss_subst_apply by blast
  then show ?thesis
    by (simp add: replace_at_set_replace_par[OF parallel_set_var_poss] replace_par_var_poss)
qed

lemma replace_at_set_nested:
  assumes "parallel_set Q" and "Q \<subseteq> poss s"
    and "\<And>q. q \<in> Q \<Longrightarrow> parallel_set (P q)" and "\<And>q. q \<in> Q \<Longrightarrow> P q \<subseteq> poss (s |_ q)"
  shows "s\<lbrakk>{q @ p | q p. q \<in> Q \<and> p \<in> P q} \<Leftarrow> c\<rbrakk> = s\<lbrakk>Q \<Leftarrow> \<lambda>q. (s |_ q)\<lbrakk>P q \<Leftarrow> \<lambda>p. c (q @ p)\<rbrakk>\<rbrakk>"
proof -
  have "s\<lbrakk>{q @ p | q p. q \<in> Q \<and> p \<in> P q} \<Leftarrow> c\<rbrakk> =
      replace_par s Q (\<lambda>q. replace_par (s |_ q) (P q) (\<lambda>p. c (q @ p)))"
    using replace_at_set_replace_par[OF parallel_set_nested[OF assms(1,3)] poss_nested[OF assms(2,4)]]
      replace_par_nested[OF assms(1,2)] by simp
  also have "\<dots> = replace_par s Q (\<lambda>q. (s |_ q)\<lbrakk>P q \<Leftarrow> \<lambda>p. c (q @ p)\<rbrakk>)"
    using assms by (intro replace_par_cong) (simp add: replace_at_set_replace_par)
  finally show ?thesis using assms by (simp add: replace_at_set_replace_par)
qed

subsubsection \<open>Basic properties of parallel reduction\<close>

lemma par_rstep_atI:
  assumes "parallel_set P" and "P \<subseteq> poss s"
    and "\<And>p. p \<in> P \<Longrightarrow> \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c p = \<sigma> \<cdot> r"
  shows "par_rstep_at R P s (s\<lbrakk>P \<Leftarrow> c\<rbrakk>)"
  using assms unfolding par_rstep_at_def by blast

lemma par_rstep_atE:
  assumes "par_rstep_at R P s t"
  obtains c where "parallel_set P" and "P \<subseteq> poss s"
    and "\<And>p. p \<in> P \<Longrightarrow> \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c p = \<sigma> \<cdot> r" and "t = s\<lbrakk>P \<Leftarrow> c\<rbrakk>"
  using assms unfolding par_rstep_at_def by blast

lemma par_rstepI: "par_rstep_at R P s t \<Longrightarrow> (s, t) \<in> par_rstep R"
  unfolding par_rstep_def by blast

lemma par_rstepE:
  assumes "(s, t) \<in> par_rstep R"
  obtains P where "par_rstep_at R P s t"
  using assms unfolding par_rstep_def by blast

text \<open>With \<open>P = \<emptyset>\<close> we see that \<open>\<rightrightarrows>\<close> is reflexive.\<close>

lemma par_rstep_at_empty: "par_rstep_at R {} t t"
  unfolding par_rstep_at_def by simp

lemma par_rstep_refl [simp]: "(t, t) \<in> par_rstep R"
  by (rule par_rstepI[OF par_rstep_at_empty])

text \<open>Fact 6.3.8: \<open>\<rightarrow> \<subseteq> \<rightrightarrows> \<subseteq> \<rightarrow>\<^sup>*\<close>.\<close>

lemma rstep_subset_par_rstep: "rstep R \<subseteq> par_rstep R"
proof (rule subrelI)
  fix s t assume "(s, t) \<in> rstep R"
  then obtain l r p \<sigma> where R: "(l, r) \<in> R" and p: "p \<in> poss s" and s: "s |_ p = \<sigma> \<cdot> l"
    and t: "t = s\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r\<rbrakk>"
    by (rule rstepE)
  have "par_rstep_at R {p} s (s\<lbrakk>{p} \<Leftarrow> \<lambda>_. \<sigma> \<cdot> r\<rbrakk>)" using R p s by (intro par_rstep_atI) auto
  then show "(s, t) \<in> par_rstep R" using p t by (simp add: replace_at_set_singleton par_rstepI)
qed

lemma par_rstep_rule: "(l, r) \<in> R \<Longrightarrow> (\<sigma> \<cdot> l, \<sigma> \<cdot> r) \<in> par_rstep R"
  using rstep_subset_par_rstep rstepI[where p = "[]"] by fastforce

text \<open>Contracting the redexes at \<open>p\<^sub>1, \<dots>, p\<^sub>n\<close> one at a time.\<close>

lemma replace_at_list_rsteps:
  assumes "distinct ps" and "parallel_set (set ps)" and "set ps \<subseteq> poss s"
    and "\<forall>p \<in> set ps. \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c p = \<sigma> \<cdot> r"
  shows "(s, replace_at_list s (map (\<lambda>p. (p, c p)) ps)) \<in> (rstep R)\<^sup>*"
  using assms
proof (induct ps arbitrary: s)
  case (Cons p ps)
  from Cons.prems(4) obtain l r \<sigma> where R: "(l, r) \<in> R" "s |_ p = \<sigma> \<cdot> l" "c p = \<sigma> \<cdot> r" by auto
  have par: "\<forall>q \<in> set ps. p \<parallel> q" using Cons.prems(1,2) by (auto intro: parallel_setD)
  have p: "p \<in> poss s" using Cons.prems(3) by simp
  have "(s, s\<lbrakk>p \<leftarrow> c p\<rbrakk>) \<in> rstep R" using R p by (intro rstepI) auto
  moreover have "(s\<lbrakk>p \<leftarrow> c p\<rbrakk>, replace_at_list (s\<lbrakk>p \<leftarrow> c p\<rbrakk>) (map (\<lambda>p. (p, c p)) ps)) \<in> (rstep R)\<^sup>*"
  proof (rule Cons.hyps)
    show "distinct ps" using Cons.prems(1) by simp
    show "parallel_set (set ps)" using Cons.prems(2) by (rule parallel_set_subset) auto
    show "set ps \<subseteq> poss (s\<lbrakk>p \<leftarrow> c p\<rbrakk>)"
      using Cons.prems(3) par p by (auto intro: parallel_poss_replace_at)
    show "\<forall>q \<in> set ps. \<exists>l r \<sigma>. (l, r) \<in> R \<and> s\<lbrakk>p \<leftarrow> c p\<rbrakk> |_ q = \<sigma> \<cdot> l \<and> c q = \<sigma> \<cdot> r"
    proof
      fix q assume q: "q \<in> set ps"
      then have "s\<lbrakk>p \<leftarrow> c p\<rbrakk> |_ q = s |_ q"
        using par Cons.prems(3) p by (intro parallel_subt_at_replace_at) auto
      then show "\<exists>l r \<sigma>. (l, r) \<in> R \<and> s\<lbrakk>p \<leftarrow> c p\<rbrakk> |_ q = \<sigma> \<cdot> l \<and> c q = \<sigma> \<cdot> r"
        using Cons.prems(4) q by auto
    qed
  qed
  ultimately show ?case by (auto intro: converse_rtrancl_into_rtrancl)
qed simp

lemma par_rstep_subset_rtrancl: "par_rstep R \<subseteq> (rstep R)\<^sup>*"
proof (rule subrelI)
  fix s t assume "(s, t) \<in> par_rstep R"
  then obtain P c where P: "parallel_set P" "P \<subseteq> poss s"
    and redex: "\<forall>p \<in> P. \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c p = \<sigma> \<cdot> r" and t: "t = s\<lbrakk>P \<Leftarrow> c\<rbrakk>"
    unfolding par_rstep_def par_rstep_at_def by blast
  have "finite P" using P(2) by (rule finite_subset) simp
  then obtain ps where ps: "distinct ps" "set ps = P" using finite_distinct_list by metis
  have "t = replace_at_list s (map (\<lambda>p. (p, c p)) ps)" using replace_at_set_any_order[OF P ps] t by simp
  then show "(s, t) \<in> (rstep R)\<^sup>*" using replace_at_list_rsteps[OF ps(1)] P redex ps(2) by simp
qed

text \<open>Parallel steps in parallel subterms combine into one parallel step.\<close>

lemma par_rstep_at_nested:
  assumes "parallel_set Q" and "Q \<subseteq> poss s"
    and "\<And>q. q \<in> Q \<Longrightarrow> par_rstep_at R (P q) (s |_ q) (u q)"
  shows "par_rstep_at R {q @ p | q p. q \<in> Q \<and> p \<in> P q} s (s\<lbrakk>Q \<Leftarrow> u\<rbrakk>)"
proof -
  let ?PP = "{q @ p | q p. q \<in> Q \<and> p \<in> P q}"
  have Pq: "parallel_set (P q)" "P q \<subseteq> poss (s |_ q)" if "q \<in> Q" for q
    using assms(3)[OF that] unfolding par_rstep_at_def by blast+
  have "\<forall>q \<in> Q. \<exists>c. (\<forall>p \<in> P q. \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ q |_ p = \<sigma> \<cdot> l \<and> c p = \<sigma> \<cdot> r) \<and>
      u q = (s |_ q)\<lbrakk>P q \<Leftarrow> c\<rbrakk>"
    using assms(3) unfolding par_rstep_at_def by blast
  then obtain C where C: "\<And>q. q \<in> Q \<Longrightarrow>
      (\<forall>p \<in> P q. \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ q |_ p = \<sigma> \<cdot> l \<and> C q p = \<sigma> \<cdot> r) \<and>
      u q = (s |_ q)\<lbrakk>P q \<Leftarrow> C q\<rbrakk>"
    by metis
  have uniq: "(THE q. q \<in> Q \<and> q \<le>\<^sub>p q' @ p) = q'" if "q' \<in> Q" for q' p
  proof (rule the_equality)
    show "q' \<in> Q \<and> q' \<le>\<^sub>p q' @ p" using that by simp
    fix q assume q: "q \<in> Q \<and> q \<le>\<^sub>p q' @ p"
    then have "q \<le>\<^sub>p q' \<or> q' \<le>\<^sub>p q" using prefix_le_cases[of q "q' @ p" q'] by simp
    then show "q = q'" using that q assms(1) unfolding parallel_set_def parallel_def by blast
  qed
  define c where "c x = (let q = THE q. q \<in> Q \<and> q \<le>\<^sub>p x in C q (drop (length q) x))" for x
  have c: "c (q @ p) = C q p" if "q \<in> Q" for q p using uniq[OF that] by (simp add: c_def)
  show ?thesis
    unfolding par_rstep_at_def
  proof (intro conjI exI)
    show par: "parallel_set ?PP" using parallel_set_nested assms(1) Pq by blast
    show poss: "?PP \<subseteq> poss s" using poss_nested assms(2) Pq by blast
    show "\<forall>x \<in> ?PP. \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ x = \<sigma> \<cdot> l \<and> c x = \<sigma> \<cdot> r"
    proof
      fix x assume "x \<in> ?PP"
      then obtain q p where x: "x = q @ p" "q \<in> Q" "p \<in> P q" by blast
      then have "q @ p \<in> poss s" using assms(2) Pq(2) poss_subt_at by blast
      then have "s |_ x = s |_ q |_ p" using x(1) by (simp add: subt_at_append)
      then show "\<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ x = \<sigma> \<cdot> l \<and> c x = \<sigma> \<cdot> r" using C[OF x(2)] x c by auto
    qed
    have "s\<lbrakk>?PP \<Leftarrow> c\<rbrakk> = s\<lbrakk>Q \<Leftarrow> \<lambda>q. (s |_ q)\<lbrakk>P q \<Leftarrow> \<lambda>p. c (q @ p)\<rbrakk>\<rbrakk>"
      using assms(1,2) Pq by (rule replace_at_set_nested)
    also have "\<dots> = s\<lbrakk>Q \<Leftarrow> u\<rbrakk>"
      using assms(1,2) Pq C c by (intro replace_at_set_cong) (auto intro: replace_at_set_cong)
    finally show "s\<lbrakk>Q \<Leftarrow> u\<rbrakk> = s\<lbrakk>?PP \<Leftarrow> c\<rbrakk>" by simp
  qed
qed

lemma par_rstep_replace_at_set:
  assumes "parallel_set Q" and "Q \<subseteq> poss s" and "\<And>q. q \<in> Q \<Longrightarrow> (s |_ q, u q) \<in> par_rstep R"
  shows "(s, s\<lbrakk>Q \<Leftarrow> u\<rbrakk>) \<in> par_rstep R"
proof -
  have "\<forall>q \<in> Q. \<exists>P. par_rstep_at R P (s |_ q) (u q)" using assms(3) unfolding par_rstep_def by blast
  then obtain P where "\<And>q. q \<in> Q \<Longrightarrow> par_rstep_at R (P q) (s |_ q) (u q)" by metis
  from par_rstep_at_nested[OF assms(1,2) this] show ?thesis by (rule par_rstepI)
qed

text \<open>Lemma 6.4.1: \<open>\<rightrightarrows>\<close> is closed under contexts.\<close>

lemma par_rstep_ctxt:
  assumes "(u, v) \<in> par_rstep R" and "p \<in> poss s"
  shows "(s\<lbrakk>p \<leftarrow> u\<rbrakk>, s\<lbrakk>p \<leftarrow> v\<rbrakk>) \<in> par_rstep R"
proof -
  have p: "p \<in> poss (s\<lbrakk>p \<leftarrow> u\<rbrakk>)" using poss_replace_at[OF assms(2), of "[]"] by simp
  have "s\<lbrakk>p \<leftarrow> u\<rbrakk> |_ p = u" using subt_at_replace_at_append[OF assms(2), of "[]"] by simp
  then have "(s\<lbrakk>p \<leftarrow> u\<rbrakk>, s\<lbrakk>p \<leftarrow> u\<rbrakk>\<lbrakk>{p} \<Leftarrow> \<lambda>_. v\<rbrakk>) \<in> par_rstep R"
    using assms(1) p by (intro par_rstep_replace_at_set) auto
  moreover have "s\<lbrakk>p \<leftarrow> u\<rbrakk>\<lbrakk>{p} \<Leftarrow> \<lambda>_. v\<rbrakk> = s\<lbrakk>p \<leftarrow> v\<rbrakk>"
    using p replace_at_replace_at_append[OF assms(2), of "[]"] by (simp add: replace_at_set_singleton)
  ultimately show ?thesis by simp
qed

text \<open>Lemma 6.4.2: if \<open>\<sigma>(x) \<rightrightarrows> \<tau>(x)\<close> for all \<open>x \<in> Var(t)\<close>, then \<open>\<sigma>(t) \<rightrightarrows> \<tau>(t)\<close>: contract, at each
  variable position of \<open>t\<close>, the parallel step \<open>\<sigma>(x) \<rightrightarrows> \<tau>(x)\<close>.\<close>

lemma par_rstep_subst:
  assumes "\<And>x. x \<in> vars t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> par_rstep R"
  shows "(\<sigma> \<cdot> t, \<tau> \<cdot> t) \<in> par_rstep R"
proof -
  have "((\<sigma> \<cdot> t) |_ q, \<tau> \<cdot> (t |_ q)) \<in> par_rstep R" if "q \<in> var_poss t" for q
  proof -
    from that obtain x where q: "q \<in> poss t" "t |_ q = Var x" by (auto simp: var_poss_def)
    then have "x \<in> vars t" by (auto simp: vars_poss)
    then show ?thesis using assms q by (simp add: subt_at_subst_apply)
  qed
  moreover have "var_poss t \<subseteq> poss (\<sigma> \<cdot> t)" using var_poss_subset poss_subst_apply by blast
  ultimately have "(\<sigma> \<cdot> t, (\<sigma> \<cdot> t)\<lbrakk>var_poss t \<Leftarrow> \<lambda>q. \<tau> \<cdot> (t |_ q)\<rbrakk>) \<in> par_rstep R"
    using parallel_set_var_poss by (intro par_rstep_replace_at_set) auto
  then show ?thesis by (simp add: replace_at_set_var_poss)
qed

text \<open>Parallel steps are closed under substitutions: the same positions of \<open>\<delta>(s)\<close> are
  contracted.\<close>

lemma par_rstep_at_subst:
  assumes "par_rstep_at R P s t"
  shows "par_rstep_at R P (\<delta> \<cdot> s) (\<delta> \<cdot> t)"
proof -
  from assms obtain c where P: "parallel_set P" "P \<subseteq> poss s"
    and redex: "\<And>p. p \<in> P \<Longrightarrow> \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c p = \<sigma> \<cdot> r"
    and t: "t = s\<lbrakk>P \<Leftarrow> c\<rbrakk>"
    unfolding par_rstep_at_def by blast
  have "\<delta> \<cdot> t = (\<delta> \<cdot> s)\<lbrakk>P \<Leftarrow> \<lambda>p. \<delta> \<cdot> c p\<rbrakk>" using t P by (simp add: subst_replace_at_set)
  moreover have "par_rstep_at R P (\<delta> \<cdot> s) ((\<delta> \<cdot> s)\<lbrakk>P \<Leftarrow> \<lambda>p. \<delta> \<cdot> c p\<rbrakk>)"
  proof (rule par_rstep_atI)
    show "P \<subseteq> poss (\<delta> \<cdot> s)" using P(2) poss_subst_apply by blast
    fix p assume p: "p \<in> P"
    then obtain l r \<sigma> where "(l, r) \<in> R" "s |_ p = \<sigma> \<cdot> l" "c p = \<sigma> \<cdot> r" using redex by blast
    moreover have "(\<delta> \<cdot> s) |_ p = \<delta> \<cdot> (s |_ p)" using p P(2) by (auto simp: subt_at_subst_apply)
    ultimately show "\<exists>l r \<sigma>. (l, r) \<in> R \<and> (\<delta> \<cdot> s) |_ p = \<sigma> \<cdot> l \<and> \<delta> \<cdot> c p = \<sigma> \<cdot> r"
      by (intro exI[of _ l] exI[of _ r] exI[of _ "\<delta> \<circ>\<^sub>s \<sigma>"]) simp
  qed (use P in simp)
  ultimately show ?thesis by simp
qed

lemma par_rstep_subst_closed: "(s, t) \<in> par_rstep R \<Longrightarrow> (\<delta> \<cdot> s, \<delta> \<cdot> t) \<in> par_rstep R"
  by (auto elim!: par_rstepE intro: par_rstepI par_rstep_at_subst)

subsubsection \<open>Splitting a parallel step at outermost positions\<close>

text \<open>If every redex position of \<open>s \<rightrightarrows>\<^sup>P t\<close> lies below some position of a parallel set \<open>Q\<close>, then
  \<open>t = s[t|\<^sub>q]\<^sub>q\<^sub>\<in>\<^sub>Q\<close> and each \<open>s|\<^sub>q \<rightrightarrows> t|\<^sub>q\<close> contracts the redexes of \<open>P\<close> below \<open>q\<close>.\<close>

lemma par_rstep_at_decompose:
  assumes step: "par_rstep_at R P s t" and Q: "parallel_set Q" "Q \<subseteq> poss s"
    and below: "\<And>p. p \<in> P \<Longrightarrow> \<exists>q \<in> Q. q \<le>\<^sub>p p"
  shows "t = s\<lbrakk>Q \<Leftarrow> \<lambda>q. t |_ q\<rbrakk>"
    and "\<And>q. q \<in> Q \<Longrightarrow> par_rstep_at R {p. q @ p \<in> P} (s |_ q) (t |_ q)"
proof -
  from step obtain c where P: "parallel_set P" "P \<subseteq> poss s"
    and redex: "\<And>p. p \<in> P \<Longrightarrow> \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c p = \<sigma> \<cdot> r"
    and t: "t = s\<lbrakk>P \<Leftarrow> c\<rbrakk>"
    unfolding par_rstep_at_def by blast
  define Pq where "Pq q = {p. q @ p \<in> P}" for q
  have PP: "P = {q @ p | q p. q \<in> Q \<and> p \<in> Pq q}"
    using below unfolding Pq_def prefix_le_def by blast
  have Pq1: "parallel_set (Pq q)" for q
    unfolding Pq_def by (rule parallel_set_below[OF P(1)])
  have Pq2: "Pq q \<subseteq> poss (s |_ q)" if "q \<in> Q" for q
    using P(2) Q(2) that poss_subt_at unfolding Pq_def by blast
  let ?u = "\<lambda>q. (s |_ q)\<lbrakk>Pq q \<Leftarrow> \<lambda>p. c (q @ p)\<rbrakk>"
  have tu: "t = s\<lbrakk>Q \<Leftarrow> ?u\<rbrakk>"
    using t replace_at_set_nested[OF Q Pq1 Pq2, of c] PP by simp
  have tq: "t |_ q = ?u q" if "q \<in> Q" for q
    using replace_at_set_subt_at[OF Q that, of ?u] tu by simp
  have "s\<lbrakk>Q \<Leftarrow> ?u\<rbrakk> = s\<lbrakk>Q \<Leftarrow> \<lambda>q. t |_ q\<rbrakk>"
    using Q tq by (intro replace_at_set_cong) auto
  then show "t = s\<lbrakk>Q \<Leftarrow> \<lambda>q. t |_ q\<rbrakk>" using tu by simp
  show "par_rstep_at R {p. q @ p \<in> P} (s |_ q) (t |_ q)" if q: "q \<in> Q" for q
  proof -
    have "par_rstep_at R (Pq q) (s |_ q) (?u q)"
    proof (rule par_rstep_atI[OF Pq1 Pq2[OF q]])
      fix p assume "p \<in> Pq q"
      then have qp: "q @ p \<in> P" by (simp add: Pq_def)
      with P(2) have "s |_ (q @ p) = s |_ q |_ p" by (intro subt_at_append) auto
      then show "\<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ q |_ p = \<sigma> \<cdot> l \<and> c (q @ p) = \<sigma> \<cdot> r"
        using redex[OF qp] by metis
    qed
    then show ?thesis using tq[OF q] by (simp add: Pq_def)
  qed
qed

text \<open>A peak \<open>t\<^sub>0 \<leftleftarrows>\<^sup>P\<^sup>0 s \<rightrightarrows>\<^sup>P\<^sup>1 t\<^sub>1\<close> can be joined by joining, for each outermost position \<open>q\<close> of
  \<open>P\<^sub>0 \<union> P\<^sub>1\<close>, the peak \<open>t\<^sub>0|\<^sub>q \<leftleftarrows> s|\<^sub>q \<rightrightarrows> t\<^sub>1|\<^sub>q\<close>; in each of these, one of the two steps is a
  contraction at the root.\<close>

lemma par_peak_outermost:
  assumes step0: "par_rstep_at R P\<^sub>0 s t\<^sub>0" and step1: "par_rstep_at R P\<^sub>1 s t\<^sub>1"
    and local: "\<And>q. q \<in> outermost (P\<^sub>0 \<union> P\<^sub>1) \<Longrightarrow>
      \<exists>u. (t\<^sub>0 |_ q, u) \<in> par_rstep R \<and> (t\<^sub>1 |_ q, u) \<in> par_rstep R"
  shows "\<exists>u. (t\<^sub>0, u) \<in> par_rstep R \<and> (t\<^sub>1, u) \<in> par_rstep R"
proof -
  let ?Q = "outermost (P\<^sub>0 \<union> P\<^sub>1)"
  have Q: "parallel_set ?Q" "?Q \<subseteq> poss s"
    using parallel_set_outermost outermost_subset step0 step1 unfolding par_rstep_at_def by blast+
  have below: "\<exists>q \<in> ?Q. q \<le>\<^sub>p p" if "p \<in> P\<^sub>0 \<union> P\<^sub>1" for p using outermost_exists[OF that] .
  obtain u where u: "\<And>q. q \<in> ?Q \<Longrightarrow> (t\<^sub>0 |_ q, u q) \<in> par_rstep R \<and> (t\<^sub>1 |_ q, u q) \<in> par_rstep R"
    using local by metis
  have join: "(t, s\<lbrakk>?Q \<Leftarrow> u\<rbrakk>) \<in> par_rstep R"
    if teq: "t = s\<lbrakk>?Q \<Leftarrow> \<lambda>q. t |_ q\<rbrakk>" and tu: "\<And>q. q \<in> ?Q \<Longrightarrow> (t |_ q, u q) \<in> par_rstep R" for t
  proof -
    have "?Q \<subseteq> poss t" by (subst teq) (rule poss_replace_at_set_subset[OF Q])
    then have "(t, t\<lbrakk>?Q \<Leftarrow> u\<rbrakk>) \<in> par_rstep R" using Q(1) tu by (intro par_rstep_replace_at_set)
    moreover have "t\<lbrakk>?Q \<Leftarrow> u\<rbrakk> = s\<lbrakk>?Q \<Leftarrow> u\<rbrakk>" by (subst teq) (rule replace_at_set_overwrite[OF Q])
    ultimately show ?thesis by simp
  qed
  have "(t\<^sub>0, s\<lbrakk>?Q \<Leftarrow> u\<rbrakk>) \<in> par_rstep R"
    using par_rstep_at_decompose(1)[OF step0 Q] below u by (intro join) auto
  moreover have "(t\<^sub>1, s\<lbrakk>?Q \<Leftarrow> u\<rbrakk>) \<in> par_rstep R"
    using par_rstep_at_decompose(1)[OF step1 Q] below u by (intro join) auto
  ultimately show ?thesis by blast
qed

lemma par_rstep_at_outermost:
  assumes step0: "par_rstep_at R P\<^sub>0 s t\<^sub>0" and step1: "par_rstep_at R P\<^sub>1 s t\<^sub>1"
    and q: "q \<in> outermost (P\<^sub>0 \<union> P\<^sub>1)"
  shows "par_rstep_at R {p. q @ p \<in> P\<^sub>0} (s |_ q) (t\<^sub>0 |_ q)"
    and "par_rstep_at R {p. q @ p \<in> P\<^sub>1} (s |_ q) (t\<^sub>1 |_ q)"
proof -
  let ?Q = "outermost (P\<^sub>0 \<union> P\<^sub>1)"
  have Q: "parallel_set ?Q" "?Q \<subseteq> poss s"
    using parallel_set_outermost outermost_subset step0 step1 unfolding par_rstep_at_def by blast+
  have below: "\<exists>q \<in> ?Q. q \<le>\<^sub>p p" if "p \<in> P\<^sub>0 \<union> P\<^sub>1" for p using outermost_exists[OF that] .
  show "par_rstep_at R {p. q @ p \<in> P\<^sub>0} (s |_ q) (t\<^sub>0 |_ q)"
    using par_rstep_at_decompose(2)[OF step0 Q _ q] below by blast
  show "par_rstep_at R {p. q @ p \<in> P\<^sub>1} (s |_ q) (t\<^sub>1 |_ q)"
    using par_rstep_at_decompose(2)[OF step1 Q _ q] below by blast
qed

text \<open>Lemma 6.4.4 (Parallel Moves Lemma). If \<open>l\<close> is linear and no redex of the parallel step
  \<open>\<sigma>(l) \<rightrightarrows>\<^sup>P t\<close> lies at a non-variable position of \<open>l\<close>, then the step takes place inside the
  substitution: \<open>t = \<tau>(l)\<close> with \<open>\<sigma>(x) \<rightrightarrows> \<tau>(x)\<close> for all \<open>x \<in> Var(l)\<close>.\<close>

lemma linear_var_pos_unique:
  assumes "linear_term t" and "p \<in> poss t" and "q \<in> poss t"
    and "t |_ p = Var x" and "t |_ q = Var x"
  shows "p = q"
  using assms
proof (induct t arbitrary: p q)
  case (Fun f ts)
  then obtain i p' j q' where p: "p = i # p'" "i < length ts" "p' \<in> poss (ts ! i)" "ts ! i |_ p' = Var x"
    and q: "q = j # q'" "j < length ts" "q' \<in> poss (ts ! j)" "ts ! j |_ q' = Var x"
    by (cases p; cases q) auto
  have "x \<in> vars (ts ! i)" "x \<in> vars (ts ! j)" using p q by (auto simp: vars_poss)
  then have "i = j" using Fun.prems(1) p(2) q(2) by auto
  then show ?case using Fun.hyps[OF nth_mem[OF p(2)]] Fun.prems(1) p q by auto
qed simp

lemma par_rstep_at_linear:
  assumes lin: "linear_term l" and step: "par_rstep_at R P (\<sigma> \<cdot> l) t"
    and var: "\<And>p. p \<in> P \<Longrightarrow> p \<in> poss l \<Longrightarrow> \<exists>x. l |_ p = Var x"
  shows "\<exists>\<tau>. t = \<tau> \<cdot> l \<and> (\<forall>x \<in> vars l. (\<sigma> x, \<tau> x) \<in> par_rstep R)"
proof -
  let ?Q = "var_poss l"
  have Q: "parallel_set ?Q" "?Q \<subseteq> poss (\<sigma> \<cdot> l)"
    using parallel_set_var_poss var_poss_subset poss_subst_apply by blast+
  have below: "\<exists>q \<in> ?Q. q \<le>\<^sub>p p" if p: "p \<in> P" for p
  proof -
    have "p \<in> poss (\<sigma> \<cdot> l)" using step p unfolding par_rstep_at_def by blast
    from poss_subst_apply_var_poss[OF this] show ?thesis
    proof
      assume "p \<in> poss l"
      then have "p \<in> ?Q" using var[OF p] by (auto simp: var_poss_def)
      then show ?thesis using prefix_le_refl by blast
    qed
  qed
  have dec1: "t = (\<sigma> \<cdot> l)\<lbrakk>?Q \<Leftarrow> \<lambda>q. t |_ q\<rbrakk>"
    using par_rstep_at_decompose(1)[OF step Q] below by blast
  have dec2: "par_rstep_at R {p. q @ p \<in> P} ((\<sigma> \<cdot> l) |_ q) (t |_ q)" if "q \<in> ?Q" for q
    using par_rstep_at_decompose(2)[OF step Q _ that] below by blast
  define \<tau> where "\<tau> x = (if x \<in> vars l then t |_ (THE q. q \<in> poss l \<and> l |_ q = Var x) else \<sigma> x)" for x
  have \<tau>q: "\<tau> x = t |_ q" if "q \<in> ?Q" and "l |_ q = Var x" for q x
  proof -
    have q: "q \<in> poss l" using that by (simp add: var_poss_def)
    then have "x \<in> vars l" using that by (auto simp: vars_poss)
    moreover have "(THE q. q \<in> poss l \<and> l |_ q = Var x) = q"
      using q that(2) linear_var_pos_unique[OF lin] by (intro the_equality) auto
    ultimately show ?thesis by (simp add: \<tau>_def)
  qed
  have "t = (\<sigma> \<cdot> l)\<lbrakk>?Q \<Leftarrow> \<lambda>q. t |_ q\<rbrakk>" by (rule dec1)
  also have "\<dots> = (\<sigma> \<cdot> l)\<lbrakk>?Q \<Leftarrow> \<lambda>q. \<tau> \<cdot> (l |_ q)\<rbrakk>"
  proof (rule replace_at_set_cong[OF Q])
    fix q assume q: "q \<in> ?Q"
    then obtain x where "l |_ q = Var x" by (auto simp: var_poss_def)
    then show "t |_ q = \<tau> \<cdot> (l |_ q)" using \<tau>q[OF q] by simp
  qed
  also have "\<dots> = \<tau> \<cdot> l" by (rule replace_at_set_var_poss)
  finally have "t = \<tau> \<cdot> l" .
  moreover have "(\<sigma> x, \<tau> x) \<in> par_rstep R" if "x \<in> vars l" for x
  proof -
    from that[unfolded vars_poss] obtain q where q: "q \<in> poss l" "l |_ q = Var x" by blast
    then have Qq: "q \<in> ?Q" by (auto simp: var_poss_def)
    have "(\<sigma> \<cdot> l) |_ q = \<sigma> x" using q by (simp add: subt_at_subst_apply)
    then show ?thesis using dec2[OF Qq] \<tau>q[OF Qq q(2)] by (auto intro: par_rstepI)
  qed
  ultimately show ?thesis by blast
qed

context TRS_inf
begin

text \<open>Overlaps at the root of two rules in an orthogonal system are trivial.\<close>

lemma root_overlap:
  assumes CP: "CP R = {}" and R: "(l\<^sub>1, r\<^sub>1) \<in> R" "(l\<^sub>2, r\<^sub>2) \<in> R" and eq: "\<sigma>\<^sub>1 \<cdot> l\<^sub>1 = \<sigma>\<^sub>2 \<cdot> l\<^sub>2"
  shows "\<sigma>\<^sub>1 \<cdot> r\<^sub>1 = \<sigma>\<^sub>2 \<cdot> r\<^sub>2"
proof (cases "(l\<^sub>1, r\<^sub>1) = (l\<^sub>2, r\<^sub>2)")
  case True
  then have l: "\<sigma>\<^sub>1 \<cdot> l\<^sub>1 = \<sigma>\<^sub>2 \<cdot> l\<^sub>1" using eq by simp
  have "\<sigma>\<^sub>1 \<cdot> r\<^sub>1 = \<sigma>\<^sub>2 \<cdot> r\<^sub>1"
    by (intro subst_apply_cong subst_apply_eq_vars[OF l]) (use rule_vars[OF R(1)] in auto)
  then show ?thesis using True by simp
next
  case False
  have "\<forall>x. l\<^sub>1 |_ [] \<noteq> Var x" using rule_lhs_not_Var[OF R(1)] by simp
  from overlap_imp_CP[OF infinite_vars R _ this _ , of \<sigma>\<^sub>1 \<sigma>\<^sub>2] eq False CP show ?thesis by simp
qed

text \<open>Lemma 6.3.9: without critical pairs, contracting a redex at a fixed position is
  deterministic.\<close>

lemma no_CP_same_position:
  assumes "CP R = {}" and "(l\<^sub>1, r\<^sub>1) \<in> R" "(l\<^sub>2, r\<^sub>2) \<in> R"
    and "s |_ p = \<sigma>\<^sub>1 \<cdot> l\<^sub>1" and "s |_ p = \<sigma>\<^sub>2 \<cdot> l\<^sub>2"
  shows "s\<lbrakk>p \<leftarrow> \<sigma>\<^sub>1 \<cdot> r\<^sub>1\<rbrakk> = s\<lbrakk>p \<leftarrow> \<sigma>\<^sub>2 \<cdot> r\<^sub>2\<rbrakk>"
proof -
  have "\<sigma>\<^sub>1 \<cdot> r\<^sub>1 = \<sigma>\<^sub>2 \<cdot> r\<^sub>2" using root_overlap[OF assms(1-3)] assms(4,5) by metis
  then show ?thesis by simp
qed

text \<open>A peak in which one of the two steps contracts a redex at the root. If the other step
  also contracts a redex at the root, both results coincide by Lemma 6.3.9. Otherwise, as there
  are no critical pairs, no redex of the other step lies at a non-variable position of the
  left-hand side, and Lemma 6.4.4 applies.\<close>

lemma orthogonal_root_peak:
  assumes orth: "orthogonal R" and step0: "par_rstep_at R P\<^sub>0 s t\<^sub>0"
    and step1: "par_rstep_at R P\<^sub>1 s t\<^sub>1" and root: "[] \<in> P\<^sub>0"
  shows "\<exists>u. (t\<^sub>0, u) \<in> par_rstep R \<and> (t\<^sub>1, u) \<in> par_rstep R"
proof -
  from step0 obtain c where P0: "parallel_set P\<^sub>0"
    and redex0: "\<And>p. p \<in> P\<^sub>0 \<Longrightarrow> \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c p = \<sigma> \<cdot> r"
    and t0: "t\<^sub>0 = s\<lbrakk>P\<^sub>0 \<Leftarrow> c\<rbrakk>"
    unfolding par_rstep_at_def by blast
  from step1 obtain c' where P1: "parallel_set P\<^sub>1"
    and redex1: "\<And>p. p \<in> P\<^sub>1 \<Longrightarrow> \<exists>l r \<sigma>. (l, r) \<in> R \<and> s |_ p = \<sigma> \<cdot> l \<and> c' p = \<sigma> \<cdot> r"
    and t1: "t\<^sub>1 = s\<lbrakk>P\<^sub>1 \<Leftarrow> c'\<rbrakk>"
    unfolding par_rstep_at_def by blast
  obtain l r \<sigma> where R: "(l, r) \<in> R" and seq: "s = \<sigma> \<cdot> l" and c: "c [] = \<sigma> \<cdot> r"
    using redex0[OF root] by auto
  have t0': "t\<^sub>0 = \<sigma> \<cdot> r" using t0 c parallel_set_Nil[OF P0 root] by (simp add: replace_at_set_singleton)
  show ?thesis
  proof (cases "[] \<in> P\<^sub>1")
    case True
    obtain l' r' \<sigma>' where R': "(l', r') \<in> R" and s': "s = \<sigma>' \<cdot> l'" and c': "c' [] = \<sigma>' \<cdot> r'"
      using redex1[OF True] by auto
    have "t\<^sub>1 = \<sigma>' \<cdot> r'" using t1 c' parallel_set_Nil[OF P1 True] by (simp add: replace_at_set_singleton)
    also have "\<dots> = \<sigma> \<cdot> r"
      using root_overlap[of l' r' l r \<sigma>' \<sigma>] R R' s' seq orth by (simp add: orthogonal_def)
    finally show ?thesis using t0' by (intro exI[of _ "\<sigma> \<cdot> r"]) simp
  next
    case False
    have var: "\<exists>x. l |_ p = Var x" if p: "p \<in> P\<^sub>1" "p \<in> poss l" for p
    proof (rule ccontr)
      assume nv: "\<nexists>x. l |_ p = Var x"
      obtain l' r' \<sigma>' where R': "(l', r') \<in> R" and "s |_ p = \<sigma>' \<cdot> l'" using redex1[OF p(1)] by blast
      then have "\<sigma> \<cdot> (l |_ p) = \<sigma>' \<cdot> l'" using seq p(2) by (simp add: subt_at_subst_apply)
      from overlap_imp_CP[OF infinite_vars R R' p(2) _ this] nv False p(1)
      have "CP R \<noteq> {}" by auto
      then show False using orth by (simp add: orthogonal_def)
    qed
    have lin: "linear_term l" using orth R unfolding orthogonal_def left_linear_def by auto
    obtain \<tau> where t1': "t\<^sub>1 = \<tau> \<cdot> l" and \<sigma>\<tau>: "\<forall>x \<in> vars l. (\<sigma> x, \<tau> x) \<in> par_rstep R"
      using par_rstep_at_linear[OF lin step1[unfolded seq] var] by blast
    have "(t\<^sub>0, \<tau> \<cdot> r) \<in> par_rstep R"
      unfolding t0' using rule_vars[OF R] \<sigma>\<tau> by (intro par_rstep_subst) auto
    moreover have "(t\<^sub>1, \<tau> \<cdot> r) \<in> par_rstep R" unfolding t1' using R by (rule par_rstep_rule)
    ultimately show ?thesis by blast
  qed
qed

text \<open>Theorem 6.3.10: in an orthogonal TRS, parallel reduction has the diamond property. Given
  \<open>t\<^sub>0 \<leftleftarrows>\<^sup>P\<^sup>0 s \<rightrightarrows>\<^sup>P\<^sup>1 t\<^sub>1\<close>, we join the peaks below the outermost positions of \<open>P\<^sub>0 \<union> P\<^sub>1\<close>.\<close>

theorem orthogonal_par_rstep_diamond:
  assumes orth: "orthogonal R"
  shows "\<diamond> (par_rstep R)"
  unfolding diamond_def
proof (intro allI impI, elim conjE)
  fix s t\<^sub>0 t\<^sub>1 assume "(s, t\<^sub>0) \<in> par_rstep R" and "(s, t\<^sub>1) \<in> par_rstep R"
  then obtain P\<^sub>0 P\<^sub>1 where step0: "par_rstep_at R P\<^sub>0 s t\<^sub>0" and step1: "par_rstep_at R P\<^sub>1 s t\<^sub>1"
    by (auto elim!: par_rstepE)
  show "\<exists>u. (t\<^sub>0, u) \<in> par_rstep R \<and> (t\<^sub>1, u) \<in> par_rstep R"
  proof (rule par_peak_outermost[OF step0 step1])
    fix q assume q: "q \<in> outermost (P\<^sub>0 \<union> P\<^sub>1)"
    note local = par_rstep_at_outermost[OF step0 step1 q]
    have "q \<in> P\<^sub>0 \<or> q \<in> P\<^sub>1" using q outermost_subset by blast
    then show "\<exists>u. (t\<^sub>0 |_ q, u) \<in> par_rstep R \<and> (t\<^sub>1 |_ q, u) \<in> par_rstep R"
    proof
      assume "q \<in> P\<^sub>0"
      then show ?thesis using orthogonal_root_peak[OF orth local] by simp
    next
      assume "q \<in> P\<^sub>1"
      then show ?thesis using orthogonal_root_peak[OF orth local(2) local(1)] by auto
    qed
  qed
qed

text \<open>Corollary 6.3.11: every orthogonal TRS is confluent.\<close>

corollary orthogonal_imp_confluent:
  assumes "orthogonal R"
  shows is_confluent
  by (rule diamond_between_imp_confluent[OF orthogonal_par_rstep_diamond[OF assms]
        rstep_subset_par_rstep par_rstep_subset_rtrancl])

end

end
