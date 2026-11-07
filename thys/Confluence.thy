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

text \<open>Definition 6.3.7. The book defines \<open>s \<rightrightarrows> t\<close> as the simultaneous contraction of redexes
  at a set of parallel positions of \<open>s\<close>. We use the equivalent inductive characterisation:
  a parallel step either contracts a redex at the root, or performs parallel steps in all
  arguments of a function symbol (possibly the empty step, which makes \<open>\<rightrightarrows>\<close> reflexive).\<close>

inductive_set par_rstep :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term rel" for R where
  var: "(Var x, Var x) \<in> par_rstep R"
| args: "length ss = length ts \<Longrightarrow> (\<And>i. i < length ts \<Longrightarrow> (ss ! i, ts ! i) \<in> par_rstep R) \<Longrightarrow>
    (Fun f ss, Fun f ts) \<in> par_rstep R"
| rule: "(l, r) \<in> R \<Longrightarrow> (\<sigma> \<cdot> l, \<sigma> \<cdot> r) \<in> par_rstep R"

lemma par_rstep_refl [simp]: "(t, t) \<in> par_rstep R"
  by (induct t) (auto intro: par_rstep.intros)

lemma par_rstep_ctxt:
  assumes "(u, v) \<in> par_rstep R" and "p \<in> poss s"
  shows "(s\<lbrakk>p \<leftarrow> u\<rbrakk>, s\<lbrakk>p \<leftarrow> v\<rbrakk>) \<in> par_rstep R"
  using assms(2)
proof (induct p arbitrary: s)
  case Nil
  then show ?case using assms(1) by simp
next
  case (Cons i p)
  then obtain f ss where s: "s = Fun f ss" and i: "i < length ss" and p: "p \<in> poss (ss ! i)"
    by (cases s) auto
  show ?case
    unfolding s using Cons.hyps[OF p] i
    by (auto intro!: par_rstep.args simp: nth_list_update)
qed

lemma par_rstep_subst:
  assumes "\<And>x. x \<in> vars t \<Longrightarrow> (\<sigma> x, \<tau> x) \<in> par_rstep R"
  shows "(\<sigma> \<cdot> t, \<tau> \<cdot> t) \<in> par_rstep R"
  using assms
proof (induct t)
  case (Fun f ts)
  show ?case
    by (simp, rule par_rstep.args) (auto intro!: Fun.hyps Fun.prems bexI[OF _ nth_mem])
qed simp

text \<open>Fact 6.3.8: \<open>\<rightarrow> \<subseteq> \<rightrightarrows> \<subseteq> \<rightarrow>\<^sup>*\<close>.\<close>

lemma rstep_subset_par_rstep: "rstep R \<subseteq> par_rstep R"
proof (rule subrelI)
  fix s t assume "(s, t) \<in> rstep R"
  then obtain l r p \<sigma> where "(l, r) \<in> R" "p \<in> poss s" "s |_ p = \<sigma> \<cdot> l" "t = s\<lbrakk>p \<leftarrow> \<sigma> \<cdot> r\<rbrakk>"
    by (rule rstepE)
  then show "(s, t) \<in> par_rstep R"
    using par_rstep_ctxt[OF par_rstep.rule, of l r R p s \<sigma>] replace_at_subt_at[of p s] by simp
qed

lemma par_rstep_subset_rtrancl: "par_rstep R \<subseteq> (rstep R)\<^sup>*"
proof (rule subrelI)
  fix s t assume "(s, t) \<in> par_rstep R"
  then show "(s, t) \<in> (rstep R)\<^sup>*"
  proof (induct rule: par_rstep.induct)
    case (args ss ts f)
    then show ?case by (intro closed_opsD[OF closed_ops_rtrancl[OF compatible_ops_rstep]]) auto
  next
    case (rule l r \<sigma>)
    then show ?case by (auto intro!: rstepI[where p = "[]"])
  qed simp
qed

lemma linear_term_subt_at: "linear_term t \<Longrightarrow> p \<in> poss t \<Longrightarrow> linear_term (t |_ p)"
proof (induct p arbitrary: t)
  case (Cons i p)
  then show ?case by (cases t) auto
qed simp

text \<open>Substitutions defined on pairwise variable-disjoint terms can be merged.\<close>

lemma merge_substs:
  assumes "\<And>i j. i < n \<Longrightarrow> j < n \<Longrightarrow> i \<noteq> j \<Longrightarrow> V i \<inter> V j = {}"
  shows "\<exists>\<tau>. \<forall>i < n. \<forall>x \<in> V i. \<tau> x = \<tau>s i x"
proof -
  define \<tau> where "\<tau> x = \<tau>s (SOME i. i < n \<and> x \<in> V i) x" for x
  have "\<tau> x = \<tau>s i x" if "i < n" "x \<in> V i" for i x
  proof -
    have "(SOME i. i < n \<and> x \<in> V i) = i"
      using that assms by (intro some_equality) blast+
    then show ?thesis by (simp add: \<tau>_def)
  qed
  then show ?thesis by blast
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

text \<open>The key lemma for orthogonal systems: in a left-linear system without critical pairs,
  a parallel step from an instance \<open>\<sigma>(u)\<close> of a proper subterm \<open>u\<close> of a left-hand side
  takes place entirely inside the substitution.\<close>

lemma par_rstep_below_lhs:
  assumes orth: "orthogonal R" and R: "(l, r) \<in> R"
  shows "p \<in> poss l \<Longrightarrow> p \<noteq> [] \<Longrightarrow> l |_ p = u \<Longrightarrow> (\<sigma> \<cdot> u, t) \<in> par_rstep R \<Longrightarrow>
    \<exists>\<tau>. t = \<tau> \<cdot> u \<and> (\<forall>x \<in> vars u. (\<sigma> x, \<tau> x) \<in> par_rstep R)"
proof (induct u arbitrary: p t)
  case (Var x)
  then show ?case by (intro exI[of _ "\<lambda>_. t"]) auto
next
  case (Fun f us)
  have lin: "linear_term (Fun f us)"
    using orth R linear_term_subt_at[OF _ Fun.prems(1)] Fun.prems(3)
    unfolding orthogonal_def left_linear_def by auto
  from Fun.prems(4) show ?case
  proof cases
    case (args ss ts g)
    then have len: "length ts = length us" and ss: "ss = map ((\<cdot>) \<sigma>) us" and g: "g = f" by auto
    have "\<exists>\<tau>. ts ! i = \<tau> \<cdot> us ! i \<and> (\<forall>x \<in> vars (us ! i). (\<sigma> x, \<tau> x) \<in> par_rstep R)"
      if i: "i < length us" for i
    proof -
      have pi: "p @ [i] \<in> poss l"
        using poss_subt_at[OF Fun.prems(1), of "[i]"] Fun.prems(3) i by simp
      moreover have "l |_ (p @ [i]) = us ! i"
        using subt_at_append[OF pi] Fun.prems(3) by simp
      moreover have "(\<sigma> \<cdot> us ! i, ts ! i) \<in> par_rstep R" using args(4) i len ss by auto
      ultimately show ?thesis using Fun.hyps[OF nth_mem[OF i]] by blast
    qed
    then obtain \<tau>s where \<tau>s: "\<And>i. i < length us \<Longrightarrow>
        ts ! i = \<tau>s i \<cdot> us ! i \<and> (\<forall>x \<in> vars (us ! i). (\<sigma> x, \<tau>s i x) \<in> par_rstep R)"
      by metis
    obtain \<tau> where \<tau>: "\<And>i x. i < length us \<Longrightarrow> x \<in> vars (us ! i) \<Longrightarrow> \<tau> x = \<tau>s i x"
      using merge_substs[of "length us" "\<lambda>i. vars (us ! i)" \<tau>s] lin by auto
    have "ts ! i = \<tau> \<cdot> us ! i" if "i < length us" for i
      using \<tau>s[OF that] \<tau>[OF that] by (auto intro: subst_apply_cong)
    then have "t = \<tau> \<cdot> Fun f us" using args(2) len g by (auto intro: nth_equalityI)
    moreover have "\<forall>x \<in> vars (Fun f us). (\<sigma> x, \<tau> x) \<in> par_rstep R"
      using \<tau>s \<tau> by (auto simp: in_set_conv_nth)
    ultimately show ?thesis by blast
  next
    case (rule l' r' \<sigma>')
    have "\<sigma> \<cdot> (l |_ p) = \<sigma>' \<cdot> l'" using rule Fun.prems(3) by simp
    from overlap_imp_CP[OF infinite_vars R rule(3) Fun.prems(1) _ this] Fun.prems(2,3)
    have "CP R \<noteq> {}" by auto
    then show ?thesis using orth by (simp add: orthogonal_def)
  qed simp
qed

text \<open>A root redex against an arbitrary parallel step.\<close>

lemma par_rstep_root_peak:
  assumes orth: "orthogonal R" and R: "(l, r) \<in> R" and st: "(\<sigma> \<cdot> l, t) \<in> par_rstep R"
  shows "\<exists>u. (\<sigma> \<cdot> r, u) \<in> par_rstep R \<and> (t, u) \<in> par_rstep R"
  using st
proof cases
  case (var x)
  then show ?thesis using rule_lhs_not_Var[OF R] by (cases l) auto
next
  case (args ss ts f)
  obtain ls where l: "l = Fun f ls" and ss: "ss = map ((\<cdot>) \<sigma>) ls"
    using args(1) rule_lhs_not_Var[OF R] by (cases l) auto
  have lin: "linear_term l" using orth R unfolding orthogonal_def left_linear_def by auto
  have "\<exists>\<tau>. ts ! i = \<tau> \<cdot> ls ! i \<and> (\<forall>x \<in> vars (ls ! i). (\<sigma> x, \<tau> x) \<in> par_rstep R)"
    if i: "i < length ls" for i
    using par_rstep_below_lhs[OF orth R, of "[i]" "ls ! i" \<sigma> "ts ! i"] args i l ss by auto
  then obtain \<tau>s where \<tau>s: "\<And>i. i < length ls \<Longrightarrow>
      ts ! i = \<tau>s i \<cdot> ls ! i \<and> (\<forall>x \<in> vars (ls ! i). (\<sigma> x, \<tau>s i x) \<in> par_rstep R)"
    by metis
  obtain \<tau> where \<tau>: "\<And>i x. i < length ls \<Longrightarrow> x \<in> vars (ls ! i) \<Longrightarrow> \<tau> x = \<tau>s i x"
    using merge_substs[of "length ls" "\<lambda>i. vars (ls ! i)" \<tau>s] lin l by auto
  have "ts ! i = \<tau> \<cdot> ls ! i" if "i < length ls" for i
    using \<tau>s[OF that] \<tau>[OF that] by (auto intro: subst_apply_cong)
  then have t: "t = \<tau> \<cdot> l" using args l ss by (auto intro: nth_equalityI)
  have \<sigma>\<tau>: "(\<sigma> x, \<tau> x) \<in> par_rstep R" if "x \<in> vars l" for x
    using that \<tau>s \<tau> l by (auto simp: in_set_conv_nth)
  have "(\<sigma> \<cdot> r, \<tau> \<cdot> r) \<in> par_rstep R"
    using rule_vars[OF R] \<sigma>\<tau> by (intro par_rstep_subst) auto
  moreover have "(t, \<tau> \<cdot> r) \<in> par_rstep R" unfolding t using R by (rule par_rstep.rule)
  ultimately show ?thesis by blast
next
  case (rule l' r' \<sigma>')
  then have "\<sigma> \<cdot> r = \<sigma>' \<cdot> r'"
    using root_overlap[OF _ R rule(3)] orth by (auto simp: orthogonal_def)
  then show ?thesis using rule(2) by (intro exI[of _ t]) simp
qed

text \<open>Theorem 6.3.10: in an orthogonal TRS, parallel reduction has the diamond property.\<close>

theorem orthogonal_par_rstep_diamond:
  assumes orth: "orthogonal R"
  shows "\<diamond> (par_rstep R)"
  unfolding diamond_def
proof (intro allI impI, elim conjE)
  fix s t\<^sub>1 t\<^sub>2 assume "(s, t\<^sub>1) \<in> par_rstep R" and "(s, t\<^sub>2) \<in> par_rstep R"
  then show "\<exists>u. (t\<^sub>1, u) \<in> par_rstep R \<and> (t\<^sub>2, u) \<in> par_rstep R"
  proof (induct arbitrary: t\<^sub>2 rule: par_rstep.induct)
    case (var x)
    from var show ?case
    proof cases
      case var
      then show ?thesis by (intro exI[of _ t\<^sub>2]) simp
    next
      case (rule l r \<sigma>)
      then show ?thesis using rule_lhs_not_Var by (cases l) auto
    qed
  next
    case (args ss ts f)
    note len = args(1) and steps = args(2) and IH = args(3)
    from args(4) show ?case
    proof cases
      case (args ts')
      then have t2: "t\<^sub>2 = Fun f ts'" and len': "length ss = length ts'"
        and steps': "\<And>i. i < length ts' \<Longrightarrow> (ss ! i, ts' ! i) \<in> par_rstep R" by auto
      have "\<exists>u. (ts ! i, u) \<in> par_rstep R \<and> (ts' ! i, u) \<in> par_rstep R" if "i < length ts" for i
        using IH[OF that steps'] that len len' by auto
      then obtain us where us: "\<And>i. i < length ts \<Longrightarrow>
          (ts ! i, us i) \<in> par_rstep R \<and> (ts' ! i, us i) \<in> par_rstep R" by metis
      have "(Fun f ts, Fun f (map us [0..<length ts])) \<in> par_rstep R"
        using us by (auto intro!: par_rstep.args)
      moreover have "(Fun f ts', Fun f (map us [0..<length ts])) \<in> par_rstep R"
        using us len len' by (auto intro!: par_rstep.args)
      ultimately show ?thesis using t2 by blast
    next
      case (rule l r \<sigma>)
      have "(\<sigma> \<cdot> l, Fun f ts) \<in> par_rstep R"
        using rule(1) len steps by (metis par_rstep.args)
      from par_rstep_root_peak[OF orth rule(3) this] show ?thesis using rule(2) by blast
    qed
  next
    case (rule l r \<sigma>)
    from par_rstep_root_peak[OF orth rule(1) rule(2)] show ?case by blast
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
