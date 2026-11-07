theory Parallel_Closed
  imports Confluence
begin

section \<open>Beyond orthogonality\<close>

text \<open>Baader \& Nipkow, Section 6.4: Huet's Parallel Closure Theorem.

  The book measures a fork \<open>t\<^sub>0 \<^sub>P\<^sub>0\<leftleftarrows> s \<rightrightarrows>\<^sup>P\<^sup>1 t\<^sub>1\<close> by the overlap \<open>m(s, P\<^sub>0, P\<^sub>1)\<close> of the two sets
  of redex positions (Definition 6.4.6, Lemma 6.4.7). We record instead, in each parallel step,
  the total size \<open>n\<close> of the contracted redexes, and measure a fork by \<open>min n\<^sub>0 n\<^sub>1\<close>. This
  quantity behaves exactly as needed in the proof of Theorem 6.4.8: it does not increase when
  passing to the arguments of a function symbol, and it strictly decreases in the critical
  case (Case 2) of the proof.\<close>

subsection \<open>Parallel steps weighted by the size of the contracted redexes\<close>

inductive par_w :: "('f, 'v) term rel \<Rightarrow> ('f, 'v) term \<Rightarrow> nat \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  for R where
  var: "par_w R (Var x) 0 (Var x)"
| args: "length ss = length ts \<Longrightarrow> length ns = length ts \<Longrightarrow>
    (\<And>i. i < length ts \<Longrightarrow> par_w R (ss ! i) (ns ! i) (ts ! i)) \<Longrightarrow>
    par_w R (Fun f ss) (sum_list ns) (Fun f ts)"
| rule: "(l, r) \<in> R \<Longrightarrow> par_w R (\<sigma> \<cdot> l) (size (\<sigma> \<cdot> l)) (\<sigma> \<cdot> r)"

lemma par_w_refl: "par_w R t 0 t"
proof (induct t)
  case (Fun f ts)
  have "par_w R (Fun f ts) (sum_list (replicate (length ts) 0)) (Fun f ts)"
    by (rule par_w.args) (auto intro: Fun nth_mem)
  then show ?case by (simp add: sum_list_replicate)
qed (rule par_w.var)

lemma par_w_imp_par_rstep: "par_w R s n t \<Longrightarrow> (s, t) \<in> par_rstep R"
  by (induct rule: par_w.induct) (auto intro: par_rstep.intros)

lemma par_rstep_imp_par_w: "(s, t) \<in> par_rstep R \<Longrightarrow> \<exists>n. par_w R s n t"
proof (induct rule: par_rstep.induct)
  case (var x)
  then show ?case by (blast intro: par_w.var)
next
  case (args ss ts f)
  then have "\<forall>i < length ts. \<exists>n. par_w R (ss ! i) n (ts ! i)" by auto
  then obtain g where g: "\<And>i. i < length ts \<Longrightarrow> par_w R (ss ! i) (g i) (ts ! i)" by metis
  have "par_w R (Fun f ss) (sum_list (map g [0..<length ts])) (Fun f ts)"
    by (rule par_w.args) (use args g in auto)
  then show ?case by blast
next
  case (rule l r \<sigma>)
  then show ?case by (blast intro: par_w.rule)
qed

lemma par_rstep_iff_par_w: "(s, t) \<in> par_rstep R \<longleftrightarrow> (\<exists>n. par_w R s n t)"
  using par_rstep_imp_par_w par_w_imp_par_rstep by metis

lemma sum_list_le_nth:
  fixes xs ys :: "nat list"
  shows "length xs = length ys \<Longrightarrow> (\<And>i. i < length ys \<Longrightarrow> xs ! i \<le> ys ! i) \<Longrightarrow>
    sum_list xs \<le> sum_list ys"
proof (induct xs ys rule: list_induct2)
  case (Cons x xs y ys)
  have "x \<le> y" using Cons.prems[of 0] by simp
  moreover have "sum_list xs \<le> sum_list ys"
    using Cons.prems by (intro Cons.hyps) (metis Suc_less_eq length_Cons nth_Cons_Suc)
  ultimately show ?case by simp
qed simp

text \<open>The contracted redexes are disjoint subterms, so their total size is bounded by the
  size of the term.\<close>

lemma par_w_size: "par_w R s n t \<Longrightarrow> n \<le> size s"
proof (induct rule: par_w.induct)
  case (args ss ts ns f)
  have "sum_list ns \<le> sum_list (map size ss)" using args by (intro sum_list_le_nth) auto
  then show ?case by (simp add: size_list_conv_sum_list)
qed simp_all

text \<open>Parallel reduction is closed under substitutions (the counterpart of Lemma 6.4.2,
  which is \<open>par_rstep_subst\<close>) and under contexts (Lemma 6.4.1, cf.\ \<open>par_rstep_ctxt\<close>).\<close>

lemma par_rstep_subst_closed:
  "(s, t) \<in> par_rstep R \<Longrightarrow> (\<delta> \<cdot> s, \<delta> \<cdot> t) \<in> par_rstep R"
proof (induct rule: par_rstep.induct)
  case (args ss ts f)
  then show ?case by (auto intro!: par_rstep.args)
next
  case (rule l r \<sigma>)
  then show ?case using par_rstep.rule[OF rule, of "\<delta> \<circ>\<^sub>s \<sigma>"] by simp
qed simp

subsection \<open>Parallel closed systems\<close>

text \<open>Definition 6.4.5. Note the orientation: \<open>u\<^sub>2 \<rightrightarrows> u\<^sub>1\<close> for every critical pair
  \<open>\<langle>u\<^sub>1, u\<^sub>2\<rangle> = \<langle>\<theta>r\<^sub>1, (\<theta>l\<^sub>1)[\<theta>r\<^sub>2]\<^sub>p\<rangle>\<close>.\<close>

definition parallel_closed :: "('f, 'v) term rel \<Rightarrow> bool" where
  "parallel_closed R \<longleftrightarrow> (\<forall>(u\<^sub>1, u\<^sub>2) \<in> CP R. (u\<^sub>2, u\<^sub>1) \<in> par_rstep R)"

text \<open>A left-linear system all of whose critical pairs are trivial is called weakly
  orthogonal (remark after Example 6.4.10).\<close>

definition weakly_orthogonal :: "('f, 'v) term rel \<Rightarrow> bool" where
  "weakly_orthogonal R \<longleftrightarrow> left_linear R \<and> (\<forall>(u, v) \<in> CP R. u = v)"

context TRS_inf
begin

text \<open>The Parallel Moves Lemma 6.4.4 and the case distinction of the proof of
  Theorem 6.4.8, in one statement: a parallel step from an instance \<open>\<sigma>(u)\<close> of a linear term
  \<open>u\<close> either takes place entirely inside the substitution (Case 1; then the result is an
  instance \<open>\<tau>(u)\<close>), or it contracts a redex at a non-variable position \<open>q\<close> of \<open>u\<close>
  (Case 2, a critical overlap); in that case the remaining redexes form a parallel step from
  \<open>\<sigma>(u)[\<sigma>\<^sub>0r\<^sub>0]\<^sub>q\<close> to the same result, of strictly smaller weight.\<close>

lemma par_w_lhs_decomp:
  assumes "linear_term u" and "par_w R (\<sigma> \<cdot> u) n t"
  shows "(\<exists>\<tau>. t = \<tau> \<cdot> u \<and> (\<forall>x \<in> vars u. (\<sigma> x, \<tau> x) \<in> par_rstep R)) \<or>
    (\<exists>q l\<^sub>0 r\<^sub>0 \<sigma>\<^sub>0 n'. q \<in> poss u \<and> (\<forall>x. u |_ q \<noteq> Var x) \<and> (l\<^sub>0, r\<^sub>0) \<in> R \<and>
       (\<sigma> \<cdot> u) |_ q = \<sigma>\<^sub>0 \<cdot> l\<^sub>0 \<and> n' < n \<and> par_w R ((\<sigma> \<cdot> u)\<lbrakk>q \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk>) n' t)"
  using assms
proof (induct u arbitrary: n t)
  case (Var x)
  then show ?case using par_w_imp_par_rstep by (intro disjI1 exI[of _ "\<lambda>_. t"]) auto
next
  case (Fun g us)
  from Fun.prems(2) show ?case
  proof cases
    case (rule l\<^sub>0 r\<^sub>0 \<sigma>\<^sub>0)
    have "par_w R ((\<sigma> \<cdot> Fun g us)\<lbrakk>[] \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk>) 0 t" using rule par_w_refl by simp
    moreover have "n = size (\<sigma> \<cdot> Fun g us)" using rule(1,2) by simp
    then have "0 < n" by simp
    ultimately show ?thesis using rule
      by (intro disjI2 exI[of _ "[]"] exI[of _ l\<^sub>0] exI[of _ r\<^sub>0] exI[of _ \<sigma>\<^sub>0] exI[of _ 0]) auto
  next
    case (args ss ts ns f')
    then have ss: "ss = map ((\<cdot>) \<sigma>) us" and t: "t = Fun g ts" and n: "n = sum_list ns"
      and len: "length ts = length us" "length ns = length us" by auto
    have steps: "par_w R (\<sigma> \<cdot> us ! i) (ns ! i) (ts ! i)" if "i < length us" for i
      using args(6)[of i] that len ss by auto
    have lin: "linear_term (us ! i)" if "i < length us" for i
      using Fun.prems(1) that by auto
    note IH = Fun.hyps[OF nth_mem lin steps]
    show ?thesis
    proof (cases "\<exists>i < length us. \<exists>q l\<^sub>0 r\<^sub>0 \<sigma>\<^sub>0 n'. q \<in> poss (us ! i) \<and> (\<forall>x. us ! i |_ q \<noteq> Var x) \<and>
        (l\<^sub>0, r\<^sub>0) \<in> R \<and> (\<sigma> \<cdot> us ! i) |_ q = \<sigma>\<^sub>0 \<cdot> l\<^sub>0 \<and> n' < ns ! i \<and>
        par_w R ((\<sigma> \<cdot> us ! i)\<lbrakk>q \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk>) n' (ts ! i)")
      case True
      then obtain i q l\<^sub>0 r\<^sub>0 \<sigma>\<^sub>0 n' where i: "i < length us" and q: "q \<in> poss (us ! i)"
        "\<forall>x. us ! i |_ q \<noteq> Var x" and R0: "(l\<^sub>0, r\<^sub>0) \<in> R" and red: "(\<sigma> \<cdot> us ! i) |_ q = \<sigma>\<^sub>0 \<cdot> l\<^sub>0"
        and n': "n' < ns ! i" and st: "par_w R ((\<sigma> \<cdot> us ! i)\<lbrakk>q \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk>) n' (ts ! i)"
        by blast
      let ?ss = "(map ((\<cdot>) \<sigma>) us)[i := (\<sigma> \<cdot> us ! i)\<lbrakk>q \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk>]"
      have "par_w R (Fun g ?ss) (sum_list (ns[i := n'])) (Fun g ts)"
        by (rule par_w.args) (use len steps st i in \<open>auto simp: nth_list_update\<close>)
      moreover have "sum_list (ns[i := n']) < n"
        using n i len n' elem_le_sum_list[of i ns] by (simp add: sum_list_update)
      moreover have "(\<sigma> \<cdot> Fun g us)\<lbrakk>i # q \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk> = Fun g ?ss" using i by simp
      ultimately show ?thesis using i q R0 red t
        by (intro disjI2 exI[of _ "i # q"] exI[of _ l\<^sub>0] exI[of _ r\<^sub>0] exI[of _ \<sigma>\<^sub>0]
            exI[of _ "sum_list (ns[i := n'])"]) auto
    next
      case False
      then have "\<exists>\<tau>. ts ! i = \<tau> \<cdot> us ! i \<and> (\<forall>x \<in> vars (us ! i). (\<sigma> x, \<tau> x) \<in> par_rstep R)"
        if "i < length us" for i
        using IH[OF that] that by blast
      then obtain \<tau>s where \<tau>s: "\<And>i. i < length us \<Longrightarrow>
          ts ! i = \<tau>s i \<cdot> us ! i \<and> (\<forall>x \<in> vars (us ! i). (\<sigma> x, \<tau>s i x) \<in> par_rstep R)"
        by metis
      obtain \<tau> where \<tau>: "\<And>i x. i < length us \<Longrightarrow> x \<in> vars (us ! i) \<Longrightarrow> \<tau> x = \<tau>s i x"
        using merge_substs[of "length us" "\<lambda>i. vars (us ! i)" \<tau>s] Fun.prems(1) by auto
      have "ts ! i = \<tau> \<cdot> us ! i" if "i < length us" for i
        using \<tau>s[OF that] \<tau>[OF that] by (auto intro: subst_apply_cong)
      then have "t = \<tau> \<cdot> Fun g us" using t len by (auto intro: nth_equalityI)
      moreover have "\<forall>x \<in> vars (Fun g us). (\<sigma> x, \<tau> x) \<in> par_rstep R"
        using \<tau>s \<tau> by (auto simp: in_set_conv_nth)
      ultimately show ?thesis by blast
    qed
  qed simp
qed

text \<open>The core of the proof of Theorem 6.4.8: a fork between a root step and an arbitrary
  parallel step, assuming the theorem for all forks of smaller measure.\<close>

lemma parallel_closed_root_peak:
  assumes ll: "left_linear R" and pc: "parallel_closed R"
    and IH: "\<forall>s' a t\<^sub>a b t\<^sub>b. min a b < n \<longrightarrow> par_w R s' a t\<^sub>a \<longrightarrow> par_w R s' b t\<^sub>b \<longrightarrow>
      (\<exists>u. (t\<^sub>a, u) \<in> par_rstep R \<and> (t\<^sub>b, u) \<in> par_rstep R)"
    and R: "(l, r) \<in> R" and st: "par_w R (\<sigma> \<cdot> l) n t"
  shows "\<exists>u. (\<sigma> \<cdot> r, u) \<in> par_rstep R \<and> (t, u) \<in> par_rstep R"
proof -
  have lin: "linear_term l" using ll R by (auto simp: left_linear_def)
  from par_w_lhs_decomp[OF lin st] show ?thesis
  proof
    assume "\<exists>\<tau>. t = \<tau> \<cdot> l \<and> (\<forall>x \<in> vars l. (\<sigma> x, \<tau> x) \<in> par_rstep R)"
    then obtain \<tau> where t: "t = \<tau> \<cdot> l" and \<sigma>\<tau>: "\<forall>x \<in> vars l. (\<sigma> x, \<tau> x) \<in> par_rstep R" by blast
    \<comment> \<open>Case 1 (Parallel Moves Lemma): \<open>\<sigma>r \<rightrightarrows> \<tau>r \<leftarrow> \<tau>l = t\<close>.\<close>
    have "(\<sigma> \<cdot> r, \<tau> \<cdot> r) \<in> par_rstep R"
      using rule_vars[OF R] \<sigma>\<tau> by (intro par_rstep_subst) auto
    moreover have "(t, \<tau> \<cdot> r) \<in> par_rstep R" unfolding t using R by (rule par_rstep.rule)
    ultimately show ?thesis by blast
  next
    assume "\<exists>q l\<^sub>0 r\<^sub>0 \<sigma>\<^sub>0 n'. q \<in> poss l \<and> (\<forall>x. l |_ q \<noteq> Var x) \<and> (l\<^sub>0, r\<^sub>0) \<in> R \<and>
       (\<sigma> \<cdot> l) |_ q = \<sigma>\<^sub>0 \<cdot> l\<^sub>0 \<and> n' < n \<and> par_w R ((\<sigma> \<cdot> l)\<lbrakk>q \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk>) n' t"
    then obtain q l\<^sub>0 r\<^sub>0 \<sigma>\<^sub>0 n' where q: "q \<in> poss l" "\<forall>x. l |_ q \<noteq> Var x"
      and R0: "(l\<^sub>0, r\<^sub>0) \<in> R" and red: "(\<sigma> \<cdot> l) |_ q = \<sigma>\<^sub>0 \<cdot> l\<^sub>0" and n': "n' < n"
      and st': "par_w R ((\<sigma> \<cdot> l)\<lbrakk>q \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk>) n' t" by blast
    have unif: "\<sigma> \<cdot> (l |_ q) = \<sigma>\<^sub>0 \<cdot> l\<^sub>0" using red subt_at_subst_apply[OF q(1)] by simp
    show ?thesis
    proof (cases "q = [] \<and> (l, r) = (l\<^sub>0, r\<^sub>0)")
      case True
      then have l: "\<sigma> \<cdot> l = \<sigma>\<^sub>0 \<cdot> l" using unif by simp
      have "\<sigma> \<cdot> r = \<sigma>\<^sub>0 \<cdot> r"
        by (intro subst_apply_cong subst_apply_eq_vars[OF l]) (use rule_vars[OF R] in auto)
      then have "(\<sigma> \<cdot> r, t) \<in> par_rstep R" using st' True par_w_imp_par_rstep by auto
      then show ?thesis by (intro exI[of _ t]) simp
    next
      case False
      \<comment> \<open>Case 2: a critical overlap. Parallel closedness closes the critical pair, and the
        remaining redexes give a fork of smaller measure.\<close>
      from overlap_imp_CP[OF infinite_vars R R0 q unif False]
      obtain u\<^sub>1 u\<^sub>2 \<delta> where cp: "(u\<^sub>1, u\<^sub>2) \<in> CP R" and "\<delta> \<cdot> u\<^sub>1 = \<sigma> \<cdot> r"
        and "\<delta> \<cdot> u\<^sub>2 = (\<sigma> \<cdot> l)\<lbrakk>q \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk>" by blast
      moreover have "(u\<^sub>2, u\<^sub>1) \<in> par_rstep R" using pc cp unfolding parallel_closed_def by auto
      ultimately have "((\<sigma> \<cdot> l)\<lbrakk>q \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk>, \<sigma> \<cdot> r) \<in> par_rstep R"
        using par_rstep_subst_closed[of u\<^sub>2 u\<^sub>1 R \<delta>] by simp
      then obtain k where "par_w R ((\<sigma> \<cdot> l)\<lbrakk>q \<leftarrow> \<sigma>\<^sub>0 \<cdot> r\<^sub>0\<rbrakk>) k (\<sigma> \<cdot> r)"
        using par_rstep_imp_par_w by blast
      from IH[rule_format, OF _ st' this] n' show ?thesis by fastforce
    qed
  qed
qed

lemma parallel_closed_fork:
  assumes ll: "left_linear R" and pc: "parallel_closed R"
  shows "par_w R s n\<^sub>0 t\<^sub>0 \<Longrightarrow> par_w R s n\<^sub>1 t\<^sub>1 \<Longrightarrow> min n\<^sub>0 n\<^sub>1 \<le> k \<Longrightarrow>
    \<exists>u. (t\<^sub>0, u) \<in> par_rstep R \<and> (t\<^sub>1, u) \<in> par_rstep R"
proof (induct k arbitrary: s n\<^sub>0 t\<^sub>0 n\<^sub>1 t\<^sub>1 rule: less_induct)
  case (less k)
  have IHk: "\<exists>u. (t\<^sub>a, u) \<in> par_rstep R \<and> (t\<^sub>b, u) \<in> par_rstep R"
    if "min a b < k" "par_w R s' a t\<^sub>a" "par_w R s' b t\<^sub>b" for s' a t\<^sub>a b t\<^sub>b
    using less.hyps[OF that(1) that(2,3)] by blast
  from less.prems show ?case
  proof (induct arbitrary: n\<^sub>1 t\<^sub>1 rule: par_w.induct)
    case (var x)
    from var(1) show ?case
    proof cases
      case var
      then show ?thesis by (intro exI[of _ "Var x"]) auto
    next
      case (rule l r \<sigma>)
      then show ?thesis using rule_lhs_not_Var by (cases l) auto
    qed
  next
    case (args ss ts ns f)
    note len = args(1,2) and IHs = args(4) and min_le = args(6)
    have st0: "par_w R (Fun f ss) (sum_list ns) (Fun f ts)"
      using args(1,2,3) by (rule par_w.args)
    from args(5) show ?case
    proof cases
      case (args ts' ns')
      have "\<exists>u. (ts ! i, u) \<in> par_rstep R \<and> (ts' ! i, u) \<in> par_rstep R" if i: "i < length ts" for i
      proof -
        have "ns ! i \<le> sum_list ns" "ns' ! i \<le> sum_list ns'"
          using i len args by (auto intro!: elem_le_sum_list)
        then have "min (ns ! i) (ns' ! i) \<le> k" using min_le args by auto
        then show ?thesis using IHs[OF i, of "ns' ! i" "ts' ! i"] args i len by auto
      qed
      then obtain us where us: "\<And>i. i < length ts \<Longrightarrow>
          (ts ! i, us i) \<in> par_rstep R \<and> (ts' ! i, us i) \<in> par_rstep R" by metis
      have "(Fun f ts, Fun f (map us [0..<length ts])) \<in> par_rstep R"
        using us by (auto intro!: par_rstep.args)
      moreover have "(Fun f ts', Fun f (map us [0..<length ts])) \<in> par_rstep R"
        using us args len by (auto intro!: par_rstep.args)
      ultimately show ?thesis using args by blast
    next
      case (rule l r \<sigma>)
      have st0': "par_w R (\<sigma> \<cdot> l) (sum_list ns) (Fun f ts)" using st0 rule(1) by simp
      have "sum_list ns \<le> size (\<sigma> \<cdot> l)" using par_w_size[OF st0'] .
      then have le: "sum_list ns \<le> k" using min_le rule by simp
      have IH': "\<forall>s' a t\<^sub>a b t\<^sub>b. min a b < sum_list ns \<longrightarrow> par_w R s' a t\<^sub>a \<longrightarrow>
          par_w R s' b t\<^sub>b \<longrightarrow> (\<exists>u. (t\<^sub>a, u) \<in> par_rstep R \<and> (t\<^sub>b, u) \<in> par_rstep R)"
      proof (intro allI impI)
        fix s' a t\<^sub>a b t\<^sub>b assume "min a b < sum_list ns" "par_w R s' a t\<^sub>a" "par_w R s' b t\<^sub>b"
        then show "\<exists>u. (t\<^sub>a, u) \<in> par_rstep R \<and> (t\<^sub>b, u) \<in> par_rstep R"
          using IHk[OF _ \<open>par_w R s' a t\<^sub>a\<close> \<open>par_w R s' b t\<^sub>b\<close>] le by simp
      qed
      have "\<exists>u. (\<sigma> \<cdot> r, u) \<in> par_rstep R \<and> (Fun f ts, u) \<in> par_rstep R"
        by (rule parallel_closed_root_peak[OF ll pc IH' rule(4) st0'])
      then show ?thesis using rule(3) by blast
    qed
  next
    case (rule l r \<sigma>)
    have "n\<^sub>1 \<le> size (\<sigma> \<cdot> l)" using par_w_size[OF rule(2)] .
    then have le: "n\<^sub>1 \<le> k" using rule(3) by simp
    have IH': "\<forall>s' a t\<^sub>a b t\<^sub>b. min a b < n\<^sub>1 \<longrightarrow> par_w R s' a t\<^sub>a \<longrightarrow>
        par_w R s' b t\<^sub>b \<longrightarrow> (\<exists>u. (t\<^sub>a, u) \<in> par_rstep R \<and> (t\<^sub>b, u) \<in> par_rstep R)"
    proof (intro allI impI)
      fix s' a t\<^sub>a b t\<^sub>b assume "min a b < n\<^sub>1" "par_w R s' a t\<^sub>a" "par_w R s' b t\<^sub>b"
      then show "\<exists>u. (t\<^sub>a, u) \<in> par_rstep R \<and> (t\<^sub>b, u) \<in> par_rstep R"
        using IHk[OF _ \<open>par_w R s' a t\<^sub>a\<close> \<open>par_w R s' b t\<^sub>b\<close>] le by simp
    qed
    have "\<exists>u. (\<sigma> \<cdot> r, u) \<in> par_rstep R \<and> (t\<^sub>1, u) \<in> par_rstep R"
      by (rule parallel_closed_root_peak[OF ll pc IH' rule(1) rule(2)])
    then show ?case by blast
  qed
qed

text \<open>Theorem 6.4.8 (Parallel Closure Theorem).\<close>

theorem parallel_closure_theorem:
  assumes "left_linear R" and "parallel_closed R"
  shows "\<diamond> (par_rstep R)"
  unfolding diamond_def
proof (intro allI impI, elim conjE)
  fix s t\<^sub>0 t\<^sub>1 assume "(s, t\<^sub>0) \<in> par_rstep R" and "(s, t\<^sub>1) \<in> par_rstep R"
  then obtain n\<^sub>0 n\<^sub>1 where "par_w R s n\<^sub>0 t\<^sub>0" and "par_w R s n\<^sub>1 t\<^sub>1"
    using par_rstep_imp_par_w by metis
  from parallel_closed_fork[OF assms this order.refl]
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
