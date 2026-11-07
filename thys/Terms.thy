theory Terms
  imports Main
begin

section \<open>Terms, substitutions, and identities\<close>

text \<open>Baader \& Nipkow, Section 3.1.\<close>

subsection \<open>Signatures and terms\<close>

text \<open>Definition 3.1.1: a signature is a set of function symbols, each with an arity.
  We represent it as a set of pairs \<open>(f, n)\<close>.\<close>

type_synonym 'f signature = "('f \<times> nat) set"

text \<open>Definition 3.1.2. The datatype below contains all terms over all function symbols of
  type \<open>'f\<close> and all variables of type \<open>'v\<close>, with no arity check. The terms \<open>T(\<Sigma>, X)\<close> of the
  book, which respect the arities of \<open>\<Sigma>\<close>, are the inductive set \<open>terms \<Sigma> X\<close>. Most results do
  not depend on the signature, so we state them for all terms.\<close>

datatype ('f, 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"

inductive_set terms :: "'f signature \<Rightarrow> 'v set \<Rightarrow> ('f, 'v) term set"
  for \<Sigma> :: "'f signature" and X :: "'v set" where
  var: "x \<in> X \<Longrightarrow> Var x \<in> terms \<Sigma> X"
| "fun": "(f, length ts) \<in> \<Sigma> \<Longrightarrow> (\<And>t. t \<in> set ts \<Longrightarrow> t \<in> terms \<Sigma> X) \<Longrightarrow> Fun f ts \<in> terms \<Sigma> X"

subsection \<open>Positions\<close>

text \<open>Definition 3.1.3. Positions are strings of natural numbers. Unlike the book, argument
  positions start at \<open>0\<close> instead of \<open>1\<close>, to match list indexing (\<open>ts ! i\<close>).\<close>

type_synonym pos = "nat list"

function poss :: "('f, 'v) term \<Rightarrow> pos set" where
  "poss (Var x) = {[]}"
| "poss (Fun f ts) = {[]} \<union> (\<Union>i<length ts. (\<lambda>p. i # p) ` poss (ts ! i))"
  by pat_completeness auto
termination
  by (relation "measure size")
    (auto simp: less_Suc_eq_le intro!: size_list_estimation' nth_mem)

definition prefix_le :: "pos \<Rightarrow> pos \<Rightarrow> bool" (infix \<open>\<le>\<^sub>p\<close> 50) where
  "p \<le>\<^sub>p q \<longleftrightarrow> (\<exists>p'. p @ p' = q)"

definition prefix_less :: "pos \<Rightarrow> pos \<Rightarrow> bool" (infix \<open><\<^sub>p\<close> 50) where
  "p <\<^sub>p q \<longleftrightarrow> p \<le>\<^sub>p q \<and> p \<noteq> q"

definition parallel :: "pos \<Rightarrow> pos \<Rightarrow> bool" (infix \<open>\<parallel>\<close> 50) where
  "p \<parallel> q \<longleftrightarrow> \<not> p \<le>\<^sub>p q \<and> \<not> q \<le>\<^sub>p p"

lemma prefix_le_refl [simp]: "p \<le>\<^sub>p p"
  unfolding prefix_le_def by auto

lemma prefix_le_trans: "p \<le>\<^sub>p q \<Longrightarrow> q \<le>\<^sub>p r \<Longrightarrow> p \<le>\<^sub>p r"
  unfolding prefix_le_def by auto

lemma prefix_le_antisym: "p \<le>\<^sub>p q \<Longrightarrow> q \<le>\<^sub>p p \<Longrightarrow> p = q"
  unfolding prefix_le_def by auto

lemma Nil_prefix_le [simp]: "[] \<le>\<^sub>p p"
  unfolding prefix_le_def by auto

lemma Cons_prefix_le_Cons [simp]: "i # p \<le>\<^sub>p j # q \<longleftrightarrow> i = j \<and> p \<le>\<^sub>p q"
  unfolding prefix_le_def by auto

lemma prefix_le_append [simp]: "p \<le>\<^sub>p p @ q"
  unfolding prefix_le_def by auto

text \<open>The prefix order is a partial order on positions.\<close>

lemma prefix_le_partial_order: "partial_order_on UNIV {(p, q). p \<le>\<^sub>p q}"
  unfolding partial_order_on_def preorder_on_def refl_on_def trans_def antisym_def
  by (auto intro: prefix_le_trans prefix_le_antisym)

lemma Nil_in_poss [simp]: "[] \<in> poss t"
  by (cases t) auto

lemma Cons_in_poss_Fun [simp]: "i # p \<in> poss (Fun f ts) \<longleftrightarrow> i < length ts \<and> p \<in> poss (ts ! i)"
  by auto

lemma Cons_notin_poss_Var [simp]: "i # p \<notin> poss (Var x)"
  by simp

lemma finite_poss [simp]: "finite (poss t)"
by (induct t) auto

text \<open>From now on we reason about positions of \<open>Fun f ts\<close> through \<open>Cons_in_poss_Fun\<close>.\<close>

declare poss.simps(2) [simp del]

text \<open>Positions are closed under prefixes.\<close>

lemma poss_append_poss: "p @ q \<in> poss t \<Longrightarrow> p \<in> poss t"
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases t) auto
qed

lemma prefix_le_poss: "q \<in> poss t \<Longrightarrow> p \<le>\<^sub>p q \<Longrightarrow> p \<in> poss t"
  unfolding prefix_le_def using poss_append_poss by blast

text \<open>The size of a term is the number of its positions.\<close>

definition term_size :: "('f, 'v) term \<Rightarrow> nat" where
  "term_size s = card (poss s)"

subsection \<open>Subterms and replacement\<close>

text \<open>Definition 3.1.3(3): the subterm \<open>s|\<^sub>p\<close> of \<open>s\<close> at position \<open>p\<close>.\<close>

fun subt_at :: "('f, 'v) term \<Rightarrow> pos \<Rightarrow> ('f, 'v) term" (infixl \<open>|'_\<close> 67) where
  "s |_ [] = s"
| "Fun f ss |_ (i # p) = (ss ! i) |_ p"
| "Var x |_ (i # p) = Var x" \<comment> \<open>junk: \<open>i # p\<close> is not a position of \<open>Var x\<close>\<close>

text \<open>Definition 3.1.3(4): \<open>s[t]\<^sub>p\<close> replaces the subterm of \<open>s\<close> at position \<open>p\<close> by \<open>t\<close>.\<close>

fun replace_at :: "('f, 'v) term \<Rightarrow> pos \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
  (\<open>_\<lbrakk>_ \<leftarrow> _\<rbrakk>\<close> [1000, 0, 0] 1000) where
  "s\<lbrakk>[] \<leftarrow> t\<rbrakk> = t"
| "(Fun f ss)\<lbrakk>i # p \<leftarrow> t\<rbrakk> = Fun f (ss[i := (ss ! i)\<lbrakk>p \<leftarrow> t\<rbrakk>])"
| "(Var x)\<lbrakk>i # p \<leftarrow> t\<rbrakk> = Var x" \<comment> \<open>junk\<close>

lemma poss_subt_at:
  assumes "p \<in> poss s"
  shows "q \<in> poss (s |_ p) \<longleftrightarrow> p @ q \<in> poss s"
  using assms
proof (induct p arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases s) auto
qed

lemma poss_replace_at:
  assumes "p \<in> poss s"
  shows "p @ q \<in> poss (s\<lbrakk>p \<leftarrow> t\<rbrakk>) \<longleftrightarrow> q \<in> poss t"
  using assms
proof (induct p arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases s) auto
qed

lemma replace_at_subt_at [simp]:
  assumes "p \<in> poss s"
  shows "s\<lbrakk>p \<leftarrow> s |_ p\<rbrakk> = s"
  using assms
proof (induct p arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases s) auto
qed

text \<open>Lemma 3.1.4.\<close>

lemma subt_at_append: \<comment> \<open>Lemma 3.1.4(1)\<close>
  assumes "p @ q \<in> poss s"
  shows "s |_ (p @ q) = s |_ p |_ q"
  using assms
proof (induct p arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases s) auto
qed

lemma subt_at_replace_at_append: \<comment> \<open>Lemma 3.1.4(2), first equation\<close>
  assumes "p \<in> poss s" and "q \<in> poss t"
  shows "s\<lbrakk>p \<leftarrow> t\<rbrakk> |_ (p @ q) = t |_ q"
  using assms(1)
proof (induct p arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases s) auto
qed

lemma replace_at_replace_at_append: \<comment> \<open>Lemma 3.1.4(2), second equation\<close>
  assumes "p \<in> poss s" and "q \<in> poss t"
  shows "s\<lbrakk>p \<leftarrow> t\<rbrakk>\<lbrakk>p @ q \<leftarrow> r\<rbrakk> = s\<lbrakk>p \<leftarrow> t\<lbrakk>q \<leftarrow> r\<rbrakk>\<rbrakk>"
  using assms(1)
proof (induct p arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases s) auto
qed

lemma subt_at_append_replace_at: \<comment> \<open>Lemma 3.1.4(3), first equation\<close>
  assumes "p @ q \<in> poss s"
  shows "s\<lbrakk>p @ q \<leftarrow> t\<rbrakk> |_ p = (s |_ p)\<lbrakk>q \<leftarrow> t\<rbrakk>"
  using assms
proof (induct p arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases s) auto
qed

lemma replace_at_append_replace_at: \<comment> \<open>Lemma 3.1.4(3), second equation\<close>
  assumes "p @ q \<in> poss s"
  shows "s\<lbrakk>p @ q \<leftarrow> t\<rbrakk>\<lbrakk>p \<leftarrow> r\<rbrakk> = s\<lbrakk>p \<leftarrow> r\<rbrakk>"
  using assms
proof (induct p arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases s) auto
qed

lemma parallel_Cons_Cons [simp]: "i # p \<parallel> j # q \<longleftrightarrow> i \<noteq> j \<or> p \<parallel> q"
  unfolding parallel_def by auto

lemma not_parallel_Nil [simp]: "\<not> [] \<parallel> p" "\<not> p \<parallel> []"
  unfolding parallel_def by auto

lemma parallel_subt_at_replace_at: \<comment> \<open>Lemma 3.1.4(4), first equation\<close>
  assumes "p \<parallel> q" and "p \<in> poss s" and "q \<in> poss s"
  shows "s\<lbrakk>p \<leftarrow> t\<rbrakk> |_ q = s |_ q"
  using assms
proof (induct p arbitrary: q s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain j q' where q: "q = j # q'" by (cases q) auto
  with Cons show ?case by (cases s) (auto simp: nth_list_update)
qed

lemma parallel_replace_at_replace_at: \<comment> \<open>Lemma 3.1.4(4), second equation\<close>
  assumes "p \<parallel> q" and "p \<in> poss s" and "q \<in> poss s"
  shows "s\<lbrakk>p \<leftarrow> t\<rbrakk>\<lbrakk>q \<leftarrow> r\<rbrakk> = s\<lbrakk>q \<leftarrow> r\<rbrakk>\<lbrakk>p \<leftarrow> t\<rbrakk>"
  using assms
proof (induct p arbitrary: q s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then obtain j q' where q: "q = j # q'" by (cases q) auto
  with Cons show ?case
    by (cases s) (auto simp: nth_list_update list_update_swap)
qed

subsection \<open>Variables and ground terms\<close>

fun vars :: "('f, 'v) term \<Rightarrow> 'v set" where
  "vars (Var x) = {x}"
| "vars (Fun f ts) = (\<Union>t \<in> set ts. vars t)"

text \<open>Definition 3.1.3(5) defines \<open>Var(s)\<close> through positions. We define \<open>vars\<close> by
  recursion and prove that it agrees with the book's definition.\<close>

lemma vars_poss: "vars s = {x. \<exists>p \<in> poss s. s |_ p = Var x}"
proof (induct s)
  case (Var y)
  then show ?case by auto
next
  case (Fun f ts)
  have "x \<in> vars (Fun f ts) \<longleftrightarrow> (\<exists>p \<in> poss (Fun f ts). Fun f ts |_ p = Var x)" for x
  proof
    assume "x \<in> vars (Fun f ts)"
    then obtain i where i: "i < length ts" "x \<in> vars (ts ! i)"
      by (auto simp: in_set_conv_nth)
    with Fun obtain p where "p \<in> poss (ts ! i)" "ts ! i |_ p = Var x"
      using nth_mem by blast
    with i show "\<exists>p \<in> poss (Fun f ts). Fun f ts |_ p = Var x"
      by (intro bexI[of _ "i # p"]) auto
  next
    assume "\<exists>p \<in> poss (Fun f ts). Fun f ts |_ p = Var x"
    then obtain i p where "i < length ts" "p \<in> poss (ts ! i)" "ts ! i |_ p = Var x"
      by (auto simp: poss.simps(2))
    with Fun show "x \<in> vars (Fun f ts)"
      using nth_mem by fastforce
  qed
  then show ?case by blast
qed

text \<open>A position \<open>p\<close> of \<open>t\<close> is a variable position if \<open>t|\<^sub>p\<close> is a variable.\<close>

definition var_poss :: "('f, 'v) term \<Rightarrow> pos set" where
  "var_poss t = {p \<in> poss t. \<exists>x. t |_ p = Var x}"

lemma finite_vars [simp]: "finite (vars t)"
  by (induct t) auto

text \<open>Definition 3.1.5.\<close>

definition ground :: "('f, 'v) term \<Rightarrow> bool" where
  "ground t \<longleftrightarrow> vars t = {}"

lemma ground_Fun [simp]: "ground (Fun f ts) \<longleftrightarrow> (\<forall>t \<in> set ts. ground t)"
  unfolding ground_def by auto

lemma not_ground_Var [simp]: "\<not> ground (Var x)"
  unfolding ground_def by simp


subsection \<open>Substitutions\<close>

text \<open>Definition 3.1.6. The book requires a substitution to change only finitely many
  variables. We allow any map from variables to terms, and call one with finite domain
  \<open>finite_subst\<close>. None of the results below need finiteness.

  We write \<open>\<sigma> \<cdot> t\<close> for the application \<open>\<sigma>(t)\<close> of (the extension of) \<open>\<sigma>\<close> to \<open>t\<close>.\<close>

type_synonym ('f, 'v) subst = "'v \<Rightarrow> ('f, 'v) term"

fun subst_apply :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" (infixr \<open>\<cdot>\<close> 70) where
  "\<sigma> \<cdot> Var x = \<sigma> x"
| "\<sigma> \<cdot> Fun f ts = Fun f (map (\<lambda>t. \<sigma> \<cdot> t) ts)"

definition subst_domain :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "subst_domain \<sigma> = {x. \<sigma> x \<noteq> Var x}"

definition subst_range :: "('f, 'v) subst \<Rightarrow> ('f, 'v) term set" where
  "subst_range \<sigma> = \<sigma> ` subst_domain \<sigma>"

definition vrange :: "('f, 'v) subst \<Rightarrow> 'v set" where
  "vrange \<sigma> = (\<Union>t \<in> subst_range \<sigma>. vars t)"

definition finite_subst :: "('f, 'v) subst \<Rightarrow> bool" where
  "finite_subst \<sigma> \<longleftrightarrow> finite (subst_domain \<sigma>)"

text \<open>The composition \<open>\<sigma>\<tau>\<close> first applies \<open>\<tau>\<close>, then \<open>\<sigma>\<close>: \<open>\<sigma>\<tau>(x) = \<sigma>(\<tau>(x))\<close>.\<close>

definition subst_compose :: "('f, 'v) subst \<Rightarrow> ('f, 'v) subst \<Rightarrow> ('f, 'v) subst"
  (infixl \<open>\<circ>\<^sub>s\<close> 75) where
  "\<sigma> \<circ>\<^sub>s \<tau> = (\<lambda>x. \<sigma> \<cdot> \<tau> x)"

lemma subst_apply_Var [simp]: "Var \<cdot> t = t"
  by (induct t) (auto intro: map_idI)

lemma subst_compose_apply [simp]: "(\<sigma> \<circ>\<^sub>s \<tau>) \<cdot> t = \<sigma> \<cdot> (\<tau> \<cdot> t)"
  by (induct t) (auto simp: subst_compose_def)

text \<open>The extension of \<open>\<sigma>\<tau>\<close> is the composition of the extensions.\<close>

lemma subst_compose_ext: "subst_apply (\<sigma> \<circ>\<^sub>s \<tau>) = subst_apply \<sigma> \<circ> subst_apply \<tau>"
  by auto

lemma subst_compose_assoc: "(\<sigma> \<circ>\<^sub>s \<tau>) \<circ>\<^sub>s \<rho> = \<sigma> \<circ>\<^sub>s (\<tau> \<circ>\<^sub>s \<rho>)" \<comment> \<open>Exercise 3.3\<close>
  by (rule ext) (metis subst_compose_apply subst_compose_def)

lemma subst_compose_Var [simp]: "\<sigma> \<circ>\<^sub>s Var = \<sigma>" "Var \<circ>\<^sub>s \<sigma> = \<sigma>"
  by (auto simp: subst_compose_def)

lemma subst_domain_compose: "subst_domain (\<sigma> \<circ>\<^sub>s \<tau>) \<subseteq> subst_domain \<sigma> \<union> subst_domain \<tau>"
  by (auto simp: subst_domain_def subst_compose_def)

lemma finite_subst_compose:
  "finite_subst \<sigma> \<Longrightarrow> finite_subst \<tau> \<Longrightarrow> finite_subst (\<sigma> \<circ>\<^sub>s \<tau>)"
  unfolding finite_subst_def using subst_domain_compose by (metis finite_UnI finite_subset)

lemma subst_apply_cong: "(\<And>x. x \<in> vars t \<Longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> \<sigma> \<cdot> t = \<tau> \<cdot> t"
  by (induct t) auto

lemma vars_subst_apply: "vars (\<sigma> \<cdot> t) = (\<Union>x \<in> vars t. vars (\<sigma> x))"
  by (induct t) auto

lemma ground_subst_apply [simp]: "ground t \<Longrightarrow> \<sigma> \<cdot> t = t"
  by (rule trans[OF subst_apply_cong subst_apply_Var]) (auto simp: ground_def)

subsubsection \<open>Substitutions, positions, and subterms\<close>

lemma poss_subst_apply: "p \<in> poss t \<Longrightarrow> p \<in> poss (\<sigma> \<cdot> t)"
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases t) auto
qed

lemma subt_at_subst_apply: "p \<in> poss t \<Longrightarrow> (\<sigma> \<cdot> t) |_ p = \<sigma> \<cdot> (t |_ p)"
proof (induct p arbitrary: t)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases t) auto
qed

lemma replace_at_subst_apply:
  "p \<in> poss s \<Longrightarrow> \<sigma> \<cdot> s\<lbrakk>p \<leftarrow> t\<rbrakk> = (\<sigma> \<cdot> s)\<lbrakk>p \<leftarrow> \<sigma> \<cdot> t\<rbrakk>"
proof (induct p arbitrary: s)
  case Nil
  then show ?case by simp
next
  case (Cons i p)
  then show ?case by (cases s) (auto simp: map_update)
qed

subsubsection \<open>Instances\<close>

text \<open>A term \<open>t\<close> is an instance of \<open>s\<close>, written \<open>t \<gtrsim> s\<close>, if \<open>\<sigma> \<cdot> s = t\<close> for some \<open>\<sigma>\<close>.
  This is a quasi-order.\<close>

definition instance_of :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix \<open>\<gtrsim>\<close> 50) where
  "t \<gtrsim> s \<longleftrightarrow> (\<exists>\<sigma>. \<sigma> \<cdot> s = t)"

lemma instance_of_refl [simp]: "t \<gtrsim> t"
  unfolding instance_of_def by (rule exI[of _ Var]) simp

lemma instance_of_trans: "t \<gtrsim> s \<Longrightarrow> s \<gtrsim> r \<Longrightarrow> t \<gtrsim> r"
  unfolding instance_of_def by (metis subst_compose_apply)

lemma instance_of_quasi_order: "preorder_on UNIV {(t, s). t \<gtrsim> s}"
  unfolding preorder_on_def refl_on_def trans_def
  by (auto intro: instance_of_trans)

subsection \<open>Identities\<close>

text \<open>Definition 3.1.7: an identity \<open>s \<approx> t\<close> is a pair of terms; \<open>s\<close> is its left-hand side,
  \<open>t\<close> its right-hand side. A set of identities is just a relation on terms.\<close>

type_synonym ('f, 'v) identity = "('f, 'v) term \<times> ('f, 'v) term"

end
