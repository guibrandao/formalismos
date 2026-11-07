theory Reduction_Systems
imports Main
begin

section \<open>Abstract reduction systems\<close>

text\<open>Baader \& Nipkow, Definition 2.1.1: an abstract reduction system is a pair \<open>(A, \<rightarrow>)\<close>
  of a set \<open>A\<close> and a binary relation \<open>\<rightarrow>\<close> on \<open>A\<close>. In HOL the carrier \<open>A\<close> is the type \<open>'a\<close>,
  so an ARS is just a relation \<open>\<^bold>\<rightarrow> :: 'a rel\<close>. All relational notions (closures,
  inverse, composition, powers, well-foundedness) are the ones of HOL's library:
  \<open>r\<^sup>=\<close>, \<open>r\<^sup>+\<close>, \<open>r\<^sup>*\<close>, \<open>r\<inverse>\<close>, \<open>r O s\<close>, \<open>r ^^ n\<close>, \<open>wf\<close>, \<open>acyclic\<close>.

  A term rewriting system can later be seen as an ARS through its rewrite relation,
  e.g.\ via \<open>sublocale TRS \<subseteq> ARS "rstep R"\<close> or \<open>interpretation\<close>.\<close>

locale ARS =
  fixes R :: "'a rel" (\<open>\<^bold>\<rightarrow>\<close>)
begin

subsection \<open>Notation for reductions\<close>

abbreviation step :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix \<open>\<rightarrow>\<close> 50) where
  "a \<rightarrow> b \<equiv> (a, b) \<in> \<^bold>\<rightarrow>"

abbreviation n_steps :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<rightarrow>\<^sup>_ _\<close> [50, 50, 50] 50) where
  "a \<rightarrow>\<^sup>n b \<equiv> (a, b) \<in> \<^bold>\<rightarrow> ^^ n"

abbreviation zero_or_one_step :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<rightarrow>\<^sup>= _\<close> [1000, 1000] 999) where
  "a \<rightarrow>\<^sup>= b \<equiv> (a, b) \<in> \<^bold>\<rightarrow>\<^sup>="

abbreviation finite_nonempty_steps :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<rightarrow>\<^sup>+ _\<close> [1000, 1000] 999) where
  "a \<rightarrow>\<^sup>+ b \<equiv> (a, b) \<in> \<^bold>\<rightarrow>\<^sup>+"

abbreviation finite_steps :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<rightarrow>\<^sup>* _\<close> [1000, 1000] 999) where
  "a \<rightarrow>\<^sup>* b \<equiv> (a, b) \<in> \<^bold>\<rightarrow>\<^sup>*"

abbreviation inv_rel :: "'a rel" (\<open>\<^bold>\<leftarrow>\<close>) where
  "\<^bold>\<leftarrow> \<equiv> \<^bold>\<rightarrow>\<inverse>"

abbreviation inv_step :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<leftarrow> _\<close> [1000, 1000] 999) where
  "a \<leftarrow> b \<equiv> (a, b) \<in> \<^bold>\<leftarrow>"

abbreviation inv_trans_closure :: "'a rel" (\<open>\<^sup>+\<^bold>\<leftarrow>\<close>) where
  "\<^sup>+\<^bold>\<leftarrow> \<equiv> \<^bold>\<leftarrow>\<^sup>+"

abbreviation inv_finite_nonempty_steps :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<^sup>+\<leftarrow> _\<close> [1000, 1000] 999) where
  "a \<^sup>+\<leftarrow> b \<equiv> (a, b) \<in> \<^sup>+\<^bold>\<leftarrow>"

abbreviation inv_refl_trans_closure :: "'a rel" (\<open>\<^sup>*\<^bold>\<leftarrow>\<close>) where
  "\<^sup>*\<^bold>\<leftarrow> \<equiv> \<^bold>\<leftarrow>\<^sup>*"

abbreviation inv_finite_steps :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<^sup>*\<leftarrow> _\<close> [1000, 1000] 999) where
  "a \<^sup>*\<leftarrow> b \<equiv> (a, b) \<in> \<^sup>*\<^bold>\<leftarrow>"

abbreviation symm_closure :: "'a rel" (\<open>\<^bold>\<leftrightarrow>\<close>) where
  "\<^bold>\<leftrightarrow> \<equiv> \<^bold>\<rightarrow> \<union> \<^bold>\<leftarrow>"

abbreviation symm_step :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<leftrightarrow> _\<close> [1000, 1000] 999) where
  "a \<leftrightarrow> b \<equiv> (a, b) \<in> \<^bold>\<leftrightarrow>"

abbreviation symm_n_steps :: "'a \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<leftrightarrow>\<^sup>_ _\<close> [50, 50, 50] 50) where
  "a \<leftrightarrow>\<^sup>n b \<equiv> (a, b) \<in> \<^bold>\<leftrightarrow> ^^ n"

abbreviation symm_finite_nonempty_steps :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<leftrightarrow>\<^sup>+ _\<close> [50, 50] 50) where
  "a \<leftrightarrow>\<^sup>+ b \<equiv> (a, b) \<in> \<^bold>\<leftrightarrow>\<^sup>+"

abbreviation symm_finite_steps :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<leftrightarrow>\<^sup>* _\<close> [50, 50] 50) where
  "a \<leftrightarrow>\<^sup>* b \<equiv> (a, b) \<in> \<^bold>\<leftrightarrow>\<^sup>*"

lemma n_steps_trans:
  assumes "x \<rightarrow>\<^sup>m y" "y \<rightarrow>\<^sup>n z"
  shows "x \<rightarrow>\<^sup>(m+n) z"
  using assms by (auto simp: relpow_add)

lemma n_steps_imp_refl_trans:
  assumes "x \<rightarrow>\<^sup>n y"
  shows "x \<rightarrow>\<^sup>* y"
  using assms by (rule relpow_imp_rtrancl)

lemma inv_rstar_iff:
  shows "a \<^sup>*\<leftarrow> b \<longleftrightarrow> b \<rightarrow>\<^sup>* a"
  by (simp add: rtrancl_converse)

lemma rstar_trans:
  assumes "x \<rightarrow>\<^sup>* y" and "y \<rightarrow>\<^sup>* z"
  shows "x \<rightarrow>\<^sup>* z"
  using assms by (rule rtrancl_trans)

lemma rstar_neq_imp_step:
  assumes "x \<rightarrow>\<^sup>* y" and "x \<noteq> y"
  shows "\<exists>a. x \<rightarrow> a \<and> a \<rightarrow>\<^sup>* y"
  using assms by (cases rule: converse_rtranclE) auto

subsection \<open>Normal forms\<close>

definition is_reductible_wrt :: "'a \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "is_reductible_wrt x r \<equiv> \<exists> y. (x, y) \<in> r"

definition is_reductible :: "'a \<Rightarrow> bool" where
  "is_reductible x = is_reductible_wrt x \<^bold>\<rightarrow>"

definition is_in_normal_form :: "'a \<Rightarrow> bool" where
  "is_in_normal_form x \<equiv> \<nexists> y. x \<rightarrow> y"

definition normal_form :: "'a \<Rightarrow> 'a set" (\<open>nf'( _ ')\<close> ) where
  "nf(x) \<equiv> {y. x \<rightarrow>\<^sup>* y \<and> (\<nexists> z. y \<rightarrow> z)}"

definition normal_forms_wrt :: "'a rel \<Rightarrow> 'a set" (\<open>NF'(_')\<close>) where
  "NF(r) \<equiv> {x. \<not> is_reductible_wrt x r}"

lemma nf_empty_exists_y:
  assumes "nf(x) = {}"
  shows "\<exists> y. x \<rightarrow> y"
  using assms unfolding normal_form_def by auto

lemma nf_nonempty_exists_y:
  assumes "nf(x) \<noteq> {}"
  shows "\<exists> y. (\<exists> n. x \<rightarrow>\<^sup>n y) \<and> (\<nexists> z. y \<rightarrow> z)"
  using assms rtrancl_imp_relpow unfolding normal_form_def by blast

lemma exists_y_reds_then_nonempty:
  assumes "\<exists> y. (\<exists> n. x \<rightarrow>\<^sup>n y) \<and> (\<nexists> z. y \<rightarrow> z)"
  shows "nf(x) \<noteq> {}"
  using assms relpow_imp_rtrancl unfolding normal_form_def by blast

lemma nf_empty_reachable:
  assumes "nf(x) = {}"
      and "x \<rightarrow>\<^sup>* y"
  shows "nf(y) = {}"
  using assms unfolding normal_form_def by (blast intro: rtrancl_trans)

lemma nf_star_eq:
  assumes "x \<in> NF(\<^bold>\<rightarrow>)"
      and "x \<rightarrow>\<^sup>* y"
    shows "x = y"
  using assms(2,1) by (cases rule: converse_rtranclE)
    (auto simp: normal_forms_wrt_def is_reductible_wrt_def)

definition only_normal_form_of :: "'a \<Rightarrow> 'a option" (\<open>_\<down>\<close> [100] 100) where
  "x\<down> \<equiv> (if \<exists>!y. y \<in> nf(x) then Some (THE y. y \<in> nf(x)) else None)"

subsection \<open>Confluence and termination properties\<close>

definition joinable :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>_ \<down> _\<close> [60,60] 60) where
  "x \<down> y \<equiv> \<exists> z. x \<rightarrow>\<^sup>* z \<and> z \<^sup>*\<leftarrow> y"

abbreviation joinable_set :: "'a rel" (\<open>\<^bold>\<down>\<close>) where
  "\<^bold>\<down> \<equiv> \<^bold>\<rightarrow>\<^sup>* O \<^sup>*\<^bold>\<leftarrow>"

definition is_church_rosser :: bool (\<open>CR\<close>) where
  "is_church_rosser \<equiv> \<forall> x y. x \<leftrightarrow>\<^sup>* y \<longrightarrow> x \<down> y"

lemma church_rosser_equivalence [simp]:
  shows "is_church_rosser = (\<^bold>\<leftrightarrow>\<^sup>* \<subseteq> \<^bold>\<down>)"
  unfolding joinable_def is_church_rosser_def by auto

definition is_confluent :: bool where
  "is_confluent \<equiv> \<forall> x y\<^sub>1 y\<^sub>2. (y\<^sub>1 \<^sup>*\<leftarrow> x \<and> x \<rightarrow>\<^sup>* y\<^sub>2) \<longrightarrow> y\<^sub>1 \<down> y\<^sub>2"

lemma confluent_equivalence [simp]:
  shows "is_confluent = (\<^sup>*\<^bold>\<leftarrow> O \<^bold>\<rightarrow>\<^sup>* \<subseteq> \<^bold>\<down>)"
  unfolding joinable_def is_confluent_def relcomp_unfold by blast

definition is_normalizing :: bool where
  "is_normalizing \<equiv> \<forall> x. \<exists> y. y \<in> nf(x)"

definition is_terminating :: bool where
  "is_terminating \<equiv> \<not> (\<exists>f. \<forall>n. f n \<rightarrow> f (Suc n))"

definition is_convergent :: bool where
 "is_convergent \<equiv> is_terminating \<and> is_confluent"

definition choose_red :: "'a \<Rightarrow> 'a" where
  "choose_red x = (SOME y. x \<rightarrow> y)"

lemma nf_empty_then_choose_red:
  assumes "nf(x) = {}"
  shows "x \<rightarrow> choose_red x"
proof-
  obtain y where "x \<rightarrow> y"
    using nf_empty_exists_y[OF assms]
    by auto
  thus "x \<rightarrow> choose_red x"
    unfolding choose_red_def
    by (rule someI)
qed

fun reduction_seq :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "reduction_seq x 0 = x" |
  "reduction_seq x (Suc n) = choose_red (reduction_seq x n)"

lemma reduction_seq_reachable:
  assumes "nf(x) = {}"
  shows "(reduction_seq x 0) \<rightarrow>\<^sup>* (reduction_seq x n)"
proof(induct n)
  case 0
  show "(reduction_seq x 0) \<rightarrow>\<^sup>* (reduction_seq x 0)"
    by simp
next
  case (Suc m)
  have ih: "(reduction_seq x 0) \<rightarrow>\<^sup>* (reduction_seq x m)" by fact
  hence nf_empty: "nf(reduction_seq x m) = {}"
    using nf_empty_reachable reduction_seq.simps(1) assms by simp
  have step: "reduction_seq x m \<rightarrow> reduction_seq x (Suc m)"
    unfolding reduction_seq.simps using nf_empty_then_choose_red[OF nf_empty] by simp
  then show "(reduction_seq x 0) \<rightarrow>\<^sup>* (reduction_seq x (Suc m))"
    using ih by (rule rtrancl_into_rtrancl[rotated])
qed

lemma nf_empty_then_infinite_reduction:
  assumes "nf(x) = {}"
  shows "\<exists>f. f 0 = x \<and> (\<forall>n. f n \<rightarrow> f (Suc n))"
proof-
  let ?f = "reduction_seq x"
  have nf_empty: "nf(?f n) = {}" for n
    using assms nf_empty_reachable reduction_seq.simps(1) reduction_seq_reachable
    by simp
  have step: "\<forall>n. ?f n \<rightarrow> ?f (Suc n)"
    using nf_empty_then_choose_red[OF nf_empty] by simp
  thus "\<exists>f. f 0 = x \<and> (\<forall>n. f n \<rightarrow> f (Suc n))"
    using step reduction_seq.simps(1) by blast
qed

lemma terminating_is_normalizing:
  assumes is_terminating
  shows is_normalizing
proof(rule ccontr)
  assume "\<not> is_normalizing"
  hence "\<exists> x. \<exists>f. f 0 = x \<and> (\<forall>n. f n \<rightarrow> f (Suc n))"
   using nf_empty_then_infinite_reduction is_normalizing_def by blast
  hence "\<not> is_terminating"
    unfolding is_terminating_def by simp
  then show False
    using assms by simp
qed

(*Fim da Aula 1*)

subsection \<open>Termination and well-foundedness\<close>

definition my_wf :: bool where
  "my_wf \<equiv> (\<forall> P. (\<forall> x. (\<forall> y. x \<rightarrow> y \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x))"

lemma my_wf_eq:
  shows "my_wf = wf \<^bold>\<leftarrow>"
  unfolding my_wf_def wf_def by simp

lemma my_wf_induct:
  assumes "my_wf"
    and "\<And>x. \<forall>y. x \<rightarrow> y \<longrightarrow> P y \<Longrightarrow> P x"
  shows "P a"
  using assms unfolding my_wf_def by blast

lemmas my_wf_induct_rule = my_wf_induct [rule_format, consumes 1, case_names less, induct set: my_wf]

lemma wf_is_terminating:
  assumes "my_wf"
  shows "is_terminating"
proof-
  have hP: "\<forall>x. (\<forall>y. x \<rightarrow> y \<longrightarrow>
          \<not> (\<exists>f. f 0 = y \<and> (\<forall>n. f n \<rightarrow> f (Suc n))))
        \<longrightarrow>
        \<not> (\<exists>f. f 0 = x \<and> (\<forall>n. f n \<rightarrow> f (Suc n)))"
  proof(rule allI, rule impI)
    fix x
    assume IH:
      "\<forall>y. x \<rightarrow> y \<longrightarrow>
        \<not> (\<exists>f. f 0 = y \<and> (\<forall>n. f n \<rightarrow> f (Suc n)))"

    show "\<not> (\<exists>f. f 0 = x \<and> (\<forall>n. f n \<rightarrow> f (Suc n)))"
    proof
      assume "\<exists>f. f 0 = x \<and> (\<forall>n. f n \<rightarrow> f (Suc n))"
      then obtain f where
        hf0: "f 0 = x"
        and hf: "\<forall>n. f n \<rightarrow> f (Suc n)"
        by blast
      have "x \<rightarrow> (f 1)"
        using hf0 hf by auto
      hence no_inf:
          "\<not> (\<exists>g. g 0 = f 1 \<and> (\<forall>n. g n \<rightarrow> g (Suc n)))"
        using IH by blast
      moreover have inf:
          "\<exists>g. g 0 = f 1 \<and> (\<forall>n. g n \<rightarrow> g (Suc n))"
      proof-
        let ?g = "\<lambda>n. f (Suc n)"
        have "?g 0 = f 1"
          by simp
        moreover have "\<forall>n. ?g n \<rightarrow> ?g (Suc n)"
          using hf
          by simp
        ultimately show ?thesis by auto
      qed
      ultimately show False by auto
     qed
  qed
  then have h_all:
      "\<forall>x. \<not> (\<exists>f. f 0 = x \<and> (\<forall>n. f n \<rightarrow> f (Suc n)))"
  proof-
  have H:
      "(\<forall>x. (\<forall>y. x \<rightarrow> y \<longrightarrow>
          (\<nexists>f. f 0 = y \<and> (\<forall>n. f n \<rightarrow> f (Suc n))))
        \<longrightarrow>
        (\<nexists>f. f 0 = x \<and> (\<forall>n. f n \<rightarrow> f (Suc n))))
      \<longrightarrow>
      (\<forall>x. (\<nexists>f. f 0 = x \<and> (\<forall>n. f n \<rightarrow> f (Suc n))))"
    using assms unfolding my_wf_def by (rule allE)
    with hP show ?thesis by blast
   qed
  thus "is_terminating"
    unfolding is_terminating_def by auto
qed

lemma terminating_is_wf:
  assumes is_terminating
  shows my_wf
proof (rule ccontr)
  assume "\<not> my_wf"
  then obtain P where not_wf: "(\<forall>x. (\<forall>y. x \<rightarrow> y \<longrightarrow> P y) \<longrightarrow> P x)" "\<exists>x. \<not> P x"
    unfolding my_wf_def by blast
  have bad_step:
    "\<forall>x. \<not> P x \<longrightarrow> (\<exists>y. \<not> P y \<and> x \<rightarrow> y)"
  proof(rule allI, rule impI)
    fix x
    assume "\<not> P x"
    show "\<exists>y. \<not> P y \<and> x \<rightarrow> y"
    proof (rule ccontr)
      assume "\<not> (\<exists>y. \<not> P y \<and> x \<rightarrow> y)"
      hence "\<forall>y. x \<rightarrow> y \<longrightarrow> P y"
        by auto
      hence "P x"
        using not_wf by blast
      thus False
        using \<open>\<not> P x\<close>
        by blast
    qed
  qed

  have infinite_bad:
    "\<exists>f. \<forall>n. \<not> P (f n) \<and> f n \<rightarrow> f (Suc n)"
  proof (rule dependent_nat_choice)
    show "\<exists>x. \<not> P x"
      using not_wf by simp
    fix x n
    assume "\<not> P x"
    show "\<exists>y. \<not> P y \<and> x \<rightarrow> y"
      using bad_step \<open>\<not> P x\<close> by blast
  qed

  then obtain f where
     "\<forall>n. \<not> P (f n) \<and> f n \<rightarrow> f (Suc n)"
    by blast
  hence "\<exists>f. \<forall>n. f n \<rightarrow> f (Suc n)"
    by blast
  hence "\<not> is_terminating"
    unfolding is_terminating_def by blast
  thus False
    using assms by blast
qed

theorem wf_terminating_equiv:
  shows "my_wf = is_terminating"
  using wf_is_terminating terminating_is_wf by auto

subsection \<open>Reduction trees and König's lemma\<close>

inductive_set reduction_tree :: "'a \<Rightarrow> 'a set" (\<open>\<T>'(_')\<close>)
for a :: 'a where
  root[intro!]: "a \<in> \<T>(a)" |
  child[intro!]: "\<lbrakk>b \<in> \<T>(a); b \<rightarrow> c\<rbrakk> \<Longrightarrow> c \<in> \<T>(a)"
inductive_cases tree_elims:
  "c \<in> \<T>(a)"

lemma reduction_tree_iff:
  shows "b \<in> \<T>(a) \<longleftrightarrow> a \<rightarrow>\<^sup>* b"
proof
  assume "b \<in> \<T>(a)"
  then show "a \<rightarrow>\<^sup>* b"
    by induct (auto intro: rtrancl_into_rtrancl)
next
  assume "a \<rightarrow>\<^sup>* b"
  then show "b \<in> \<T>(a)"
    by (induct rule: rtrancl_induct) blast+
qed

lemma reduction_tree_subset:
  "\<T>(a) \<subseteq> insert a (\<Union>b\<in>{b. a \<rightarrow> b}. \<T>(b))"
proof
  fix x
  assume "x \<in> \<T>(a)"
  hence "a \<rightarrow>\<^sup>* x"
    by (simp add: reduction_tree_iff)
  thus "x \<in> insert a (\<Union>b\<in>{b. a \<rightarrow> b}. \<T>(b))"
    by (cases rule: converse_rtranclE) (simp_all add: reduction_tree_iff, blast)
qed

definition finitely_branching :: bool where
  "finitely_branching \<equiv> \<forall> a. finite {b. a \<rightarrow> b}"

lemma reduction_path:
  assumes "\<forall>n. f n \<rightarrow> f (Suc n)"
  shows "i < j \<Longrightarrow> (f i) \<rightarrow>\<^sup>+ (f j)"
proof (induct j)
  case 0
  thus ?case by simp
next
  case (Suc j)
  thus ?case
    using assms by (auto simp: less_Suc_eq intro: trancl_into_trancl)
qed

lemma infinite_reduction_path:
  assumes "\<forall>n. f n \<rightarrow> f (Suc n)"
      and "acyclic \<^bold>\<rightarrow>"
    shows "inj f"
proof
  fix i j
  assume eq: "f i = f j"
  show "i = j"
  proof (rule ccontr)
    assume "i \<noteq> j"
    hence "i < j \<or> j < i"
      by auto
    hence "(f i) \<rightarrow>\<^sup>+ (f j) \<or> (f j) \<rightarrow>\<^sup>+ (f i)"
      using reduction_path[OF assms(1)] by blast
    with eq have "(f i) \<rightarrow>\<^sup>+ (f i)"
      by auto
    thus False
      using assms(2) unfolding acyclic_def by simp
  qed
qed

lemma Konigs_1:
      assumes "acyclic \<^bold>\<rightarrow>"
      and "\<forall>a. finite \<T>(a)"
    shows is_terminating
proof(rule ccontr)
  assume "\<not> is_terminating"
  then obtain f where not_terminate: "f n \<rightarrow> f (Suc n)" for n
    unfolding is_terminating_def by auto
  have all_n_in_tree: "f n \<in> \<T>(f 0)" for n
  proof (induct n)
    case (Suc n)
    thus ?case using not_terminate[of n] by (rule child)
  qed (rule root)
  have "inj f"
    using infinite_reduction_path not_terminate assms(1) by simp
  moreover have "range f \<subseteq> \<T>(f 0)"
    using all_n_in_tree by force
  ultimately have "infinite \<T>(f 0)"
    using infinite_iff_countable_subset by auto
  thus False using assms by simp
qed

lemma Konigs_2:
  assumes finitely_branching
      and is_terminating
    shows "\<forall>a. finite \<T>(a)"
proof-
  have is_wf: "my_wf"
    using terminating_is_wf assms(2)
    by simp
  show "\<forall>a. finite \<T>(a)"
  proof
    fix a
    show "finite \<T>(a)"
    proof(induct rule: my_wf_induct_rule[OF is_wf])
      case (1 x)
      have "finite {y. x \<rightarrow> y}"
        using assms(1)
        unfolding finitely_branching_def by simp
      moreover have "\<forall>y \<in> {y. x \<rightarrow> y}. finite \<T>(y)"
        using 1 by simp
      ultimately have"finite (\<Union>y\<in>{y. x \<rightarrow> y}. \<T>(y))"
        by simp
      hence "finite (insert x (\<Union>y\<in>{y. x \<rightarrow> y}. \<T>(y)))"
        by simp
      thus "finite \<T>(x)"
        using reduction_tree_subset[of x] finite_subset by auto
    qed
  qed
qed

lemma Konig:
  assumes finitely_branching
      and "acyclic \<^bold>\<rightarrow>"
    shows "is_terminating = (\<forall>a. finite \<T>(a))"
using assms Konigs_1 Konigs_2 by auto

(*Fim da Aula 2*)

subsection \<open>The confluence hierarchy\<close>

definition strongly_confluent :: "bool" (\<open>SC\<close>) where
  "SC \<equiv> \<forall>a b c. b \<leftarrow> a \<and> a \<rightarrow> c \<longrightarrow>(\<exists>d. b \<rightarrow>\<^sup>= d \<and> d \<^sup>*\<leftarrow> c)"

lemma sc_equivalence [simp]:
  shows "SC = (\<^bold>\<leftarrow> O \<^bold>\<rightarrow> \<subseteq> \<^bold>\<rightarrow>\<^sup>= O \<^sup>*\<^bold>\<leftarrow>)"
  unfolding strongly_confluent_def relcomp_unfold by blast

definition locally_confluent :: "bool" (\<open>LC\<close>) where
  "LC \<equiv> \<forall>a b c. b \<leftarrow> a \<and> a \<rightarrow> c \<longrightarrow>(\<exists>d. b \<rightarrow>\<^sup>* d \<and> d \<^sup>*\<leftarrow> c)"

lemma lc_equivalence [simp]:
  shows "LC = (\<^bold>\<leftarrow> O \<^bold>\<rightarrow> \<subseteq> \<^bold>\<rightarrow>\<^sup>* O \<^sup>*\<^bold>\<leftarrow>)"
  unfolding locally_confluent_def relcomp_unfold by blast

abbreviation weakly_church_rosser :: "bool" (\<open>WCR\<close>) where
  "WCR \<equiv> LC"

definition unique_normal_forms_wrt :: "bool" (\<open>UNF\<^bold>\<rightarrow>\<close>) where
  "UNF\<^bold>\<rightarrow> \<equiv> \<forall> a b c. b \<^sup>*\<leftarrow> a \<longrightarrow> a \<rightarrow>\<^sup>* c \<longrightarrow> b \<in> NF(\<^bold>\<rightarrow>) \<longrightarrow> c \<in> NF(\<^bold>\<rightarrow>) \<longrightarrow> b = c"

definition has_unique_normal_forms :: "bool" (\<open>UNF\<close>) where
  "UNF \<equiv> \<forall> a b. a \<leftrightarrow>\<^sup>* b \<longrightarrow> a \<in> NF(\<^bold>\<rightarrow>) \<longrightarrow> b \<in> NF(\<^bold>\<rightarrow>) \<longrightarrow> a = b"

definition has_normal_form_property :: "bool" (\<open>NFP\<close>) where
  "NFP \<equiv> \<forall> a b. a \<leftrightarrow>\<^sup>* b \<longrightarrow> b \<in> NF(\<^bold>\<rightarrow>) \<longrightarrow> a \<rightarrow>\<^sup>* b"

proposition confluent_iff_CR:
  shows "is_confluent \<longleftrightarrow> CR"
proof
  assume conf: is_confluent
  show CR
    unfolding is_church_rosser_def
  proof (intro allI impI)
    fix x y
    assume "x \<leftrightarrow>\<^sup>* y"
    then show "x \<down> y"
    proof (induct rule: rtrancl_induct)
      case base
      show ?case unfolding joinable_def by auto
    next
      case (step y z)
      from step(3) obtain d where xd: "x \<rightarrow>\<^sup>* d" and yd: "y \<rightarrow>\<^sup>* d"
        unfolding joinable_def inv_rstar_iff by auto
      from step(2) show ?case
      proof
        assume "y \<rightarrow> z"
        hence "y \<rightarrow>\<^sup>* z" by simp
        then obtain e where "d \<rightarrow>\<^sup>* e" "z \<rightarrow>\<^sup>* e"
          using conf yd unfolding is_confluent_def joinable_def inv_rstar_iff by blast
        thus "x \<down> z"
          using xd unfolding joinable_def inv_rstar_iff by (blast intro: rtrancl_trans)
      next
        assume "(y, z) \<in> \<^bold>\<leftarrow>"
        hence "z \<rightarrow>\<^sup>* d"
          using yd by (blast intro: converse_rtrancl_into_rtrancl)
        thus "x \<down> z"
          using xd unfolding joinable_def inv_rstar_iff by blast
      qed
    qed
  qed
next
  assume cr: CR
  show is_confluent
    unfolding is_confluent_def
  proof (intro allI impI)
    fix x y\<^sub>1 y\<^sub>2
    assume "y\<^sub>1 \<^sup>*\<leftarrow> x \<and> x \<rightarrow>\<^sup>* y\<^sub>2"
    hence "y\<^sub>1 \<leftrightarrow>\<^sup>* x" and "x \<leftrightarrow>\<^sup>* y\<^sub>2"
      using rtrancl_mono[of "\<^bold>\<leftarrow>" "\<^bold>\<leftrightarrow>"] rtrancl_mono[of "\<^bold>\<rightarrow>" "\<^bold>\<leftrightarrow>"] by blast+
    hence "y\<^sub>1 \<leftrightarrow>\<^sup>* y\<^sub>2"
      by (rule rtrancl_trans)
    thus "y\<^sub>1 \<down> y\<^sub>2"
      using cr unfolding is_church_rosser_def by blast
  qed
qed

lemma relpow_converse:
  fixes r :: "'b rel"
  shows "(r\<inverse>) ^^ n = (r ^^ n)\<inverse>"
  by (induct n) (simp_all, metis converse_relcomp relpow_commute)

lemma inv_comp:
  fixes r :: "'b rel"
  shows "(x, y) \<in> (r\<inverse>) ^^ n \<longleftrightarrow> (y, x) \<in> r ^^ n"
  by (simp add: relpow_converse)

lemma sc_imp_lc:
  assumes SC
  shows LC
  using assms unfolding strongly_confluent_def locally_confluent_def
  by (metis Un_iff pair_in_Id_conv r_into_rtrancl rtrancl.rtrancl_refl)

lemma lc_imp_wcr:
  assumes LC
  shows WCR
  using assms by simp

lemma confluent_imp_lc:
  assumes is_confluent
  shows LC
  using assms unfolding is_confluent_def locally_confluent_def joinable_def
  by (meson converse_iff r_into_rtrancl)

lemma church_rosser_imp_nfp:
  assumes CR
  shows NFP
proof (unfold has_normal_form_property_def, intro allI impI)
  fix a b
  assume "a \<leftrightarrow>\<^sup>* b" and "b \<in> NF(\<^bold>\<rightarrow>)"
  have "a \<down> b"
    using assms \<open>a \<leftrightarrow>\<^sup>* b\<close>
    unfolding is_church_rosser_def by blast
  then obtain z where "a \<rightarrow>\<^sup>* z" and "b \<rightarrow>\<^sup>* z"
    unfolding joinable_def inv_rstar_iff by auto
  hence "z = b"
    using nf_star_eq[of b z] \<open>b \<in> NF(\<^bold>\<rightarrow>)\<close> by simp
  thus "a \<rightarrow>\<^sup>* b"
    using \<open>a \<rightarrow>\<^sup>* z\<close> by simp
qed

lemma nfp_imp_unf:
  assumes NFP
  shows UNF
proof (unfold has_unique_normal_forms_def, intro allI impI)
  fix a b
  assume "a \<leftrightarrow>\<^sup>* b" and "a \<in> NF(\<^bold>\<rightarrow>)" and "b \<in> NF(\<^bold>\<rightarrow>)"
  have "a \<rightarrow>\<^sup>* b"
    using assms \<open>a \<leftrightarrow>\<^sup>* b\<close> \<open>b \<in> NF(\<^bold>\<rightarrow>)\<close>
    unfolding has_normal_form_property_def by blast
  thus "a = b"
    using nf_star_eq[of a b] \<open>a \<in> NF(\<^bold>\<rightarrow>)\<close> by simp
qed

lemma church_rosser_imp_unf:
  assumes CR
  shows UNF
  using church_rosser_imp_nfp[OF assms] nfp_imp_unf by simp

lemma newman_lemma:
  assumes is_terminating
      and LC
    shows CR
proof -
  have wf: "my_wf"
    using terminating_is_wf assms(1) by simp
  have conf: "is_confluent"
    unfolding is_confluent_def
  proof (intro allI)
    fix x y\<^sub>1 y\<^sub>2
    show "y\<^sub>1 \<^sup>*\<leftarrow> x \<and> x \<rightarrow>\<^sup>* y\<^sub>2 \<longrightarrow> y\<^sub>1 \<down> y\<^sub>2"
    proof (induct x arbitrary: y\<^sub>1 y\<^sub>2 rule: my_wf_induct_rule[OF wf])
      case (1 x)
      show ?case
      proof (intro impI)
        assume "y\<^sub>1 \<^sup>*\<leftarrow> x \<and> x \<rightarrow>\<^sup>* y\<^sub>2"
        hence hy1: "y\<^sub>1 \<^sup>*\<leftarrow> x" and hy2: "x \<rightarrow>\<^sup>* y\<^sub>2" by auto
        hence hy1': "x \<rightarrow>\<^sup>* y\<^sub>1" using inv_rstar_iff by simp
        show "y\<^sub>1 \<down> y\<^sub>2"
        proof (cases "x = y\<^sub>1")
          case True
          hence "y\<^sub>1 \<rightarrow>\<^sup>* y\<^sub>2" using hy2 by simp
          moreover have "y\<^sub>2 \<^sup>*\<leftarrow> y\<^sub>2"
            by simp
          ultimately show "y\<^sub>1 \<down> y\<^sub>2" unfolding joinable_def by auto
        next
          case False
          show ?thesis
          proof (cases "x = y\<^sub>2")
            case True
            have "y\<^sub>1 \<rightarrow>\<^sup>* y\<^sub>1"
              by simp
            thus "y\<^sub>1 \<down> y\<^sub>2"
              unfolding joinable_def using hy1 True by auto
          next
            case False
            from hy1' \<open>x \<noteq> y\<^sub>1\<close> obtain a1 where step1: "x \<rightarrow> a1" and hstar1: "a1 \<rightarrow>\<^sup>* y\<^sub>1"
              using rstar_neq_imp_step by blast
            from hy2 \<open>x \<noteq> y\<^sub>2\<close> obtain a2 where step2: "x \<rightarrow> a2" and hstar2: "a2 \<rightarrow>\<^sup>* y\<^sub>2"
              using rstar_neq_imp_step by blast
            have ha1: "a1 \<leftarrow> x"
              using step1 by simp
            obtain d where "a1 \<rightarrow>\<^sup>* d" and hd: "d \<^sup>*\<leftarrow> a2"
              using assms(2)[unfolded locally_confluent_def] ha1 step2 by blast
            have hstard: "a2 \<rightarrow>\<^sup>* d"
              using hd inv_rstar_iff by simp
            have hIH1: "y\<^sub>1 \<^sup>*\<leftarrow> a1 \<and> a1 \<rightarrow>\<^sup>* d \<longrightarrow> y\<^sub>1 \<down> d"
              using "1"[of a1 y\<^sub>1 d] step1 by simp
            have "y\<^sub>1 \<^sup>*\<leftarrow> a1"
              using hstar1 inv_rstar_iff by simp
            hence "y\<^sub>1 \<down> d"
              using hIH1 \<open>a1 \<rightarrow>\<^sup>* d\<close> by simp
            then obtain e where he1: "y\<^sub>1 \<rightarrow>\<^sup>* e" and he2: "e \<^sup>*\<leftarrow> d"
              unfolding joinable_def by auto
            have "d \<rightarrow>\<^sup>* e"
              using he2 inv_rstar_iff by simp
            have "a2 \<rightarrow>\<^sup>* e"
              using rstar_trans[OF hstard \<open>d \<rightarrow>\<^sup>* e\<close>] .
            have hIH2: "e \<^sup>*\<leftarrow> a2 \<and> a2 \<rightarrow>\<^sup>* y\<^sub>2 \<longrightarrow> e \<down> y\<^sub>2"
              using "1"[of a2 e y\<^sub>2] step2 by simp
            have "e \<^sup>*\<leftarrow> a2"
              using \<open>a2 \<rightarrow>\<^sup>* e\<close> inv_rstar_iff by simp
            hence "e \<down> y\<^sub>2"
              using hIH2 hstar2 by simp
            then obtain f where hf1: "e \<rightarrow>\<^sup>* f" and hf2: "f \<^sup>*\<leftarrow> y\<^sub>2"
              unfolding joinable_def by auto
            have "y\<^sub>1 \<rightarrow>\<^sup>* f"
              using rstar_trans[OF he1 hf1] .
            thus "y\<^sub>1 \<down> y\<^sub>2"
              unfolding joinable_def using hf2 by auto
          qed
        qed
      qed
    qed
  qed
  thus CR
    using confluent_iff_CR by simp
qed

proposition hierarchy_of_confluence:
  shows "SC \<Longrightarrow> LC"
    and "LC \<Longrightarrow> WCR"
    and "is_confluent \<Longrightarrow> LC"
    and "is_confluent \<longleftrightarrow> CR"
    and "CR \<Longrightarrow> NFP"
    and "NFP \<Longrightarrow> UNF"
    and "CR \<Longrightarrow> UNF"
    and "is_terminating \<Longrightarrow> LC \<Longrightarrow> CR"
  using sc_imp_lc lc_imp_wcr confluent_imp_lc confluent_iff_CR
        church_rosser_imp_nfp nfp_imp_unf church_rosser_imp_unf newman_lemma by auto

end

end
