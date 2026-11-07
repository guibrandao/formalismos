theory Partial_Orders
  imports Reduction_Systems
begin

section \<open>Orderings\<close>

text\<open>An ordering is just a binary relation with some extra properties. We write
  \<open>a \<succ>\<^sub>r b\<close> for \<open>(a, b) \<in> r\<close>, read ``\<open>a\<close> is greater than \<open>b\<close> in \<open>r\<close>''.\<close>

abbreviation succ :: "'a \<Rightarrow> 'a rel \<Rightarrow> 'a \<Rightarrow> bool" (\<open>(_/ \<succ>\<^sub>_ _)\<close> [51, 0, 51] 50) where
  "a \<succ>\<^sub>r b \<equiv> (a, b) \<in> r"

subsection \<open>Partial and total orderings\<close>

text\<open>Definition 2.3.1. We use HOL's \<open>irrefl\<close>, \<open>trans\<close>, \<open>refl\<close>, \<open>antisym\<close> and \<open>total\<close>.\<close>

definition partial_ordering :: "'a rel \<Rightarrow> bool" where
  "partial_ordering r \<equiv> irrefl r \<and> trans r"

definition total_ordering :: "'a rel \<Rightarrow> bool" where
  "total_ordering r \<equiv> partial_ordering r \<and> total r"

lemma succ_irrefl:
  assumes "partial_ordering r"
  shows "\<not> a \<succ>\<^sub>r a"
  using assms unfolding partial_ordering_def irrefl_def by simp

lemma succ_trans:
  assumes "partial_ordering r" and "a \<succ>\<^sub>r b" and "b \<succ>\<^sub>r c"
  shows "a \<succ>\<^sub>r c"
  using assms unfolding partial_ordering_def trans_def by blast

lemma succ_total:
  assumes "total_ordering r" and "a \<noteq> b"
  shows "a \<succ>\<^sub>r b \<or> b \<succ>\<^sub>r a"
  using assms unfolding total_ordering_def total_on_def by blast

lemma total_ordering_imp_partial_ordering:
  assumes "total_ordering r"
  shows "partial_ordering r"
  using assms unfolding total_ordering_def by simp

subsection \<open>Orderings as abstract reduction systems\<close>

text\<open>Every relation \<open>r\<close> is an ARS whose reduction \<open>\<^bold>\<rightarrow>\<close> is \<open>r\<close> itself. So a partial
  ordering is an ARS whose reduction relation is irreflexive and transitive.\<close>

text\<open>Well-foundedness of \<open>r\<close> is the notion \<open>my_wf\<close> of the corresponding ARS:
  there is no infinite descending chain \<open>a\<^sub>0 \<succ>\<^bsub>r\<^esub> a\<^sub>1 \<succ>\<^bsub>r\<^esub> a\<^sub>2 \<succ>\<^bsub>r\<^esub> \<dots>\<close>.\<close>

definition well_founded :: "'a rel \<Rightarrow> bool" where
  "well_founded r \<equiv> ARS.my_wf r"

lemma well_founded_iff_wf: "well_founded r \<longleftrightarrow> wf (r\<inverse>)"
proof -
  interpret ARS r .
  show ?thesis
    unfolding well_founded_def my_wf_eq ..
qed

subsection \<open>Quasi-orderings and reflexive partial orderings\<close>

text\<open>Definition 2.3.2 (1)\<close>

definition quasi_ordering :: "'a rel \<Rightarrow> bool" where
  "quasi_ordering r \<equiv> refl r \<and> trans r"

text\<open>Definition 2.3.2 (2)\<close>

definition reflexive_partial_ordering :: "'a rel \<Rightarrow> bool" where
  "reflexive_partial_ordering r \<equiv> quasi_ordering r \<and> antisym r"

text\<open>Lemma 2.3.4\<close>

lemma refl_cl_of_partial_ordering_is_reflexive_partial_ordering:
  assumes "partial_ordering r"
  shows "reflexive_partial_ordering (r\<^sup>=)"
proof -
  have irr_r: "irrefl r" and trans_r: "trans r"
    using assms unfolding partial_ordering_def by simp_all
  have refl: "refl (r\<^sup>=)"
    by (rule refl_reflcl)
  have trans: "trans (r\<^sup>=)"
    using trans_r unfolding trans_def by blast
  have antisym: "antisym (r\<^sup>=)"
    using irr_r trans_r unfolding antisym_def irrefl_def trans_def by blast
  show ?thesis
    unfolding reflexive_partial_ordering_def quasi_ordering_def
    using refl trans antisym by simp
qed

lemma strict_part_of_reflexive_partial_ordering_is_partial_ordering:
  assumes "reflexive_partial_ordering r"
  shows "partial_ordering (r - Id)"
proof -
  have trans_r: "trans r" and antisym_r: "antisym r"
    using assms unfolding reflexive_partial_ordering_def quasi_ordering_def by simp_all
  have irr: "irrefl (r - Id)"
    unfolding irrefl_def by auto
  have trans: "trans (r - Id)"
    using trans_r antisym_r unfolding trans_def antisym_def by blast
  show ?thesis
    unfolding partial_ordering_def using irr trans by simp
qed

lemma strict_part_of_quasi_ordering_is_partial_ordering:
  assumes "quasi_ordering r"
  shows "partial_ordering (r - r\<inverse>)"
proof -
  have refl_r: "refl r" and trans_r: "trans r"
    using assms unfolding quasi_ordering_def by simp_all
  have irr: "irrefl (r - r\<inverse>)"
    unfolding irrefl_def by auto
  have trans: "trans (r - r\<inverse>)"
    using trans_r unfolding trans_def by blast
  show ?thesis
    unfolding partial_ordering_def using irr trans by simp
qed

subsection \<open>Lexicographic ordering\<close>

text\<open>\<open>(a, b)\<close> is greater than \<open>(c, d)\<close> if \<open>a \<succ>\<^sub>r c\<close>, or \<open>a = c\<close> and \<open>b \<succ>\<^sub>s d\<close>.\<close>

definition lex_prod :: "'a rel \<Rightarrow> 'b rel \<Rightarrow> ('a \<times> 'b) rel" where
  "lex_prod r s \<equiv> {((a, b), (c, d)). a \<succ>\<^sub>r c \<or> (a = c \<and> b \<succ>\<^sub>s d)}"

lemma partial_ordering_lex_prod:
  assumes "partial_ordering r" and "partial_ordering s"
  shows "partial_ordering (lex_prod r s)"
proof -
  have trans_r: "trans r" and trans_s: "trans s"
    using assms unfolding partial_ordering_def by auto
  have irr: "irrefl (lex_prod r s)"
    using assms unfolding partial_ordering_def irrefl_def lex_prod_def by auto
  have trans: "trans (lex_prod r s)"
  proof (rule transI)
    fix x y z
    assume "(x, y) \<in> lex_prod r s" "(y, z) \<in> lex_prod r s"
    then obtain a b c d e f where x: "x = (a, b)" and "y = (c, d)" and z: "z = (e, f)"
      and 1: "a \<succ>\<^sub>r c \<or> (a = c \<and> b \<succ>\<^sub>s d)"
      and 2: "c \<succ>\<^sub>r e \<or> (c = e \<and> d  \<succ>\<^sub>s f)"
      unfolding lex_prod_def by auto
    from 1 2 show "(x, z) \<in> lex_prod r s"
    proof (elim disjE)
      assume "a \<succ>\<^sub>r c" "c  \<succ>\<^sub>r e"
      with trans_r have "a  \<succ>\<^sub>r e" unfolding trans_def by blast
      thus ?thesis unfolding lex_prod_def x z by auto
    next
      assume "a  \<succ>\<^sub>r c" "c = e \<and> d  \<succ>\<^sub>s f"
      hence "a  \<succ>\<^sub>r e" by simp
      thus ?thesis unfolding lex_prod_def x z by auto
    next
      assume "a = c \<and> b  \<succ>\<^sub>s d" "c  \<succ>\<^sub>r e"
      hence "a  \<succ>\<^sub>r e" by simp
      thus ?thesis unfolding lex_prod_def x z by auto
    next
      assume "a = c \<and> b  \<succ>\<^sub>s d" "c = e \<and> d  \<succ>\<^sub>s f"
      hence "a = e" and "b  \<succ>\<^sub>s d" "d  \<succ>\<^sub>s f" by auto
      with trans_s have "b  \<succ>\<^sub>s f" unfolding trans_def by blast
      with \<open>a = e\<close> show ?thesis unfolding lex_prod_def x z by auto
    qed
  qed
  show ?thesis
    unfolding partial_ordering_def using irr trans by simp
qed

lemma total_lex_prod:
  assumes "total r" and "total s"
  shows "total (lex_prod r s)"
proof (unfold total_on_def, intro ballI impI)
  fix x y :: "'a \<times> 'b"
  assume "x \<noteq> y"
  obtain a b c d where x: "x = (a, b)" and y: "y = (c, d)" by fastforce
  have "a \<noteq> c \<or> (a = c \<and> b \<noteq> d)" using \<open>x \<noteq> y\<close> x y by auto
  thus "(x, y) \<in> lex_prod r s \<or> (y, x) \<in> lex_prod r s"
  proof
    assume "a \<noteq> c"
    hence "a  \<succ>\<^sub>r c \<or> c \<succ>\<^sub>r a" using assms(1) unfolding total_on_def by auto
    thus ?thesis unfolding lex_prod_def x y by auto
  next
    assume "a = c \<and> b \<noteq> d"
    hence "b  \<succ>\<^sub>s d \<or> d  \<succ>\<^sub>s b" using assms(2) unfolding total_on_def by auto
    thus ?thesis unfolding lex_prod_def x y using \<open>a = c \<and> b \<noteq> d\<close> by auto
  qed
qed

lemma total_ordering_lex_prod:
  assumes "total_ordering r" and "total_ordering s"
  shows "total_ordering (lex_prod r s)"
  using assms partial_ordering_lex_prod total_lex_prod
  unfolding total_ordering_def by blast

lemma well_founded_lex_prod:
  assumes "well_founded r" and "well_founded s"
  shows "well_founded (lex_prod r s)"
proof -
  have "wf (r\<inverse> <*lex*> s\<inverse>)"
    using assms Wellfounded.wf_lex_prod unfolding well_founded_iff_wf by blast
  moreover have "(lex_prod r s)\<inverse> = r\<inverse> <*lex*> s\<inverse>"
    unfolding lex_prod_def by auto
  ultimately show ?thesis
    unfolding well_founded_iff_wf by simp
qed

end
