theory Commutation
imports Multisets_WF
begin

definition diamond :: "'a rel \<Rightarrow> bool" (\<open>\<diamond>\<close>) where
  "\<diamond> R \<equiv> \<forall>a b c. (a, b) \<in> R \<and> (a, c) \<in> R \<longrightarrow> (\<exists>d. (b, d) \<in> R \<and> (c, d) \<in> R)"

lemma diamond_iff_comp:
  fixes R :: "'a rel"
  shows "\<diamond> R \<longleftrightarrow> R\<inverse> O R \<subseteq> R O R\<inverse>"
  unfolding diamond_def by blast

text\<open>Unfolding \<open>R ^^ n\<close> one step at a time, from the left.\<close>

lemma comp_zero_iff:
  fixes R :: "'a rel"
  shows "(x, y) \<in> R ^^ 0 \<longleftrightarrow> x = y"
  by simp

lemma comp_suc_iff:
  fixes R :: "'a rel"
  shows "(x, y) \<in> R ^^ Suc n \<longleftrightarrow> (\<exists>z. (x, z) \<in> R \<and> (z, y) \<in> R ^^ n)"
  by (blast intro: relpow_Suc_I2 dest: relpow_Suc_D2)

lemma diamond_strip:
  fixes R :: "'a rel"
  assumes "\<diamond> R" and "(a, b) \<in> R" and "(a, c) \<in> R ^^ n"
  shows "\<exists>d. (b, d) \<in> R ^^ n \<and> (c, d) \<in> R"
  using assms(2,3)
proof(induction n arbitrary: a b)
  case 0
  hence "a = c" unfolding comp_zero_iff by blast
  hence "(b, b) \<in> R ^^ 0" and "(c, b) \<in> R"
    using 0(1) unfolding comp_zero_iff by blast+
  thus ?case by blast
next
  case (Suc n)
  obtain z where "(a, z) \<in> R" and "(z, c) \<in> R ^^ n"
    using Suc.prems(2) unfolding comp_suc_iff by blast
  then obtain e where "(b, e) \<in> R" and "(z, e) \<in> R"
    using assms(1) Suc.prems(1) unfolding diamond_def by blast
  then obtain d where "(e, d) \<in> R ^^ n" and "(c, d) \<in> R"
    using Suc.IH \<open>(z, c) \<in> R ^^ n\<close> by blast
  have "(b, d) \<in> R ^^ (Suc n)"
    unfolding comp_suc_iff using \<open>(b, e) \<in> R\<close> \<open>(e, d) \<in> R ^^ n\<close> by blast
  thus ?case using \<open>(c, d) \<in> R\<close> by blast
qed

lemma diamond_comp:
  fixes R :: "'a rel"
  assumes "\<diamond> R" and "(a, b) \<in> R ^^ m" and "(a, c) \<in> R ^^ n"
  shows "\<exists>d. (b, d) \<in> R ^^ n \<and> (c, d) \<in> R ^^ m"
  using assms(2,3)
proof(induction m arbitrary: a b c)
  case 0
  hence "a = b" unfolding comp_zero_iff by blast
  hence "(b, c) \<in> R ^^ n" and "(c, c) \<in> R ^^ 0"
    using 0(2) unfolding comp_zero_iff by blast+
  thus ?case by blast
next
  case (Suc m)
  obtain z where "(a, z) \<in> R" and "(z, b) \<in> R ^^ m"
    using Suc.prems(1) unfolding comp_suc_iff by blast
  then obtain e where "(z, e) \<in> R ^^ n" and "(c, e) \<in> R"
    using diamond_strip[OF assms(1)] Suc.prems(2) by blast
  then obtain d where "(b, d) \<in> R ^^ n" and "(e, d) \<in> R ^^ m"
    using Suc.IH \<open>(z, b) \<in> R ^^ m\<close> by blast
  have "(c, d) \<in> R ^^ (Suc m)"
    unfolding comp_suc_iff using \<open>(c, e) \<in> R\<close> \<open>(e, d) \<in> R ^^ m\<close> by blast
  thus ?case using \<open>(b, d) \<in> R ^^ n\<close> by blast
qed

lemma diamond_rstar:
  assumes "\<diamond> R"
  shows "\<diamond> (R\<^sup>*)"
  unfolding diamond_def rtrancl_power
  using diamond_comp[OF assms] by blast

lemma rstar_rstar_subset:
  fixes r :: "'a rel"
  shows "(r\<^sup>*)\<^sup>* \<subseteq> r\<^sup>*"
  by simp

context ARS
begin


lemma conf_iff_diamond_rtc:
  shows "is_confluent \<longleftrightarrow> \<diamond> (\<^bold>\<rightarrow>\<^sup>*)"
  unfolding is_confluent_def diamond_def joinable_def
  using inv_rstar_iff by simp

text \<open>Lemma 2.4.2\<close>

lemma diamond_between_imp_confluent:
  fixes S :: "'a rel"
  assumes "\<diamond> S" and "\<^bold>\<rightarrow> \<subseteq> S" and "S \<subseteq> \<^bold>\<rightarrow>\<^sup>*"
  shows is_confluent
proof -
  have "\<^bold>\<rightarrow>\<^sup>* = S\<^sup>*"
    using rtrancl_subset[OF assms(2,3)] by simp
  thus ?thesis
    using conf_iff_diamond_rtc diamond_rstar[OF assms(1)] by simp
qed


end

end 