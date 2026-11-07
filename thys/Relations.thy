theory Relations
imports Main
begin

type_synonym 'a relation = "('a \<times> 'a) set"

definition composition :: "'a relation \<Rightarrow> 'a relation \<Rightarrow> 'a relation" (infix \<open>\<^bold>\<circ>\<close> 100) where
  "r \<^bold>\<circ> s = {(x,z). \<exists> y. (x,y) \<in> r \<and> (y,z) \<in> s}"

lemma composition_assoc:
  "(r \<^bold>\<circ> s) \<^bold>\<circ> t = r \<^bold>\<circ> (s \<^bold>\<circ> t)"
unfolding composition_def by auto


text\<open>Properties of relations\<close>

type_synonym 'a rel_prop = "'a relation \<Rightarrow> bool"

definition reflexive :: "'a rel_prop" where
  "reflexive r \<equiv> \<forall> x. (x, x) \<in> r"

definition symmetric :: "'a rel_prop" where
  "symmetric r \<equiv> \<forall> x y.(x, y) \<in> r \<longrightarrow> (y, x) \<in> r"

definition transitive :: "'a rel_prop" where
  "transitive r \<equiv> \<forall> x y z. ((x, y) \<in> r \<and> (y, z) \<in> r) \<longrightarrow> (x, z) \<in> r"

definition irreflexive :: "'a rel_prop" where
  "irreflexive r \<equiv> \<forall> x. (x, x) \<notin> r"

definition assymetric :: "'a rel_prop" where
  "assymetric r \<equiv> \<forall> x y. (x, y) \<in> r \<longrightarrow> (y, x) \<notin> r"

definition antisymmetric :: "'a rel_prop" where
  "antisymmetric r \<equiv> \<forall> x y. ((x, y) \<in> r \<and> (y, x) \<in> r) \<longrightarrow> x = y"

definition total :: "'a rel_prop" where
  "total r \<equiv> \<forall> x y.  x \<noteq> y \<longrightarrow> (x, y) \<in> r \<or> (y, x) \<in> r"

text\<open>Closure of a relation w.r.t a given property\<close>

definition closure :: "'a relation \<Rightarrow> 'a rel_prop \<Rightarrow> 'a relation" where
  "closure r P = \<Inter>{s. r \<subseteq> s \<and> P s}"

lemma closure_is_minimal:
  assumes "P s" and "r \<subseteq> s"
  shows "closure r P \<subseteq> s"
using assms unfolding closure_def by auto

lemma r_is_in_closure:
  shows "r \<subseteq> closure r P"
unfolding closure_def by auto


definition is_related :: "'a \<Rightarrow> 'a relation \<Rightarrow> bool" where
  "is_related x s \<equiv> \<exists> y. (x, y) \<in> s"

lemma refl_closure_is_reflexive:
"reflexive (closure R reflexive)"
  unfolding closure_def reflexive_def by simp

lemma symm_closure_is_symmetric:
"symmetric (closure R symmetric)"
  unfolding closure_def symmetric_def by simp

lemma trans_closure_is_transitive:
"transitive (closure R transitive)"
proof(unfold transitive_def, auto)
  let ?trans = "(\<lambda>R. \<forall>x y z. (x, y) \<in> R \<and> (y, z) \<in> R \<longrightarrow> (x, z) \<in> R)"
  fix x y z
  assume "(x, y) \<in> closure R ?trans" "(y, z) \<in> closure R ?trans" 
  then show "(x, z) \<in> closure R ?trans"
    unfolding closure_def by blast
qed

no_notation trancl (\<open>(\<open>notation=\<open>postfix +\<close>\<close>_\<^sup>+)\<close> [1000] 999)
no_notation rtrancl (\<open>(\<open>notation=\<open>postfix *\<close>\<close>_\<^sup>*)\<close> [1000] 999)
no_notation reflcl (\<open>(\<open>notation=\<open>postfix =\<close>\<close>_\<^sup>=)\<close> [1000] 999)

definition Id :: "('a \<times> 'a) set" where
  "Id = {(x, x) | x. True}"

fun comp :: "'a relation  \<Rightarrow> nat \<Rightarrow> 'a relation" (\<open>(\<open>notation=\<open>postfix _\<close>\<close>_\<^sup>_)\<close> [1000] 999) where
 "comp r 0  = Id" |
 "comp r (Suc i) = r \<^bold>\<circ> (comp r i)"

lemma r1_is_r [simp]:
shows "comp r (Suc 0) = r"
  unfolding comp.simps composition_def Id_def by simp

lemma comp_zero_iff:
  shows "(x,y) \<in> comp r 0 \<longleftrightarrow> x = y"
  unfolding comp.simps Id_def by auto

lemma comp_suc_iff:
  shows "(x,y) \<in> comp r (Suc n) \<longleftrightarrow> (\<exists>z. (x,z) \<in> r \<and> (z,y) \<in> comp r n)"
  unfolding comp.simps composition_def by auto

lemma comp_comp:
  shows "comp r m \<^bold>\<circ> comp r n = comp r (m + n)"
proof (induction m)
  case 0
  show "comp r 0 \<^bold>\<circ> comp r n = comp r (0 + n)"
  unfolding comp.simps Id_def composition_def
    by auto
next
  case (Suc m)
  have "comp r ((Suc m) + n) = comp r (Suc (m + n))"
     using add_Suc_right add_Suc_shift by simp
  also have "... = r \<^bold>\<circ> (comp r m \<^bold>\<circ> comp r n)"
    using Suc unfolding comp.simps by simp
  also have "... = (r \<^bold>\<circ> comp r m) \<^bold>\<circ> comp r n"
    using composition_assoc by auto
  finally show "comp r (Suc m) \<^bold>\<circ> comp r n = comp r ((Suc m) + n)"
    unfolding comp.simps by simp
qed

lemma comp_commutes:
  "comp r m \<^bold>\<circ> comp r n = comp r n \<^bold>\<circ> comp r m"
 by (simp add: comp_comp add.commute)

lemma comp_subset_trans_closure:
  assumes "n > 0"
  shows "comp r n \<subseteq> closure r transitive"
using assms
proof(induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
  proof (cases n)
    case 0
    then show ?thesis 
      using r1_is_r[of r] r_is_in_closure[of r transitive] by simp
  next
    case (Suc n')
    show ?thesis
      unfolding comp.simps
    proof
      fix p
      assume assm: "p \<in> r \<^bold>\<circ> r\<^sup>n"
      then obtain x z where "p = (x, z)" by force
      hence "\<exists>y. (x,y) \<in> r \<and> (y,z) \<in> comp r (Suc n')" 
        using assm Suc unfolding composition_def by simp
      then obtain y where
        "(x,y) \<in> r"
        "(y,z) \<in> comp r (Suc n')"
        by auto
      hence "(x,y) \<in> closure r transitive"
        unfolding closure_def by auto
      moreover have "(y,z) \<in> closure r transitive"
        using Suc.IH Suc \<open>(y,z) \<in> comp r (Suc n')\<close>
          by auto
      moreover have "transitive (closure r transitive)"
        using trans_closure_is_transitive by auto
      ultimately have  "(x,z) \<in> closure r transitive"
        unfolding transitive_def by blast
      thus "p \<in> closure r transitive" 
        using \<open>p = (x, z)\<close> by simp
    qed
  qed
qed

lemma comp_imp_path:
  assumes "(x,y) \<in> comp r n"
  shows "\<exists>f. f 0 = x \<and>
              f n = y \<and>
              (\<forall>i<n. (f i, f (Suc i)) \<in> r)"
  using assms
proof (induction n arbitrary: x y)
  case 0
  then show ?case 
  unfolding comp.simps Id_def by auto
next
  case (Suc n)
  then obtain z where
    "(x,z) \<in> r"
    and "(z,y) \<in> comp r n"
    unfolding comp.simps composition_def
    by auto
  obtain f where
    "f 0 = z"
    and "f n = y"
    and "\<forall>i<n. (f i, f (Suc i)) \<in> r"
  using Suc.IH[OF \<open>(z,y) \<in> comp r n\<close>] by auto
  
  let ?g = "\<lambda>i. if i = 0 then x else f (i - 1)"
  have "?g 0 = x" "?g (Suc n) = y"
   using \<open>f n = y\<close> by simp+
  
  moreover have "\<forall>i<Suc n. (?g i, ?g (Suc i)) \<in> r"
  proof(auto)
    show "(x, f 0) \<in> r"
      using \<open>(x, z) \<in> r\<close> \<open>f 0 = z\<close> by auto
    next
    fix i
    assume "i > 0" "i < Suc n"
    then show "(f (i - Suc 0), f i) \<in> r"
    proof (cases i)
      case 0
      then show ?thesis 
        using \<open>i > 0\<close> by simp
    next
      case (Suc j)
      then show ?thesis
        using \<open>\<forall>i<n. (f i, f (Suc i)) \<in> r\<close> \<open>i < Suc n\<close>
        by simp
    qed
  qed
  ultimately show ?case by fast
qed

definition rel_refl_cl :: "'a relation \<Rightarrow> 'a relation" (\<open>(\<open>notation=\<open>postfix =\<close>\<close>_\<^sup>=)\<close> [1000] 999) where
  "r\<^sup>= = r \<union> Id"

lemma refl_cl_is_reflexive_closure:
shows "r\<^sup>= = closure r reflexive"
proof
  show "r\<^sup>= \<subseteq> closure r reflexive"
  proof
    fix p
    assume "p \<in> r\<^sup>="
    thus "p \<in> closure r reflexive"
      unfolding rel_refl_cl_def closure_def reflexive_def comp.simps Id_def by auto
  qed
  show "closure r reflexive \<subseteq> r\<^sup>="
  proof
    fix p
    assume "p \<in> closure r reflexive"
    thus "p \<in> r\<^sup>="                                                   
      unfolding rel_refl_cl_def closure_def reflexive_def comp.simps Id_def by auto
  qed
qed

definition rel_trans_cl :: "'a relation \<Rightarrow> 'a relation" (\<open>(\<open>notation=\<open>postfix +\<close>\<close>_\<^sup>+)\<close> [1000] 999) where
  "r\<^sup>+ = (\<Union> i \<in> {n. n > 0}. (r\<^sup>i))"



lemma r_is_in_trans_cl:
  shows "r \<subseteq> r\<^sup>+"
  using r1_is_r unfolding rel_trans_cl_def by blast

lemma rel_trans_cl_is_transitive:
  shows "transitive (r\<^sup>+)"
proof(unfold transitive_def, auto)
  fix x y z
  assume assms: "(x,y) \<in> r\<^sup>+" "(y,z) \<in> r\<^sup>+"
  then obtain m where "m > 0" and "(x,y) \<in> comp r m"
    unfolding rel_trans_cl_def by auto
  moreover obtain n where "n > 0" and "(y,z) \<in> comp r n"
    using assms(2) unfolding rel_trans_cl_def by auto
  ultimately have "(x,z) \<in> comp r m \<^bold>\<circ> comp r n"
    unfolding composition_def by auto
  hence "(x,z) \<in> comp r (m + n)"
    using comp_comp by auto
  moreover have "m + n > 0"
    using \<open>m > 0\<close> \<open>n > 0\<close>
    by simp
  ultimately show "(x,z) \<in> r\<^sup>+"
    unfolding rel_trans_cl_def by auto
qed


lemma trans_cl_is_transitive_closure:
  "r\<^sup>+ = closure r transitive"
proof
  show "r\<^sup>+ \<subseteq> closure r transitive"
  proof 
    fix p 
    assume "p \<in> r\<^sup>+" 
    thus "p \<in> closure r transitive" 
      using comp_subset_trans_closure unfolding rel_trans_cl_def closure_def transitive_def
        by auto
    qed
  show "closure r transitive \<subseteq> r\<^sup>+"
  proof
    fix p
    assume "p \<in> closure r transitive"
    have "r\<^sup>+ \<in> {s. r \<subseteq> s \<and> transitive s}"
      using r_is_in_trans_cl rel_trans_cl_is_transitive
      by auto
    have "p \<in> r\<^sup>+"
      using \<open>p \<in> closure r transitive\<close> \<open>r\<^sup>+ \<in> {s. r \<subseteq> s \<and> transitive s}\<close>
      unfolding closure_def by auto
    thus "p \<in> r\<^sup>+".
  qed
qed

lemma plus_imp_path:
  assumes "(x,y) \<in> r\<^sup>+"
  shows "\<exists>n>0. \<exists>f.
           f 0 = x \<and>
           f n = y \<and>
           (\<forall>i<n. (f i, f (Suc i)) \<in> r)"
proof-
  obtain n where
    "n > 0"
    and "(x,y) \<in> comp r n"
    using assms
    unfolding rel_trans_cl_def
    by auto
  moreover obtain f where
    "f 0 = x"
    and "f n = y"
    and "\<forall>i<n. (f i, f (Suc i)) \<in> r"
    using comp_imp_path[OF \<open>(x,y) \<in> comp r n\<close>]
    by auto
  ultimately show ?thesis by auto
qed

definition rel_rtrans_cl :: "'a relation \<Rightarrow> 'a relation" (\<open>(\<open>notation=\<open>postfix *\<close>\<close>_\<^sup>*)\<close> [1000] 999) where
   "r\<^sup>* = r\<^sup>+ \<union> r\<^sup>0"

lemma rel_rtrans_cl_reflexive:
  shows "reflexive (r\<^sup>*)"
 unfolding comp.simps reflexive_def rel_rtrans_cl_def Id_def by auto

lemma rel_rtrans_cl_transitive:
  shows "transitive (r\<^sup>*)"
proof(unfold transitive_def, auto)
  fix x y z
  assume "(x, y) \<in> r\<^sup>*" "(y, z) \<in> r\<^sup>*"
  hence xy_cases: "(x,y) \<in> r\<^sup>+ \<or> (x,y) \<in> Id" and yz_cases: "(y,z) \<in> r\<^sup>+ \<or> (y,z) \<in> Id"
   unfolding rel_rtrans_cl_def by auto
  
  then show "(x, z) \<in> r\<^sup>*"
    proof(elim disjE)
    assume "(x, y) \<in> r\<^sup>+" "(y, z) \<in> r\<^sup>+"
    thus "(x, z) \<in> r\<^sup>*" 
      using rel_trans_cl_is_transitive 
      unfolding rel_rtrans_cl_def transitive_def by fast
    next
    assume "(x, y) \<in> r\<^sup>+" "(y, z) \<in> Id"
    thus "(x, z) \<in> r\<^sup>*"
      using comp_zero_iff 
        unfolding rel_rtrans_cl_def Id_def by simp
    next
    assume "(x, y) \<in> Id" "(y, z) \<in> r\<^sup>+"
    thus "(x, z) \<in> r\<^sup>*"
      using comp_zero_iff 
        unfolding rel_rtrans_cl_def Id_def by simp
    next
    assume "(x, y) \<in> Id" "(y, z) \<in> Id"
    thus "(x, z) \<in> r\<^sup>*"
      using comp_zero_iff \<open>(y, z) \<in> r\<^sup>*\<close>
        unfolding Id_def by simp
    qed
qed
  
lemma r_in_rstar:
  shows "r \<subseteq> r\<^sup>*"
  using r_is_in_trans_cl unfolding rel_rtrans_cl_def by auto

lemma rplus_in_rstar:
  shows "r\<^sup>+ \<subseteq> r\<^sup>*"
  unfolding rel_rtrans_cl_def by auto

lemma r_comp_rstar_in_rplus:
  shows "r \<^bold>\<circ> (r\<^sup>*) \<subseteq> r\<^sup>+"
proof
  fix p 
  assume assm: "p \<in> r \<^bold>\<circ> (r\<^sup>*)"
  then obtain x y z where i: "p = (x, z)" "(x, y) \<in> r" "(y, z) \<in> r\<^sup>*"
    using assm unfolding composition_def by blast
  hence "(y, z) \<in> (r\<^sup>0) \<or> (y, z) \<in> (r\<^sup>+)"
    unfolding rel_rtrans_cl_def by auto
  thus "p \<in> r\<^sup>+"
  proof(elim disjE)
    assume "(y, z) \<in> (r\<^sup>0)"
    hence "y = z" 
      unfolding comp_zero_iff by simp
    thus"p \<in> r\<^sup>+"
      using i(1,2) r_is_in_trans_cl by auto
    next
    assume ii: "(y, z) \<in> r\<^sup>+"
    with i(2) have "(x, y) \<in> r\<^sup>+"
      using r_is_in_trans_cl by auto
    with ii show "p \<in> r\<^sup>+"
      using i(1) rel_trans_cl_is_transitive 
      unfolding transitive_def by fast
  qed
qed    

lemma r_comp_rstar_in_rstar:
  shows "r \<^bold>\<circ> (r\<^sup>*) \<subseteq> r\<^sup>*"
  using rplus_in_rstar r_comp_rstar_in_rplus by auto

lemma rstar_comp_r_in_rplus:
  shows "(r\<^sup>*) \<^bold>\<circ> r \<subseteq> r\<^sup>+"
proof
  fix p 
  assume assm: "p \<in> (r\<^sup>*) \<^bold>\<circ> r"
  then obtain x y z where i: "p = (x, z)" "(x, y) \<in> r\<^sup>*" "(y, z) \<in> r"
    using assm unfolding composition_def by blast
  hence "(x, y) \<in> (r\<^sup>0) \<or> (x, y) \<in> (r\<^sup>+)"
    unfolding rel_rtrans_cl_def by auto
  thus "p \<in> r\<^sup>+"
  proof(elim disjE)
    assume "(x, y) \<in> (r\<^sup>0)"
    hence "x = y" 
      unfolding comp_zero_iff by simp
    thus "p \<in> r\<^sup>+"
      using i(1,3) r_is_in_trans_cl by auto
    next
    assume ii: "(x, y) \<in> r\<^sup>+"
    with i(3) have "(y, z) \<in> r\<^sup>+"
      using r_is_in_trans_cl by auto
    with ii show "p \<in> r\<^sup>+"
      using i(1) rel_trans_cl_is_transitive 
      unfolding transitive_def by fast
  qed
qed

lemma rstar_comp_r_in_rstar:
  shows "(r\<^sup>*) \<^bold>\<circ> r \<subseteq> r\<^sup>*"
  using rplus_in_rstar rstar_comp_r_in_rplus by auto

lemma r_star_exists_n:
  assumes "(a, b) \<in> r\<^sup>*"
  shows "\<exists> n. (a, b) \<in> comp r n"
using assms unfolding rel_rtrans_cl_def rel_trans_cl_def by blast

definition rel_inv :: "'a relation \<Rightarrow> 'a relation" (\<open>(\<open>notation=\<open>postfix -\<close>\<close>_\<^sup>-)\<close> [1000] 999) where
  "r\<^sup>- = {(y, x). (x, y) \<in> r}"

definition rel_symm_cl :: "'a relation \<Rightarrow> 'a relation" (\<open>(\<open>notation=\<open>postfix \<s>\<close>\<close>_\<^sup>\<s>)\<close> [1000] 999) where
  "r\<^sup>\<s> = r \<union> r\<^sup>-"

lemma symm_cl_is_symmetric_closure:
  "r\<^sup>\<s> = closure r symmetric"
proof
  show "r\<^sup>\<s> \<subseteq> closure r symmetric"
  proof
    fix p
    assume "p \<in> r\<^sup>\<s>"
    thus "p \<in> closure r symmetric"
      unfolding rel_symm_cl_def closure_def symmetric_def comp.simps rel_inv_def by auto
  qed
  show "closure r symmetric \<subseteq> r\<^sup>\<s>"
  proof
    fix p
    assume "p \<in> closure r symmetric"
    thus "p \<in> r\<^sup>\<s>"
      unfolding rel_symm_cl_def closure_def symmetric_def comp.simps rel_inv_def by auto
  qed
qed

lemma symm_cl_is_symmetric:
  "symmetric (r\<^sup>\<s>)"
  using symm_cl_is_symmetric_closure[of r] symm_closure_is_symmetric[of r] by auto

lemma irreflexive_symm_cl_iff:
  "irreflexive (r\<^sup>\<s>) \<longleftrightarrow> irreflexive r"
  unfolding irreflexive_def rel_symm_cl_def rel_inv_def
  by auto

lemma antisymmetric_iff_no_loop_intersection:
  "antisymmetric r \<longleftrightarrow> r \<inter> r\<^sup>- \<subseteq> Id"
  unfolding antisymmetric_def rel_inv_def Id_def
  by auto

lemma asymmetric_iff:
  "(irreflexive r \<and> antisymmetric r) \<longleftrightarrow> r \<inter> r\<^sup>- = {}"
  unfolding irreflexive_def antisymmetric_def rel_inv_def Id_def
  by auto

lemma path_imp_comp:
  assumes "\<forall>i<n. (f i, f (Suc i)) \<in> r"
  shows "(f 0, f n) \<in> comp r n"
  using assms
proof(induction n arbitrary: f)
  case 0
  then show ?case unfolding comp.simps Id_def by auto
next
  case (Suc n)
  define f' where "f' i = f (Suc i)" for i
  have "\<forall>i<n. (f' i, f' (Suc i)) \<in> r"
    using Suc.prems unfolding f'_def by auto
  hence H: "(f 1, f (Suc n)) \<in> comp r n"
    using Suc.IH[of f'] unfolding f'_def by auto
  show "(f 0, f (Suc n)) \<in> comp r (Suc n)"
  proof(unfold comp_suc_iff)
    show "\<exists>z. (f 0, z) \<in> r \<and> (z, f (Suc n)) \<in> comp r n"
      using Suc.prems H by (intro exI[of _ "f 1"] conjI) auto
  qed
qed

lemma trans_cl_symmetric_pair:
  assumes "symmetric r" and "(x, y) \<in> r\<^sup>+"
  shows "(y, x) \<in> r\<^sup>+"
proof-
  obtain n f where
    "n > 0"
    and "f 0 = x"
    and "f n = y"
    and "\<forall>i<n. (f i, f (Suc i)) \<in> r"
    using plus_imp_path[of x y r] assms(2) by auto
  define g where "g i = f (n - i)" for i
  have "g 0 = y" using \<open>f n = y\<close> unfolding g_def by auto
  have "g n = x" using \<open>f 0 = x\<close> unfolding g_def by auto
  have steps: "\<forall>i<n. (g i, g (Suc i)) \<in> r"
  proof(rule allI, rule impI)
    fix i
    assume "i < n"
    have "(f (n - Suc i), f (n - i)) \<in> r"
    proof-
      have "n - Suc i < n" using \<open>i < n\<close> by auto
      hence "(f (n - Suc i), f (Suc (n - Suc i))) \<in> r"
        using \<open>\<forall>i<n. (f i, f (Suc i)) \<in> r\<close> by auto
      moreover have "Suc (n - Suc i) = n - i" using \<open>i < n\<close> by simp
      ultimately show ?thesis by auto
    qed
    hence "(f (n - i), f (n - Suc i)) \<in> r"
      using assms(1) unfolding symmetric_def by auto
    thus "(g i, g (Suc i)) \<in> r"
      unfolding g_def by auto
  qed
  have "(g 0, g n) \<in> comp r n"
    using steps by (rule path_imp_comp[of n g])
  hence "(y, x) \<in> comp r n"
    using \<open>g 0 = y\<close> \<open>g n = x\<close> by auto
  then show ?thesis
    using \<open>n > 0\<close> unfolding rel_trans_cl_def by auto
qed

lemma symmetric_imp_trans_cl_symmetric:
  assumes "symmetric r"
  shows "symmetric (r\<^sup>+)"
proof(unfold symmetric_def, intro allI impI)
  fix x y
  assume "(x, y) \<in> r\<^sup>+"
  show "(y, x) \<in> r\<^sup>+"
    by (rule trans_cl_symmetric_pair[OF assms \<open>(x, y) \<in> r\<^sup>+\<close>])
qed

lemma rstar_symmetric_pair:
  assumes "symmetric r" and "(x, y) \<in> r\<^sup>*"
  shows "(y, x) \<in> r\<^sup>*"
proof-
  have "(x, y) \<in> r\<^sup>+ \<or> (x, y) \<in> comp r 0"
    using assms(2) unfolding rel_rtrans_cl_def by auto
  thus ?thesis
  proof(elim disjE)
    assume "(x, y) \<in> r\<^sup>+"
    have "(y, x) \<in> r\<^sup>+"
      by (rule trans_cl_symmetric_pair[OF assms(1) \<open>(x, y) \<in> r\<^sup>+\<close>])
    thus ?thesis unfolding rel_rtrans_cl_def by auto
  next
    assume A: "(x, y) \<in> comp r 0"
    hence "x = y" unfolding comp.simps Id_def by auto
    hence "(y, x) \<in> comp r 0" unfolding comp.simps Id_def using \<open>x = y\<close> by auto
    thus ?thesis unfolding rel_rtrans_cl_def by auto
  qed
qed

lemma symmetric_rstar:
  assumes "symmetric r"
  shows "symmetric (r\<^sup>*)"
proof(unfold symmetric_def, intro allI impI)
  fix x y
  assume "(x, y) \<in> r\<^sup>*"
  show "(y, x) \<in> r\<^sup>*"
    by (rule rstar_symmetric_pair[OF assms \<open>(x, y) \<in> r\<^sup>*\<close>])
qed

definition rel_symm_trans_cl :: "'a relation \<Rightarrow> 'a relation" where
  "rel_symm_trans_cl r = (r\<^sup>\<s>)\<^sup>+"

definition rel_equiv_cl :: "'a relation \<Rightarrow> 'a relation" (\<open>(\<open>notation=\<open>postfix \<sim>\<close>\<close>_\<^sup>\<sim>)\<close> [1000] 999) where
  "r\<^sup>\<sim> = (r\<^sup>\<s>)\<^sup>*"

lemma rel_equiv_reflexive:
  shows "reflexive (r\<^sup>\<sim>)"
using rel_rtrans_cl_reflexive unfolding rel_equiv_cl_def by auto

lemma rel_equiv_symmetric:
  shows "symmetric (r\<^sup>\<sim>)"
  using symmetric_rstar[of \<open>r\<^sup>\<s>\<close>] symm_cl_is_symmetric
  unfolding rel_equiv_cl_def by auto

lemma rel_equiv_transitive:
  shows "transitive (r\<^sup>\<sim>)"
using rel_rtrans_cl_transitive unfolding rel_equiv_cl_def by auto

text\<open>Pair-level closure properties\<close>

lemma closure_reflexive_pair:
  "(a, a) \<in> closure r reflexive"
  using refl_closure_is_reflexive[of r] unfolding reflexive_def by auto

lemma closure_symmetric_pair:
  assumes "(a, b) \<in> closure r symmetric"
  shows "(b, a) \<in> closure r symmetric"
  using symm_closure_is_symmetric[of r] assms unfolding symmetric_def by auto

lemma closure_transitive_pair:
  assumes "(a, b) \<in> closure r transitive" and "(b, c) \<in> closure r transitive"
  shows "(a, c) \<in> closure r transitive"
  using trans_closure_is_transitive[of r] assms unfolding transitive_def by blast

lemma refl_cl_reflexive_pair:
  "(a, a) \<in> r\<^sup>="
  unfolding rel_refl_cl_def Id_def by auto

lemma trans_cl_transitive_pair:
  assumes "(a, b) \<in> r\<^sup>+" and "(b, c) \<in> r\<^sup>+"
  shows "(a, c) \<in> r\<^sup>+"
  using rel_trans_cl_is_transitive[of r] assms unfolding transitive_def by blast

lemma rstar_reflexive_pair:
  "(a, a) \<in> r\<^sup>*"
  using rel_rtrans_cl_reflexive[of r] unfolding reflexive_def by auto

lemma rstar_transitive_pair:
  assumes "(a, b) \<in> r\<^sup>*" and "(b, c) \<in> r\<^sup>*"
  shows "(a, c) \<in> r\<^sup>*"
  using rel_rtrans_cl_transitive[of r] assms unfolding transitive_def by blast

lemma symm_cl_symmetric_pair:
  assumes "(a, b) \<in> r\<^sup>\<s>"
  shows "(b, a) \<in> r\<^sup>\<s>"
  using symm_cl_is_symmetric[of r] assms unfolding symmetric_def by auto

lemma rel_symm_trans_cl_symmetric:
  "symmetric (rel_symm_trans_cl r)"
  using symmetric_imp_trans_cl_symmetric[of \<open>r\<^sup>\<s>\<close>] symm_cl_is_symmetric[of r]
  unfolding rel_symm_trans_cl_def by auto

lemma symm_trans_cl_symmetric_pair:
  assumes "(a, b) \<in> rel_symm_trans_cl r"
  shows "(b, a) \<in> rel_symm_trans_cl r"
  using trans_cl_symmetric_pair[of \<open>r\<^sup>\<s>\<close> a b] symm_cl_is_symmetric[of r] assms
  unfolding rel_symm_trans_cl_def by auto

lemma symm_trans_cl_transitive_pair:
  assumes "(a, b) \<in> rel_symm_trans_cl r" and "(b, c) \<in> rel_symm_trans_cl r"
  shows "(a, c) \<in> rel_symm_trans_cl r"
  using rel_trans_cl_is_transitive[of \<open>r\<^sup>\<s>\<close>] assms
  unfolding transitive_def rel_symm_trans_cl_def by blast

lemma equiv_cl_reflexive_pair:
  "(a, a) \<in> r\<^sup>\<sim>"
  using rel_equiv_reflexive[of r] unfolding reflexive_def by auto

lemma equiv_cl_symmetric_pair:
  assumes "(a, b) \<in> r\<^sup>\<sim>"
  shows "(b, a) \<in> r\<^sup>\<sim>"
  using rel_equiv_symmetric[of r] assms unfolding symmetric_def by auto

lemma equiv_cl_transitive_pair:
  assumes "(a, b) \<in> r\<^sup>\<sim>" and "(b, c) \<in> r\<^sup>\<sim>"
  shows "(a, c) \<in> r\<^sup>\<sim>"
  using rel_equiv_transitive[of r] assms unfolding transitive_def by blast


lemma comp_subset_mono:
  assumes "r \<subseteq> s"
  shows "comp r n \<subseteq> comp s n"
  using assms
proof(induction n)
  case 0
  then show ?case unfolding comp.simps by auto
next
  case (Suc n)
  show ?case
  proof
    fix p
    assume "p \<in> comp r (Suc n)"
    hence "p \<in> r \<^bold>\<circ> comp r n"
      unfolding comp.simps by auto
    then obtain a b c where
      "p = (a, c)" and "(a, b) \<in> r" and "(b, c) \<in> comp r n"
      unfolding composition_def by blast
    have "(a, b) \<in> s"
      using \<open>(a, b) \<in> r\<close> assms by auto
    have "(b, c) \<in> comp s n"
      using Suc.IH[OF assms] \<open>(b, c) \<in> comp r n\<close> by auto
    hence "p \<in> s \<^bold>\<circ> comp s n"
      unfolding composition_def using \<open>p = (a, c)\<close> \<open>(a, b) \<in> s\<close> by auto
    thus "p \<in> comp s (Suc n)"
      unfolding comp.simps by auto
  qed
qed

lemma rstar_mono:
  assumes "r \<subseteq> s"
  shows "r\<^sup>* \<subseteq> s\<^sup>*"
proof
  fix p
  assume "p \<in> r\<^sup>*"
  obtain x y where "p = (x, y)" by (cases p) blast
  hence "(x, y) \<in> r\<^sup>*" using \<open>p \<in> r\<^sup>*\<close> by auto
  then obtain n where "(x, y) \<in> comp r n"
    using r_star_exists_n[of x y r] by auto
  have "(x, y) \<in> comp s n"
    using \<open>(x, y) \<in> comp r n\<close> comp_subset_mono[OF assms] by auto
  have "(x, y) \<in> s\<^sup>*"
  proof(cases "n = 0")
    case True
    then show ?thesis
      using \<open>(x, y) \<in> comp s n\<close> unfolding comp.simps rel_rtrans_cl_def by auto
  next
    case False
    then have "n > 0" by simp
    hence "(x, y) \<in> s\<^sup>+"
      using \<open>(x, y) \<in> comp s n\<close> unfolding rel_trans_cl_def by auto
    thus ?thesis unfolding rel_rtrans_cl_def by auto
  qed
  thus "p \<in> s\<^sup>*" using \<open>p = (x, y)\<close> by auto
qed

lemma invstar_rstar_in_equiv:
  shows "(r\<^sup>-)\<^sup>* \<^bold>\<circ> r\<^sup>* \<subseteq> r\<^sup>\<sim>"
proof
  fix p
  assume "p \<in> (r\<^sup>-)\<^sup>* \<^bold>\<circ> r\<^sup>*"
  then obtain x y z where
    "p = (x, z)" and "(x, y) \<in> (r\<^sup>-)\<^sup>*" and "(y, z) \<in> r\<^sup>*"
    unfolding composition_def by blast
  have A: "r\<^sup>- \<subseteq> r\<^sup>\<s>"
    unfolding rel_symm_cl_def by auto
  have B: "r \<subseteq> r\<^sup>\<s>"
    unfolding rel_symm_cl_def by auto
  have "(x, y) \<in> (r\<^sup>\<s>)\<^sup>*"
    using rstar_mono[OF A] \<open>(x, y) \<in> (r\<^sup>-)\<^sup>*\<close> by auto
  have "(y, z) \<in> (r\<^sup>\<s>)\<^sup>*"
    using rstar_mono[OF B] \<open>(y, z) \<in> r\<^sup>*\<close> by auto
  have "(x, z) \<in> (r\<^sup>\<s>)\<^sup>*"
    using rel_rtrans_cl_transitive[of \<open>r\<^sup>\<s>\<close>] \<open>(x, y) \<in> (r\<^sup>\<s>)\<^sup>*\<close> \<open>(y, z) \<in> (r\<^sup>\<s>)\<^sup>*\<close>
    unfolding transitive_def by blast
  thus "p \<in> r\<^sup>\<sim>"
    unfolding rel_equiv_cl_def using \<open>p = (x, z)\<close> by auto
qed

lemma comp_inv:
  shows "(comp r n)\<^sup>- = comp (r\<^sup>-) n"
proof(induction n)
  case 0
  show ?case unfolding comp.simps rel_inv_def Id_def by auto
next
  case (Suc n)
  have "(comp r (Suc n))\<^sup>- = (comp r n)\<^sup>- \<^bold>\<circ> r\<^sup>-"
    unfolding comp.simps rel_inv_def composition_def by auto
  also have "... = comp (r\<^sup>-) n \<^bold>\<circ> comp (r\<^sup>-) (Suc 0)"
    by (simp only: Suc.IH r1_is_r)
  also have "... = comp (r\<^sup>-) (Suc n)"
    using comp_comp[of "r\<^sup>-" n "Suc 0"] by simp
  finally show ?case .
qed

lemma comp_inv_pair:
  shows "(x, y) \<in> comp (r\<^sup>-) n \<longleftrightarrow> (y, x) \<in> comp r n"
  using comp_inv[of r n] unfolding rel_inv_def by blast

lemma rstar_iff_exists_n:
  shows "(a, b) \<in> r\<^sup>* \<longleftrightarrow> (\<exists>n. (a, b) \<in> comp r n)"
proof
  assume "(a, b) \<in> r\<^sup>*"
  thus "\<exists>n. (a, b) \<in> comp r n" by (rule r_star_exists_n)
next
  assume "\<exists>n. (a, b) \<in> comp r n"
  then obtain n where "(a, b) \<in> comp r n" by blast
  thus "(a, b) \<in> r\<^sup>*"
    unfolding rel_rtrans_cl_def rel_trans_cl_def by (cases n) auto
qed

lemma rel_irtc_is_rtc_irel:
  shows "(r\<^sup>*)\<^sup>- = (r\<^sup>-)\<^sup>*"
proof (rule set_eqI)
  fix p :: "'a \<times> 'a"
  obtain x y where p: "p = (x, y)" by (cases p) blast
  have "p \<in> (r\<^sup>*)\<^sup>- \<longleftrightarrow> (y, x) \<in> r\<^sup>*"
    unfolding p rel_inv_def by blast
  also have "... \<longleftrightarrow> (\<exists>n. (x, y) \<in> comp (r\<^sup>-) n)"
    unfolding rstar_iff_exists_n comp_inv_pair ..
  also have "... \<longleftrightarrow> p \<in> (r\<^sup>-)\<^sup>*"
    unfolding p rstar_iff_exists_n ..
  finally show "p \<in> (r\<^sup>*)\<^sup>- \<longleftrightarrow> p \<in> (r\<^sup>-)\<^sup>*" .
qed
   







end