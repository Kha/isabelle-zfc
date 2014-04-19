theory ZFC
imports HOL
begin

typedecl set

axiomatization
  member :: "set \<Rightarrow> set \<Rightarrow> bool"

notation
  member  ("op :") and
  member  ("(_/ : _)" [51, 51] 50)

abbreviation not_member where
  "not_member x A \<equiv> ~ (x : A)" -- "non-membership"

notation
  not_member  ("op ~:") and
  not_member  ("(_/ ~: _)" [51, 51] 50)

notation (xsymbols)
  member      ("op \<in>") and
  member      ("(_/ \<in> _)" [51, 51] 50) and
  not_member  ("op \<notin>") and
  not_member  ("(_/ \<notin> _)" [51, 51] 50)

section "Zermelo-Fraenkel Axiom System"

axiomatization where
  extensionality: "\<forall>z. (z \<in> x \<longleftrightarrow> z \<in> y) \<Longrightarrow> x = y" and
  foundation: "\<exists>y. y \<in> x \<Longrightarrow> \<exists>y. y \<in> x \<and> (\<forall>z. \<not>(z \<in> x \<and> z \<in> y))" and
  subset_set: "\<exists>y. \<forall>z. z \<in> y \<longleftrightarrow> z \<in> x \<and> P z" and
  empty_set: "\<exists>y. \<forall>x. x \<notin> y" and
  pair_set: "\<exists>y. \<forall>x. x \<in> y \<longleftrightarrow> x = z\<^sub>1 \<or> x = z\<^sub>2" and
  power_set: "\<exists>y. \<forall>z. z \<in> y \<longleftrightarrow> (\<forall>u. u \<in> z \<longrightarrow> u \<in> x)" and
  sum_set: "\<exists>y. \<forall>z. z \<in> y \<longleftrightarrow> (\<exists>u. z \<in> u \<and> u \<in> x)"

definition empty :: set ("{}") where
  "empty \<equiv> THE y. \<forall>x. x \<notin> y"

axiomatization where
  infinity: "\<exists>w. {} \<in> w \<and> (\<forall>x. x \<in> w \<longrightarrow> (\<exists>z. z \<in> w \<and> (\<forall>u. u \<in> z \<longleftrightarrow> u \<in> x \<or> u = x)))" and
  replacement: "P x y \<and> P x z \<longrightarrow> y = z \<Longrightarrow> \<exists>u. (\<forall>w\<^sub>1. w\<^sub>1 \<in> u \<longleftrightarrow> (\<exists>w\<^sub>2. w\<^sub>2 \<in> a \<and> P w\<^sub>2 w\<^sub>1))"
(* choice: *)


lemma empty[simp]: "x \<notin> empty"
proof-
  have "\<exists>!y. \<forall>x. x \<notin>y "
  proof (rule ex_ex1I)
    fix y y'
    assume "\<forall>x. x \<notin> y" "\<forall>x. x \<notin> y'"
    thus "y = y'" by -(rule extensionality, simp)
  qed (rule empty_set)
  hence "\<forall>x. x \<notin> {}"
    unfolding empty_def
    by (rule theI')
  thus ?thesis ..
qed

text {* Let's try to generalize that for the other introduction axioms. *}

lemma exAxiomD1:
  assumes "\<exists>y. \<forall>x. x \<in> y \<longleftrightarrow> P x"
  shows "\<exists>!y. \<forall>x. x \<in> y \<longleftrightarrow> P x"
using assms
by (auto intro:extensionality)

lemma exAxiomD2:
  assumes "\<exists>y. \<forall>x. x \<in> y \<longleftrightarrow> P x"
  shows "x \<in> (THE y. \<forall>x. x \<in> y \<longleftrightarrow> P x) \<longleftrightarrow> P x"
apply (rule spec[of _ x])
by (rule theI'[OF assms[THEN exAxiomD1]])

lemma exAxiomD3:
  assumes "\<exists>y. \<forall>x. x \<in> y \<longleftrightarrow> P x"  "x \<in> (THE y. \<forall>x. x \<in> y \<longleftrightarrow> P x)"
  shows "P x"
using assms exAxiomD2
by auto

lemma empty': "x \<notin> empty"
apply (rule exAxiomD2[of "\<lambda>_. False", simplified, folded empty_def])
by (rule empty_set)


definition pair :: "set \<Rightarrow> set \<Rightarrow> set" ("{_, _}") where
  "pair z\<^sub>1 z\<^sub>2 \<equiv> THE y. \<forall>x. x \<in> y \<longleftrightarrow> x = z\<^sub>1 \<or> x = z\<^sub>2"

definition singleton :: "set \<Rightarrow> set" ("{_}") where
  "singleton x \<equiv> {x, x}"

definition sum :: "set \<Rightarrow> set" where
  "sum x \<equiv> THE y. \<forall>z. z \<in> y \<longleftrightarrow> (\<exists>u. z \<in> u \<and> u \<in> x)"

definition subset :: "(set \<Rightarrow> bool) \<Rightarrow> set \<Rightarrow> set" where
  "subset P x \<equiv> THE y. \<forall>z. z \<in> y \<longleftrightarrow> z \<in> x \<and> P z"

syntax
  "subset" :: "pttrn => set \<Rightarrow> bool => set" ("(1{_ \<in> _./ _})")
translations
  "{z \<in> x. P}" == "subset (%z. P) x"

lemma pair[simp]: "x \<in> {z\<^sub>1, z\<^sub>2} \<longleftrightarrow> x = z\<^sub>1 \<or> x = z\<^sub>2"
by (rule exAxiomD2[of "\<lambda>x. x = z\<^sub>1 \<or> x = z\<^sub>2", simplified, folded pair_def]) (rule pair_set)

lemma singleton[simp]: "x \<in> {y} \<longleftrightarrow> x = y"
by -(unfold singleton_def, simp)

lemma sum[simp]: "z \<in> sum x \<longleftrightarrow> (\<exists>u. z \<in> u \<and> u \<in> x)"
by (rule exAxiomD2[of "\<lambda>z. \<exists>u. z \<in> u \<and> u \<in> x", simplified, folded sum_def]) (rule sum_set)

lemma subset[simp]: "z \<in> {z \<in> x. P z} \<longleftrightarrow> z \<in> x \<and> P z"
by (rule exAxiomD2[of "\<lambda>z. z \<in> x \<and> P z", simplified, folded subset_def]) (rule subset_set)

(*
section "Class Terms"

type_synonym class_term = "set \<Rightarrow> bool"

syntax
  "_Coll" :: "pttrn => bool => class_term" ("(1{_./ _})")
translations
  "{x. P}" == "(%x. P)"

section "Some Abbreviations For Sets"

*)

section "Lemmas on Unions and Intersections"

definition union :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "\<union>" 65) where
  "union x y \<equiv> sum (pair x y)"

lemma union[simp]: "z \<in> a \<union> b \<longleftrightarrow> z \<in> a \<or> z \<in> b"
by (auto simp:union_def)

lemma union_script: "\<exists>y. \<forall>z. z \<in> y \<longleftrightarrow> z \<in> a \<or> z \<in> b"
by (rule exI[of _ "a \<union> b"]) simp

definition intersect :: "set \<Rightarrow> set \<Rightarrow> set" (infixl "\<inter>" 70) where
  "a \<inter> b \<equiv> {x \<in> a. x \<in> b}"

lemma intersect[simp]: "z \<in> a \<inter> b \<longleftrightarrow> z \<in> a \<and> z \<in> b"
by (simp add:intersect_def)

lemma intersect_script: "\<exists>y. \<forall>z. z \<in> y \<longleftrightarrow> z \<in> a \<and> z \<in> b"
(* by (rule exI[of _ "a \<inter> b"]) simp *)
by (rule subset_set)

section {* Ordered Pairs *}

definition ordered_pair :: "set \<Rightarrow> set \<Rightarrow> set" ("\<langle>_,_\<rangle>") where
  "\<langle>a,b\<rangle> \<equiv> {{a}, {a,b}}"

lemma intersect_singleton[simp]: "x \<inter> {y} = (if y \<in> x then {y} else {})"
by (auto intro:extensionality)

lemma empty_singleton_neq[simp]: "{x} \<noteq> {}"
proof
  assume assm: "{x} = {}"
  have "x \<notin> {}" by simp
  with assm have "x \<notin> {x}" by simp
  thus False by simp
qed

lemma singleton_eqD[dest!]: "{x} = {y} \<Longrightarrow> x = y"
by (drule arg_cong[of _ _"\<lambda>z. y \<in> z"]) simp

lemma singleton_pair_eqD[dest!]:
  assumes "{x} = {y, z}"
  shows "x = y \<and> y = z"
proof-
  from assms have "y \<in> {x} \<longleftrightarrow> y \<in> {y, z}" by simp
  hence "x = y" by simp
  from assms have "z \<in> {x} \<longleftrightarrow> z \<in> {y, z}" by simp
  hence "x = z" by simp
  with `x = y` show ?thesis by simp
qed

lemma singleton_pair_eqD'[dest!]:
  assumes "{y, z} = {x}"
  shows "x = y \<and> y = z"
using assms[symmetric] by (rule singleton_pair_eqD)

lemma pair_singleton[simp]: "{x, x} = {x}"
unfolding singleton_def ..

lemma pair_eq_fstD[dest!]:
  assumes "{x,y} = {x,z}"
  shows "y = z"
using assms
proof (cases "x = y")
  case False
  from assms have "y \<in> {x,y} \<longleftrightarrow> y \<in> {x,z}" by simp
  with False show ?thesis by simp
qed auto

lemma ordered_pair_eq[simp]: "\<langle>x\<^sub>1,x\<^sub>2\<rangle> = \<langle>y\<^sub>1,y\<^sub>2\<rangle> \<longleftrightarrow> x\<^sub>1 = y\<^sub>1 \<and> x\<^sub>2 = y\<^sub>2"
proof
  assume assm: "\<langle>x\<^sub>1,x\<^sub>2\<rangle> = \<langle>y\<^sub>1,y\<^sub>2\<rangle>"
  hence "{x\<^sub>1} \<in> \<langle>x\<^sub>1,x\<^sub>2\<rangle> \<longleftrightarrow> {x\<^sub>1} \<in> \<langle>y\<^sub>1,y\<^sub>2\<rangle>" by simp
  hence[simp]: "x\<^sub>1 = y\<^sub>1" by (auto simp:ordered_pair_def)
  show "x\<^sub>1 = y\<^sub>1 \<and> x\<^sub>2 = y\<^sub>2" using assm
  proof (cases "x\<^sub>2 = x\<^sub>1")
    case False
    from assm have "{x\<^sub>1,x\<^sub>2} \<in> \<langle>x\<^sub>1,x\<^sub>2\<rangle> \<longleftrightarrow> {x\<^sub>1,x\<^sub>2} \<in> \<langle>y\<^sub>1,y\<^sub>2\<rangle>" by simp
    with False show ?thesis by (auto simp:ordered_pair_def)
  qed (auto simp:ordered_pair_def)
qed simp

end
