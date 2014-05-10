theory ModalLogic
imports Main
begin

section {* Modal Logic *}

subsection {* Definition *}

datatype 'a PModFml
 = V 'a
 | Not "'a PModFml" ("\<not>\<^sub>M_" [140] 140)
 | And "'a PModFml" "'a PModFml" (infixr "\<and>\<^sub>M" 125)
 | Box "'a PModFml" ("\<box>_" [140] 140)

definition Or :: "'a PModFml \<Rightarrow> 'a PModFml \<Rightarrow> 'a PModFml" (infixr "\<or>\<^sub>M" 130) where
  "x \<or>\<^sub>M y \<equiv> \<not>\<^sub>M(\<not>\<^sub>Mx \<and>\<^sub>M \<not>\<^sub>My)"

definition Implies :: "'a PModFml \<Rightarrow> 'a PModFml \<Rightarrow> 'a PModFml" (infixr "\<longrightarrow>\<^sub>M" 125) where
  "x \<longrightarrow>\<^sub>M y \<equiv> \<not>\<^sub>M x \<or>\<^sub>M y"

definition Iff :: "'a PModFml \<Rightarrow> 'a PModFml \<Rightarrow> 'a PModFml" (infixr "\<longleftrightarrow>\<^sub>M" 110) where
  "x \<longleftrightarrow>\<^sub>M y \<equiv> (x \<longrightarrow>\<^sub>M y) \<and>\<^sub>M (y \<longrightarrow>\<^sub>M x)"

definition Diamond :: "'a PModFml \<Rightarrow> 'a PModFml" ("\<diamond>_" [140] 140) where
  "\<diamond>x \<equiv> \<not>\<^sub>M \<box> \<not>\<^sub>M x"

definition Mod_True :: "'a PModFml" ("True\<^sub>M") where
  "True\<^sub>M \<equiv> V undefined \<or>\<^sub>M \<not>\<^sub>M V undefined"

typedef 'g KripkeFrame = "{(G :: 'g set, R :: 'g rel). Field R \<subseteq> G}" by auto

abbreviation "G Fr \<equiv> fst (Rep_KripkeFrame Fr)"
abbreviation "R Fr \<equiv> snd (Rep_KripkeFrame Fr)"

lemma Frame_wf: "Field (R Fr) \<subseteq> G Fr"
using Rep_KripkeFrame[of Fr] by auto

lemma[simp]:
  assumes "(g,h) \<in> R Fr"
  shows "g \<in> G Fr" "h \<in> G Fr"
proof-
  from assms have "g \<in> Domain (R Fr)" by auto
  also from Frame_wf[of Fr] have "Domain (R Fr) \<subseteq> G Fr" by (simp add:Field_def)
  finally show "g \<in> G Fr" .
  from assms have "h \<in> Range (R Fr)" by auto
  also from Frame_wf[of Fr] have "Range (R Fr) \<subseteq> G Fr" by (simp add:Field_def)
  finally show "h \<in> G Fr" .
qed

type_synonym ('g, 'a) KripkeStruct = "'g KripkeFrame \<times> (['g, 'a] \<Rightarrow> bool)"

abbreviation "Frame \<K> \<equiv> fst \<K>"
abbreviation "v \<K> \<equiv> snd \<K>"
abbreviation "G' \<K> \<equiv> G (Frame \<K>)"
abbreviation "R' \<K> \<equiv> R (Frame \<K>)"

fun eval :: "[('g, 'a) KripkeStruct, 'g, 'a PModFml] \<Rightarrow> bool" ("\<langle>_,_\<rangle> \<Turnstile> _" [0,0,51] 50) where
  "\<langle>\<K>,g\<rangle> \<Turnstile> (V var) = (v \<K>) g var"
| "\<langle>\<K>,g\<rangle> \<Turnstile> \<not>\<^sub>Mf = (\<not> \<langle>\<K>,g\<rangle> \<Turnstile> f)"
| "\<langle>\<K>,g\<rangle> \<Turnstile> f1 \<and>\<^sub>M f2 = (\<langle>\<K>,g\<rangle> \<Turnstile> f1 \<and> \<langle>\<K>,g\<rangle> \<Turnstile> f2)"
| "\<langle>\<K>,g\<rangle> \<Turnstile> \<box>f = (\<forall>h. (g,h) \<in> R' \<K> \<longrightarrow> \<langle>\<K>,h\<rangle> \<Turnstile> f)"

lemma eval_or[simp]: "\<langle>\<K>,g\<rangle> \<Turnstile> f1 \<or>\<^sub>M f2 \<longleftrightarrow> \<langle>\<K>,g\<rangle> \<Turnstile> f1 \<or> \<langle>\<K>,g\<rangle> \<Turnstile> f2" by (simp add:Or_def)
lemma eval_implies[simp]: "\<langle>\<K>,g\<rangle> \<Turnstile> f1 \<longrightarrow>\<^sub>M f2 \<longleftrightarrow> \<langle>\<K>,g\<rangle> \<Turnstile> f1 \<longrightarrow> \<langle>\<K>,g\<rangle> \<Turnstile> f2" by (simp add:Implies_def)
lemma eval_iff[simp]: "\<langle>\<K>,g\<rangle> \<Turnstile> f1 \<longleftrightarrow>\<^sub>M f2 \<longleftrightarrow> (\<langle>\<K>,g\<rangle> \<Turnstile> f1) = (\<langle>\<K>,g\<rangle> \<Turnstile> f2)" by (auto simp add:Iff_def)
lemma eval_diamond[simp]: "\<langle>\<K>,g\<rangle> \<Turnstile> \<diamond>f \<longleftrightarrow> (\<exists>h. (g,h) \<in> R' \<K> \<and> \<langle>\<K>,h\<rangle> \<Turnstile> f)" by (simp add:Diamond_def)
lemma eval_true[simp]: "\<langle>\<K>,g\<rangle> \<Turnstile> True\<^sub>M" by (simp add:Mod_True_def)

lemmas eval_impliesI[intro] = eval_implies[THEN iffD2, rule_format]
lemmas eval_boxI[intro] = eval.simps(4)[THEN iffD2, rule_format]
lemmas eval_boxD[dest] = eval.simps(4)[THEN iffD1, rule_format]

abbreviation global_eval :: "[('g, 'a) KripkeStruct, 'a PModFml] \<Rightarrow> bool" ("_ \<Turnstile> _" [51,51] 50) where
  "\<K> \<Turnstile> F \<equiv> (\<forall>g \<in> G' \<K>. \<langle>\<K>,g\<rangle> \<Turnstile> F)"

subsection {* Tautologies *}

abbreviation "tautology F \<equiv> \<forall>(\<K> :: (nat,_) KripkeStruct). \<K> \<Turnstile> F"

lemma taut1: "tautology (\<box>F \<longleftrightarrow>\<^sub>M \<not>\<^sub>M\<diamond>\<not>\<^sub>MF)" by auto
lemma taut2: "tautology (\<box>(P \<longrightarrow>\<^sub>M Q) \<longrightarrow>\<^sub>M (\<box>P \<longrightarrow>\<^sub>M \<box>Q))" by simp
lemma taut3: "tautology (\<box>(P \<and>\<^sub>M Q) \<longleftrightarrow>\<^sub>M (\<box>P \<and>\<^sub>M \<box>Q))" by auto
lemma taut4: "tautology (\<diamond>(P \<or>\<^sub>M Q) \<longleftrightarrow>\<^sub>M (\<diamond>P \<or>\<^sub>M \<diamond>Q))" by auto
lemma taut5: "tautology ((\<box>P \<or>\<^sub>M \<box>Q) \<longrightarrow>\<^sub>M \<box>(P \<or>\<^sub>M Q))" by simp
lemma taut6: "tautology (\<diamond>(P \<and>\<^sub>M Q) \<longrightarrow>\<^sub>M (\<diamond>P \<and>\<^sub>M \<diamond>Q))" by auto

subsection {* Classes of Kripke Frames *}

type_synonym 'g KripkeClass = "'g KripkeFrame set"
abbreviation K :: "'g KripkeClass" where "K \<equiv> UNIV"
abbreviation "T \<equiv> {Fr \<in> K. refl_on (G Fr) (R Fr)}"
abbreviation "S4 \<equiv> {Fr \<in> T. trans (R Fr)}"
abbreviation "S5 \<equiv> {Fr \<in> S4. sym (R Fr)}"
abbreviation "K4 \<equiv> {Fr \<in> K. trans (R Fr)}"
abbreviation "B \<equiv> {Fr \<in> K4. sym (R Fr)}"
abbreviation "D \<equiv> {Fr \<in> K. Domain (R Fr) = G Fr}"

lemma T[simp]: "Fr \<in> T \<longleftrightarrow> (\<forall>g \<in> G Fr. (g,g) \<in> R Fr)" using Frame_wf[of Fr] by (auto simp:refl_on_def)

subsection {* Relative Tautologies *}

definition "CTaut C F \<equiv> \<forall>Fr \<in> C. \<forall>v. \<forall>g \<in> G Fr. \<langle>(Fr,v),g\<rangle> \<Turnstile> F"

lemma pred_def_rewrite: "P \<equiv> Q \<Longrightarrow> Q \<Longrightarrow> P" by simp
lemmas CTautI = CTaut_def[THEN pred_def_rewrite, rule_format]


lemma ttaut1: "CTaut (T :: 'g KripkeClass) (\<box>p \<longrightarrow>\<^sub>M p)"
proof (rule CTautI)
  fix Fr :: "'g KripkeFrame"
  fix v :: "'g \<Rightarrow> 'a \<Rightarrow> bool"
  fix g
  let ?\<K> = "(Fr,v)"
  assume "Fr \<in> T" "g \<in> G Fr"
  from this(1) have "refl_on (G Fr) (R Fr)" by simp
  hence "(g,g) \<in> R Fr" using `g \<in> G Fr` by (rule refl_onD)
  hence "(g,g) \<in> R' ?\<K>" by simp
  show "\<langle>?\<K>,g\<rangle> \<Turnstile> (\<box>p \<longrightarrow>\<^sub>M p)"
  proof (rule eval_impliesI)
    assume "\<langle>?\<K>,g\<rangle> \<Turnstile> (\<box>p)"
    thus "\<langle>?\<K>,g\<rangle> \<Turnstile> p" using `(g,g) \<in> R' ?\<K>` by (rule eval_boxD)
  qed
qed
(* by (auto simp:CTaut_def intro:refl_onD) *)

lemma ttaut2: "CTaut T (p \<longrightarrow>\<^sub>M \<diamond>p)"
by (auto simp:CTaut_def intro:refl_onD)

lemma ttaut3: "CTaut T (\<box>\<box>p \<longrightarrow>\<^sub>M \<box>p)"
by (rule ttaut1)

lemma ttaut4: "CTaut T (\<box>\<diamond>p \<longrightarrow>\<^sub>M \<diamond>p)"
by (rule ttaut1)

lemma ttaut5: "CTaut T (\<box>p \<longrightarrow>\<^sub>M \<diamond>\<box>p)"
by (rule ttaut2)

lemma ttaut6: "CTaut T (\<diamond>p \<longrightarrow>\<^sub>M \<diamond>\<diamond>p)"
by (rule ttaut2)

subsection {* Modal Logical Consequence *}

definition conseq :: "['a PModFml, 'a PModFml] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>L _" [31,31] 30) where
  "M \<Turnstile>\<^sub>L F \<equiv> \<forall>\<K> :: (nat,_) KripkeStruct. \<forall>g \<in> G' \<K>. \<langle>\<K>,g\<rangle> \<Turnstile> M \<longrightarrow> \<langle>\<K>,g\<rangle> \<Turnstile> F"

definition global_conseq :: "['a PModFml, 'a PModFml] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>G _" [31,31] 30) where
  "M \<Turnstile>\<^sub>G F \<equiv> \<forall>\<K> :: (nat,_) KripkeStruct. \<K> \<Turnstile> M \<longrightarrow> \<K> \<Turnstile> F"

definition rel_conseq :: "['a PModFml, 'g KripkeClass, 'a PModFml] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>L\<^sup>_ _" [31,0,31] 30) where
  "M \<Turnstile>\<^sub>L\<^sup>C F \<equiv> \<forall>\<K>. Frame \<K> \<in> C \<longrightarrow> (\<forall>g \<in> G' \<K>. \<langle>\<K>,g\<rangle> \<Turnstile> M \<longrightarrow> \<langle>\<K>,g\<rangle> \<Turnstile> F)"

definition global_rel_conseq :: "['a PModFml, 'g KripkeClass, 'a PModFml] \<Rightarrow> bool" ("_ \<Turnstile>\<^sub>G\<^sup>_ _" [31,0,31] 30) where
  "M \<Turnstile>\<^sub>G\<^sup>C F \<equiv> \<forall>\<K>. Frame \<K> \<in> C \<longrightarrow> \<K> \<Turnstile> M \<longrightarrow> \<K> \<Turnstile> F"

subsection {* Model Deduction Theorem *}

theorem modal_deduction: "F\<^sub>1 \<Turnstile>\<^sub>L F\<^sub>2 \<longleftrightarrow> True\<^sub>M \<Turnstile>\<^sub>L (F\<^sub>1 \<longrightarrow>\<^sub>M F\<^sub>2)" by (simp add:conseq_def)

end
