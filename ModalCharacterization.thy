theory ModalCharacterization
imports ModalLogic
begin

section {* Correspondence Theory *}

subsection {* What Is It About? *}

abbreviation "char \<G> F \<equiv> \<forall>Fr. Fr \<in> \<G> \<longleftrightarrow> (\<forall>v. (Fr,v) \<Turnstile> F)"

lemma "char (T :: 'g KripkeClass) (\<box>V p \<longrightarrow>\<^sub>M V p)"
proof (rule, rule)
  fix Fr :: "'g KripkeFrame"
  show "Fr \<in> T \<Longrightarrow> \<forall>v. (Fr, v) \<Turnstile> \<box>V p \<longrightarrow>\<^sub>M V p" by (auto intro:refl_onD)
next
  fix Fr :: "'g KripkeFrame"
  assume asm: "\<forall>v. (Fr, v) \<Turnstile> \<box>V p \<longrightarrow>\<^sub>M V p"
  show "Fr \<in> T"
  proof (rule ccontr)
    assume "Fr \<notin> T"
    then obtain "g\<^sub>0" where g0: "g\<^sub>0 \<in> G Fr" "(g\<^sub>0,g\<^sub>0) \<notin> R Fr" by (auto simp:refl_on_def)
    let ?v0 = "\<lambda>g p. (g\<^sub>0,g) \<in> R Fr"
    have "\<not> \<langle>(Fr,?v0),g\<^sub>0\<rangle> \<Turnstile> \<box>V p \<longrightarrow>\<^sub>M V p" using g0(2) by simp
    with asm[THEN spec[where x="?v0"], THEN bspec[where x="g\<^sub>0"]] g0(1) show False by simp
  qed
qed

lemma "char (K4 :: 'g KripkeClass) (\<box>V p \<longrightarrow>\<^sub>M \<box>\<box>V p)"
proof (rule, rule)
  fix Fr :: "'g KripkeFrame"
  show "Fr \<in> K4 \<Longrightarrow> \<forall>v. (Fr, v) \<Turnstile> \<box>V p \<longrightarrow>\<^sub>M \<box>\<box>V p" by (auto elim:transE)
next
  fix Fr :: "'g KripkeFrame"
  assume asm: "\<forall>v. (Fr, v) \<Turnstile> \<box>V p \<longrightarrow>\<^sub>M \<box>\<box>V p"
  show "Fr \<in> K4"
  proof (rule ccontr)
    assume "Fr \<notin> K4"
    then obtain x y z where xyz: "x \<in> G Fr" "y \<in> G Fr" "z \<in> G Fr" "(x,y) \<in> R Fr" "(y,z) \<in> R Fr" "(x,z) \<notin> R Fr" by (auto simp:trans_def)
    let ?v = "\<lambda>g p. g \<noteq> z"
    have "\<not> \<langle>(Fr,?v),x\<rangle> \<Turnstile> \<box>V p \<longrightarrow>\<^sub>M \<box>\<box>V p" using xyz by auto
    with asm[THEN spec[where x="?v"], THEN bspec[where x=x]] show False by simp
  qed
qed

subsection {* A More General Characterization *}

no_notation power (infixr "^" 80)
primrec power :: "'a rel \<Rightarrow> nat \<Rightarrow> 'a rel" (infixr "^" 80) where
    power_0: "a ^ 0 = Id"
  | power_Suc: "a ^ Suc n = a ^ n O a"

notation (latex output)
  power ("(_\<^bsup>_\<^esup>)" [1000] 1000)

primrec box_n :: "nat \<Rightarrow> 'a PModFml \<Rightarrow> 'a PModFml" ("\<box>\<^sup>__" [0,140] 140) where
  "\<box>\<^sup>0 F = F"
| "box_n (Suc n) F = \<box>\<^sup>n\<box> F"

primrec diamond_n :: "nat \<Rightarrow> 'a PModFml \<Rightarrow> 'a PModFml" ("\<diamond>\<^sup>__" [0,140] 140) where
  "\<diamond>\<^sup>0 F = F"
| "diamond_n (Suc n) F = \<diamond>\<^sup>n\<diamond> F"

lemma box_n[simp]:
  assumes "g \<in> G' \<K>"
  shows "\<langle>\<K>,g\<rangle> \<Turnstile> \<box>\<^sup>n F \<longleftrightarrow> (\<forall>h \<in> G' \<K>. (g,h) \<in> (R' \<K>)^n \<longrightarrow> \<langle>\<K>,h\<rangle> \<Turnstile> F)"
proof (induction n arbitrary: F)
  case (Suc n)
  show ?case
  proof (rule, rule, rule)
    fix h
    assume asm: "\<langle>\<K>,g\<rangle> \<Turnstile> box_n (Suc n) F" "h \<in> G' \<K>" "(g, h) \<in> R' \<K> ^ Suc n"
    with Suc.IH[THEN iffD1, OF asm(1)[simplified]] show "\<langle>\<K>,h\<rangle> \<Turnstile> F" by auto
  next
    assume "\<forall>h\<in>G' \<K>. (g, h) \<in> R' \<K> ^ Suc n \<longrightarrow> \<langle>\<K>,h\<rangle> \<Turnstile> F"
    hence "\<langle>\<K>,g\<rangle> \<Turnstile> \<box>\<^sup>n\<box>F" by - (rule Suc.IH[THEN iffD2], auto)
    thus "\<langle>\<K>,g\<rangle> \<Turnstile> box_n (Suc n) F" by simp
  qed
qed (simp add:assms)

lemmas box_nI[intro] = box_n[THEN iffD2, rule_format]

lemma diamond_n[simp]:
  assumes "g \<in> G' \<K>"
  shows "\<langle>\<K>,g\<rangle> \<Turnstile> \<diamond>\<^sup>n F \<longleftrightarrow> (\<exists>h \<in> G' \<K>. (g,h) \<in> (R' \<K>)^n \<and> \<langle>\<K>,h\<rangle> \<Turnstile> F)"
proof (induction n arbitrary: F)
  case (Suc n)
  show ?case
  proof
    fix h
    assume asm: "\<langle>\<K>,g\<rangle> \<Turnstile> diamond_n (Suc n) F"
    with Suc.IH[THEN iffD1, OF asm(1)[simplified]] show "\<exists>h\<in>G' \<K>. (g, h) \<in> R' \<K> ^ Suc n \<and> \<langle>\<K>,h\<rangle> \<Turnstile> F" by auto
  next
    assume "\<exists>h\<in>G' \<K>. (g, h) \<in> R' \<K> ^ Suc n \<and> \<langle>\<K>,h\<rangle> \<Turnstile> F"
    hence "\<langle>\<K>,g\<rangle> \<Turnstile> \<diamond>\<^sup>n\<diamond>F" by - (rule Suc.IH[THEN iffD2], auto)
    thus "\<langle>\<K>,g\<rangle> \<Turnstile> diamond_n (Suc n) F" by simp
  qed
qed (simp add:assms)

lemmas diamond_nI[intro] = diamond_n[THEN iffD2, rule_format]

subsection {* The C Property *}

abbreviation "C m n j k \<equiv> {Fr \<in> K. \<forall>w\<^sub>1 w\<^sub>2 w\<^sub>3. (w\<^sub>1,w\<^sub>3) \<in> R Fr ^ m \<and> (w\<^sub>1,w\<^sub>2) \<in> R Fr ^ j \<longrightarrow> (\<exists>w\<^sub>4. (w\<^sub>3,w\<^sub>4) \<in> R Fr ^ n \<and> (w\<^sub>2,w\<^sub>4) \<in> R Fr ^ k)}"

lemma "\<not> char (C 0 0 0 1 :: 'a KripkeClass) (\<diamond>\<^sup>0\<box>\<^sup>0 (V p) \<longrightarrow>\<^sub>M \<box>\<^sup>0\<diamond>\<^sup>1 (V p))"
proof-
  let ?Fr = "Abs_KripkeFrame ({},{})"
  have[simp]: "G (?Fr) = {}" using Abs_KripkeFrame_inverse[of "({},{})"] by (metis (no_types) Field_empty empty_subsetI fst_conv mem_Collect_eq split_conv)
  have[simp]: "R (?Fr) = {}" using Abs_KripkeFrame_inverse[of "({},{})"] by (metis (no_types) Field_empty empty_subsetI fst_conv mem_Collect_eq split_conv surjective_pairing)
  have l: "\<not> ?Fr \<in> C 0 0 0 1" by simp
  have r: "\<forall>v. (?Fr,\<lambda>g p. True) \<Turnstile> (\<diamond>\<^sup>0\<box>\<^sup>0 (V p) \<longrightarrow>\<^sub>M \<box>\<^sup>0\<diamond>\<^sup>1 (V p))" by simp
  show ?thesis
  apply (rule, drule spec[where x= ?Fr])
  using l r by auto
qed

-- {* Well... maybe this definition shouldn't be taken quite as literally *}

abbreviation "C' m n j k \<equiv> {Fr \<in> K. \<forall>w\<^sub>1 \<in> G Fr. \<forall>w\<^sub>2 \<in> G Fr. \<forall>w\<^sub>3 \<in> G Fr. (w\<^sub>1,w\<^sub>3) \<in> R Fr ^ m \<and> (w\<^sub>1,w\<^sub>2) \<in> R Fr ^ j \<longrightarrow> (\<exists>w\<^sub>4. (w\<^sub>3,w\<^sub>4) \<in> R Fr ^ n \<and> (w\<^sub>2,w\<^sub>4) \<in> R Fr ^ k)}"

lemma R_n_closed:
  assumes "g \<in> G Fr" "(g,h) \<in> R Fr ^ n"
  shows "h \<in> G Fr"
using assms by (induct n) auto

theorem "char (C' m n j k :: 'g KripkeClass) (\<diamond>\<^sup>m\<box>\<^sup>n (V p) \<longrightarrow>\<^sub>M \<box>\<^sup>j\<diamond>\<^sup>k (V p))"
proof (rule, rule, rule)
  fix Fr :: "'g KripkeFrame"
  fix v
  assume asm: "Fr \<in> C' m n j k"
  show "(Fr, v) \<Turnstile> \<diamond>\<^sup>m\<box>\<^sup>n (V p) \<longrightarrow>\<^sub>M \<box>\<^sup>j\<diamond>\<^sup>k (V p)"
  proof (rule, rule)
    fix w\<^sub>1
    assume w\<^sub>1: "w\<^sub>1 \<in> G' (Fr, v)" "\<langle>(Fr, v),w\<^sub>1\<rangle> \<Turnstile> \<diamond>\<^sup>m\<box>\<^sup>n (V p)"
    then obtain w\<^sub>3 where w\<^sub>3: "w\<^sub>3 \<in> G Fr" "(w\<^sub>1,w\<^sub>3) \<in> R Fr ^ m" "\<langle>(Fr,v),w\<^sub>3\<rangle> \<Turnstile> \<box>\<^sup>n (V p)" by auto
    from this(1,3) have p: "\<forall>w\<^sub>4 \<in> G Fr. (w\<^sub>3,w\<^sub>4) \<in> R Fr ^ n \<longrightarrow> \<langle>(Fr,v),w\<^sub>4\<rangle> \<Turnstile> (V p)" by simp
    from w\<^sub>1(1) show "\<langle>(Fr, v),w\<^sub>1\<rangle> \<Turnstile> \<box>\<^sup>j\<diamond>\<^sup>k (V p)"
    proof
      fix w\<^sub>2
      assume w\<^sub>2: "w\<^sub>2 \<in> G' (Fr, v)" "(w\<^sub>1, w\<^sub>2) \<in> R' (Fr, v) ^ j"
      from asm w\<^sub>1(1) w\<^sub>3 this obtain w\<^sub>4 where w\<^sub>4: "(w\<^sub>3,w\<^sub>4) \<in> R Fr ^ n" "(w\<^sub>2,w\<^sub>4) \<in> R Fr ^ k" by atomize_elim auto
      from this(1) w\<^sub>3(1) have[simp]: "w\<^sub>4 \<in> G Fr" by -(rule R_n_closed)
      from w\<^sub>4(1) have "\<langle>(Fr,v),w\<^sub>4\<rangle> \<Turnstile> (V p)" using p[THEN bspec[where x=w\<^sub>4]] by simp
      with w\<^sub>2(1) w\<^sub>4(2) show "\<langle>(Fr, v),w\<^sub>2\<rangle> \<Turnstile> \<diamond>\<^sup>k (V p)" by auto
    qed
  qed
next
  fix Fr :: "'g KripkeFrame"
  assume asm: "\<forall>v. (Fr, v) \<Turnstile> \<diamond>\<^sup>m\<box>\<^sup>n (V p) \<longrightarrow>\<^sub>M \<box>\<^sup>j\<diamond>\<^sup>k (V p)"
  show "Fr \<in> C' m n j k"
  proof (simp, rule, rule, rule, rule)
    fix w\<^sub>1 w\<^sub>2 w\<^sub>3
    assume [simp]: "w\<^sub>1 \<in> G Fr" "w\<^sub>2 \<in> G Fr" "w\<^sub>3 \<in> G Fr"
    assume 123: "(w\<^sub>1, w\<^sub>3) \<in> R Fr ^ m \<and> (w\<^sub>1, w\<^sub>2) \<in> R Fr ^ j"
    let ?v = "\<lambda>g p. (w\<^sub>3,g) \<in> R Fr ^ n"
    have "\<langle>(Fr,?v),w\<^sub>1\<rangle> \<Turnstile> \<diamond>\<^sup>m\<box>\<^sup>n(V p)" using 123 by auto
    with asm[THEN spec[where x= ?v], THEN bspec[where x=w\<^sub>1]] have "\<langle>(Fr,?v),w\<^sub>1\<rangle> \<Turnstile> \<box>\<^sup>j\<diamond>\<^sup>k (V p)" by auto
    with 123 obtain w\<^sub>4 where "(w\<^sub>2,w\<^sub>4) \<in> R Fr ^ k" "(w\<^sub>3,w\<^sub>4) \<in> R Fr ^ n" by auto
    thus "\<exists>w\<^sub>4. (w\<^sub>3, w\<^sub>4) \<in> R Fr ^ n \<and> (w\<^sub>2, w\<^sub>4) \<in> R Fr ^ k" by auto
  qed
qed

subsection {* Meaning of Some C-Properties *}

lemma[simp]: "r ^ 2 = r O r" by (simp add:Suc_1[symmetric])

lemma "K4 = C 0 1 2 0" by (auto simp add:trans_def)
lemma "T = C' 0 1 0 0" by (rule set_eqI, subst T, auto)
lemma "{Fr \<in> K. sym (R Fr)} = C 1 1 0 0" by (simp add:sym_def)

end
