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

end
