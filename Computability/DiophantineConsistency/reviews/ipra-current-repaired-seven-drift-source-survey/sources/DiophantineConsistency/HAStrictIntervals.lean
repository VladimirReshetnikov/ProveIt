import DiophantineConsistency.FoundationHAOrderDecidable

/-! # Strict finite intervals inside conventional HA

The successor split uses the actual predecessor witness in `ltFormula` and
the proved HA zero/successor cases. These are object-language derivations,
with all free terms and finite open contexts retained. No order DNE, model
semantics, bounded-matrix theorem or proof-checker normalization is used.
-/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.HAStrictIntervals
open SetTheory.PA HA FoundationPAHFSyntax
open FoundationHAOrderWitnesses FoundationHAOrderBase

theorem not_lt_zero (s : Term) : Proves (neg (ltFormula s .zero)) := by
  apply Relative.imp_intro
  apply Relative.ex_elim Formula.Ax_s_sentences
    (Relative.hypothesis List.mem_cons_self)
  let ss := Term.rename Nat.succ s
  have he : Relative Formula.Ax_s
      (.eq (.add ss (.succ (.var 0))) .zero ::
        [ltFormula s .zero].map (Formula.rename Nat.succ))
      (.eq (.add ss (.succ (.var 0))) .zero) :=
    Relative.hypothesis List.mem_cons_self
  have hs := ((Arithmetic.add_succ ss (.var 0)).eq_symm.weaken (by simp)).eq_trans he
  exact ((Arithmetic.succ_ne_zero (.add ss (.var 0))).weaken (by simp)).mp hs

/-- Zero is the literal predecessor witness for s < S s. -/
theorem lt_self_succ (s : Term) : Proves (ltFormula s (.succ s)) := by
  apply Relative.ex_intro _ .zero
  simpa only [Proves, Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ] using Arithmetic.add_one s

/-- Eliminate the actual d in s+S d=S t. At d=0 obtain s=t;
at d=S e retain e as the witness for s<t. -/
theorem lt_succ_split {G : List Formula} {s t : Term}
    (h : Relative Formula.Ax_s G (ltFormula s (.succ t))) :
    Relative Formula.Ax_s G (.or (ltFormula s t) (.eq s t)) := by
  apply Relative.ex_elim Formula.Ax_s_sentences h
  change Relative Formula.Ax_s _
    (.or (Formula.rename Nat.succ (ltFormula s t))
      (.eq (Term.rename Nat.succ s) (Term.rename Nat.succ t)))
  rw [rename_ltFormula]
  let ss := Term.rename Nat.succ s
  let ts := Term.rename Nat.succ t
  let H := .eq (.add ss (.succ (.var 0))) (.succ ts) ::
    G.map (Formula.rename Nat.succ)
  have he : Relative Formula.Ax_s H
      (.eq (.add ss (.succ (.var 0))) (.succ ts)) :=
    Relative.hypothesis List.mem_cons_self
  apply Relative.or_elim ((NaturalCases.zero_or_succ (.var 0)).weaken (G' := H) (by simp))
  · apply Relative.or_intro_right
    have hz : Relative Formula.Ax_s (.eq (.var 0) .zero :: H) (.eq (.var 0) .zero) :=
      Relative.hypothesis List.mem_cons_self
    have hs := (((Arithmetic.add_one ss).eq_symm.weaken (by simp)).eq_trans
      (hz.eq_succ.eq_add_right ss).eq_symm).eq_trans (he.prepend _)
    exact ((Arithmetic.succ_inj ss ts).weaken (by simp)).mp hs
  · apply Relative.ex_elim Formula.Ax_s_sentences
      (Relative.hypothesis List.mem_cons_self)
    change Relative Formula.Ax_s _
      (.or (Formula.rename Nat.succ (ltFormula ss ts))
        (.eq (Term.rename Nat.succ ss) (Term.rename Nat.succ ts)))
    rw [rename_ltFormula]
    apply Relative.or_intro_left
    apply Relative.ex_intro _ (.var 0)
    simp only [Formula.subst, Term.subst, Formula.instTerm,
      Formula.term_subst_instTerm_rename_succ]
    let s₂ := Term.rename Nat.succ ss
    let t₂ := Term.rename Nat.succ ts
    let J := .eq (.var 1) (.succ (.var 0)) ::
      (.ex (.eq (.var 1) (.succ (.var 0))) :: H).map (Formula.rename Nat.succ)
    have hd : Relative Formula.Ax_s J (.eq (.var 1) (.succ (.var 0))) :=
      Relative.hypothesis List.mem_cons_self
    have ht : Relative Formula.Ax_s J
        (.eq (.add s₂ (.succ (.var 1))) (.succ t₂)) := by
      apply Relative.hypothesis
      simp only [J, H, List.map_cons, List.mem_cons, Formula.rename, Term.rename]
      exact Or.inr (Or.inr (Or.inl rfl))
    have hs := (((Arithmetic.add_succ s₂ (.succ (.var 0))).eq_symm.weaken
      (G' := J) (by simp)).eq_trans (hd.eq_succ.eq_add_right s₂).eq_symm).eq_trans ht
    exact ((Arithmetic.succ_inj (.add s₂ (.succ (.var 0))) t₂).weaken (by simp)).mp hs

theorem lt_succ_join {G : List Formula} {s t : Term}
    (h : Relative Formula.Ax_s G (.or (ltFormula s t) (.eq s t))) :
    Relative Formula.Ax_s G (ltFormula s (.succ t)) := by
  apply Relative.or_elim h
  · exact lt_trans (Relative.hypothesis List.mem_cons_self)
      ((lt_self_succ t).weaken (by simp))
  · have he : Relative Formula.Ax_s (.eq s t :: G) (.eq s t) :=
      Relative.hypothesis List.mem_cons_self
    exact FoundationHAOrderDecidable.transport_right
      ((lt_self_succ s).weaken (by simp)) he.eq_succ

/-- Both directions are actual HA implications; this is not a semantic iff. -/
theorem lt_succ_iff (s t : Term) : Proves (.and
    (.imp (ltFormula s (.succ t)) (.or (ltFormula s t) (.eq s t)))
    (.imp (.or (ltFormula s t) (.eq s t)) (ltFormula s (.succ t)))) := by
  apply Relative.and_intro
  · apply Relative.imp_intro
    exact lt_succ_split (Relative.hypothesis List.mem_cons_self)
  · apply Relative.imp_intro
    exact lt_succ_join (Relative.hypothesis List.mem_cons_self)

end DiophantineConsistency.HAStrictIntervals
