import DiophantineConsistency.FoundationHAOrderAdditive

/-! # Successor and transitive order images in conventional HA

Both ordinary order constructions use actual existential witnesses. Their
negative translations preserve double-negated order premises; only the
literal negative disjunction consequent uses intuitionistic stability.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderWitnesses
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAEquality FoundationHAOrderBase FoundationHAOrderAdditive
open SetTheory.PA HA

/-- Pair two double-negated premises without extracting either premise. -/
theorem pair_doubleNeg {B : Formula → Prop} {G : List Formula} {a b : Formula}
    (ha : Relative B G (doubleNeg a)) (hb : Relative B G (doubleNeg b)) :
    Relative B G (doubleNeg (.and a b)) := by
  apply Relative.imp_intro
  apply (ha.prepend (neg (.and a b))).mp
  apply Relative.imp_intro
  apply ((hb.prepend (neg (.and a b))).prepend a).mp
  apply Relative.imp_intro
  have hn : Relative B (b :: a :: neg (.and a b) :: G) (neg (.and a b)) :=
    Relative.hypothesis (by simp)
  exact hn.mp ((Relative.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)).and_intro
    (Relative.hypothesis List.mem_cons_self))

/-- In an actual 0<t witness, its predecessor is zero or a successor by the
proved HA natural-case theorem. The second case supplies that successor's
predecessor as the actual witness for 1<t. -/
theorem one_le_of_zero_lt {G : List Formula} {t : Term}
    (h : Relative Formula.Ax_s G (ltFormula .zero t)) :
    Relative Formula.Ax_s G (.or (.eq (.succ .zero) t) (ltFormula (.succ .zero) t)) := by
  apply Relative.ex_elim Formula.Ax_s_sentences h
  change Relative Formula.Ax_s _ (.or (.eq (.succ .zero) (Term.rename Nat.succ t))
    (Formula.rename Nat.succ (ltFormula (.succ .zero) t)))
  rw [rename_ltFormula]
  let ts := Term.rename Nat.succ t
  let H := .eq (.add .zero (.succ (.var 0))) ts :: G.map (Formula.rename Nat.succ)
  have he : Relative Formula.Ax_s H (.eq (.succ (.var 0)) ts) :=
    ((Arithmetic.zero_add (.succ (.var 0))).eq_symm.weaken (by simp)).eq_trans
      (Relative.hypothesis List.mem_cons_self)
  apply Relative.or_elim ((NaturalCases.zero_or_succ (.var 0)).weaken (G' := H) (by simp))
  · apply Relative.or_intro_left
    have hz : Relative Formula.Ax_s (.eq (.var 0) .zero :: H) (.eq (.var 0) .zero) :=
      Relative.hypothesis List.mem_cons_self
    exact hz.eq_succ.eq_symm.eq_trans (he.prepend _)
  · apply Relative.ex_elim Formula.Ax_s_sentences
      (Relative.hypothesis List.mem_cons_self)
    change Relative Formula.Ax_s _ (.or (.eq (.succ .zero) (Term.rename Nat.succ ts))
      (Formula.rename Nat.succ (ltFormula (.succ .zero) ts)))
    rw [rename_ltFormula]
    apply Relative.or_intro_right
    apply Relative.ex_intro _ (.var 0)
    simp only [Formula.subst, Term.subst, Formula.instTerm,
      Formula.term_subst_instTerm_rename_succ]
    let J := .eq (.var 1) (.succ (.var 0)) ::
      (.ex (.eq (.var 1) (.succ (.var 0))) :: H).map (Formula.rename Nat.succ)
    have hd : Relative Formula.Ax_s J (.eq (.var 1) (.succ (.var 0))) :=
      Relative.hypothesis List.mem_cons_self
    have ht : Relative Formula.Ax_s J
        (.eq (.add .zero (.succ (.var 1))) (Term.rename Nat.succ ts)) := by
      apply Relative.hypothesis
      simp only [J, H, List.map_cons, List.mem_cons, Formula.rename, Term.rename,
        SetTheory.up]
      exact Or.inr (Or.inr (Or.inl True.intro))
    have hleft := ((Arithmetic.succ_add .zero (.succ (.var 0))).eq_trans
      (Arithmetic.zero_add (.succ (.var 0))).eq_succ).weaken (G' := J) (by simp)
    have hright := ((Arithmetic.zero_add (.succ (.var 1))).eq_symm.weaken
      (G' := J) (by simp)).eq_trans ht
    exact (hleft.eq_trans hd.eq_succ.eq_symm).eq_trans hright

/-- Ordinary transitivity retains both predecessor witnesses. Below both
binders d is slot1 and e is slot0; the resulting predecessor is S d + e. -/
theorem lt_trans_imp (s t u : Term) :
    Proves (.imp (.and (ltFormula s t) (ltFormula t u)) (ltFormula s u)) := by
  apply Relative.imp_intro
  have hp : Relative Formula.Ax_s [.and (ltFormula s t) (ltFormula t u)]
      (.and (ltFormula s t) (ltFormula t u)) := Relative.hypothesis List.mem_cons_self
  apply Relative.ex_elim Formula.Ax_s_sentences hp.and_left
  rw [rename_ltFormula]
  let ss := Term.rename Nat.succ s
  let ts := Term.rename Nat.succ t
  let us := Term.rename Nat.succ u
  let H := .eq (.add ss (.succ (.var 0))) ts ::
    [.and (ltFormula s t) (ltFormula t u)].map (Formula.rename Nat.succ)
  have hh : Relative Formula.Ax_s H
      (Formula.rename Nat.succ (.and (ltFormula s t) (ltFormula t u))) := by
    exact Relative.hypothesis (List.mem_cons_of_mem _ (by simp))
  have htu : Relative Formula.Ax_s H (ltFormula ts us) := by
    have hright := hh.and_right
    simpa only [rename_ltFormula] using hright
  apply Relative.ex_elim Formula.Ax_s_sentences htu
  rw [rename_ltFormula]
  apply Relative.ex_intro _ (.add (.succ (.var 1)) (.var 0))
  simp only [Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ]
  let s₂ := Term.rename Nat.succ ss
  let t₂ := Term.rename Nat.succ ts
  let u₂ := Term.rename Nat.succ us
  let J := .eq (.add t₂ (.succ (.var 0))) u₂ :: H.map (Formula.rename Nat.succ)
  have he : Relative Formula.Ax_s J (.eq (.add t₂ (.succ (.var 0))) u₂) :=
    Relative.hypothesis List.mem_cons_self
  have hd : Relative Formula.Ax_s J (.eq (.add s₂ (.succ (.var 1))) t₂) := by
    apply Relative.hypothesis
    simp only [J, H, List.map_cons, List.mem_cons, Formula.rename, Term.rename]
    exact Or.inr (Or.inl rfl)
  have h₁ := ((Arithmetic.add_succ (.succ (.var 1)) (.var 0)).eq_symm.eq_add_right s₂).weaken
    (G' := J) (by simp)
  have h₂ := (Arithmetic.add_assoc s₂ (.succ (.var 1)) (.succ (.var 0))).eq_symm.weaken
    (G' := J) (by simp)
  exact ((h₁.eq_trans h₂).eq_trans (hd.eq_add_left (.succ (.var 0)))).eq_trans he

theorem lt_trans {G : List Formula} {s t u : Term}
    (hst : Relative Formula.Ax_s G (ltFormula s t))
    (htu : Relative Formula.Ax_s G (ltFormula t u)) :
    Relative Formula.Ax_s G (ltFormula s u) :=
  ((lt_trans_imp s t u).weaken (by simp)).mp (hst.and_intro htu)

theorem negative_one_le {G : List Formula} {t : Term}
    (h : Relative Formula.Ax_s G (doubleNeg (ltFormula .zero t))) :
    Relative Formula.Ax_s G (neg (.and (neg (doubleNeg (.eq (.succ .zero) t)))
      (neg (doubleNeg (ltFormula (.succ .zero) t))))) := by
  have hp : Proves (.imp (ltFormula .zero t)
      (neg (.and (neg (doubleNeg (.eq (.succ .zero) t)))
        (neg (doubleNeg (ltFormula (.succ .zero) t)))))) := by
    apply Relative.imp_intro
    exact encoded_or (one_le_of_zero_lt (Relative.hypothesis List.mem_cons_self))
  exact apply_negative (.neg _) (hp.weaken (by simp)) h

theorem negative_lt_trans {G : List Formula} {s t u : Term}
    (hst : Relative Formula.Ax_s G (doubleNeg (ltFormula s t)))
    (htu : Relative Formula.Ax_s G (doubleNeg (ltFormula t u))) :
    Relative Formula.Ax_s G (doubleNeg (ltFormula s u)) :=
  (map_doubleNeg ((lt_trans_imp s t u).weaken (by simp))).mp (pair_doubleNeg hst htu)

theorem oneLeOfZeroLt : Proves (sentence PeanoMinus.Axiom.oneLeOfZeroLtᴺ) := by
  change Proves (Formula.closeN 1 (formula
    (“0 < &0 → 1 ≤ &0” : Proposition ℒₒᵣ)ᴺ))
  apply Arithmetic.reclose 1
  apply translated_imp
  apply Relative.imp_intro
  exact negative_one_le (Relative.hypothesis List.mem_cons_self)

theorem ltTrans : Proves (sentence PeanoMinus.Axiom.ltTransᴺ) := by
  change Proves (Formula.closeN 3 (formula
    (“&2 < &1 ∧ &1 < &0 → &2 < &0” : Proposition ℒₒᵣ)ᴺ))
  apply Arithmetic.reclose 3
  apply translated_imp
  apply Relative.imp_intro
  have h : Relative Formula.Ax_s
      [formula (“&2 < &1 ∧ &1 < &0” : Proposition ℒₒᵣ)ᴺ]
      (formula (“&2 < &1 ∧ &1 < &0” : Proposition ℒₒᵣ)ᴺ) :=
    Relative.hypothesis List.mem_cons_self
  exact negative_lt_trans h.and_left h.and_right

end DiophantineConsistency.FoundationHAOrderWitnesses
