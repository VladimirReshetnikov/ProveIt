import DiophantineConsistency.FoundationHAOrderWitnesses

/-! # The actual multiplicative order axiom in conventional HA

The strict-product witness is d*u+e, where s+S d=t and S e=u.
Only proved HA arithmetic equalities are composed; the GG premises remain
double-negated and no new induction or order decision principle is used.
-/

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHAOrderMultiplicative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open FoundationPAHFSyntax FoundationHAEquality FoundationHAOrderBase
open FoundationHAOrderAdditive FoundationHAOrderWitnesses
open SetTheory.PA HA

/-- Both existential binders shift all ambient terms and the complete context.
At the product witness, d is slot1 and e is slot0. -/
theorem mul_lt_mul_imp (s t u : Term) : Proves (.imp
    (.and (ltFormula s t) (ltFormula .zero u))
    (ltFormula (.mul s u) (.mul t u))) := by
  apply Relative.imp_intro
  have hp : Relative Formula.Ax_s [.and (ltFormula s t) (ltFormula .zero u)]
      (.and (ltFormula s t) (ltFormula .zero u)) := Relative.hypothesis List.mem_cons_self
  apply Relative.ex_elim Formula.Ax_s_sentences hp.and_left
  rw [rename_ltFormula]
  let ss := Term.rename Nat.succ s
  let ts := Term.rename Nat.succ t
  let us := Term.rename Nat.succ u
  let H := .eq (.add ss (.succ (.var 0))) ts ::
    [.and (ltFormula s t) (ltFormula .zero u)].map (Formula.rename Nat.succ)
  have hh : Relative Formula.Ax_s H
      (Formula.rename Nat.succ (.and (ltFormula s t) (ltFormula .zero u))) :=
    Relative.hypothesis (List.mem_cons_of_mem _ (by simp))
  have hu : Relative Formula.Ax_s H (ltFormula .zero us) := by
    have hr := hh.and_right
    simpa only [rename_ltFormula, Term.rename] using hr
  apply Relative.ex_elim Formula.Ax_s_sentences hu
  rw [rename_ltFormula]
  let s₂ := Term.rename Nat.succ ss
  let t₂ := Term.rename Nat.succ ts
  let u₂ := Term.rename Nat.succ us
  let J := .eq (.add .zero (.succ (.var 0))) u₂ :: H.map (Formula.rename Nat.succ)
  apply Relative.ex_intro _ (.add (.mul (.var 1) u₂) (.var 0))
  simp only [Formula.subst, Term.subst, Formula.instTerm,
    Formula.term_subst_instTerm_rename_succ]
  have he : Relative Formula.Ax_s J (.eq (.succ (.var 0)) u₂) :=
    ((Arithmetic.zero_add (.succ (.var 0))).eq_symm.weaken (by simp)).eq_trans
      (Relative.hypothesis List.mem_cons_self)
  have hd : Relative Formula.Ax_s J (.eq (.add s₂ (.succ (.var 1))) t₂) := by
    apply Relative.hypothesis
    simp only [J, H, List.map_cons, List.mem_cons, Formula.rename, Term.rename]
    exact Or.inr (Or.inl rfl)
  have hprod : Relative Formula.Ax_s J
      (.eq (.mul (.succ (.var 1)) u₂) (.succ (.add (.mul (.var 1) u₂) (.var 0)))) :=
    (((Arithmetic.succ_mul (.var 1) u₂).weaken (by simp)).eq_trans
      (he.eq_symm.eq_add_right (.mul (.var 1) u₂))).eq_trans
        ((Arithmetic.add_succ (.mul (.var 1) u₂) (.var 0)).weaken (by simp))
  have hdist := (Arithmetic.add_mul s₂ (.succ (.var 1)) u₂).eq_symm.weaken
    (G' := J) (by simp)
  exact ((hprod.eq_symm.eq_add_right (.mul s₂ u₂)).eq_trans hdist).eq_trans
    (hd.eq_mul_left u₂)

theorem mul_lt_mul {G : List Formula} {s t u : Term}
    (hst : Relative Formula.Ax_s G (ltFormula s t))
    (hu : Relative Formula.Ax_s G (ltFormula .zero u)) :
    Relative Formula.Ax_s G (ltFormula (.mul s u) (.mul t u)) :=
  ((mul_lt_mul_imp s t u).weaken (by simp)).mp (hst.and_intro hu)

theorem negative_mul_lt_mul {G : List Formula} {s t u : Term}
    (hst : Relative Formula.Ax_s G (doubleNeg (ltFormula s t)))
    (hu : Relative Formula.Ax_s G (doubleNeg (ltFormula .zero u))) :
    Relative Formula.Ax_s G (doubleNeg (ltFormula (.mul s u) (.mul t u))) :=
  (map_doubleNeg ((mul_lt_mul_imp s t u).weaken (by simp))).mp (pair_doubleNeg hst hu)

/-- The actual source quantifiers x,y,z bind target matrix slots2,1,0. -/
theorem mulLtMul : Proves (sentence PeanoMinus.Axiom.mulLtMulᴺ) := by
  change Proves (Formula.closeN 3 (formula
    (“&2 < &1 ∧ 0 < &0 → &2 * &0 < &1 * &0” : Proposition ℒₒᵣ)ᴺ))
  apply Arithmetic.reclose 3
  apply translated_imp
  apply Relative.imp_intro
  have h : Relative Formula.Ax_s
      [formula (“&2 < &1 ∧ 0 < &0” : Proposition ℒₒᵣ)ᴺ]
      (formula (“&2 < &1 ∧ 0 < &0” : Proposition ℒₒᵣ)ᴺ) :=
    Relative.hypothesis List.mem_cons_self
  exact negative_mul_lt_mul h.and_left h.and_right

end DiophantineConsistency.FoundationHAOrderMultiplicative
