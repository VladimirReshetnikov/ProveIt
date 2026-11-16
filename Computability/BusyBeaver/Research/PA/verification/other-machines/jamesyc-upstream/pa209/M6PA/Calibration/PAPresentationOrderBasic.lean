module
public import M6PA.Theory
public import M6PA.Calibration.PAPresentationMulAssoc
@[expose] public section

namespace M6.PA.Presentation
open FFL FFL.FirstOrder

theorem less_body_subst (a b w : GroundTerm) :
    Semiformula.rewAux (Rew.subst ![w])
      (eq (add (Rew.bShift a) (succ (.bvar 0))) (Rew.bShift b)) =
      eq (add a (succ w)) b := by
  simp only [eq_rew,rew_add,rew_succ,Rew.subst_bShift_app,Rew.subst_bvar,Matrix.cons_val_zero]

def ND.lessIntro {Γ : List ND.Form} (a b w : GroundTerm)
    (h : ND.Proof Γ (eq (add a (succ w)) b)) : ND.Proof Γ (less a b) := by
  apply ND.exsIntro _ w
  change ND.Proof Γ (Semiformula.rewAux (Rew.subst ![w])
    (eq (add (Rew.bShift a) (succ (.bvar 0))) (Rew.bShift b)))
  rw [less_body_subst]
  exact h

def foundationZeroLtOneProof : ordinaryPAeq.Proof (formula Arithmetic.PeanoMinus.Axiom.zeroLtOne) := by
  let Γ : List ND.Form := [addZero]
  have az : ND.Proof Γ addZero := ND.assumption (by simp [Γ])
  have h : ND.Proof Γ (eq (add zero (succ zero)) (succ zero)) := by
    have d := ND.allElim _ (succ zero) az
    convert d using 1 <;> dsimp [addZero] <;> equalityInstanceSyntax
  have hp : ND.Proof Γ (Rewriting.emb (formula Arithmetic.PeanoMinus.Axiom.zeroLtOne)) := by
    have d := ND.lessIntro zero (succ zero) zero h
    change ND.Proof Γ (Semiformula.rewAux Rew.emb (formula Arithmetic.PeanoMinus.Axiom.zeroLtOne))
    rw [←formula_emb]
    exact d
  have ht : ∀ q ∈ Γ,q.univCl ∈ ordinaryPAeq := by
    intro q hq
    have : q = addZero := by simpa [Γ] using hq
    subst q
    exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  have d := ND.parameterTheoryProof hp ht
  simpa only [Semiformula.univCl_coe_sentence] using d

#print axioms foundationZeroLtOneProof
end M6.PA.Presentation
