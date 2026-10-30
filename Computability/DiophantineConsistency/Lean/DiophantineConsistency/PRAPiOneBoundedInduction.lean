import DiophantineConsistency.PRAPiOneImplication
import DiophantineConsistency.PRABoundedOneInduction

/-! A one-instance conservation client for equivalences of unary Π₁ formulas. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPiOneBoundedInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAPiOneImplication

/-- For unary open-matrix Π₁ statements, eliminate one closed Σ₁ induction
instance whose three-argument matrix is bounded. This does not assert that
any particular equation or consistency sentence has this unary form. -/
theorem eliminate_one_from_equivalence (ψ : Semisentence language 3)
    (hψ : Hierarchy 𝚺 0 ψ) (p q : Semisentence language 1) (hp : p.Open) (hq : q.Open)
    (h : (PRA ∪ {(succInd (PRAOpenOneInduction.openSigma ψ)).univCl}) ⊢
      ((∀⁰ p) 🡘 (∀⁰ q))) : PRA ⊢ ((∀⁰ p) 🡘 (∀⁰ q)) := by
  let T := PRA ∪ {(succInd (PRAOpenOneInduction.openSigma ψ)).univCl}
  letI : 𝗘𝗤 language ⪯ T := Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl (Or.inl (Or.inl h))))
  have hn₁ : T ⊢ normal p q := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    have hm := models_of_provable hM h
    simp only [LogicalConnective.iff, Semantics.And.models_and] at hm
    exact (model_equiv p q).mp hm.1
  have hn₂ : T ⊢ normal q p := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    have hm := models_of_provable hM h
    simp only [LogicalConnective.iff, Semantics.And.models_and] at hm
    exact (model_equiv q p).mp hm.2
  apply (proves_equivalence_iff p q).mpr
  exact ⟨PRABoundedOneInduction.PRA_proves_goal_of_boundedSuccInd ψ hψ (matrix p q) (matrix_open p q hp hq) hn₁,
    PRABoundedOneInduction.PRA_proves_goal_of_boundedSuccInd ψ hψ (matrix q p) (matrix_open q p hq hp) hn₂⟩
end DiophantineConsistency.PRAPiOneBoundedInduction
