import DiophantineConsistency.PRAISigmaOnePiOneComparison
import DiophantineConsistency.PRABoundedWitness
import DiophantineConsistency.ParsonsHierarchyMap
/-! Every unary bounded Π₁ source has a candidate-PRA equivalent unary open
Π₁ predicate. This is not a representation of an arbitrary Π₁ sentence. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRABoundedPiOneUnary
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRABoundedFormula PRABoundedWitness

theorem unary_open (D : ArithmeticSemiformula Empty 1) (hD : Hierarchy 𝚺 0 D) :
    ∃ q : Semisentence language 1, q.Open ∧
      PRA ⊢ (Semiformula.lMap embedding (∀⁰ ∼D) 🡘 ∀⁰ q) := by
  let C := Semiformula.lMap embedding D
  obtain ⟨c,_,_,hc⟩ := PRA_proves_boundedBooleanCharacteristic C (ParsonsHierarchyMap.hierarchy hD)
  let q : Semisentence language 1 := ∼ characteristicMatrix c
  refine ⟨q,?_,?_⟩
  · simp [q, characteristicMatrix, Semiformula.Open]
  · apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ hM
    letI : M↓[language] ⊧* PRA := hM
    have hcorrect := models_of_provable hM hc
    simp only [models_iff, LogicalConnective.iff, Semantics.And.models_and,
      Semantics.Imp.models_imply]
    have heq (x : M) : (characteristicMatrix c).Eval ![x] Empty.elim ↔ C.Eval ![x] Empty.elim :=
      modelCharacteristicMatrix c C hcorrect ![x]
    have hv : (Semiformula.lMap embedding (∀⁰ ∼D)).Evalb (M := M) ![] ↔ ∀ x : M, ¬C.Eval ![x] Empty.elim := by
      simp [C, Semiformula.eval_all]
    have hq : (∀⁰ q).Evalb (M := M) ![] ↔ ∀ x : M, ¬(characteristicMatrix c).Eval ![x] Empty.elim := by
      simp [q, Semiformula.eval_all]
    constructor
    · intro h
      apply hq.mpr
      intro x hx
      exact (hv.mp h x) ((heq x).mp hx)
    · intro h
      apply hv.mpr
      intro x hx
      exact (hq.mp h x) ((heq x).mpr hx)
end DiophantineConsistency.PRABoundedPiOneUnary
