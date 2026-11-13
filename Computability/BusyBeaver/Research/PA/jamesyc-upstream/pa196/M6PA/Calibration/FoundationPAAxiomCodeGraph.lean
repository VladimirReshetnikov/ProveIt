module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAAxiomCodeInduction
@[expose] public section

/-! An arithmetic relation retaining the three induction annotations. Its
correctness holds for arbitrary elements of every IΣ₁ model. -/
namespace M6.PA.FoundationAxiomCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

/-- Coordinates are axiom code, parameter count, closed body, induction formula. -/
noncomputable def inductionWitnessGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “p m b K.
    m ≤ p ∧ b ≤ p ∧ !qqAllsDef p b m ∧
    !(isUFormula ℒₒᵣ).sigma b ∧ !(shiftGraph ℒₒᵣ) b b ∧
    !(bvGraph ℒₒᵣ) m b ∧
    ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(substsGraph ℒₒᵣ) s fv b ∧
      K ≤ s ∧ !(isSemiformula ℒₒᵣ).sigma 1 K ∧ !indBodyValGraph s K”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem inductionWitnessGraph_iff (p m b k : V) :
    (V ⊧/![p,m,b,k] inductionWitnessGraph.val) ↔
      (InductionData.mk m b k).Valid p := by
  simp [inductionWitnessGraph, InductionData.Valid, eq_comm]

/-- Internal witness existence is equivalent to the same induction branch,
including for nonstandard formula codes and parameter counts. -/
theorem inductionWitnessGraph_exists_iff (p : V) :
    (∃ m b k : V, V ⊧/![p,m,b,k] inductionWitnessGraph.val) ↔
      InductionR (fun _ => True) p := by
  rw [← inductionData_iff]
  constructor
  · rintro ⟨m,b,k,h⟩
    exact ⟨⟨m,b,k⟩,(inductionWitnessGraph_iff p m b k).mp h⟩
  · rintro ⟨⟨m,b,k⟩,h⟩
    exact ⟨m,b,k,(inductionWitnessGraph_iff p m b k).mpr h⟩

#print axioms inductionWitnessGraph_iff
#print axioms inductionWitnessGraph_exists_iff
end M6.PA.FoundationAxiomCode

