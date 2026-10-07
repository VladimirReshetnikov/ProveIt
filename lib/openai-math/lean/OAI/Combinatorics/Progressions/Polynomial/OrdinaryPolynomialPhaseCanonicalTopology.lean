import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest

namespace OAI

section

namespace Erdos3.OrdinaryPolynomialPhase

open PolynomialTranslationLie
open scoped TensorProduct

@[instance_reducible]
noncomputable def canonicalTopology (s : ℕ) :
    TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
  moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)

theorem canonicalTopologicalAddGroup (s : ℕ) :
    letI := canonicalTopology s
    IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight s) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)
  exact IsModuleTopology.isTopologicalAddGroup ℝ _

theorem canonicalContinuousSMul (s : ℕ) :
    letI := canonicalTopology s
    ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s) := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight s)
  infer_instance

theorem canonicalT2Space (s : ℕ) :
    letI := canonicalTopology s
    T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight s) :=
  realification_moduleTopology_t2 (nilmanifold s).basis

theorem withCanonicalTopology {P : Prop}
    (h : ∀ [∀ r, TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra weight r)]
      [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra weight r)]
      [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra weight r)]
      [∀ r, T2Space (ℝ ⊗[ℚ] weightedSubalgebra weight r)], P) : P := by
  let (r : ℕ) := canonicalTopology r
  let (r : ℕ) := canonicalTopologicalAddGroup r
  let (r : ℕ) := canonicalContinuousSMul r
  let (r : ℕ) := canonicalT2Space r
  exact h

end Erdos3.OrdinaryPolynomialPhase

end

end OAI
