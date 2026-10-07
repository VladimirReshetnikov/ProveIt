import OAI.Combinatorics.Progressions.Linear.PreparedFiniteNestedSourceProjectionBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem le_preparedConditionalExcessRequired (m : ℕ) (Plate E : ℝ) :
    E ≤ preparedConditionalExcessRequired m Plate E := by
  let C := allocatedExternalConditionalExcessExponent m
  have hC : 2 ≤ C := (allocatedExternalConditionalExcessExponent_spec m).1
  have hCReal : (2 : ℝ) ≤ C := Nat.cast_le.mpr hC
  have hbase : 1 ≤ max (4 * (Plate + 8) ^ 2) E + C := by
    have hzero : (0 : ℝ) ≤ max (4 * (Plate + 8) ^ 2) E :=
      (by positivity : (0 : ℝ) ≤ 4 * (Plate + 8) ^ 2).trans (le_max_left _ _)
    linarith only [hzero, hCReal]
  calc
    E ≤ max (4 * (Plate + 8) ^ 2) E + C :=
      (le_max_right _ _).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
    _ = (max (4 * (Plate + 8) ^ 2) E + C) ^ 1 := (pow_one _).symm
    _ ≤ (max (4 * (Plate + 8) ^ 2) E + C) ^ C :=
      pow_le_pow_right₀ hbase (by omega)

theorem preparedNestedFrontProjectionEnvelope_endpoint_le
    {K : Type*} [Fintype K]
    (A : ℕ) (constants : ℕ → ℕ) (innerDepth : ℕ)
    (outer inner : K → ℕ) (native : K → ℝ)
    {x gainLog stageLog : ℝ} (endpoint : ℝ)
    (hA : 2 ≤ A) (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hs : stageLog ∈ Set.Icc 0 x) :
    endpoint ≤ preparedNestedFrontProjectionEnvelope A constants innerDepth
      outer inner native x gainLog stageLog endpoint := by
  have hsum : 0 ≤ ∑ k : K, preparedFiniteForwardFrontProjectionPrecision
      (preparedFiniteForwardModelPrecision A constants (inner k)
        (candidateNestedForwardSeed A constants innerDepth (outer k) x) gainLog stageLog)
      (preparedFiniteForwardWork A constants (inner k)
        (candidateNestedForwardSeed A constants innerDepth (outer k) x)) (native k) := by
    apply Finset.sum_nonneg
    intro k _
    have hseed := le_candidateNestedForwardSeed A constants innerDepth (outer k) hA hx
    have hseed0 := candidateNestedForwardSeed_nonneg A constants innerDepth (outer k) hx
    exact preparedFiniteForwardFrontProjectionPrecision_nonneg
      (preparedFiniteForward_model_precision_bounds A constants (inner k) hseed0
        ⟨hg.1, hg.2.trans hseed⟩ ⟨hs.1, hs.2.trans hseed⟩).1
      (preparedFiniteForwardWork_nonneg A constants (inner k) hseed0)
  unfold preparedNestedFrontProjectionEnvelope
  linarith only [hsum]

theorem preparedFiniteNestedSourceRequired_endpoint_le
    {Slot : Type*} [Fintype Slot]
    (m A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth cutoff : ℕ)
    (x anchorRequired Plate E : ℝ) (detectorRequired : Slot → ℝ)
    {endpoint : ℝ} (hendpoint : endpoint ≤ E) :
    endpoint ≤ preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorRequired (preparedConditionalExcessRequired m Plate E) detectorRequired :=
  hendpoint.trans ((le_preparedConditionalExcessRequired m Plate E).trans
    (conditionalRequired_le_preparedFiniteNestedSourceRequired A constants innerDepth outerDepth cutoff
      x anchorRequired (preparedConditionalExcessRequired m Plate E) detectorRequired))

end Erdos3.VectorPolynomial

end

end OAI
