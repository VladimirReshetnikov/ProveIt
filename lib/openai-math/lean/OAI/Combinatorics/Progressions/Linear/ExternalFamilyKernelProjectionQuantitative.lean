import OAI.Combinatorics.Progressions.Estimates.ExternalUnitFamilyVerticalExpansion
import OAI.Combinatorics.Progressions.Linear.ExternalFamilyPrecenterProjectionData

namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_external_family_quantitative_kernel_projection_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ X Ω G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [Fintype Ω] [Fintype G]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (T : X → D.Niltest w) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (∀ x, (T x).UnitIntervalValued) → (∀ x, (T x).ComplexityLE p) →
      ∀ (P : Submodule ℚ L) (hP : P ≤ D.filtration.layer s),
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights G) (physical : Ω → G → X)
        (path : Ω → G → D.Space) (weight : Ω → G → ℂ),
      (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
      (∀ a ∈ productive, Real.exp (-p) ≤ ((localLaw a).complexMean
        (fun x => weight a x * (T (physical a x)).observable (path a x))).re) →
      ∃ (J : Type) (inst : Fintype J), letI := inst
      ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → X → D.Niltest w)
        (code : Fin (finrank ℚ P) → Option J) (S : X → D.Niltest w) (retained : Finset Ω),
        (Fintype.card J : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + 2) ^ C) ∧
        (∀ j x, (U j x).ComplexityLE ((p + 2) ^ C) ∧
          (U j x).orbit = (T x).orbit ∧ (U j x).normBound = (T x).normBound ∧
          (U j x).lipBound = (T x).lipBound) ∧
        (∀ j a (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j a).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
              (U j a).observable x) ∧
        (∀ x, (S x).UnitIntervalValued ∧ (S x).ComplexityLE ((p + 2) ^ C) ∧
          (S x).orbit = (T x).orbit) ∧
        (∀ x, S x = (T x).kernelProjection (frequencyCodeKernel P eta code)
          ((finiteFrequencyKernel_le P _ _).trans hP)) ∧
        (∀ a (z : D.RealGroup), z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
          ∀ x, (S a).observable (z • x) = (S a).observable x) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained,
          (∀ i j, code i = some j → Real.exp (-((p + 2) ^ C)) <
            ‖(localLaw a).complexMean (fun x =>
              weight a x * (U j (physical a x)).observable (path a x))‖) ∧
          Real.exp (-((p + 2) ^ C)) ≤ ((localLaw a).complexMean
            (fun x => weight a x * (S (physical a x)).observable (path a x))).re := by
  let R : Polynomial ℕ := Polynomial.X
  let Q := 2 * R + 8
  let A := (Q + 3) ^ 9 + 2 * Q + 2
  let V := 2 * A * (2 * A + 2) ^ 4 + ((2 * A + 2) ^ 4 + A + (Q + 3) ^ 5 + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Q + 2 * V + R + 10 + R * (V + 1))
  refine ⟨C, hC, ?_⟩
  intro L σ X Ω G _ _ s d _ _ _ _ _ _ D w T p hp hD hT hTc P hP
    outer productive localLaw physical path weight hweight hscore
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let q := 2 * p + 8
  let v := verticalDecompositionBudget q
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hv : 0 ≤ v := verticalDecompositionBudget_nonneg hq
  have hprod : 0 ≤ p * (v + 1) := by positivity
  have hb : q + 2 * v + p + 10 + p * (v + 1) ≤ (p + 2) ^ C := by
    simpa [R, Q, A, V, q, v, verticalDecompositionBudget, centralActionBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  have hvC : v ≤ (p + 2) ^ C := by linarith
  have htC : p + v + 8 ≤ (p + 2) ^ C := by linarith
  have hnC : p * (v + 1) ≤ (p + 2) ^ C := by linarith
  have hsC : p + 1 ≤ (p + 2) ^ C := by linarith
  obtain ⟨J, inst, eta, U, hJ, hheight, hU, hvert, hint, hchar, happrox, hintError, hrealError⟩ :=
    D.exists_externalFamily_vertical_expansion hq (hD.mono D hpq) T
      (fun x => (hTc x).mono hpq) (Real.exp (-q)) (Real.exp_pos (-q))
      (by rw [Real.exp_neg, inv_inv])
  let _ := inst
  have hsmall := frequency_projection_error_bound hp hJ
  obtain ⟨code, S, retained, hidentity, hS, hSinv, hretained, hmass, hlocal⟩ :=
    RationalFilteredNilmanifold.Niltest.exists_external_family_common_positive_kernel_projection
      T hT hTc P hP eta U hvert outer productive localLaw physical path weight
      (Real.exp_nonneg p) (Real.exp_nonneg (-(p + v + 8))) hweight happrox hscore hsmall
  have hdim : (finrank ℚ P : ℝ) ≤ p := by
    have h := Submodule.finrank_le P
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at h
    exact (Nat.cast_le.mpr h).trans hD.1
  refine ⟨J, inst, eta, U, code, S, retained,
    hJ.trans (Real.exp_le_exp.mpr hvC), fun j i => (hheight j i).trans hvC,
    fun j x => ⟨(hU j x).1.mono hqC, (hU j x).2⟩, hvert,
    fun x => ⟨(hS x).1, (hS x).2.1.mono (hpq.trans hqC), (hS x).2.2⟩,
    hidentity, hSinv, hretained, ?_, ?_⟩
  · exact (mass_div_frequency_count (outer.mass_nonneg productive) hp hv hdim hJ hnC).trans hmass
  · intro a ha
    obtain ⟨hpivot, hpositive⟩ := hlocal a ha
    refine ⟨fun i j hij => (Real.exp_le_exp.mpr (neg_le_neg htC)).trans_lt (hpivot i j hij), ?_⟩
    exact ((Real.exp_le_exp.mpr (by linarith : -((p + 2) ^ C) ≤ -p - 1)).trans
      (exp_sub_one_le_half_exp (-p))).trans hpositive

end Erdos3

end

end OAI
