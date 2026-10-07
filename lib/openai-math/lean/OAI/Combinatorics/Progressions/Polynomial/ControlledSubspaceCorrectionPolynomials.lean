import OAI.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_controlled_subspace_correction_polynomials
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {H J l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P small rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPE : ∀ α, coefficients P α ∈ E.baseChange ℝ)
    (hsmall0 : coefficients small 0 = 0) (hrational0 : coefficients rational 0 = 0)
    (hsmall : ∀ α, ‖realQuotientCoordinateMap f (coefficients small α)‖ ≤
      Real.exp p / monomialScale T α)
    (hrational : ∀ α, realQuotientCoordinateMap f (coefficients rational α) ∈
      realDenominatorGrid l)
    (hsplit : ∀ α, coefficients (P - small - rational) α ∈ V.baseChange ℝ) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) A =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) small ∧
      map ((realQuotientCoordinateMap f).restrictScalars ℚ) B =
        map ((realQuotientCoordinateMap f).restrictScalars ℚ) rational ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, coefficients small α = 0 → coefficients A α = 0) ∧
      (∀ α, coefficients rational α = 0 → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      ∀ α, coefficients (P - A - B) α ∈ (E ⊓ V).baseChange ℝ := by
  have h := exists_controlled_linear_splitting (subspaceQuotientMatrix e f)
    hH hl hA hp hrows hcols hHp hlp T hT
  obtain ⟨Q, m, hm, hmp, hQ⟩ := h
  let q := realQuotientCoordinateMap f
  let C : (ι → ℝ) →ₗ[ℝ] (ν → ℝ) := Matrix.mulVecLin (fun i j => (Q i j : ℝ))
  let D := (bracketSystemLift e).comp (C.comp q)
  let A := map (D.restrictScalars ℚ) small
  let B := map (D.restrictScalars ℚ) rational
  have hAc (α : σ →₀ ℕ) : coefficients A α =
      bracketSystemLift e (C (q (coefficients small α))) := coefficients_map _ _ _
  have hBc (α : σ →₀ ℕ) : coefficients B α =
      bracketSystemLift e (C (q (coefficients rational α))) := coefficients_map _ _ _
  have hcoeff (α : σ →₀ ℕ) :
      q (bracketSystemLift e (C (q (coefficients small α)))) = q (coefficients small α) ∧
      q (bracketSystemLift e (C (q (coefficients rational α)))) = q (coefficients rational α) ∧
      ‖C (q (coefficients small α))‖ ≤
        Real.exp ((p + 2) ^ 18 + p) / monomialScale T α ∧
      C (q (coefficients rational α)) ∈ realDenominatorGrid m := by
    by_cases hα : α = 0
    · simp only [hα, hsmall0, hrational0, map_zero, norm_zero, monomialScale_zero, div_one]
      exact ⟨True.intro, True.intro, Real.exp_nonneg _, ⟨0, by ext i; simp⟩⟩
    · obtain ⟨v, hv⟩ := exists_subspace_basis_coordinates e _ (hPE α)
      have hz : q (coefficients P α) - q (coefficients small α) -
          q (coefficients rational α) = 0 := by
        have hz := (realQuotientCoordinateMap_eq_zero_iff f _).mpr (hsplit α)
        simpa only [map_sub, Finsupp.sub_apply] using hz
      have heq : (fun i n => (subspaceQuotientMatrix e f i n : ℝ)) *ᵥ v =
          q (coefficients small α) + q (coefficients rational α) := by
        rw [subspaceQuotientMatrix_real_apply, hv]
        exact sub_eq_zero.mp (by simpa only [sub_sub] using hz)
      have hd := hQ α hα (q (coefficients small α)) (q (coefficients rational α)) v
        (hsmall α) (hrational α) heq
      rcases hd with ⟨hleft, hright, hnorm, hgrid, _⟩
      rw [subspaceQuotientMatrix_real_apply] at hleft hright
      exact ⟨hleft, hright, hnorm, hgrid⟩
  refine ⟨m, A, B, hm, hmp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [coefficients_map, LinearMap.restrictScalars_apply, hAc]
    exact (hcoeff α).1
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    simp only [coefficients_map, LinearMap.restrictScalars_apply, hBc]
    exact (hcoeff α).2.1
  · intro α
    rw [hAc, hBc]
    exact ⟨bracketSystemLift_mem e _, bracketSystemLift_mem e _⟩
  · intro α hα
    rw [hAc, hα, map_zero, map_zero, map_zero]
  · intro α hα
    rw [hBc, hα, map_zero, map_zero, map_zero]
  · intro α
    rw [hAc]
    apply (bracketSystemLift_norm_bound b e he _).trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hcoeff α).2.2.1
      (by positivity : 0 ≤ ((Fintype.card ν : ℝ) + 1) * (J + 1))
  · intro α
    rw [hBc]
    exact bracketSystemLift_grid b e m _ (hcoeff α).2.2.2
  · intro α
    rw [realification_inf]
    refine ⟨?_, ?_⟩
    · simp only [map_sub, Finsupp.sub_apply, hAc, hBc]
      exact (E.baseChange ℝ).sub_mem
        ((E.baseChange ℝ).sub_mem (hPE α) (bracketSystemLift_mem e _))
        (bracketSystemLift_mem e _)
    · apply (realQuotientCoordinateMap_eq_zero_iff f _).mp
      simp only [map_sub, Finsupp.sub_apply, hAc, hBc]
      change q (coefficients P α) - q (bracketSystemLift e (C (q (coefficients small α)))) -
        q (bracketSystemLift e (C (q (coefficients rational α)))) = 0
      rw [(hcoeff α).1, (hcoeff α).2.1]
      have hz := (realQuotientCoordinateMap_eq_zero_iff f _).mpr (hsplit α)
      simpa only [map_sub, Finsupp.sub_apply] using hz

end Erdos3

end

end OAI
