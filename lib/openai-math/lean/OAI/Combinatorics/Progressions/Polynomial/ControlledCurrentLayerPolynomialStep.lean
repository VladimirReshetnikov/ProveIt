import OAI.Combinatorics.Progressions.Estimates.HomogeneousSubspaceCorrections
import OAI.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct Matrix

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_current_layer_polynomial_step
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    (hgraded : BasisHomogeneousBrackets (b.baseChange ℝ) w)
    {j H J l : ℕ} (hj : 0 < j)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : ((l * j : ℕ) : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P Pj : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hPU : ∀ α, coefficients P α ∈ U)
    (hPgraded : P ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPj : Pj = map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P)
    (hPjE : ∀ α, coefficients Pj α ∈ E.baseChange ℝ)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hS : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients (S i) α = 0)
    (hR : ∀ i α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients (R i) α = 0)
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) Pj - S i - R i) α ∈ V.baseChange ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hbudget : (Fintype.card σ : ℝ) / j * M ≤ Real.exp p)
    (hslow : ∀ i α n, |realQuotientCoordinateMap f (coefficients (S i) α) n| ≤
      M / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈ realDenominatorGrid l) :
    ∃ (m : ℕ) (A B P' : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      P' = bchRemove s A P B ∧ lieBCH s (lieBCH s A P') B = P ∧
      coefficients P' 0 = coefficients P 0 ∧
      P' ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
      (∀ α, coefficients P' α ∈ U) ∧
      (∀ α, coefficients (map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P') α ∈
        (E ⊓ V).baseChange ℝ) ∧
      ∀ d < j, map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P' =
        map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P := by
  have hPjhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients Pj α = 0 := by
    intro α hα
    rw [hPj]
    exact gradedPolynomialSubmodule_projection_homogeneous (b.baseChange ℝ) w (fun _ => 1)
      P hPgraded j α hα
  have h := exists_homogeneous_subspace_corrections_from_derivatives b e f hH hl hj
    hA he hp hrows hcols hHp hlp T hT Pj hPjE hPjhom S R hS hR hsplit hM hbudget hslow hrational
  obtain ⟨m, A, B, hm, hmp, _, _, hAB, hAhom, hBhom, hAnorm, hBgrid, hres⟩ := h
  have hA0 : coefficients A 0 = 0 := hAhom 0 (by simpa using Nat.ne_of_lt hj)
  have hB0 : coefficients B 0 = 0 := hBhom 0 (by simpa using Nat.ne_of_lt hj)
  have hgrades := F.polynomial_bchRemove_grades b w hlayers (E.baseChange ℝ) j hE A P B
    (fun α => (hAB α).1) (fun α => (hAB α).2)
  have hAgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    j A hAhom (fun α => hE _ (hAB α).1)
  have hBgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ => 1)
    j B hBhom (fun α => hE _ (hAB α).2)
  refine ⟨m, A, B, bchRemove s A P B, hm, hmp, hAB, hAhom, hBhom, hAnorm, hBgrid, rfl,
    bchRemove_factorization F.realification.lowerCentralSeries_eq_bot A P B,
    bchRemove_constant F.realification.lowerCentralSeries_eq_bot A P B hA0 hB0,
    bchRemove_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w hgraded (fun _ => 1) s A P B
      hAgraded hPgraded hBgraded,
    bchRemove_coefficients_mem U s A P B (fun α => hEU _ (hAB α).1) hPU
      (fun α => hEU _ (hAB α).2), ?_, hgrades.2⟩
  intro α
  rw [hgrades.1, ← hPj]
  exact hres α

end Erdos3.NilpotentLieFiltration

end

end OAI
