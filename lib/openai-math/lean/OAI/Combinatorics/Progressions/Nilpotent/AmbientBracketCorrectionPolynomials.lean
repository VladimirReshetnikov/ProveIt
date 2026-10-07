import OAI.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {L ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype κ] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_controlled_bracket_corrections
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ (Q : Matrix ν (κ × ι) ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      let C := Matrix.mulVecLin (fun i j => (Q i j : ℝ))
      ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (small rational : κ × ι → ℝ) (v : ν → ℝ),
        ‖small‖ ≤ Real.exp p / monomialScale T α → rational ∈ realDenominatorGrid l →
        realBracketSystem f k (bracketSystemLift e v) = small + rational →
        bracketSystemLift e (C small) ∈ E.baseChange ℝ ∧
        bracketSystemLift e (C rational) ∈ E.baseChange ℝ ∧
        realBracketSystem f k (bracketSystemLift e (C small)) = small ∧
        realBracketSystem f k (bracketSystemLift e (C rational)) = rational ∧
        ‖C small‖ ≤ Real.exp ((p + 2) ^ 18 + p) / monomialScale T α ∧
        C rational ∈ realDenominatorGrid m ∧
        ∀ b, ⁅bracketSystemLift e v - bracketSystemLift e (C small) -
          bracketSystemLift e (C rational), (1 : ℝ) ⊗ₜ[ℚ] k b⁆ ∈ V.baseChange ℝ := by
  have hsplit := exists_controlled_linear_splitting (bracketSystemMatrix e f k)
    hH hl hA hp hrows hcols hHp hlp T hT
  obtain ⟨Q, m, hm, hmp, hQ⟩ := hsplit
  refine ⟨Q, m, hm, hmp, ?_⟩
  intro C α hα small rational v hsmall hrational heq
  have heq' := (bracketSystemMatrix_real_apply e f k v).trans heq
  obtain ⟨hsmallQ, hratQ, hnorm, hgrid, hzero⟩ :=
    hQ α hα small rational v hsmall hrational heq'
  refine ⟨bracketSystemLift_mem e _, bracketSystemLift_mem e _,
    (bracketSystemMatrix_real_apply e f k (C small)).symm.trans hsmallQ,
    (bracketSystemMatrix_real_apply e f k (C rational)).symm.trans hratQ,
    hnorm, hgrid, ?_⟩
  apply (realBracketSystem_eq_zero_iff f k _).mp
  have h := (bracketSystemMatrix_real_apply e f k (v - C small - C rational)).symm.trans hzero
  simpa only [map_sub] using h

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L μ ν : Type*} [LieRing L] [LieAlgebra ℚ L] {E : Submodule ℚ L}

noncomputable def bracketLiftMatrix (b : Basis μ ℚ L) (e : Basis ν ℚ E) : Matrix μ ν ℚ :=
  fun i j => b.repr (e j : L) i

theorem bracketSystemLift_coordinates [Fintype μ] [Fintype ν]
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (x : ν → ℝ) :
    (b.baseChange ℝ).equivFun (bracketSystemLift e x) =
      (fun i j => (bracketLiftMatrix b e i j : ℝ)) *ᵥ x := by
  classical
  have h : (b.baseChange ℝ).equivFun.toLinearMap.comp (bracketSystemLift e) =
      Matrix.mulVecLin (fun i j => (bracketLiftMatrix b e i j : ℝ)) := by
    apply (Pi.basisFun ℝ ν).ext
    intro j
    change (b.baseChange ℝ).equivFun (bracketSystemLift e (Pi.single j 1)) =
      Matrix.of (fun i n => (bracketLiftMatrix b e i n : ℝ)) *ᵥ Pi.single j 1
    rw [bracketSystemLift_single, Matrix.mulVec_single_one]
    funext i
    simp only [Basis.equivFun_apply, Basis.baseChange_repr_tmul, Matrix.col_apply,
      Matrix.of_apply, bracketLiftMatrix]
    simp [Algebra.smul_def]
  exact DFunLike.congr_fun h x

theorem bracketSystemLift_norm_bound [Fintype μ] [Fintype ν]
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) {H : ℕ}
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) H) (x : ν → ℝ) :
    ‖(b.baseChange ℝ).equivFun (bracketSystemLift e x)‖ ≤
      ((Fintype.card ν : ℝ) + 1) * (H + 1) * ‖x‖ := by
  rw [bracketSystemLift_coordinates]
  exact norm_matrix_mulVec_le _ (H : ℝ≥0) (fun i j => (he i j).abs_real_le) x

theorem bracketSystemLift_grid [Fintype μ] [Fintype ν]
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (m : ℕ) (x : ν → ℝ)
    (hx : x ∈ realDenominatorGrid m) :
    (b.baseChange ℝ).equivFun (bracketSystemLift e x) ∈
      realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m) := by
  rw [bracketSystemLift_coordinates]
  exact real_matrix_denominator_grid (bracketLiftMatrix b e) m x hx

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype ι] [Fintype κ] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_bracket_correction_polynomials
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ν → ℝ))
    (small rational : VectorPolynomial σ ℚ (κ × ι → ℝ))
    (hP0 : coefficients P 0 = 0) (hsmall0 : coefficients small 0 = 0)
    (hrational0 : coefficients rational 0 = 0)
    (hsmall : ∀ α, ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α)
    (hrational : ∀ α, coefficients rational α ∈ realDenominatorGrid l)
    (heq : ∀ α, realBracketSystem f k (bracketSystemLift e (coefficients P α)) =
      coefficients small α + coefficients rational α) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ν → ℝ)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map (((realBracketSystem f k).comp (bracketSystemLift e)).restrictScalars ℚ) A = small ∧
      map (((realBracketSystem f k).comp (bracketSystemLift e)).restrictScalars ℚ) B = rational ∧
      (∀ α, coefficients small α = 0 → coefficients A α = 0) ∧
      (∀ α, coefficients rational α = 0 → coefficients B α = 0) ∧
      (∀ α, ‖coefficients A α‖ ≤ Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, coefficients B α ∈ realDenominatorGrid m) ∧
      ∀ α b, ⁅bracketSystemLift e (coefficients (P - A - B) α),
        (1 : ℝ) ⊗ₜ[ℚ] k b⁆ ∈ V.baseChange ℝ := by
  have h := exists_controlled_bracket_corrections e f k hH hl hA hp hrows hcols hHp hlp T hT
  obtain ⟨Q, m, hm, hmp, hQ⟩ := h
  let C : (κ × ι → ℝ) →ₗ[ℝ] (ν → ℝ) := Matrix.mulVecLin (fun i j => (Q i j : ℝ))
  let A := map (C.restrictScalars ℚ) small
  let B := map (C.restrictScalars ℚ) rational
  have hAc (α : σ →₀ ℕ) : coefficients A α = C (coefficients small α) :=
    coefficients_map _ _ _
  have hBc (α : σ →₀ ℕ) : coefficients B α = C (coefficients rational α) :=
    coefficients_map _ _ _
  have hcoeff (α : σ →₀ ℕ) (hα : α ≠ 0) :=
    hQ α hα (coefficients small α) (coefficients rational α) (coefficients P α)
      (hsmall α) (hrational α) (heq α)
  refine ⟨m, A, B, hm, hmp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hAc]
    change realBracketSystem f k (bracketSystemLift e (C (coefficients small α))) = _
    by_cases hα : α = 0
    · simp only [hα, hsmall0, map_zero]
    · exact (hcoeff α hα).2.2.1
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hBc]
    change realBracketSystem f k (bracketSystemLift e (C (coefficients rational α))) = _
    by_cases hα : α = 0
    · simp only [hα, hrational0, map_zero]
    · exact (hcoeff α hα).2.2.2.1
  · intro α hα
    rw [hAc, hα, map_zero]
  · intro α hα
    rw [hBc, hα, map_zero]
  · intro α
    rw [hAc]
    by_cases hα : α = 0
    · simp only [hα, hsmall0, map_zero, norm_zero, monomialScale_zero, div_one]
      exact Real.exp_nonneg _
    · exact (hcoeff α hα).2.2.2.2.1
  · intro α
    rw [hBc]
    by_cases hα : α = 0
    · rw [hα, hrational0, map_zero]
      exact ⟨0, by ext i; simp⟩
    · exact (hcoeff α hα).2.2.2.2.2.1
  · intro α b
    simp only [map_sub, Finsupp.sub_apply, hAc, hBc]
    by_cases hα : α = 0
    · simp only [hα, hP0, hsmall0, hrational0, map_zero, sub_zero, zero_lie]
      exact (V.baseChange ℝ).zero_mem
    · simpa only [map_sub] using (hcoeff α hα).2.2.2.2.2.2 b

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped Matrix TensorProduct

variable {L μ ι κ ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] {E V : Submodule ℚ L}

theorem exists_ambient_bracket_correction_polynomials
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    {H J l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (bracketSystemMatrix e f k i n) H)
    (he : ∀ i j, RationalHeightLE (b.repr (e j : L) i) J)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (κ × ι) : ℝ) ≤ p)
    (hcols : (Fintype.card ν : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ν → ℝ))
    (small rational : VectorPolynomial σ ℚ (κ × ι → ℝ))
    (hP0 : coefficients P 0 = 0) (hsmall0 : coefficients small 0 = 0)
    (hrational0 : coefficients rational 0 = 0)
    (hsmall : ∀ α, ‖coefficients small α‖ ≤ Real.exp p / monomialScale T α)
    (hrational : ∀ α, coefficients rational α ∈ realDenominatorGrid l)
    (heq : ∀ α, realBracketSystem f k (bracketSystemLift e (coefficients P α)) =
      coefficients small α + coefficients rational α) :
    ∃ (m : ℕ) (A B : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      map ((realBracketSystem f k).restrictScalars ℚ) A = small ∧
      map ((realBracketSystem f k).restrictScalars ℚ) B = rational ∧
      (∀ α, coefficients A α ∈ E.baseChange ℝ ∧ coefficients B α ∈ E.baseChange ℝ) ∧
      (∀ α, coefficients small α = 0 → coefficients A α = 0) ∧
      (∀ α, coefficients rational α = 0 → coefficients B α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) *
          Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      ∀ α t, ⁅coefficients (map ((bracketSystemLift e).restrictScalars ℚ) P - A - B) α,
        (1 : ℝ) ⊗ₜ[ℚ] k t⁆ ∈ V.baseChange ℝ := by
  have h := exists_bracket_correction_polynomials e f k hH hl hA hp hrows hcols hHp hlp
    T hT P small rational hP0 hsmall0 hrational0 hsmall hrational heq
  obtain ⟨m, A₀, B₀, hm, hmp, hAQ, hBQ, hAzero, hBzero, hAnorm, hBgrid, hres⟩ := h
  let A := map ((bracketSystemLift e).restrictScalars ℚ) A₀
  let B := map ((bracketSystemLift e).restrictScalars ℚ) B₀
  have hAc (α : σ →₀ ℕ) : coefficients A α = bracketSystemLift e (coefficients A₀ α) :=
    coefficients_map _ _ _
  have hBc (α : σ →₀ ℕ) : coefficients B α = bracketSystemLift e (coefficients B₀ α) :=
    coefficients_map _ _ _
  refine ⟨m, A, B, hm, hmp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hAc]
    simpa only [coefficients_map, LinearMap.restrictScalars_apply, LinearMap.comp_apply]
      using congrArg (fun q => coefficients q α) hAQ
  · apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map, hBc]
    simpa only [coefficients_map, LinearMap.restrictScalars_apply, LinearMap.comp_apply]
      using congrArg (fun q => coefficients q α) hBQ
  · intro α
    rw [hAc, hBc]
    exact ⟨bracketSystemLift_mem e _, bracketSystemLift_mem e _⟩
  · intro α hα
    rw [hAc, hAzero α hα, map_zero]
  · intro α hα
    rw [hBc, hBzero α hα, map_zero]
  · intro α
    rw [hAc]
    apply (bracketSystemLift_norm_bound b e he _).trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hAnorm α)
      (by positivity : 0 ≤ ((Fintype.card ν : ℝ) + 1) * (J + 1))
  · intro α
    rw [hBc]
    exact bracketSystemLift_grid b e m _ (hBgrid α)
  · intro α t
    simp only [map_sub, Finsupp.sub_apply, coefficients_map, hAc, hBc]
    simpa only [map_sub, Finsupp.sub_apply, LinearMap.restrictScalars_apply] using hres α t

end Erdos3

end

end OAI
