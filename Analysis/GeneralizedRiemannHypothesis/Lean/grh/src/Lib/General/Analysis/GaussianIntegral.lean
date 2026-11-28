import Lib.Base

/-!
# Matrix norm estimates, the Ostrowski–Taussky inequality, and the complex Gaussian integral

This file proves estimates for complex matrices and computes the complex Gaussian integral on
`ι → ℂ`. Here `‖A‖` is the `ℓ²` operator norm. For accretive `A`, the integral of
`exp (-x* A (x - a))` against normalised Lebesgue measure is `(det A)⁻¹`.

## Main definitions and results

* `New.norm_apply_le_l2_opNorm`, `New.l2_opNorm_le_of_apply`: the operator norm bounds the entries,
  and for an `m × n` matrix it is at most `|m| |n|` times a bound for the entries.
* `New.ostrowski_taussky`: the Ostrowski–Taussky inequality, in the form
  `|det H| ≤ 2 ^ card n |det Θ|` when `0 ≤ H ≤ Θ + Θᴴ`.
* `Matrix.IsAccretive`: the matrices `A` with `A + Aᴴ` positive definite. Positive definite matrices
  are accretive (`Matrix.PosDef.isAccretive`), and accretive matrices have nonzero determinant
  (`Matrix.IsAccretive.det_ne_zero`).
* `New.Fock.normalizedVolume`: Lebesgue measure divided by `π ^ card ι`, so that `exp (-|x|²)` has
  integral `1`.
* `New.Fock.map_mulVec_addHaar_eq_smul`, `New.lintegral_eq_norm_det_sq_mul_lintegral_mulVec`: the
  change of variables by an invertible complex matrix `u`, whose real Jacobian is `‖det u‖ ^ 2`.
* `New.Fock.integral_gauss`: if `A` is accretive, the integral of `exp (-x* A (x - a))` is
  `(det A)⁻¹`.

## Relation to the literature

The Ostrowski–Taussky inequality and the complex Gaussian integral are known results.
-/

/-! ## Operator norm, matrix entries and the Ostrowski–Taussky inequality -/

namespace New

open Matrix Norms.L2Operator ComplexOrder Fintype

variable {m n : Type _} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}

lemma l2_opNorm_single [DecidableEq m] {i : m} {j : n} {c : ℂ} : ‖single i j c‖ = ‖c‖ := by
  simp [← mul_self_inj, ← l2_opNorm_conjTranspose_mul_self, ← diagonal_single, Pi.norm_single]

/-- If all entries of an `m × n` complex matrix `A` have norm at most `M`, then the `ℓ²` operator
norm of `A` is at most `|m| |n| M`. -/
lemma l2_opNorm_le_of_apply {M : ℝ} (h_apply : ∀ (i : m) (j : n), ‖A i j‖ ≤ M) :
    ‖A‖ ≤ card m * card n * M := by
  classical
  -- `A` is the sum of `card m * card n` matrices with one entry each.
  grw [A.matrix_eq_sum_single, norm_sum_le, norm_sum_le, l2_opNorm_single.le, h_apply]
  simp [field]

lemma norm_apply_le_l2_opNorm (i : m) (j : n) : ‖A i j‖ ≤ ‖A‖ :=
  calc ‖A i j‖ = ‖WithLp.toLp 2 (A *ᵥ Pi.single j 1) i‖ := by simp
    _ ≤ ‖WithLp.toLp 2 (A *ᵥ Pi.single j 1)‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖A‖ := by simpa using A.l2_opNorm_mulVec (EuclideanSpace.single j 1)

/-- If `H` is positive definite and `Θ + Θᴴ - H` is positive semidefinite, then every eigenvalue
`l` of `H⁻¹ (Θ + Θ)` has real part at least `1`. -/
lemma one_le_re_of_mem_roots_charpoly_inv_mul {Θ H : Matrix n n ℂ} (hH : H.PosDef)
    (h_sub : (Θ + Θᴴ - H).PosSemidef) {l : ℂ} (hl : l ∈ (H⁻¹ * (Θ + Θ)).charpoly.roots) :
    1 ≤ l.re := by
  -- For an eigenvector `v`, `l.re * vᴴ H v = vᴴ (Θ + Θᴴ) v ≥ vᴴ H v > 0`.
  obtain ⟨v, hv_ne, hv⟩ : ∃ v : n → ℂ, v ≠ 0 ∧ l • v = (H⁻¹ * (Θ + Θ)) *ᵥ v := by
    simpa [eval_charpoly, ← exists_mulVec_eq_zero_iff, sub_mulVec, sub_eq_zero] using
      Polynomial.isRoot_of_mem_roots hl
  have h_eigen : l • H *ᵥ v = Θ *ᵥ v + Θ *ᵥ v := by
    simp [← mulVec_smul, hv, ← add_mulVec, hH.det_pos.ne']
  obtain ⟨h_pos, h_im⟩ : 0 < (star v ⬝ᵥ H *ᵥ v).re ∧ 0 = (star v ⬝ᵥ H *ᵥ v).im :=
    Complex.pos_iff.1 (hH.dotProduct_mulVec_pos hv_ne)
  have h_re : l.re * (star v ⬝ᵥ H *ᵥ v).re = 2 * (star v ⬝ᵥ Θ *ᵥ v).re := by
    simpa [← h_im, two_mul] using congrArg (fun w : n → ℂ ↦ (star v ⬝ᵥ w).re) h_eigen
  have h_le : (star v ⬝ᵥ H *ᵥ v).re ≤ 2 * (star v ⬝ᵥ Θ *ᵥ v).re := by
    simpa [add_mulVec, sub_mulVec, mulVec_conjTranspose, dotProduct_star, ← dotProduct_mulVec,
      two_mul] using h_sub.re_dotProduct_nonneg v
  exact le_of_mul_le_mul_right (by rwa [one_mul, h_re]) h_pos

/-- Ostrowski–Taussky inequality: if `H` and `Θ + Θᴴ - H` are positive semidefinite complex matrices
indexed by `n`, then `|det H| ≤ 2 ^ card n |det Θ|`. -/
lemma ostrowski_taussky {Θ H : Matrix n n ℂ} (hH : H.PosSemidef)
    (h_sub : (Θ + Θᴴ - H).PosSemidef) : ‖H.det‖ ≤ 2 ^ card n * ‖Θ.det‖ := by
  by_cases h_det : H.det = 0
  · simp [h_det]
  set M : Matrix n n ℂ := H⁻¹ * (Θ + Θ)
  have h_root (l : ℂ) (hl : l ∈ M.charpoly.roots) : 1 ≤ ‖l‖ :=
    (one_le_re_of_mem_roots_charpoly_inv_mul (hH.posDef_iff_det_ne_zero.2 h_det) h_sub hl).trans
      l.re_le_norm
  -- The determinant of `M` is the product of its eigenvalues.
  have h_prod : 1 ≤ ‖M.det‖ := by
    rw [det_eq_prod_roots_charpoly]
    exact Multiset.prod_induction (1 ≤ ‖·‖) _
      (fun a b ha hb ↦ by simpa using one_le_mul_of_one_le_of_one_le ha hb) norm_one.ge h_root
  have h_norm : ‖M.det‖ = 2 ^ card n * ‖Θ.det‖ / ‖H.det‖ := by simp [M, ← two_smul ℂ, field]
  rwa [h_norm, one_le_div (norm_pos_iff.2 h_det)] at h_prod

end New

/-! ## Accretive matrices, normalised measure on `ι → ℂ` and the complex Gaussian integral -/

section GaussianIntegral

open MeasureTheory Matrix Complex Finset ComplexOrder MatrixOrder PiLp CStarAlgebra NNReal WithLp

variable {ι : Type _} [Fintype ι] (x : ι → ℂ) {A : Matrix ι ι ℂ}

/-- A complex square matrix `A` is (strictly) accretive if `A + Aᴴ` is positive definite. -/
def Matrix.IsAccretive (A : Matrix ι ι ℂ) : Prop := (A + Aᴴ).PosDef

omit [Fintype ι] in
lemma Matrix.PosDef.isAccretive (hA : A.PosDef) : A.IsAccretive := hA.add hA.conjTranspose

lemma Matrix.IsAccretive.det_ne_zero [DecidableEq ι]
    (hA : A.IsAccretive) : A.det ≠ 0 := fun h_det ↦ by
  have h_le : ‖(A + Aᴴ).det‖ ≤ 2 ^ Fintype.card ι * ‖A.det‖ :=
    New.ostrowski_taussky hA.posSemidef (by simpa using PosSemidef.zero)
  simp [h_det, hA.det_pos.ne'] at h_le

namespace New.Fock

/-- Lebesgue measure on `ι → ℂ` divided by `π ^ card ι`. -/
noncomputable def normalizedVolume (ι : Type*) [Fintype ι] : Measure (ι → ℂ) :=
  NNReal.pi⁻¹ ^ Fintype.card ι • volume

instance : (normalizedVolume ι).IsAddHaarMeasure := .nnreal_smul _ (by simp [pi_ne_zero])

/-- The image of an additive Haar measure `μ` on `ι → ℂ` under an invertible complex matrix `u` is
`|det u|⁻² μ`. -/
lemma map_mulVec_addHaar_eq_smul [DecidableEq ι]
    {μ : Measure (ι → ℂ)} [μ.IsAddHaarMeasure] {u : Matrix ι ι ℂ} (hu : det u ≠ 0) :
    μ.map (fun x : ι → ℂ ↦ u *ᵥ x) = (ENNReal.ofReal (‖u.det‖ ^ 2))⁻¹ • μ := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := u.toLin'.restrictScalars ℝ
  -- the real determinant of the complex linear map `u` is `‖det u‖ ^ 2`
  have h_det : LinearMap.det f = ‖u.det‖ ^ 2 := by
    simp [f, LinearMap.det_restrictScalars, Algebra.norm_complex_eq, ← Complex.sq_norm]
  change μ.map f = _
  simp [μ.map_linearMap_addHaar_eq_smul_addHaar, h_det, hu]

/-- Change of variables on `ι → ℂ`: for a complex square matrix `u` with `det u ≠ 0` and any
`g : (ι → ℂ) → [0, ∞]`, one has `∫ g(y) dy = |det u|² ∫ g(u y) dy` (lower Lebesgue integrals). -/
lemma _root_.New.lintegral_eq_norm_det_sq_mul_lintegral_mulVec [DecidableEq ι]
    (u : Matrix ι ι ℂ) (hu : u.det ≠ 0) (g : (ι → ℂ) → ENNReal) :
    ∫⁻ y : ι → ℂ, g y = ENNReal.ofReal (‖u.det‖ ^ 2) * ∫⁻ y : ι → ℂ, g (u *ᵥ y) := by
  have h_emb : MeasurableEmbedding (fun y : ι → ℂ ↦ u *ᵥ y) :=
    Continuous.measurableEmbedding (by fun_prop) (mulVec_injective_of_det_ne_zero hu)
  rw [← h_emb.lintegral_map, map_mulVec_addHaar_eq_smul hu]
  simp [ENNReal.mul_inv_cancel_left, hu]

lemma star_dotProduct_self_eq_sum : star x ⬝ᵥ x = (∑ i : ι, ‖x i‖ ^ 2 : ℝ) := by
  simp [dotProduct, conj_mul']

lemma star_dotProduct_self_eq_norm_sq : star x ⬝ᵥ x = (‖toLp 2 x‖ : ℂ) ^ 2 := by
  rw [star_dotProduct_self_eq_sum, ← ofReal_pow, norm_sq_eq_of_L2]

/-- The square of the sup norm of `x : ι → ℂ` is at most `x* x = ∑ |x i|²`. -/
lemma norm_sq_le_re_star_dotProduct_self : ‖x‖ ^ 2 ≤ (star x ⬝ᵥ x).re := by
  rw [star_dotProduct_self_eq_norm_sq, ← ofReal_pow, ofReal_re]
  gcongr
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (PiLp.norm_apply_le (toLp 2 x))

/-- An accretive matrix `A` (that is, `A + Aᴴ` is positive definite) is congruent to a diagonal
matrix whose entries have positive real part. -/
lemma exists_eq_conjTranspose_mul_diagonal_mul [DecidableEq ι] (hA : A.IsAccretive) :
    ∃ (p : GL ι ℂ) (d : ι → ℂ),
      A = (p : Matrix ι ι ℂ)ᴴ * diagonal d * (p : Matrix ι ι ℂ) ∧ ∀ i : ι, 0 < (d i).re := by
  -- Write `A + Aᴴ = Bᴴ B` and diagonalise `H = B⁻ᴴ (Im A) B⁻¹` by a unitary `U`, with real
  -- eigenvalues `λ`. Then `p = U⁻¹ B` and `d = i λ + 1 / 2`.
  obtain ⟨b, hb_unit, hb : A + Aᴴ = star b * b⟩ :=
    isStrictlyPositive_iff_eq_star_mul_self.mp hA.isStrictlyPositive
  lift b to GL ι ℂ using hb_unit with B
  set H : Matrix ι ι ℂ := star (B : Matrix ι ι ℂ)⁻¹ * imaginaryPart A * (B : Matrix ι ι ℂ)⁻¹
  have hH : H.IsHermitian := ((imaginaryPart A).prop.conjugate' B⁻¹).isHermitian
  set U : Matrix ι ι ℂ := ↑hH.eigenvectorUnitary
  have h_spectral : U * diagonal (ofReal ∘ hH.eigenvalues) * star U = H := by
    simpa using hH.spectral_theorem.symm
  let d : ι → ℂ := fun i ↦ I * hH.eigenvalues i + 2⁻¹
  have hd : diagonal d = I • diagonal (ofReal ∘ hH.eigenvalues) + (2⁻¹ : ℂ) • 1 := by
    simp [smul_one_eq_diagonal, ← diagonal_smul, d]
  refine ⟨Unitary.toUnits hH.eigenvectorUnitary⁻¹ * B, d, ?_, by simp [d]⟩
  calc
    A = I • (imaginaryPart A : Matrix ι ι ℂ) + (2⁻¹ : ℂ) • (A + Aᴴ) := by
      rw [imaginaryPart_apply_coe, smul_smul, mul_neg, I_mul_I, neg_neg, star_eq_conjTranspose]
      module
    _ = star (B : Matrix ι ι ℂ) * (I • H + (2⁻¹ : ℂ) • 1) * B := by
      simp [mul_add, add_mul, hb, H, ← mul_assoc, ← star_mul]
    _ = star (B : Matrix ι ι ℂ) * (U * diagonal d * star U) * B := by
      simp [hd, mul_add, add_mul, h_spectral, U]
    _ = _ := by simp [U, star_eq_conjTranspose, mul_assoc]

/-- The complex Gaussian integral in one variable: if `0 < re d`, then `exp (-z̄ d (z - a))` has
integral `π / d` over `ℂ`. -/
lemma integral_cexp_neg_star_mul {d : ℂ} (hd : 0 < d.re) (a : ℂ) :
    ∫ z : ℂ, exp (-(star z * (d * (z - a)))) = Real.pi / d := by
  -- With `z = v 0 + i v 1` the linear part `star z * (d a)` has the coefficients `d a` of `v 0`
  -- and `-i d a` of `v 1`; apply the Gaussian integral on `ℝ²`.
  let c : Fin 2 → ℂ := (d * a) • ![1, -I]
  let g (v : Fin 2 → ℝ) : ℂ := exp (-d * ∑ i : Fin 2, (v i : ℂ) ^ 2 + ∑ i : Fin 2, c i * v i)
  have h_exponent (z : ℂ) : -(star z * (d * (z - a))) =
      -d * ((z.re : ℂ) ^ 2 + (z.im : ℂ) ^ 2) + (d * a * z.re - I * (d * a) * z.im) := by
    rw [show star z = z.re - z.im * I by simp [Complex.ext_iff]]
    linear_combination (z.re - z.im * I) * d * re_add_im z + d * z.im ^ 2 * I_sq
  have h_coeff : ∑ i : Fin 2, c i ^ 2 = 0 := by simp [c, mul_pow]
  calc
    _ = ∫ z : ℂ, g (measurableEquivPi z) := by
      simp only [h_exponent]
      simp [g, c, sub_eq_add_neg, mul_comm]
    _ = ∫ v : Fin 2 → ℝ, g v := volume_preserving_equiv_pi.integral_comp' g
    _ = Real.pi / d := by
      simpa [h_coeff, g] using GaussianFourier.integral_cexp_neg_mul_sum_add hd c

/-- The complex Gaussian integral: if `A` is accretive (that is, `A + Aᴴ` is positive definite),
then `exp (-x* A (x - a))` has integral `(det A)⁻¹` for `normalizedVolume ι`, Lebesgue measure on
`ι → ℂ` divided by `π ^ card ι`. -/
lemma integral_gauss [DecidableEq ι] (hA : A.IsAccretive) (a : ι → ℂ) :
    ∫ x : ι → ℂ, exp (-(star x ⬝ᵥ A *ᵥ (x - a))) ∂normalizedVolume ι = A.det⁻¹ := by
  -- Write `A = pᴴ diagonal d p`. After the change of variables `y = p x` the integrand is a
  -- product of Gaussians in one variable.
  obtain ⟨p, d, rfl, hd⟩ := exists_eq_conjTranspose_mul_diagonal_mul hA
  set P : Matrix ι ι ℂ := (p : Matrix ι ι ℂ)
  let g (i : ι) (z : ℂ) : ℂ := exp (-(star z * (d i * (z - (P *ᵥ a) i))))
  have h_form (x : ι → ℂ) :
      exp (-(star x ⬝ᵥ (Pᴴ * diagonal d * P) *ᵥ (x - a))) = ∏ i : ι, g i ((P *ᵥ x) i) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dotProduct, mulVec_sub]
    simp [g, dotProduct, mulVec_diagonal, ← exp_sum]
  have h_prod : ∫ y : ι → ℂ, ∏ i : ι, g i (y i) = ∏ i : ι, Real.pi / d i := by
    simp only [integral_fintype_prod_volume_eq_prod g, g, integral_cexp_neg_star_mul (hd _)]
  have h_det : (Pᴴ * diagonal d * P).det = ‖P.det‖ ^ 2 * ∏ i : ι, d i := by
    simp [← mul_conj', mul_comm, mul_left_comm]
  calc
    _ = ∫ y : ι → ℂ, ∏ i : ι, g i (y i) ∂(normalizedVolume ι).map (fun x : ι → ℂ ↦ P *ᵥ x) := by
      rw [integral_map (by fun_prop) (Continuous.aestronglyMeasurable (by fun_prop)), funext h_form]
    _ = (‖P.det‖ ^ 2 * Real.pi ^ Fintype.card ι)⁻¹ * ∏ i : ι, Real.pi / d i := by
      rw [map_mulVec_addHaar_eq_smul p.det_ne_zero]
      simp [normalizedVolume, P, h_prod, NNReal.smul_def, field]
    _ = (Pᴴ * diagonal d * P).det⁻¹ := by simp [h_det, field]

end New.Fock

end GaussianIntegral
