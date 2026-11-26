import Lib.DiscreteSeries.FlenstedJensen.Defs
import Lib.Shimura.ComplexTheta.AppellHumbertData

/-!
# Matrices near the identity: Jacobi's formula and norm estimates

This file collects known facts on complex matrices near the identity.
It proves Jacobi's formula for the derivative of the determinant at the identity and
`det (exp M) = exp (tr M)`.
Estimates in the Hilbert–Schmidt norm, which is the norm of all matrices in this file, control the
inverse and the logarithm of `1 + X` and the exponential of `X`.
The logarithm of an element of `USign ε` near `1` lies in the Lie algebra.
A matrix at distance less than `1` from the identity is accretive.

## Main definitions and results

* `New.hasDerivAt_det_of_eq_one`: along a differentiable curve of complex matrices through the
  identity, the derivative of the determinant there is the trace of the velocity.
* `New.DiscreteSeries.logOneAdd` and `exp_logOneAdd`: the logarithm of `1 + X` for `‖X‖ ≤ 1 / 2`.

Notions from other files:
* `signMatrix ε` is the diagonal matrix with entries `ε i = ±1`, and `USign ε` is its unitary group.
* `unitaryLie J` is the space of matrices `X` with `Xᴴ * J + J * X = 0`.
* `entryMask r X` keeps the entries `(i, j)` of `X` with `r i j` and replaces the others by `0`.
* A matrix `A` is accretive (`A.IsAccretive`) if `A + Aᴴ` is positive definite.
-/

noncomputable section

/-! ## Jacobi's formula for the derivative of the determinant -/

/-- Jacobi's formula at the identity: if `γ s = 1` and `γ` has derivative `Y` at `s`, then
`det ∘ γ` has derivative `Y.trace` at `s`. -/
lemma New.hasDerivAt_det_of_eq_one {n : Type*} [Fintype n] [DecidableEq n] {γ : ℝ → Matrix n n ℂ}
    {Y : Matrix n n ℂ} {s : ℝ} (hγ_one : γ s = 1) (hγ_deriv : HasDerivAt γ Y s) :
    HasDerivAt (fun t : ℝ ↦ (γ t).det) Y.trace s := by
  -- The determinant is a continuous multilinear function `D` of the rows.
  let D : ContinuousMultilinearMap ℝ (fun _ : n ↦ n → ℂ) ℂ :=
    ⟨(Matrix.detRowAlternating (n := n) (R := ℂ)).toMultilinearMap.restrictScalars ℝ,
      continuous_id.matrix_det⟩
  refine ((D.hasFDerivAt _).comp_hasDerivAt s hγ_deriv).congr_deriv ?_
  -- Its derivative at `1` replaces one row of `1` at a time by that row of `Y`; this gives `Y i i`.
  calc D.linearDeriv (γ s) Y = ∑ i, ((γ s).updateRow i (Y i)).det := sum_apply ..
    _ = Y.trace := by simp [hγ_one, ← Matrix.cramer_transpose_apply, Matrix.trace]

/-!
## Matrices near the identity in the Hilbert–Schmidt norm

The main results are the bound `‖tr (X Y)‖ ≤ ‖X‖ ‖Y‖`, invariance under unitary left factors, the
inverse of `1 + X` for small `X`, the formula `det (exp M) = exp (tr M)`, and the logarithm of
`1 + X`, written as the integral of `(1 + s X)⁻¹ X` over `[0, 1]`. The logarithm of an element of
`USign ε` near `1` lies in the Lie algebra, and a matrix at distance less than `1` from the identity
is accretive.
-/

section FrobeniusNormTools

open Matrix Finset Norms.Frobenius Complex intervalIntegral ComplexConjugate MatrixOrder WithLp

namespace New.DiscreteSeries

variable {n : Type*} [Fintype n] [DecidableEq n] {P X Y : Matrix n n ℂ} {ρ : ℝ}

/-- An integral weight as a diagonal matrix. -/
@[simp] abbrev intDiagonal (w : n → ℤ) : Matrix n n ℂ := diagonal fun i ↦ (w i : ℂ)

lemma frobenius_norm_sq_eq_sum : ‖X‖ ^ 2 = ∑ i : n, ∑ j : n, ‖X i j‖ ^ 2 := by
  simp only [frobenius_norm_def, Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]

/-- The Cauchy–Schwarz inequality for the trace form: `‖tr (X * Y)‖` is at most the product of the
Hilbert–Schmidt norms of `X` and `Y`. -/
lemma norm_trace_mul_le_norm_mul_norm (X Y : Matrix n n ℂ) : ‖(X * Y).trace‖ ≤ ‖X‖ * ‖Y‖ := by
  -- The trace is the inner product of `Xᴴ` and `Y` as vectors of entries.
  let vec (M : Matrix n n ℂ) : PiLp 2 fun _ : n ↦ EuclideanSpace ℂ n :=
    WithLp.toLp 2 fun i ↦ WithLp.toLp 2 (M i)
  have h_vec (M : Matrix n n ℂ) : ‖vec M‖ = ‖M‖ := rfl
  calc ‖(X * Y).trace‖ = ‖inner ℂ (vec (star X)) (vec Y)‖ := by
        rw [trace_mul_comm]
        simp [vec, inner, trace, mul_apply]
    _ ≤ ‖X‖ * ‖Y‖ := by grw [norm_inner_le_norm, h_vec, h_vec, norm_star]

lemma norm_trace_mul_le {X Y : Matrix n n ℂ} {ρ σ : ℝ} (hX : ‖X‖ ≤ ρ) (hY : ‖Y‖ ≤ σ) :
    ‖(X * Y).trace‖ ≤ ρ * σ := by
  grw [norm_trace_mul_le_norm_mul_norm, hX, hY]
  exact (norm_nonneg X).trans hX

lemma trace_star_mul_self_eq_norm_sq : (Xᴴ * X).trace = ((‖X‖ ^ 2 : ℝ) : ℂ) := by
  rw [frobenius_norm_sq_eq_sum, Finset.sum_comm]
  simp [trace, mul_apply, conj_mul']

/-- Left multiplication by a unitary matrix preserves the Hilbert–Schmidt norm. -/
lemma frobenius_norm_mul_of_unitary (hX : Xᴴ * X = 1) (Y : Matrix n n ℂ) : ‖X * Y‖ = ‖Y‖ := by
  have h_gram : (X * Y)ᴴ * (X * Y) = Yᴴ * Y := by simp [mul_assoc, ← mul_assoc Xᴴ, hX]
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← ofReal_inj, ← trace_star_mul_self_eq_norm_sq,
    h_gram, trace_star_mul_self_eq_norm_sq]

lemma norm_smul_le_of_le_one {X : Matrix n n ℂ} {σ : ℝ} (ρ : ℝ) (hX : ‖X‖ ≤ σ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : ‖ρ • X‖ ≤ σ := by
  grw [norm_smul_of_nonneg hρ.1, hρ.2, one_mul, hX]

lemma det_one_add_ne_zero (hX : ‖X‖ < 1) : (1 + X).det ≠ 0 := by
  have h_unit : IsUnit (1 - -X) := isUnit_one_sub_of_norm_lt_one (by rwa [norm_neg])
  simpa [isUnit_iff_isUnit_det] using h_unit

lemma one_add_mul_inv_one_add (hX : ‖X‖ < 1) : (1 + X) * (1 + X)⁻¹ = 1 :=
  mul_nonsing_inv _ (det_one_add_ne_zero hX).isUnit

lemma inv_one_add_mul_one_add (hX : ‖X‖ < 1) : (1 + X)⁻¹ * (1 + X) = 1 :=
  nonsing_inv_mul _ (det_one_add_ne_zero hX).isUnit

/-- If `X` has Hilbert–Schmidt norm at most `1 / 2`, then `(1 + X)⁻¹` is within `2 * ‖X‖` of `1`. -/
lemma norm_inv_one_add_sub_one_le (hX : ‖X‖ ≤ 2⁻¹) : ‖(1 + X)⁻¹ - 1‖ ≤ 2 * ‖X‖ := by
  set V : Matrix n n ℂ := (1 + X)⁻¹ - 1
  have h_inv : (V + 1) * (1 + X) = 1 := by
    simp [V, inv_one_add_mul_one_add (hX.trans_lt two_inv_lt_one)]
  have h_eq : V = -(X + V * X) := by linear_combination (norm := noncomm_ring) h_inv
  have h_bound : ‖X + V * X‖ ≤ ‖X‖ + ‖V‖ * 2⁻¹ :=
    norm_add_le_of_le le_rfl (norm_mul_le_of_le le_rfl hX)
  rw [← norm_neg, ← h_eq] at h_bound
  linarith

/-- The logarithm of `1 + X`, as the integral of `(1 + s • X)⁻¹ * X` over `[0, 1]`. -/
def logOneAdd (X : Matrix n n ℂ) : Matrix n n ℂ := ∫ s : ℝ in 0..1, (1 + s • X)⁻¹ * X

lemma det_one_add_smul_ne_zero (hX : ‖X‖ ≤ 2⁻¹) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (1 + s • X).det ≠ 0 :=
  det_one_add_ne_zero ((norm_smul_le_of_le_one s hX hs).trans_lt two_inv_lt_one)

/-- For `‖X‖ ≤ 1 / 2` the integrand of `logOneAdd X` is continuous at every point of `[0, 1]`. -/
lemma continuousAt_inv_one_add_smul_mul (hX : ‖X‖ ≤ 2⁻¹) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt (fun t : ℝ ↦ (1 + t • X)⁻¹ * X) s := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  fun_prop (disch := exact det_one_add_smul_ne_zero hX hs)

/-- For `‖X‖ ≤ 1 / 2` the integrand of `logOneAdd X` is continuous on `[0, 1]`. -/
lemma continuousOn_inv_one_add_smul_mul (hX : ‖X‖ ≤ 2⁻¹) :
    ContinuousOn (fun s : ℝ ↦ (1 + s • X)⁻¹ * X) (Set.uIcc 0 1) :=
  fun _ hs ↦ (continuousAt_inv_one_add_smul_mul hX (by simpa using hs)).continuousWithinAt

/-- For `‖X‖ ≤ 1 / 2` and `0 ≤ s ≤ 1` the integral of `(1 + u • X)⁻¹ * X` over `[0, t]` has
derivative `(1 + s • X)⁻¹ * X` at `t = s`. -/
lemma hasDerivAt_integral_inv_one_add_smul_mul (hX : ‖X‖ ≤ 2⁻¹) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun t : ℝ ↦ ∫ u : ℝ in 0..t, (1 + u • X)⁻¹ * X) ((1 + s • X)⁻¹ * X) s := by
  have h_meas : MeasureTheory.AEStronglyMeasurable (fun u : ℝ ↦ (1 + u • X)⁻¹ * X) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    fun_prop
  exact integral_hasDerivAt_right ((continuousOn_inv_one_add_smul_mul hX).mono
      (Set.uIcc_subset_uIcc_left (by simpa using hs))).intervalIntegrable
    ⟨Set.univ, Filter.univ_mem, h_meas.restrict⟩ (continuousAt_inv_one_add_smul_mul hX hs)

lemma commute_inv_one_add_smul (hY : Commute Y X) (s : ℝ) : Commute Y (1 + s • X)⁻¹ := by
  simpa using Matrix.Commute.zpow_right ((Commute.one_right Y).add_right (hY.smul_right s)) (-1)

/-- A matrix that commutes with all values of a continuous function `G` commutes with its
integral. -/
lemma commute_intervalIntegral {G : ℝ → Matrix n n ℂ} {a b : ℝ}
    (hG : ContinuousOn G (Set.uIcc a b)) (hY : ∀ s : ℝ, Commute Y (G s)) :
    Commute Y (∫ s in a..b, G s) :=
  calc Y * ∫ s in a..b, G s = ∫ s in a..b, Y * G s :=
        ((ContinuousLinearMap.mul ℝ _ Y).intervalIntegral_comp_comm hG.intervalIntegrable).symm
    _ = ∫ s in a..b, G s * Y := by simp only [(hY _).eq]
    _ = (∫ s in a..b, G s) * Y :=
        ((ContinuousLinearMap.mul ℝ _).flip Y).intervalIntegral_comp_comm hG.intervalIntegrable

/-- For `‖X‖ ≤ 1 / 2` the function `s ↦ tr (D * (1 + s • X)⁻¹ * X)` is integrable on `[0, 1]`. -/
lemma intervalIntegrable_trace_mul_inv_one_add_smul_mul (hX : ‖X‖ ≤ 2⁻¹) (D : Matrix n n ℂ) :
    IntervalIntegrable (fun s : ℝ ↦ (D * ((1 + s • X)⁻¹ * X)).trace) MeasureTheory.volume 0 1 :=
  (continuous_id.matrix_trace.comp_continuousOn'
    (continuousOn_const.mul (continuousOn_inv_one_add_smul_mul hX))).intervalIntegrable

/-- For `‖X‖ ≤ 1 / 2` the integral of `s ↦ tr (D * (1 + s • X)⁻¹ * X)` over `[0, 1]` is
`tr (D * logOneAdd X)`, where `logOneAdd X` is the integral of `(1 + s • X)⁻¹ * X`. -/
lemma integral_trace_mul_inv_one_add_smul_mul (hX : ‖X‖ ≤ 2⁻¹) (D : Matrix n n ℂ) :
    ∫ s : ℝ in 0..1, (D * ((1 + s • X)⁻¹ * X)).trace = (D * logOneAdd X).trace :=
  -- The continuous linear form `M ↦ tr (D * M)` commutes with the integral.
  (traceLinearMap n ℂ ℂ ∘ₗ .mulLeft ℂ D).toContinuousLinearMap.intervalIntegral_comp_comm
    (continuousOn_inv_one_add_smul_mul hX).intervalIntegrable

/-- Jacobi's formula along `t ↦ exp (t • M)`: the derivative of `det (exp (t • M))` at `s` is
`det (exp (s • M)) * tr M`. -/
lemma hasDerivAt_det_exp_smul (M : Matrix n n ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ ↦ (NormedSpace.exp (t • M)).det)
      ((NormedSpace.exp (s • M)).det * M.trace) s := by
  have h_path : HasDerivAt (fun t : ℝ ↦ NormedSpace.exp ((t - s) • M)) M s := by
    -- `using!`: the two instances of the topology on matrices agree only up to defeq.
    simpa using! (hasDerivAt_exp_smul_const M (s - s)).comp_sub_const s s
  have h_split (t : ℝ) : NormedSpace.exp (t • M) =
      NormedSpace.exp (s • M) * NormedSpace.exp ((t - s) • M) := by
    simp [← Matrix.exp_add_of_commute _ _ (((Commute.refl M).smul_left s).smul_right _), ← add_smul]
  simpa only [← det_mul, ← h_split] using
    (hasDerivAt_det_of_eq_one (by simp) h_path).const_mul (NormedSpace.exp (s • M)).det

/-- The determinant of the exponential of a matrix is the exponential of its trace. -/
lemma det_exp (M : Matrix n n ℂ) : (NormedSpace.exp M).det = cexp M.trace := by
  -- The function `t ↦ det (exp (t M)) * exp (-t tr M)` has derivative zero, by Jacobi's formula,
  -- so it takes equal values at `1` and `0`.
  have h_deriv (s : ℝ) : HasDerivAt
      (fun t : ℝ ↦ (NormedSpace.exp (t • M)).det * cexp (-(t * M.trace))) 0 s := by
    have h_scalar : HasDerivAt (fun t : ℝ ↦ cexp (-(t * M.trace)))
        (cexp (-(s * M.trace)) * -M.trace) s := by
      simpa using ((ofRealCLM.hasDerivAt (x := s)).mul_const M.trace).neg.cexp
    exact ((hasDerivAt_det_exp_smul M s).fun_mul h_scalar).congr_deriv (by ring)
  simpa [Complex.exp_neg, mul_inv_eq_one₀] using
    is_const_of_deriv_eq_zero (fun s ↦ (h_deriv s).differentiableAt) (fun s ↦ (h_deriv s).deriv) 1 0

/-- If `L` has derivative `L'` at `s` and `L s` commutes with `L t` for all `t ∈ S`, then
`exp (-L t)` has derivative `exp (-L s) * -L'` at `s` within `S`. -/
lemma hasDerivWithinAt_exp_neg_of_commute {L : ℝ → Matrix n n ℂ} {L' : Matrix n n ℂ} {S : Set ℝ}
    {s : ℝ} (hL : HasDerivAt L L' s) (h_comm : ∀ t ∈ S, Commute (L s) (L t)) :
    HasDerivWithinAt (fun t : ℝ ↦ NormedSpace.exp (-L t)) (NormedSpace.exp (-L s) * -L') S s := by
  -- On `S` we have `exp (-L t) = exp (-L s) * exp (L s - L t)`; differentiate `exp` at `0`.
  have h_zero : HasFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      (1 : Matrix n n ℂ →L[ℝ] Matrix n n ℂ) (L s - L s) := by
    -- `using!`: the two instances of the topology on matrices agree only up to defeq.
    simpa using! hasFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix n n ℂ)
  have h_near : HasDerivAt (fun t : ℝ ↦ NormedSpace.exp (-L s) * NormedSpace.exp (L s - L t))
      (NormedSpace.exp (-L s) * -L') s := (h_zero.comp_hasDerivAt s (hL.const_sub _)).const_mul _
  refine h_near.hasDerivWithinAt.congr (fun t ht ↦ ?_) (by simp)
  rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl _).sub_right (h_comm t ht)).neg_left,
    neg_add_eq_sub, sub_sub_cancel_left]

/-- For `‖X‖ ≤ 1 / 2` and `0 ≤ s ≤ 1` the matrix `(1 + s • X)⁻¹ * X` times `1 + s • X` is `X`. -/
lemma inv_one_add_smul_mul_mul_one_add_smul (hX : ‖X‖ ≤ 2⁻¹) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : (1 + s • X)⁻¹ * X * (1 + s • X) = X := by
  rw [← (commute_inv_one_add_smul (.refl X) s).eq, mul_assoc,
    nonsing_inv_mul _ (det_one_add_smul_ne_zero hX hs).isUnit, mul_one]

/-- If the Hilbert–Schmidt norm of `X` is at most `1 / 2`, then `logOneAdd X`, the integral of
`(1 + s • X)⁻¹ * X` over `[0, 1]`, is a logarithm of `1 + X`. -/
lemma exp_logOneAdd (hX : ‖X‖ ≤ 2⁻¹) : NormedSpace.exp (logOneAdd X) = 1 + X := by
  -- Put `G s = (1 + s X)⁻¹ X` and `L t = ∫ G over [0, t]`. All these matrices commute, so
  -- `exp (-L t) * (1 + t X)` has derivative zero on `[0, 1]`.
  let G (s : ℝ) : Matrix n n ℂ := (1 + s • X)⁻¹ * X
  let L (t : ℝ) : Matrix n n ℂ := ∫ s in 0..t, G s
  have hL_comm {Y : Matrix n n ℂ} (hY : Commute Y X) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      Commute Y (L t) :=
    commute_intervalIntegral ((continuousOn_inv_one_add_smul_mul hX).mono
      (Set.uIcc_subset_uIcc_left (by simpa using ht)))
      fun s ↦ (commute_inv_one_add_smul hY s).mul_right hY
  have hLL {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      Commute (L s) (L t) := hL_comm (hL_comm (.refl X) hs).symm ht
  have h_exp (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : HasDerivWithinAt
      (fun t ↦ NormedSpace.exp (-L t)) (NormedSpace.exp (-L s) * -G s) (Set.Icc 0 1) s :=
    hasDerivWithinAt_exp_neg_of_commute (hasDerivAt_integral_inv_one_add_smul_mul hX hs)
      fun _ ht ↦ hLL hs ht
  have h_deriv (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) : HasDerivWithinAt
      (fun t ↦ NormedSpace.exp (-L t) * (1 + t • X)) 0 (Set.Icc 0 1) s := by
    have h_line : HasDerivAt (fun t : ℝ ↦ 1 + t • X) X s := by
      -- `using!`: the two instances of the topology on matrices agree only up to defeq.
      simpa only [one_smul] using! ((hasDerivAt_id' s).smul_const X).const_add (1 : Matrix n n ℂ)
    have h_cancel : G s * (1 + s • X) = X := inv_one_add_smul_mul_mul_one_add_smul hX hs
    refine ((h_exp s hs).fun_mul h_line.hasDerivWithinAt).congr_deriv ?_
    simp [mul_assoc, h_cancel]
  have h_const : NormedSpace.exp (-L 1) * (1 + (1 : ℝ) • X) =
      NormedSpace.exp (-L 0) * (1 + (0 : ℝ) • X) :=
    eq_of_norm_sub_le_zero (norm_image_sub_le_of_norm_deriv_le_segment_01' h_deriv (by simp))
  have h_exp_inv : NormedSpace.exp (logOneAdd X) * NormedSpace.exp (-logOneAdd X) = 1 := by
    simp [← Matrix.exp_add_of_commute _ _ (Commute.refl (logOneAdd X)).neg_right]
  exact left_inv_eq_right_inv h_exp_inv (by simpa [L, G, logOneAdd] using h_const)

lemma det_one_add_eq_exp_trace_logOneAdd (hX : ‖X‖ ≤ 2⁻¹) :
    (1 + X).det = cexp (logOneAdd X).trace := by
  rw [← det_exp, exp_logOneAdd hX]

/-- If `1 + X` preserves the form `J`, that is `(1 + X)ᴴ * J * (1 + X) = J`, and `‖X‖ ≤ 1 / 2`, then
for `0 ≤ s ≤ 1` the integrand `G s = (1 + s • X)⁻¹ * X` of `logOneAdd X` satisfies
`(G s)ᴴ * J = -(J * G (1 - s))`. -/
lemma conjTranspose_inv_one_add_smul_mul_form {X J : Matrix n n ℂ}
    (h_form : (1 + X)ᴴ * J * (1 + X) = J) (h_norm : ‖X‖ ≤ 2⁻¹) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ((1 + s • X)⁻¹ * X)ᴴ * J = -(J * ((1 + (1 - s) • X)⁻¹ * X)) := by
  set A : Matrix n n ℂ := 1 + s • X
  set A' : Matrix n n ℂ := 1 + (1 - s) • X
  have h_adj : Xᴴ * J * (1 + X) = -(J * X) := by
    rw [conjTranspose_add, conjTranspose_one] at h_form
    linear_combination (norm := noncomm_ring) h_form
  have h_inv : A * A⁻¹ = 1 := mul_nonsing_inv _ (det_one_add_smul_ne_zero h_norm hs).isUnit
  have h_inv' : A' * A'⁻¹ = 1 :=
    mul_nonsing_inv _ (det_one_add_smul_ne_zero h_norm (Set.Icc.one_sub_mem hs)).isUnit
  have h_line : Aᴴ * (J * (1 + X)) = J * A' :=
    calc Aᴴ * (J * (1 + X)) = J * (1 + X) + s • (Xᴴ * J * (1 + X)) := by
          simp [A, add_mul, mul_assoc, star_trivial]
      _ = J * A' := by
          simp [h_adj, A', mul_add J, sub_smul, mul_sub, add_sub_assoc, ← sub_eq_add_neg]
  calc (A⁻¹ * X)ᴴ * J = Xᴴ * A⁻¹ᴴ * (J * A') * A'⁻¹ := by
        simp only [conjTranspose_mul, mul_assoc, h_inv', mul_one]
    _ = Xᴴ * (A * A⁻¹)ᴴ * (J * (1 + X)) * A'⁻¹ := by
        simp only [← h_line, conjTranspose_mul, mul_assoc]
    _ = -(J * (A'⁻¹ * X)) := by
        rw [h_inv, conjTranspose_one, mul_one, ← mul_assoc, h_adj, neg_mul, mul_assoc,
          commute_inv_one_add_smul (.refl X)]

/-- Let `g` be in `USign ε`, the unitary group of the sign matrix `J = signMatrix ε`, with
Hilbert–Schmidt distance at most `1 / 2` from `1`. Then its logarithm `L = logOneAdd (g - 1)` lies
in the Lie algebra `unitaryLie J`, that is, `Lᴴ * J + J * L = 0`. -/
lemma logOneAdd_mem_unitaryLie {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} (g : USign ε)
    (h_near : ‖((g : GL n ℂ) : Matrix n n ℂ) - 1‖ ≤ 2⁻¹) :
    logOneAdd (((g : GL n ℂ) : Matrix n n ℂ) - 1) ∈ unitaryLie (signMatrix ε) := by
  -- Let `J = signMatrix ε`, `X = g - 1` and `G s = (1 + s X)⁻¹ X`. From `gᴴ J g = J` we get
  -- `(G s)ᴴ J = -J G (1 - s)`; integrate over `s`.
  set X : Matrix n n ℂ := ((g : GL n ℂ) : Matrix n n ℂ) - 1
  let G (s : ℝ) : Matrix n n ℂ := (1 + s • X)⁻¹ * X
  have h_form : (1 + X)ᴴ * signMatrix ε * (1 + X) = signMatrix ε := by
    rw [add_sub_cancel]
    exact g.property
  have h_reflect (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) 1) :
      (G s)ᴴ * signMatrix ε = -(signMatrix ε * G (1 - s)) :=
    conjTranspose_inv_one_add_smul_mul_form h_form h_near (by simpa using hs)
  have hG : ContinuousOn G (Set.uIcc 0 1) := continuousOn_inv_one_add_smul_mul h_near
  let adj : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := (ContinuousLinearMap.mul ℝ _).flip (signMatrix ε) ∘L
    (starL' ℝ (A := Matrix n n ℂ)).toContinuousLinearMap
  have h_left : ∫ s in 0..1, (G s)ᴴ * signMatrix ε = (logOneAdd X)ᴴ * signMatrix ε :=
    adj.intervalIntegral_comp_comm hG.intervalIntegrable
  have h_right : ∫ s in 0..1, signMatrix ε * G s = signMatrix ε * logOneAdd X :=
    (ContinuousLinearMap.mul ℝ _ (signMatrix ε)).intervalIntegral_comp_comm hG.intervalIntegrable
  change (logOneAdd X)ᴴ * signMatrix ε + signMatrix ε * logOneAdd X = 0
  rw [← h_left, ← h_right, integral_congr h_reflect, integral_neg,
    integral_comp_sub_left (fun s ↦ signMatrix ε * G s)]
  simp

/-- If `X` has Hilbert–Schmidt norm at most `1`, then `exp X` is within `2 * ‖X‖` of `1`. -/
lemma norm_exp_sub_one_le (hX : ‖X‖ ≤ 1) : ‖NormedSpace.exp X - 1‖ ≤ 2 * ‖X‖ := by
  -- Compare the series `∑ X ^ (i + 1) / (i + 1)!` with the series of `exp ‖X‖ - 1`.
  have h_matrix : HasSum (fun i : ℕ ↦ ((i + 1).factorial : ℝ)⁻¹ • X ^ (i + 1))
      (NormedSpace.exp X - 1) := by
    -- `using!`: the two instances of the topology on matrices agree only up to defeq.
    simpa using! (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) X)
  have h_real : HasSum (fun i : ℕ ↦ ((i + 1).factorial : ℝ)⁻¹ * ‖X‖ ^ (i + 1))
      (Real.exp ‖X‖ - 1) := by
    simpa [← Real.exp_eq_exp_ℝ] using
      (hasSum_nat_add_iff' 1).2 (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖X‖)
  calc ‖NormedSpace.exp X - 1‖ ≤ Real.exp ‖X‖ - 1 := h_matrix.norm_le_of_bounded h_real fun i ↦ by
        grw [norm_smul_of_nonneg (by positivity), norm_pow_le' X i.succ_pos]
    _ ≤ 2 * ‖X‖ := by grw [le_abs_self (_ - 1), Real.abs_exp_sub_one_le (by simpa), abs_norm]

/-- If `X` has Hilbert–Schmidt norm at most `1 / 2`, then `logOneAdd X`, the integral of
`(1 + s • X)⁻¹ * X` over `[0, 1]`, has norm at most `2 * ‖X‖`. -/
lemma norm_logOneAdd_le (hX : ‖X‖ ≤ 2⁻¹) : ‖logOneAdd X‖ ≤ 2 * ‖X‖ := by
  have h_integrand (s : ℝ) (hs : s ∈ Set.uIoc (0 : ℝ) 1) : ‖(1 + s • X)⁻¹ * X‖ ≤ 2 * ‖X‖ := by
    have h_smul : ‖s • X‖ ≤ 2⁻¹ := norm_smul_le_of_le_one s hX (by grind)
    have h_near : ‖(1 + s • X)⁻¹ - 1‖ ≤ 1 := by linarith [norm_inv_one_add_sub_one_le h_smul]
    calc ‖(1 + s • X)⁻¹ * X‖ = ‖X + ((1 + s • X)⁻¹ - 1) * X‖ := by simp [sub_one_mul]
      _ ≤ 2 * ‖X‖ := by grw [norm_add_le, norm_mul_le, h_near, one_mul, two_mul]
  simpa [logOneAdd] using norm_integral_le_of_norm_le_const h_integrand

/-- If `P` is an orthogonal projection and `X` has Hilbert–Schmidt norm at most `ρ`, then so has
`P * X`. -/
lemma norm_proj_mul_le (hP : IsStarProjection P) (hX : ‖X‖ ≤ ρ) : ‖P * X‖ ≤ ρ := by
  -- `2 * P - 1` is unitary, and `2 • (P * X) = (2 * P - 1) * X + X`.
  have h_two : (2 : ℝ) • (P * X) = (2 * P - 1) * X + X := by
    rw [sub_mul, one_mul, sub_add_cancel, two_mul, add_mul, two_smul]
  have h_sum : 2 * ‖P * X‖ ≤ ‖X‖ + ‖X‖ := by
    grw [← norm_smul_of_nonneg zero_le_two, h_two, norm_add_le,
      frobenius_norm_mul_of_unitary hP.two_mul_sub_one_mem_unitary.1]
  linarith

/-- The diagonal matrix whose entry at `i` is `1` if `p i` holds and `0` otherwise. It is the
coordinate projection onto the indices satisfying `p`. -/
def coordProj (p : n → Prop) [DecidablePred p] : Matrix n n ℂ :=
  diagonal fun i : n ↦ if p i then 1 else 0

lemma isStarProjection_coordProj (p : n → Prop) [DecidablePred p] :
    IsStarProjection (coordProj p) := by
  simp [isStarProjection_iff', coordProj, star_eq_conjTranspose, Pi.star_def, ← ite_and, apply_ite]

/-- Replacing some entries of a matrix by `0` does not increase its Hilbert–Schmidt norm. -/
lemma norm_entryMask_le {n : Type} [Fintype n] {X : Matrix n n ℂ} {r : n → n → Prop}
    [DecidableRel r] : ‖entryMask r X‖ ≤ ‖X‖ := by
  simp only [frobenius_norm_def]
  gcongr with i _ j _
  by_cases hij : r i j <;> simp [hij]

/-- If `X` has Hilbert–Schmidt distance less than `1` from the identity, then the real spectrum of
`X + star X` is positive. -/
lemma pos_of_mem_spectrum_add_star (h_near : ‖X - 1‖ < 1) {x : ℝ}
    (hx : x ∈ spectrum ℝ (X + star X)) : 0 < x := by
  -- For real `x ≤ 0`, up to the factor `x - 2` the matrix `x - (X + star X)` is `1 - W` with
  -- `‖W‖ < 2 / (2 - x) ≤ 1`, hence invertible.
  by_contra! h_nonpos
  have h_pos : 0 < 2 - x := by linarith
  let W : Matrix n n ℂ := (2 - x)⁻¹ • (1 - X - star (X - 1))
  have hW : ‖W‖ < 1 := by
    rw [norm_smul_of_nonneg (inv_pos.2 h_pos).le, inv_mul_lt_one₀ h_pos]
    grw [norm_sub_le, norm_star, norm_sub_rev 1 X]
    linarith
  have h_eq : algebraMap ℝ (Matrix n n ℂ) x - (X + star X) = (x - 2) • (1 - W) := by
    simp only [W, Algebra.algebraMap_eq_smul_one, star_sub, star_one]
    match_scalars <;> field
  rw [spectrum.mem_iff, h_eq] at hx
  exact hx ((isUnit_one_sub_of_norm_lt_one hW).smul (Units.mk0 (x - 2) (by linarith)))

/-- A matrix `X` at Hilbert–Schmidt distance less than `1` from the identity is accretive, that is,
`X + Xᴴ` is positive definite. -/
lemma isAccretive_of_norm_sub_one_lt (h_near : ‖X - 1‖ < 1) : X.IsAccretive := by
  rw [Matrix.IsAccretive, ← star_eq_conjTranspose]
  exact ((StarOrderedRing.isStrictlyPositive_iff_spectrum_pos _ (.add_star_self X)).2
    fun _ hx ↦ pos_of_mem_spectrum_add_star h_near hx).posDef

end New.DiscreteSeries

end FrobeniusNormTools

end
