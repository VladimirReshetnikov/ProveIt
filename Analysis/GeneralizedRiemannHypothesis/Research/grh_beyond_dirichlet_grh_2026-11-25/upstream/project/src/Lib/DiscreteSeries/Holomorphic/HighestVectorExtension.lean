import Lib.General.Analysis.MeanValueAndTaylor
import Lib.General.LinearAlgebra.PolarDecomposition

/-!
# Exponentials in U(diag ε) and holomorphic extension of coefficients of highest vectors

The group is `New.USign ε = U(diag ε)` with compact subgroup `New.maxCompactU ε = U(diag ε) ∩ U(n)`.
Every element of the compact subgroup is an exponential, and every element of the group is a product
of two exponentials, so each element is joined to `1` by an analytic path in the group. A function
`F` on a product of copies of this group is holomorphic of weight `u` for the order `o`
(`New.IsHolOfWeight ε o u F ε'`) if it extends analytically to products `h * b` of tuples by
`F' (h * b) = (∏ τ, diagChar (u τ) (b τ)) * F h`. Here each `b τ` is triangular for `o`, and `h τ`,
`b τ` are block diagonal for `ε'` (no condition for `ε' = 1`). For injective `o`, products of
principal minors `New.weightMinors` of dominant weights (`weightMinors l g` is the product over
integers `t` of the principal minor of `g` on `{i | t ≤ l i}`, divided by `det g` when `t ≤ 0`) and
coefficients of highest vectors are such functions. For dominant weights the file computes their
weighted means over circles and, for a single copy of the group, their integrals against
`conj (weightMinors w)` over `New.maxCompactU ε`.

## Main definitions and results

* `New.exists_expU_eq_maxCompactU`: an element of the compact subgroup
  `New.maxCompactU ε = U(diag ε) ∩ U(n)` is the exponential of a block diagonal element of the Lie
  algebra (take the logarithm by the functional calculus).
* `New.exists_eq_expU_mul_expU`: every element of the group is a product of two exponentials, by the
  polar decomposition `New.exists_polar`.
* `New.isHolOfWeight_weightMinors`, `New.HCParam.IsKHighest.isHolOfWeight_coeffMap`: products of
  principal minors `New.weightMinors` and coefficients of highest vectors are holomorphic of a
  weight (`New.IsHolOfWeight`).
* `New.IsHolOfWeight.integral_mul_conj_weightMinors`: the integral of `F` against
  `conj (weightMinors w)` over the compact group `New.maxCompactU ε`.

Notions from other files:
* `New.unitaryLie J`, `New.expU`: the Lie algebra of U(J), made of the matrices `X` with
  `Xᴴ J + J X = 0`, and its exponential map to U(J).
* `New.blockDiagAlg ε`: the matrices that commute with `diag ε` (`New.signMatrix ε`), that is the
  block diagonal matrices for the signs `ε`.
* `New.IsBorelMatrix o b`: `b` is invertible and `b i j = 0` whenever `o j < o i`.
* `New.diagChar w b`: the product `∏ i, b i i ^ w i` of powers of the diagonal entries.
* `New.IsKDominant ε o w`: `w j ≤ w i` whenever `ε i = ε j` and `o i < o j`.

## Relation to the literature

Known result: the coefficient of the highest vector of a holomorphic discrete series representation
and its reproducing property. Here the setting is powers of U(p,q), using functions on the group
that extend holomorphically to the group times a Borel subgroup instead of the bounded domain.
Source: Harish-Chandra, Representations of semisimple Lie groups IV-VI, Amer. J. Math. 77 (1955), 78
(1956); A. Knapp (1986); A. Koranyi, A simplified approach to the holomorphic discrete series, arXiv
2312.16350.
-/

/-! ## Exponentials in U(diag ε) and its maximal compact subgroup -/

section ExpSurjective

open Matrix Complex Norms.L2Operator spectrum

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}

/-- Every `k` in `K = U(diag ε) ∩ U(n)` is `exp X` for some `X` in the Lie algebra of `U(diag ε)`
that commutes with `diag ε`. -/
theorem New.exists_expU_eq_maxCompactU (k : maxCompactU ε) :
    ∃ X : unitaryLie (signMatrix ε),
      expU X = (k : USign ε) ∧ (X : Matrix n n ℂ) ∈ blockDiagAlg ε := by
  -- A unitary matrix is the exponential of its logarithm `cfc (arg · * I) k`; the logarithm is
  -- skew-Hermitian and, like `k`, commutes with `signMatrix ε`.
  let A : Matrix n n ℂ := (k : USign ε)
  let L : Matrix n n ℂ := cfc (fun z : ℂ ↦ z.arg * I) A
  have h_unitary : A ∈ unitaryGroup n ℂ := U_one_mem_unitaryGroup ⟨_, k.property⟩
  have h_comm : Commute A (signMatrix ε) :=
    (DiscreteSeries.mem_blockDiagAlg_iff_commute.1 (mem_maxCompactU.1 k.property)).symm
  have h_log_comm : Commute L (signMatrix ε) :=
    h_comm.cfc ((isStarNormal_of_mem_unitary h_unitary).commute_star_left h_comm) _
  have h_skew : Lᴴ = -L := by simp [L, ← star_eq_conjTranspose, ← cfc_star, cfc_neg]
  have h_lie : L ∈ unitaryLie (signMatrix ε) := by simp [unitaryLie, h_skew, h_log_comm.eq]
  -- the spectrum lies on the unit circle, where `exp (arg z * I) = z`
  have h_exp : ∀ z ∈ spectrum ℂ A, cexp (z.arg * I) = z := fun z hz ↦ by
    have h_norm : ‖z‖ = 1 := by simpa using subset_circle_of_unitary h_unitary hz
    simpa [h_norm] using norm_mul_exp_arg_mul_I z
  have h_exp_log : NormedSpace.exp L = A := by
    rw [← CFC.complex_exp_eq_normedSpace_exp,
      ← cfc_comp' (hf := (finite_spectrum A).continuousOn _) cexp, cfc_congr h_exp, cfc_id' ℂ A]
  exact ⟨⟨L, h_lie⟩, Subtype.ext (Units.ext h_exp_log),
    DiscreteSeries.mem_blockDiagAlg_iff_commute.2 h_log_comm.symm⟩

/-- Every element of `U(diag ε)` is a product of two exponentials. -/
theorem New.exists_eq_expU_mul_expU (g : USign ε) :
    ∃ X Y : unitaryLie (signMatrix ε), g = expU X * expU Y := by
  -- in the polar decomposition `g = k * expU Y` the factor `k` is an exponential too
  obtain ⟨k, z, -, g_eq, Y, exp_Y⟩ := exists_polar g
  obtain ⟨X, exp_X, -⟩ := exists_expU_eq_maxCompactU k
  exact ⟨X, Y, by rw [exp_X, exp_Y, g_eq]⟩

end ExpSurjective

/-!
## Holomorphic functions of weight u: coefficients of highest vectors and circle means

The extension of coefficients and the circle mean both use a local factorisation `y = a * b` near
`1` with `b` triangular, which the inverse function theorem gives (`New.exists_borel_chart`).
-/

namespace New

open Matrix Finset Complex Topology Circle Filter DiscreteSeries MeasureTheory Metric
  ComplexConjugate Norms.L2Operator ContinuousLinearMap U

variable {n Φ : Type} [Fintype n] [DecidableEq n] [Fintype Φ] (ε ε' : n → ℤˣ) (o : n → ℤ)

/-- The part of a matrix strictly below the diagonal for the order `o`, inside the blocks of `ε`. -/
@[simp]
noncomputable abbrev lowerMask : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  entryMask fun i j ↦ o j < o i ∧ ε i = ε j

/-- The real linear map `X ↦ N - J Nᴴ J` on complex matrices, where `J = diag ε` and `N` is
`lowerMask ε' o X` plus `c` times the diagonal of `X`. -/
noncomputable def lowerLiePart (c : ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  (1 - mulLeftRight ℝ (Matrix n n ℂ) (signMatrix ε) (signMatrix ε) * starL' (A := Matrix n n ℂ) ℝ) *
    (lowerMask ε' o + c • entryMask Eq).restrictScalars ℝ

/-- The values of `lowerLiePart` lie in the Lie algebra of `U(diag ε)`. -/
lemma lowerLiePart_mem_unitaryLie (c : ℂ) (Z : Matrix n n ℂ) :
    lowerLiePart ε ε' o c Z ∈ unitaryLie (signMatrix ε) := by
  let N : Matrix n n ℂ := lowerMask ε' o Z + c • entryMask Eq Z
  let J : Matrix n n ℂ := signMatrix ε
  have J_sq : J * J = 1 := IsHermitianInvolution.mul_self
  have J_herm : Jᴴ = J := IsHermitianInvolution.isHermitian.eq
  have h_left : (N - J * Nᴴ * J)ᴴ * J = Nᴴ * J - J * N := by
    simp [sub_mul, mul_assoc, J_sq, J_herm]
  have h_right : J * (N - J * Nᴴ * J) = J * N - Nᴴ * J := by
    simp [mul_sub, ← mul_assoc, J_sq]
  change (N - J * Nᴴ * J)ᴴ * J + J * (N - J * Nᴴ * J) = 0
  rw [h_left, h_right, sub_add_sub_cancel, sub_self]

/-- A chart at `1` adapted to the triangular matrices. Let `E` send `0` to `1` with strict
derivative the identity. Let `L` be real linear, with every `E (L Z)` block diagonal for `ε`, and
let `L Z` and `Z` have the same entries below the diagonal inside the blocks (`lowerMask` keeps
these entries). Then there is `ψ` with `ψ 1 = 0` and derivative the identity at `1` such that each
block diagonal `y` near `1` is the product of the block diagonal matrices `E (L (ψ y))` and
`1 + (1 - L) (ψ y)`, the second being invertible and triangular for the order `o`. -/
theorem exists_borel_chart (L : Matrix n n ℂ →L[ℝ] Matrix n n ℂ) {E : Matrix n n ℂ → Matrix n n ℂ}
    (E_deriv : HasStrictFDerivAt E (ContinuousLinearMap.id ℝ (Matrix n n ℂ)) 0)
    (E_zero : E 0 = 1) (hL_mem : ∀ Z : Matrix n n ℂ, E (L Z) ∈ blockDiagAlg ε)
    (hL_lower : ∀ Z : Matrix n n ℂ, lowerMask ε o (L Z) = lowerMask ε o Z) :
    ∃ ψ : Matrix n n ℂ → Matrix n n ℂ,
      (HasFDerivAt ψ (ContinuousLinearMap.id ℝ (Matrix n n ℂ)) 1 ∧ ψ 1 = 0) ∧
      ∀ᶠ y : Matrix n n ℂ in 𝓝 1, y ∈ blockDiagAlg ε →
        letI a : Matrix n n ℂ := E (L (ψ y))
        letI b : Matrix n n ℂ := 1 + (1 - L) (ψ y)
        IsBorelMatrix o b ∧ (a ∈ blockDiagAlg ε ∧ b ∈ blockDiagAlg ε) ∧ y = a * b := by
  -- `ψ` is the local inverse of `f`, which maps `0` to `1` with derivative `L + (1 - L) = id`.
  let f (x : Matrix n n ℂ) : Matrix n n ℂ := E (L x) * (1 + (1 - L) x)
  have f_zero : f 0 = 1 := by simp [f, E_zero]
  have f_deriv : HasStrictFDerivAt f
      (ContinuousLinearEquiv.refl ℝ (Matrix n n ℂ)).toContinuousLinearMap 0 := by
    have first : HasStrictFDerivAt (fun x ↦ E (L x)) (.comp (.id ℝ (Matrix n n ℂ)) L) 0 :=
      .comp 0 (by simpa using E_deriv) L.hasStrictFDerivAt
    exact (first.mul' (.const_add 1 (1 - L).hasStrictFDerivAt)).congr_fderiv
      (ContinuousLinearMap.ext fun Z ↦ by simp [E_zero])
  let ψ : Matrix n n ℂ → Matrix n n ℂ := f_deriv.localInverse f _ 0
  have ψ_one : ψ 1 = 0 := by simpa [f_zero] using f_deriv.localInverse_apply_image
  have ψ_deriv : HasFDerivAt ψ (ContinuousLinearMap.id ℝ (Matrix n n ℂ)) 1 := by
    simpa [f_zero] using f_deriv.to_localInverse.hasFDerivAt
  have right_inverse : ∀ᶠ y : Matrix n n ℂ in 𝓝 1, f (ψ y) = y := by
    simpa [f_zero] using f_deriv.eventually_right_inverse
  refine ⟨ψ, ⟨ψ_deriv, ψ_one⟩, ?_⟩
  -- Near `1`, `y = f x` is invertible, hence so are both factors.
  filter_upwards [right_inverse, Units.nhds 1] with y
  generalize ψ y = x
  rintro rfl h_unit h_mem
  obtain ⟨det_a, det_b⟩ : (E (L x)).det ≠ 0 ∧ (1 + (1 - L) x).det ≠ 0 := by
    simpa [f, isUnit_iff_isUnit_det] using h_unit
  have b_mem : 1 + (1 - L) x ∈ blockDiagAlg ε := by
    simpa [f, det_a] using mul_mem (blockDiagAlg.inv_mem (hL_mem x)) h_mem
  refine ⟨⟨fun i j hij ↦ ?_, det_b⟩, ⟨hL_mem x, b_mem⟩, rfl⟩
  -- Below the diagonal, `x - L x` vanishes inside the blocks by `hL_lower` and outside by `b_mem`.
  by_cases h_sign : ε i = ε j
  · have h_ne : i ≠ j := fun h_eq ↦ hij.ne (congrArg o h_eq.symm)
    simpa [h_sign, hij, h_ne, sub_eq_zero] using congr_fun₂ (hL_lower x).symm i j
  · exact mem_blockDiagAlg.1 b_mem i j h_sign

variable {ε ε' : n → ℤˣ} {o : n → ℤ} {M X : Type*} [AddCommGroup M] [Module ℂ M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Let `D` be a continuous family of `ℂ`-linear maps from `E` to a Banach space `X`. If
`t ↦ f (t • Y)` has derivative `D (t • Y) Y` at every real `t`, for all `Y`, then `f` is complex
differentiable at `0` with derivative `D 0`. -/
theorem hasFDerivAt_of_rays [CompleteSpace X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : E → X)
    (D : E → E →L[ℂ] X) (hD_cont : Continuous D)
    (h_ray : ∀ (Y : E) (t : ℝ), HasDerivAt (fun s : ℝ ↦ f (s • Y)) (D (t • Y) Y) t) :
    HasFDerivAt f (D 0) 0 := by
  -- `f Y - f 0` is the integral of the form `D` along the segment from `0` to `Y`.
  have ftc (Y : E) : ∫ t in (0 : ℝ)..1, D (t • Y) Y = f ((1 : ℝ) • Y) - f ((0 : ℝ) • Y) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ h_ray Y t)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
  have integral_eq (Y : E) : ∫ᶜ Z in .segment 0 Y, D Z = f Y - f 0 := by
    simp [curveIntegral_segment, AffineMap.lineMap, ftc]
  simpa [integral_eq] using HasFDerivAt.curveIntegral_segment_source (a := 0) hD_cont

/-- The product of principal minors `weightMinors w` is continuous along a continuous family of
invertible matrices. -/
@[fun_prop]
theorem DiscreteSeries.continuous_weightMinors {X : Type*} {w : n → ℤ} [TopologicalSpace X]
    {f : X → Matrix n n ℂ} (hf : Continuous f) (h_det : ∀ a : X, (f a).det ≠ 0) :
    Continuous fun a : X ↦ weightMinors w (f a) :=
  continuous_iff_continuousAt.2 fun a ↦
    (analyticAt_weightMinors (h_det a)).continuousAt.comp hf.continuousAt

/-- For an integer vector `w`, let `w.kTypeNormSq` be the integral of the squared norm of
`weightMinors w k` (a product of principal minors of `k`) for the Haar measure of
`K = U(diag ε) ∩ U(n)`. It is positive. -/
@[simp]
theorem kTypeNormSq_pos (w : HCParam ε) : 0 < w.kTypeNormSq := by
  -- The integrand is continuous, nonnegative and nonzero at `k = 1`.
  have h_cont : Continuous fun k : maxCompactU ε ↦ ‖weightMinors w (k : USign ε)‖ ^ 2 := by
    fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero])
  unfold HCParam.kTypeNormSq
  exact integral_pos_of_integrable_nonneg_nonzero (x := 1) h_cont
    (h_cont.integrable_of_hasCompactSupport (.of_compactSpace _)) (fun k ↦ sq_nonneg _) (by simp)

/-- For `|s| = 1` the matrix `diag (s ^ o)` is invertible and triangular for the order `o`. -/
@[simp]
theorem isBorelMatrix_diagonal (s : Circle) :
    IsBorelMatrix o (diagonal fun i : n ↦ (s : ℂ) ^ o i) := by
  simp [IsBorelMatrix, blockTriangular_diagonal, prod_eq_zero_iff, zpow_ne_zero]

/-- Let `ε'` be `1` or `ε`. An element of `U(diag ε)` that is block diagonal for `ε'` is joined to
`1` by a real analytic path of such elements. -/
theorem exists_analytic_path (hε : ε' = 1 ∨ ε' = ε) (g : USign ε)
    (hg : (g : Matrix n n ℂ) ∈ blockDiagAlg ε') :
    ∃ c : ℝ → USign ε,
      c 0 = 1 ∧
      c 1 = g ∧
      (∀ t : ℝ, AnalyticAt ℝ (fun s : ℝ ↦ (c s : Matrix n n ℂ)) t) ∧
      ∀ t : ℝ, (c t : Matrix n n ℂ) ∈ blockDiagAlg ε' := by
  have analytic (X : unitaryLie (signMatrix ε)) (t : ℝ) :
      AnalyticAt ℝ (fun s : ℝ ↦ (expU (s • X) : Matrix n n ℂ)) t :=
    (NormedSpace.exp_analytic _).comp (f := fun s : ℝ ↦ s • (X : Matrix n n ℂ)) (by fun_prop)
  obtain rfl | rfl := hε
  · -- No condition on the path: write `g` as a product of two exponentials.
    obtain ⟨X, Y, rfl⟩ := exists_eq_expU_mul_expU g
    exact ⟨fun t ↦ expU (t • X) * expU (t • Y), by simp, by simp,
      fun t ↦ (analytic X t).mul (analytic Y t), by simp⟩
  · -- Here `g` lies in the compact subgroup, so it is the exponential of a block diagonal `X`.
    obtain ⟨X, exp_X, X_mem⟩ := exists_expU_eq_maxCompactU ⟨g, mem_maxCompactU.2 hg⟩
    refine ⟨fun t ↦ expU (t • X), by simp, by simp [exp_X], analytic X, fun t ↦ ?_⟩
    rw [mem_blockDiagAlg_iff_commute] at X_mem ⊢
    exact (X_mem.smul_right t).exp_right

/-- A function on a product of copies of `U(diag ε)` that is holomorphic of weight `u` (with no
block condition) is continuous. -/
theorem IsHolOfWeight.continuous {u : Φ → n → ℤ} {F : (Φ → USign ε) → ℂ}
    (hF : IsHolOfWeight ε o u F) : Continuous F := by
  -- Taking `b = 1`: `F` agrees with its extension `F'`, which is analytic at every `h`.
  obtain ⟨F', hF'⟩ := hF
  have at_one (h : Φ → USign ε) : AnalyticAt ℂ F' (fun τ ↦ h τ) ∧ F' (fun τ ↦ h τ) = F h := by
    simpa [IsBorelMatrix, blockTriangular_one, diagChar] using hF' h 1
  refine .congr (continuous_iff_continuousAt.2 fun h ↦ ?_) fun h ↦ (at_one h).2
  exact (at_one h).1.continuousAt.comp_of_eq (Continuous.continuousAt (by fun_prop)) rfl

/-- A function `F` that is holomorphic of weight `u` (with no block condition) transforms by the
character `u` under right translation by `diagTorus ε t = diag t`, for `t` with `|t i| = 1`. -/
theorem IsHolOfWeight.apply_mul_diagTorus {u : Φ → n → ℤ} {F : (Φ → USign ε) → ℂ}
    (hF : IsHolOfWeight ε o u F) (h : Φ → USign ε) (t : n → Circle) :
    F (h * fun _ : Φ ↦ diagTorus ε t) = (∏ τ : Φ, ∏ i : n, (t i : ℂ) ^ u τ i) * F h := by
  -- Evaluate the extension `F'` at `h * diagTorus ε t` in two ways: with `b = diagTorus ε t` and
  -- with `b = 1`.
  obtain ⟨F', hF'⟩ := hF
  let z (τ : Φ) : Matrix n n ℂ := h τ * diagTorus ε t
  have as_triangular : F' z = (∏ τ : Φ, ∏ i : n, (t i : ℂ) ^ u τ i) * F h := by
    simpa [z, diagTorus, diagChar] using (hF' h (fun _ ↦ diagTorus ε t) (fun _ ↦ by
      simp [IsBorelMatrix, diagTorus, blockTriangular_diagonal, prod_eq_zero_iff]) (by simp)).right
  have as_unitary : F' z = F (h * fun _ ↦ diagTorus ε t) := by
    simpa [z, Pi.mul_def, diagChar] using (hF' (fun τ ↦ h τ * diagTorus ε t) 1
      (by simp [IsBorelMatrix, blockTriangular_one]) (by simp)).right
  rw [← as_unitary, as_triangular]

/-- For injective `o`, weights `u τ` that are dominant within the blocks of `ε'` for the order `o`,
and invertible `a`, the function `g ↦ ∏ τ, weightMinors (u τ) (a * g τ)`, a product of principal
minors, is holomorphic of weight `u`: it extends analytically to products `g * b`, with `g` and `b`
block diagonal for `ε'` and `b` triangular, picking up the factor `∏ τ, diagChar (u τ) (b τ)`. -/
theorem isHolOfWeight_weightMinors {u : Φ → n → ℤ} (ho : o.Injective) (a : Matrix n n ℂ)
    (hu : ∀ τ : Φ, IsKDominant ε' o (u τ)) (ha_det : a.det ≠ 0) :
    IsHolOfWeight ε o u (fun g : Φ → USign ε ↦ ∏ τ : Φ, weightMinors (u τ) (a * g τ)) ε' := by
  -- The same formula, read on tuples of matrices, is the extension.
  refine ⟨fun z ↦ ∏ τ, weightMinors (u τ) (a * z τ), fun h b b_borel h_block ↦ ?_⟩
  have det_ah (τ : Φ) : (a * h τ).det ≠ 0 := by simp [ha_det, GeneralLinearGroup.det_ne_zero]
  have det_ahb (τ : Φ) : (a * (h τ * b τ)).det ≠ 0 := by
    simpa [← mul_assoc, det_mul] using mul_ne_zero (det_ah τ) (b_borel τ).2
  have minors_mul (τ : Φ) : weightMinors (u τ) (a * (h τ * b τ)) =
      diagChar (u τ) (b τ) * weightMinors (u τ) (a * h τ) := by
    rw [← mul_assoc, (hu τ).weightMinors_mul_borel ho (det_ah τ) (h_block τ).2 (b_borel τ),
      mul_comm]
  refine ⟨Finset.analyticAt_fun_prod univ fun τ _ ↦ ?_, by simp [minors_mul, prod_mul_distrib]⟩
  exact (analyticAt_weightMinors (det_ahb τ)).comp_of_eq
    (analyticAt_const.mul ((proj (R := ℂ) (φ := fun _ : Φ ↦ Matrix n n ℂ) τ).analyticAt _)) rfl

/-- Let `o` be injective. An element of `U(diag ε)` that is triangular for the order `o` is
diagonal, with entries `exp (θ i * I)` of norm one. -/
theorem IsBorelMatrix.exists_eq_diagonal_exp (ho : o.Injective) {t : USign ε}
    (ht : IsBorelMatrix o t) :
    ∃ θ : n → ℝ, (t : Matrix n n ℂ) = diagonal fun i : n ↦ cexp (θ i * I) := by
  -- The inverse of `t` is triangular and equals `signMatrix * tᴴ * signMatrix`: so `t` vanishes on
  -- both sides of the diagonal, and the diagonal entries have norm one.
  have norm_one (i : n) : ‖(t : Matrix n n ℂ) i i‖ = 1 := by
    have norm_inv : ‖(t : Matrix n n ℂ) i i‖⁻¹ = ‖(t : Matrix n n ℂ) i i‖ := by
      simp [← _root_.norm_inv, ← ht.inv_apply_diag ho i, signMatrix, abs_unit_intCast,
        inv_coe_eq_mul_conjTranspose_mul]
    field_simp [norm_ne_zero_iff.2 (ht.diag_ne_zero ho i)] at norm_inv
    nlinarith [norm_nonneg ((t : Matrix n n ℂ) i i)]
  refine ⟨fun i ↦ arg ((t : Matrix n n ℂ) i i), ext fun i j ↦ ?_⟩
  obtain rfl | hij := eq_or_ne i j
  · simpa [norm_one i] using (norm_mul_exp_arg_mul_I ((t : Matrix n n ℂ) i i)).symm
  · rw [diagonal_apply_ne _ hij]
    obtain h_lt | h_gt := (ho.ne hij).lt_or_gt
    · simpa [signMatrix, inv_coe_eq_mul_conjTranspose_mul] using ht.inv.1 h_lt
    · exact ht.1 h_gt

/-- Let `x` be a highest vector of weight `u` in the `gl n`-module `ρ` for the blocks of `ε'` and
the order `-o`, with `o` injective: `E a a` acts on `x` by `u a`, and `E a b` kills it if
`ε' a = ε' b` and `o a < o b`. Then a matrix `Y` that is block diagonal for `ε'` and upper
triangular for `o` acts on `x` by the scalar `∑ a, u a * Y a a`. -/
theorem HCParam.IsKHighest.apply_triangular (ho : o.Injective) {ρ : GlModule n M} {u : n → ℤ}
    {x : M} (hx : (toHCParam ε' (-o)).IsKHighest ρ u x) (Y : Matrix n n ℂ)
    (hY_block : Y ∈ blockDiagAlg ε') (hY_tri : Y.BlockTriangular o) :
    ρ Y x = (∑ a : n, u a * Y a a) • x := by
  obtain ⟨h_weight, h_kill⟩ := hx
  have off_diag (a b : n) (hab : b ≠ a) : Y a b • ρ.E a b x = 0 := by
    by_cases h_sign : ε' a = ε' b
    · obtain h_lt | h_gt := (ho.ne hab).lt_or_gt
      · simp [hY_tri h_lt]
      · simp [h_kill a b h_sign (neg_lt_neg h_gt)]
    · simp [mem_blockDiagAlg.1 hY_block a b h_sign]
  have row (a : n) : ∑ b : n, Y a b • ρ.E a b x = (u a * Y a a) • x := by
    rw [Fintype.sum_eq_single a (off_diag a), h_weight, smul_smul, mul_comm]
  simp [ρ.apply_eq_sum Y, sum_smul, row]

/-- Let `x` be a highest vector of weight `u` for the order `-o` and the blocks of `ε'` (see
`New.HCParam.IsKHighest.apply_triangular`), with `o` injective, and let `c` be a coefficient map for
`ρ` (`s ↦ c (h * expU (s • Y)) v` has derivative `c (h * expU (s • Y)) (ρ Y v)` for `Y` in the Lie
algebra). Right multiplication by an element `t` of `U(diag ε)` that is triangular for `o`
multiplies `c h x` by `diagChar u t = ∏ i, t i i ^ u i`. -/
theorem HCParam.IsKHighest.coef_mul_triangular (ho : o.Injective) {ρ : GlModule n M} {u : n → ℤ}
    {x : M} {c : USign ε → M →ₗ[ℂ] X} (hx : (toHCParam ε' (-o)).IsKHighest ρ u x)
    (hc : ρ.IsCoeffMap c) (h t : USign ε) (ht : IsBorelMatrix o t) :
    c (h * t) x = diagChar u t • c h x := by
  -- `t` is diagonal with entries `exp (θ i * I)`, so `t = exp Y` with `Y` diagonal.
  obtain ⟨θ, hθ⟩ := ht.exists_eq_diagonal_exp ho
  let Y : unitaryLie (signMatrix ε) :=
    ⟨diagonal fun a ↦ θ a * I, by simp [unitaryLie, signMatrix, mul_comm]⟩
  have exp_Y : expU Y = t := Subtype.ext (Units.ext (by simp [hθ, Y, exp_diagonal, exp_eq_exp_ℂ]))
  let lam : ℂ := ∑ a : n, u a * (θ a * I)
  have act_Y : ρ Y x = lam • x := by
    simp [hx.apply_triangular ho Y (diagonal_mem_blockDiagAlg _) (blockTriangular_diagonal _),
      lam, Y]
  -- Along `expU (s • Y)` the coefficient grows by the weight `lam` of `Y`; the factor `cexp` undoes
  -- it, so `f` is constant.
  let f (s : ℝ) : X := cexp ((1 - s) * lam) • c (h * expU (s • Y)) x
  have deriv_zero (s : ℝ) : HasDerivAt f 0 s := by
    have factor : HasDerivAt (fun s : ℝ ↦ cexp ((1 - s) * lam)) (cexp ((1 - s) * lam) * -lam) s :=
      ((hasDerivAt_mul_const lam).comp_const_sub 1 (s : ℂ)).cexp.comp_ofReal
    exact (factor.smul (hc h Y x s)).congr_deriv (by rw [act_Y, map_smul]; module)
  have f_const : f 1 = f 0 := is_const_of_deriv_eq_zero
    (fun s ↦ (deriv_zero s).differentiableAt) (fun s ↦ (deriv_zero s).deriv) 1 0
  simpa [f, lam, exp_Y, hθ, exp_sum, exp_int_mul, diagChar] using f_const

/-- Under the hypotheses of `New.HCParam.IsKHighest.coef_mul_triangular` (`x` highest of weight
`u`, `c` a coefficient map), the vector `diagChar u b • c h x` depends only on the product `h * b`
of `h` in `U(diag ε)` and an invertible triangular matrix `b`. -/
theorem HCParam.IsKHighest.diagChar_smul_coeffMap_eq (ho : o.Injective) {ρ : GlModule n M}
    {u : n → ℤ} {x : M} {c : USign ε → M →ₗ[ℂ] X} (hx : (toHCParam ε' (-o)).IsKHighest ρ u x)
    (hc : ρ.IsCoeffMap c) {h h' : USign ε} {b b' : Matrix n n ℂ} (hb : IsBorelMatrix o b)
    (hb' : IsBorelMatrix o b') (h_eq : (h' : Matrix n n ℂ) * b' = h * b) :
    diagChar u b' • c h' x = diagChar u b • c h x := by
  -- write `h' = h * t`; then `t = b * b'⁻¹` is triangular
  obtain ⟨t, rfl⟩ : ∃ t : USign ε, h * t = h' := mul_left_surjective h h'
  obtain rfl : t * b' = b := by simpa [mul_assoc] using h_eq
  have ht : IsBorelMatrix o t := by simpa [hb'.2] using hb.mul hb'.inv
  have char_mul : diagChar u (t * b') = diagChar u b' * diagChar u t := by
    simp only [diagChar, ht.mul_apply_diag ho hb', mul_zpow, prod_mul_distrib, mul_comm]
  rw [hx.coef_mul_triangular ho hc h t ht, smul_smul, char_mul]

variable [CompleteSpace X]

/-- The exponential of `lowerLiePart ε ε' o 0 Z = N - J Nᴴ J` is block diagonal for `ε'`. Here
`J = diag ε` and `N` is the part of `Z` below the diagonal for `o` inside the blocks of `ε'`. -/
lemma exp_lowerLiePart_zero_mem_blockDiagAlg (Z : Matrix n n ℂ) :
    NormedSpace.exp (lowerLiePart ε ε' o 0 Z) ∈ blockDiagAlg ε' := by
  have h_mem : lowerLiePart ε ε' o 0 Z ∈ blockDiagAlg ε' :=
    mem_blockDiagAlg.2 fun i j h_sign ↦ by simp [lowerLiePart, signMatrix, h_sign, Ne.symm h_sign]
  rw [mem_blockDiagAlg_iff_commute] at h_mem ⊢
  exact h_mem.exp_right

/-- Let `x` be highest of weight `u` for the order `-o` and the blocks of `ε'`, with `o` injective.
Then `lowerLiePart ε ε' o 0 Y = N - J Nᴴ J` acts on `x` as `N = lowerMask ε' o Y`: the strictly
upper triangular part `J Nᴴ J` kills `x`. -/
lemma HCParam.IsKHighest.apply_lowerLiePart_zero (ho : o.Injective) {ρ : GlModule n M}
    {u : n → ℤ} {x : M} (hx : (toHCParam ε' (-o)).IsKHighest ρ u x) (Y : Matrix n n ℂ) :
    ρ (lowerLiePart ε ε' o 0 Y) x = ρ (lowerMask ε' o Y) x := by
  let U : Matrix n n ℂ := signMatrix ε * (lowerMask ε' o Y)ᴴ * signMatrix ε
  have eq_lower_sub : lowerLiePart ε ε' o 0 Y = lowerMask ε' o Y - U := by
    simp [lowerLiePart, U, star_eq_conjTranspose]
  have U_block : U ∈ blockDiagAlg ε' :=
    mem_blockDiagAlg.2 fun i j hij ↦ by simp [U, signMatrix, Ne.symm hij]
  have U_tri : U.BlockTriangular o := fun i j hij ↦ by simp [U, signMatrix, hij.not_gt]
  have U_diag (a : n) : U a a = 0 := by simp [U, signMatrix]
  have U_apply : ρ U x = 0 := by simp [hx.apply_triangular ho U U_block U_tri, U_diag]
  rw [eq_lower_sub, map_sub, LinearMap.sub_apply, U_apply, sub_zero]

/-- The matrices `lowerLiePart ε ε' o 0 Z` and `Z` have the same entries below the diagonal for `o`
inside the blocks of `ε'`. -/
lemma lowerMask_lowerLiePart_zero (Z : Matrix n n ℂ) :
    lowerMask ε' o (lowerLiePart ε ε' o 0 Z) = lowerMask ε' o Z := by
  ext i j
  by_cases h_lower : o j < o i ∧ ε' i = ε' j
  · simp [lowerLiePart, signMatrix, h_lower, h_lower.1.asymm]
  · simp [h_lower]

/-- Let `x` be highest for the order `-o` and the blocks of `ε'`, with `o` injective, and let `c` be
a continuous coefficient map for `ρ` (its derivative along `exp (s • Y)` is given by `ρ Y`). Write
`v Z = lowerLiePart ε ε' o 0 Z = N - J Nᴴ J`, with `J = diag ε` and `N` the part of `Z` below the
diagonal inside the blocks of `ε'`. Then `Z ↦ c (h * exp (v Z)) x` is complex differentiable at `0`,
although `v` is only real linear. -/
theorem HCParam.IsKHighest.differentiableAt_coeffMap_expU (ho : o.Injective) {ρ : GlModule n M}
    {u : n → ℤ} {x : M} {c : USign ε → M →ₗ[ℂ] X} (hx : (toHCParam ε' (-o)).IsKHighest ρ u x)
    (hc : ρ.IsCoeffMap c) (hc_cont : ∀ y : M, Continuous fun h : USign ε ↦ c h y) (h : USign ε) :
    DifferentiableAt ℂ (fun Z : Matrix n n ℂ ↦
      c (h * expU ⟨lowerLiePart ε ε' o 0 Z, lowerLiePart_mem_unitaryLie ε ε' o 0 Z⟩) x) 0 := by
  let v (Z : Matrix n n ℂ) : unitaryLie (signMatrix ε) :=
    ⟨lowerLiePart ε ε' o 0 Z, lowerLiePart_mem_unitaryLie ε ε' o 0 Z⟩
  -- The upper part of `v Y` kills `x`, so the derivative along real rays is complex linear.
  let D (Z : Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] X :=
    (c (h * expU (v Z)) ∘ₗ ρ.ρ.flip x).toContinuousLinearMap ∘L lowerMask ε' o
  have D_cont : Continuous D := continuous_clm_apply.2 fun Y ↦ (hc_cont _).comp (by fun_prop)
  have D_apply (Y Z : Matrix n n ℂ) : D Z Y = c (h * expU (v Z)) (ρ (v Y : Matrix n n ℂ) x) := by
    simp [D, v, hx.apply_lowerLiePart_zero ho, -lowerMask]
  have ray (Y : Matrix n n ℂ) (t : ℝ) :
      HasDerivAt (fun t : ℝ ↦ c (h * expU (v (t • Y))) x) (D (t • Y) Y) t := by
    have v_smul (s : ℝ) : v (s • Y) = s • v Y := Subtype.ext (by simp [v])
    simpa only [D_apply, v_smul] using hc h (v Y) x t
  exact (hasFDerivAt_of_rays (fun Z ↦ c (h * expU (v Z)) x) D D_cont ray).differentiableAt

/-- Let `o` be injective. For each `τ` let `x τ` be a `K`-highest vector of weight `u τ` in the
`gl n`-module `ρ τ` for the parameter `-o` and signs `ε'`: each `E a a` acts on it by `u τ a`, and
`E a b` kills it when `ε' a = ε' b` and `o a < o b`. Let `c τ` be a continuous coefficient map for
`ρ τ`: the maps `c τ h : M → X` are linear, and `t ↦ c τ (h * exp (t • Y)) v` has derivative
`c τ (h * exp (t • Y)) (ρ τ Y v)` for `Y` in the Lie algebra of `U(diag ε)`. Let `ℓ` be a continuous
multilinear form. Then `h ↦ ℓ fun τ ↦ c τ (h τ) (x τ)` is holomorphic of weight `u`: it extends
analytically to products `h * b` with `b` invertible and triangular for `o` and `h`, `b` block
diagonal for `ε'`, with factor `∏ τ, diagChar (u τ) (b τ)`. -/
theorem HCParam.IsKHighest.isHolOfWeight_coeffMap (ho : o.Injective) {ρ : Φ → GlModule n M}
    {u : Φ → n → ℤ} {x : Φ → M} {c : Φ → USign ε → M →ₗ[ℂ] X}
    (hx : ∀ τ : Φ, (toHCParam ε' (-o)).IsKHighest (ρ τ) (u τ) (x τ))
    (hc : ∀ τ : Φ, (ρ τ).IsCoeffMap (c τ)) (ℓ : ContinuousMultilinearMap ℂ (fun _ : Φ ↦ X) ℂ)
    (hc_cont : ∀ (τ : Φ) (y : M), Continuous fun h : USign ε ↦ c τ h y) :
    IsHolOfWeight ε o u (fun h : Φ → USign ε ↦ ℓ fun τ : Φ ↦ c τ (h τ) (x τ)) ε' := by
  -- Extend `h ↦ c τ h (x τ)` by `extend τ (h * b) = diagChar (u τ) b • c τ h (x τ)`, show that this
  -- is well defined and complex differentiable (in the chart of `exists_borel_chart`), and compose
  -- with `ℓ`. The set `factors y` holds the factorisations of the block diagonal part of `y`.
  let factors (y : Matrix n n ℂ) : Set (USign ε × Matrix n n ℂ) := {(h, b) |
    IsBorelMatrix o b ∧ (↑h ∈ blockDiagAlg ε' ∧ b ∈ blockDiagAlg ε') ∧ blockDiagPart ε' y = h * b}
  have well_defined (τ : Φ) (y : Matrix n n ℂ) :
      ∃ z : X, ∀ p ∈ factors y, diagChar (u τ) p.2 • c τ p.1 (x τ) = z := by
    refine ((factors y).pairwise_eq_iff_exists_eq _).1 ?_
    rintro ⟨h', b'⟩ ⟨hb', -, y_eq'⟩ ⟨h, b⟩ ⟨hb, -, y_eq⟩ -
    exact (hx τ).diagChar_smul_coeffMap_eq ho (hc τ) hb hb' (y_eq'.symm.trans y_eq)
  choose extend extend_eq using well_defined
  -- The chart `Z ↦ exp (v Z) * (1 + Z - v Z)` at `1`, with local inverse `ψ`.
  let v : Matrix n n ℂ →L[ℝ] Matrix n n ℂ := lowerLiePart ε ε' o 0
  obtain ⟨ψ, ⟨ψ_deriv, ψ_one⟩, chart⟩ := exists_borel_chart ε' o v hasStrictFDerivAt_exp_zero
    NormedSpace.exp_zero exp_lowerLiePart_zero_mem_blockDiagAlg lowerMask_lowerLiePart_zero
  -- the real derivative of `ψ` at `1` is the identity, which is complex linear
  have ψ_complex : HasFDerivAt ψ (ContinuousLinearMap.id ℂ (Matrix n n ℂ)) 1 :=
    .of_isLittleO ψ_deriv.isLittleO
  have differentiable (τ : Φ) (y : Matrix n n ℂ) (hy : (factors y).Nonempty) :
      DifferentiableAt ℂ (extend τ) y ∧ ∀ᶠ y' in 𝓝 y, (factors y').Nonempty := by
    obtain ⟨⟨h, b⟩, hb : IsBorelMatrix o b, ⟨h_mem, b_mem⟩, y_eq : blockDiagPart ε' y = h * b⟩ := hy
    -- `shift` takes the block diagonal part of `h⁻¹ * y' * b⁻¹`, so sends `y` to `1`.
    let shift : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
      blockDiagPart ε' ∘L mulLeftRight ℂ (Matrix n n ℂ) (h : Matrix n n ℂ)⁻¹ b⁻¹
    have shift_y : shift y = 1 := by simp [shift, hb.2, y_eq, h_mem, b_mem]
    let unit (Z : Matrix n n ℂ) : USign ε := h * expU ⟨v Z, lowerLiePart_mem_unitaryLie ε ε' o 0 Z⟩
    let tri (Z : Matrix n n ℂ) : Matrix n n ℂ := 1 + (1 - v) Z
    have factor : ∀ᶠ y' in 𝓝 y, IsBorelMatrix o (tri (ψ (shift y'))) ∧
        (unit (ψ (shift y')), tri (ψ (shift y')) * b) ∈ factors y' := by
      filter_upwards [shift.cont.tendsto' y 1 shift_y chart] with y' hy'
      obtain ⟨tri_borel, ⟨exp_mem, tri_mem⟩, shift_eq⟩ := hy' (blockDiagPart_mem _)
      refine ⟨tri_borel, tri_borel.mul hb, ⟨mul_mem h_mem exp_mem, mul_mem tri_mem b_mem⟩, ?_⟩
      simpa [shift, unit, tri, h_mem, b_mem, hb.2, mul_assoc] using
        congrArg (fun z : Matrix n n ℂ ↦ h * z * b) shift_eq
    refine ⟨?_, factor.mono fun y' hy' ↦ Set.nonempty_of_mem hy'.2⟩
    let inChart (Z : Matrix n n ℂ) : X :=
      (diagChar (u τ) (1 + Z) * diagChar (u τ) b) • c τ (unit Z) (x τ)
    have comp_diff : DifferentiableAt ℂ (inChart ∘ ψ) (shift y) := by
      rw [shift_y]
      refine .comp 1 ?_ ψ_complex.differentiableAt
      rw [ψ_one]
      exact .smul (by fun_prop (disch := simp) [diagChar])
        ((hx τ).differentiableAt_coeffMap_expU ho (hc τ) (hc_cont τ) h)
    -- Near `y` we have `extend τ = inChart ∘ ψ ∘ shift`, because `v Z` has zero diagonal.
    have tri_diag (Z : Matrix n n ℂ) (i : n) : tri Z i i = (1 + Z) i i := by
      simp [tri, v, lowerLiePart, signMatrix]
    refine (comp_diff.comp y shift.differentiableAt).congr_of_eventuallyEq (factor.mono ?_)
    rintro y' ⟨tri_borel, h_factor⟩
    change extend τ y' = inChart (ψ (shift y'))
    simp only [← extend_eq τ y' _ h_factor, inChart, diagChar, tri_borel.mul_apply_diag ho hb,
      tri_diag, mul_zpow, prod_mul_distrib]
  refine ⟨fun z ↦ ℓ fun τ ↦ extend τ (z τ), fun h b hb h_block ↦ ?_⟩
  have mem (τ : Φ) : (h τ, b τ) ∈ factors (h τ * b τ) := ⟨hb τ, h_block τ, by simp [h_block]⟩
  refine ⟨analyticAt_of_eventually_differentiableAt ?_,
    by simp [← extend_eq _ _ (h _, b _) (mem _), ℓ.map_smul_univ]⟩
  have all_near : ∀ᶠ y in 𝓝 (fun τ ↦ h τ * b τ), ∀ τ, DifferentiableAt ℂ (extend τ) (y τ) :=
    nhds_pi.le (eventually_pi fun τ ↦
      (differentiable τ _ ⟨_, mem τ⟩).2.mono fun y hy ↦ (differentiable τ y hy).1)
  exact all_near.mono fun y hy ↦ ℓ.analyticAt.differentiableAt.comp y (by fun_prop)

variable (ε o) in
/-- The translates of `x` by the circle `diag (s ^ o)` factor through an entire curve `A` from `1`
and a fixed block diagonal triangular `b`: `diag (s ^ o) * x = A s * (diag (s ^ o) * b)` for
`|s| = 1`. The diagonal of `b` gives the product of minors `weightMinors w x`. -/
structure IsCircleFactorization (w : n → ℤ) (x : Matrix n n ℂ) (A : ℂ → Matrix n n ℂ)
    (b : Matrix n n ℂ) : Prop where
  /-- `b` is block diagonal for `ε`. -/
  mem_blockDiagAlg : b ∈ blockDiagAlg ε
  /-- `b` is invertible and triangular for the order `o`. -/
  isBorelMatrix : IsBorelMatrix o b
  /-- `A` is entire. -/
  analyticAt : ∀ s : ℂ, AnalyticAt ℂ A s
  /-- `A` starts at the identity. -/
  apply_zero : A 0 = 1
  /-- The product of minors `weightMinors w x` is `∏ i, b i i ^ w i`. -/
  weightMinors_eq : weightMinors w x = diagChar w b
  /-- The factorisation on the unit circle. -/
  diagonal_mul_eq : ∀ s : Circle,
    diagonal (fun i : n ↦ (s : ℂ) ^ o i) * x = A s * (diagonal (fun i : n ↦ (s : ℂ) ^ o i) * b)

/-- For `|s| = 1`, conjugation by `diag (s ^ o)` multiplies the entry `(i, j)` of `lowerMask ε o Z`
(the entries `Z i j` with `o j < o i` and `ε i = ε j`, others `0`) by `s ^ (o i - o j)`, a natural
power of `s`. -/
lemma diagonal_mul_one_add_lowerMask (s : Circle) (Z : Matrix n n ℂ) :
    diagonal (fun i : n ↦ (s : ℂ) ^ o i) * (1 + lowerMask ε o Z) =
      (1 + of fun i j : n ↦ (s : ℂ) ^ (o i - o j).toNat * lowerMask ε o Z i j) *
        diagonal fun i : n ↦ (s : ℂ) ^ o i := by
  ext i j
  simp only [diagonal_mul, mul_diagonal, Matrix.add_apply, of_apply]
  by_cases h : o j < o i ∧ ε i = ε j
  · have h_pow : (s : ℂ) ^ (o i - o j).toNat * (s : ℂ) ^ o j = (s : ℂ) ^ o i := by
      rw [← zpow_natCast, ← zpow_add₀ (coe_ne_zero s), Int.toNat_of_nonneg (by omega),
        sub_add_cancel]
    rw [Matrix.one_apply_ne (show i ≠ j by grind), zero_add, zero_add, ← h_pow]
    ring
  · obtain rfl | h_ne := eq_or_ne i j <;> simp [*]

/-- For injective `o` the matrix `1 + lowerMask ε o Z`, which has diagonal entries `1` and off the
diagonal the entries `Z i j` with `o j < o i` and `ε i = ε j` (others `0`), is invertible and
triangular for the order `-o`. -/
lemma isBorelMatrix_one_add_lowerMask (ho : o.Injective) (Z : Matrix n n ℂ) :
    IsBorelMatrix (-o) (1 + lowerMask ε o Z) := by
  have triangular : (1 + lowerMask ε o Z).BlockTriangular (-o) := fun i j hij ↦ by
    simp [(neg_lt_neg_iff.1 hij : o i < o j).not_gt, show i ≠ j by grind]
  refine ⟨triangular, ?_⟩
  rw [det_eq_prod_diag_of_blockTriangular (neg_injective.comp ho) triangular]
  simp

/-- Let `o` be injective, `w` dominant within the blocks of `ε` (`w j ≤ w i` whenever `ε i = ε j`
and `o i < o j`) and `P` a neighbourhood of `1`. Then each block diagonal `x` (commuting with
`diag ε`) near `1` has a circle factorisation (`New.IsCircleFactorization`), and its entire curve
`A` maps the closed unit disc into `P`. Such a factorisation is an entire curve `A` from `1` and a
fixed block diagonal `b`, triangular for `o`, with `diag (s ^ o) * x = A s * (diag (s ^ o) * b)` for
`|s| = 1`, where the diagonal of `b` gives `weightMinors w x`. -/
lemma eventually_exists_isCircleFactorization (ho : o.Injective) {w : n → ℤ}
    {P : Set (Matrix n n ℂ)} (hw : IsKDominant ε o w) (hP : P ∈ 𝓝 1) :
    ∀ᶠ x : Matrix n n ℂ in 𝓝 1, x ∈ blockDiagAlg ε →
      ∃ (A : ℂ → Matrix n n ℂ) (b : Matrix n n ℂ),
        IsCircleFactorization ε o w x A b ∧ ∀ s ∈ closedBall (0 : ℂ) 1, A s ∈ P := by
  -- Near `1` write `x = a b` with `a = 1 + lowerMask (ψ x)` lower unipotent; conjugation by
  -- `diag (s ^ o)` multiplies its entry `(i, j)` by `s ^ (o i - o j)`, a polynomial in `s`.
  have lower_mem (Z : Matrix n n ℂ) : 1 + lowerMask ε o Z ∈ blockDiagAlg ε :=
    add_mem (one_mem _) (mem_blockDiagAlg.2 fun i j h_sign ↦ by simp [h_sign])
  have lower_idem (Z : Matrix n n ℂ) : lowerMask ε o (lowerMask ε o Z) = lowerMask ε o Z :=
    Matrix.ext fun i j ↦ by simp +contextual
  obtain ⟨ψ, ⟨ψ_deriv, ψ_one⟩, chart⟩ := exists_borel_chart ε o ((lowerMask ε o).restrictScalars ℝ)
    (E := fun Z ↦ 1 + Z) (.const_add 1 (hasStrictFDerivAt_id 0)) (add_zero 1) lower_mem lower_idem
  let A (Z : Matrix n n ℂ) (s : ℂ) : Matrix n n ℂ :=
    1 + of fun i j ↦ s ^ (o i - o j).toNat * lowerMask ε o Z i j
  -- `A 0 s = 1`, so by compactness of the disc `A Z s ∈ P` holds on it for `Z` near `0 = ψ 1`.
  have A_one (s : ℂ) : A (ψ 1) s = 1 := by simp [A, ψ_one, ← ext_iff]
  have near : ∀ᶠ Z in 𝓝 (ψ 1), ∀ s ∈ closedBall (0 : ℂ) 1, A Z s ∈ P :=
    (isCompact_closedBall 0 1).eventually_forall_mem A P fun s _ ↦ by rwa [A_one]
  filter_upwards [chart, ψ_deriv.continuousAt near] with x hx_chart hx_near hx
  let a : Matrix n n ℂ := 1 + lowerMask ε o (ψ x)
  let b : Matrix n n ℂ := 1 + (1 - (lowerMask ε o).restrictScalars ℝ) (ψ x)
  obtain ⟨hb, ⟨ha_mem, hb_mem⟩, x_eq⟩ :
      IsBorelMatrix o b ∧ (a ∈ blockDiagAlg ε ∧ b ∈ blockDiagAlg ε) ∧ x = a * b := hx_chart hx
  have A_differentiable : Differentiable ℂ (A (ψ x)) :=
    differentiable_pi.2 fun i ↦ differentiable_pi.2 fun j ↦ by
      simp only [A, Matrix.add_apply, of_apply]
      fun_prop
  have det_b : b.det ≠ 0 := hb.2
  -- The lower unipotent factor `a` does not change `weightMinors w`.
  have minors_x : weightMinors w x = diagChar w b :=
    calc weightMinors w x = weightMinors w (a * b) := congrArg (weightMinors w) x_eq
      _ = diagChar w a * weightMinors w b :=
        hw.weightMinors_oppBorel_mul ho det_b ha_mem (isBorelMatrix_one_add_lowerMask ho _)
      _ = weightMinors w b := by simp [a, diagChar]
      _ = diagChar w b := by
        simpa using hw.weightMinors_mul_borel ho (x := 1) (by simp) hb_mem hb
  have on_circle (s : Circle) : diagonal (fun i : n ↦ (s : ℂ) ^ o i) * x =
      A (ψ x) s * (diagonal (fun i : n ↦ (s : ℂ) ^ o i) * b) :=
    calc _ = diagonal (fun i : n ↦ (s : ℂ) ^ o i) * a * b := by rw [mul_assoc, ← x_eq]
      _ = _ := by rw [diagonal_mul_one_add_lowerMask, mul_assoc]
  exact ⟨A (ψ x), b,
    { mem_blockDiagAlg := hb_mem
      isBorelMatrix := hb
      analyticAt := A_differentiable.analyticAt
      apply_zero := by simp +contextual [A, ← ext_iff]
      weightMinors_eq := minors_x
      diagonal_mul_eq := on_circle }, hx_near⟩

/-- The circle mean at a point with a circle factorisation, for injective `o`. Let `F'` extend `F`
to products `h * b` with factor `∏ τ, diagChar (u τ) (b τ)`, as in `New.IsHolOfWeight`, with blocks
given by `ε'`. Let each `g τ` be block diagonal with circle factorisation
`diag (s ^ o) * g τ = A τ s * (diag (s ^ o) * b τ)` (`New.IsCircleFactorization`), and let `F'` be
analytic along `A` over the closed unit disc. Then for `q` analytic on the disc the mean over
`|s| = 1` of `F (diag (s ^ o) * g) * ((∏ τ, ∏ i, (s ^ o i) ^ u τ i)⁻¹ * q s)` is
`q 0 * (∏ τ, weightMinors (u τ) (g τ)) * F 1`. -/
theorem circle_mean_of_isCircleFactorization (ho : o.Injective) {u : Φ → n → ℤ}
    {F : (Φ → USign ε) → ℂ} {F' : (Φ → Matrix n n ℂ) → ℂ}
    (hF' : ∀ (h : Φ → USign ε) (b : Φ → Matrix n n ℂ), (∀ τ : Φ, IsBorelMatrix o (b τ)) →
      (∀ τ : Φ, (h τ : Matrix n n ℂ) ∈ blockDiagAlg ε' ∧ b τ ∈ blockDiagAlg ε') →
      F' (fun τ : Φ ↦ h τ * b τ) = (∏ τ : Φ, diagChar (u τ) (b τ)) * F h)
    {g : Φ → USign ε} (hg : ∀ τ : Φ, (g τ : Matrix n n ℂ) ∈ blockDiagAlg ε')
    {A : Φ → ℂ → Matrix n n ℂ} {b : Φ → Matrix n n ℂ}
    (h_factor : ∀ τ : Φ, IsCircleFactorization ε' o (u τ) (g τ) (A τ) (b τ))
    (hA : ∀ s ∈ closedBall (0 : ℂ) 1, AnalyticAt ℂ F' fun τ : Φ ↦ A τ s)
    {q : ℂ → ℂ} (hq : AnalyticOnNhd ℂ q (closedBall 0 1)) :
    ∫ θ : UnitAddCircle,
        F (fun τ : Φ ↦ diagTorus ε (fun i : n ↦ θ.toCircle ^ o i) * g τ) *
          ((∏ τ : Φ, ∏ i : n, ((θ.toCircle : ℂ) ^ o i) ^ u τ i)⁻¹ * q θ.toCircle) =
      q 0 * (∏ τ : Φ, weightMinors (u τ) (g τ)) * F 1 := by
  have b_tri (τ : Φ) : IsBorelMatrix o (b τ) := (h_factor τ).isBorelMatrix
  let β : ℂ := ∏ τ : Φ, ∏ i : n, b τ i i ^ u τ i
  have β_ne : β ≠ 0 := by simp [β, (b_tri _).diag_ne_zero ho, prod_eq_zero_iff, zpow_ne_zero]
  -- With `d = diag (s ^ o)` we have `A s = (d g) (d b)⁻¹`, and `d b` is triangular.
  have on_circle (s : Circle) : F' (fun τ ↦ A τ s) = β⁻¹ * (∏ τ, ∏ i, ((s : ℂ) ^ o i) ^ u τ i)⁻¹ *
      F fun τ ↦ diagTorus ε (fun i ↦ s ^ o i) * g τ := by
    let dg (τ : Φ) : USign ε := diagTorus ε (fun i ↦ s ^ o i) * g τ
    let db (τ : Φ) : Matrix n n ℂ := diagonal (fun i ↦ (s : ℂ) ^ o i) * b τ
    have db_tri (τ : Φ) : IsBorelMatrix o (db τ) := (isBorelMatrix_diagonal s).mul (b_tri τ)
    have blocks (τ : Φ) : ↑(dg τ) ∈ blockDiagAlg ε' ∧ (db τ)⁻¹ ∈ blockDiagAlg ε' := by
      simp [dg, db, hg, (h_factor τ).mem_blockDiagAlg, Matrix.mul_inv_rev, diagTorus,
        diagonal_mem_blockDiagAlg, mul_mem]
    have A_eq (τ : Φ) : dg τ * (db τ)⁻¹ = A τ s := by
      have dg_eq : dg τ = A τ s * db τ := by
        simpa [dg, db, diagTorus] using (h_factor τ).diagonal_mul_eq s
      simp [dg_eq, (db_tri τ).2]
    have char_inv (τ : Φ) : diagChar (u τ) (db τ)⁻¹ =
        (∏ i, b τ i i ^ u τ i)⁻¹ * (∏ i, ((s : ℂ) ^ o i) ^ u τ i)⁻¹ := by
      simp [diagChar, (db_tri τ).inv_apply_diag ho, db, mul_zpow, prod_mul_distrib]
    simpa only [A_eq, char_inv, prod_mul_distrib, prod_inv_distrib] using
      hF' dg (fun τ ↦ (db τ)⁻¹) (fun τ ↦ (db_tri τ).inv) blocks
  have at_centre : F' (fun τ ↦ A τ 0) = F 1 := by
    simpa [(h_factor _).apply_zero, IsBorelMatrix, blockTriangular_one, diagChar] using hF' 1 1
  have holomorphic : AnalyticOnNhd ℂ (fun s ↦ q s * β * F' fun τ ↦ A τ s) (closedBall 0 1) :=
    (hq.mul analyticOnNhd_const).mul fun s hs ↦
      .comp (hA s hs) (.pi fun τ ↦ (h_factor τ).analyticAt s)
  calc _ = ∫ θ : UnitAddCircle, q θ.toCircle * β * F' fun τ ↦ A τ θ.toCircle := by
        congr with θ
        rw [on_circle]
        field_simp
    _ = q 0 * β * F' fun τ ↦ A τ 0 := integral_comp_toCircle_eq_apply_zero
      holomorphic.differentiableOn
    _ = _ := by simp [β, at_centre, (h_factor _).weightMinors_eq, diagChar]

/-- The mean over the circle `diag (s ^ o)` of a function of weight `u`. Let `o` be injective and
`ε'` be `1` or `ε`, and let `F` on `(USign ε)^Φ`, the tuples in the unitary group of `diag ε`, be
holomorphic of weight `u` for `o` and `ε'` (`IsHolOfWeight`), with each `u τ` `K`-dominant:
`u τ j ≤ u τ i` whenever `ε' i = ε' j` and `o i < o j`. Let each `g τ` commute with `diag ε'` and
let `q` be analytic on a neighbourhood of the closed unit disc. Then the mean over `|s| = 1` of
`F (diag (s ^ o) * g) * ((∏ τ, ∏ i, (s ^ o i) ^ u τ i)⁻¹ * q s)` is
`q 0 * (∏ τ, weightMinors (u τ) (g τ)) * F 1`, where `weightMinors l g` is the product over all
integers `t` of the principal minor of `g` on `{i | t ≤ l i}`, divided by `det g` when `t ≤ 0`. -/
theorem IsHolOfWeight.circle_mean_weightMinors (ho : o.Injective) {u : Φ → n → ℤ}
    {F : (Φ → USign ε) → ℂ} {g : Φ → USign ε} (hF : IsHolOfWeight ε o u F ε')
    (hε : ε' = 1 ∨ ε' = ε) (hu : ∀ τ : Φ, IsKDominant ε' o (u τ))
    (hg : ∀ τ : Φ, (g τ : Matrix n n ℂ) ∈ blockDiagAlg ε')
    (q : ℂ → ℂ) (hq : AnalyticOnNhd ℂ q (closedBall 0 1)) :
    ∫ θ : UnitAddCircle,
        F (fun τ : Φ ↦ diagTorus ε (fun i : n ↦ θ.toCircle ^ o i) * g τ) *
          ((∏ τ : Φ, ∏ i : n, ((θ.toCircle : ℂ) ^ o i) ^ u τ i)⁻¹ * q θ.toCircle) =
      q 0 * (∏ τ : Φ, weightMinors (u τ) (g τ)) * F 1 := by
  -- Join `1` to `g` by analytic paths `c τ`. Both sides are analytic along them, and near `1` the
  -- formula is the mean value property along the curve of a circle factorisation.
  choose c c_zero c_one c_analytic c_mem using fun τ : Φ ↦ exists_analytic_path hε (g τ) (hg τ)
  obtain ⟨F', hF'⟩ := hF
  let d (s : Circle) : Matrix n n ℂ := diagonal fun i ↦ (s : ℂ) ^ o i
  have on_path (s : Circle) (t : ℝ) : AnalyticAt ℂ F' (fun τ ↦ d s * c τ t) ∧
      F' (fun τ ↦ d s * c τ t) = F fun τ ↦ diagTorus ε (fun i ↦ s ^ o i) * c τ t := by
    simpa [d, c_mem, diagTorus, IsBorelMatrix, blockTriangular_one, diagonal_mem_blockDiagAlg,
      mul_mem, diagChar] using hF' (fun τ ↦ diagTorus ε (fun i ↦ s ^ o i) * c τ t) 1
  let weight (s : ℂ) : ℂ := (∏ τ, ∏ i, (s ^ o i) ^ u τ i)⁻¹ * q s
  let lhs (t : ℝ) : ℂ :=
    ∫ θ : UnitAddCircle, F' (fun τ ↦ d θ.toCircle * c τ t) * weight θ.toCircle
  let rhs (t : ℝ) : ℂ := q 0 * (∏ τ, weightMinors (u τ) (c τ t)) * F 1
  suffices h_path : lhs = rhs by
    simpa only [lhs, rhs, weight, on_path, c_one] using congrFun h_path 1
  have lhs_analytic : AnalyticOnNhd ℝ lhs .univ := fun t _ ↦ by
    -- the integrand is analytic in the point, uniformly in `θ`, which enters through `ι θ`
    let ι (θ : UnitAddCircle) : (Φ → Matrix n n ℂ) × ℂ := (fun _ ↦ d θ.toCircle, weight θ.toCircle)
    have q_analytic (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : AnalyticAt ℂ q z := hq z hz
    have hι : Continuous ι := continuous_iff_continuousAt.2 <| by
      fun_prop (disch := simp [zpow_ne_zero, prod_eq_zero_iff, norm_coe])
    have F'_analytic (s : Circle) : AnalyticAt ℂ F' (fun τ ↦ d s * c τ t) := (on_path s t).1
    exact ((IsAnalyticFamily.of_analyticAt hι (fun (a, b, w) ↦ F' (b * a) * w) (by fun_prop)
      ).analyticAt_integral volume).restrictScalars.comp_of_eq (.pi fun τ ↦ c_analytic τ t) rfl
  have rhs_analytic : AnalyticOnNhd ℝ rhs .univ := fun t _ ↦ by
    have minors_analytic (τ : Φ) : AnalyticAt ℝ (fun t : ℝ ↦ weightMinors (u τ) (c τ t)) t :=
      (analyticAt_weightMinors (by simp [GeneralLinearGroup.det_ne_zero])).restrictScalars.comp
        (c_analytic τ t)
    fun_prop
  refine lhs_analytic.eq_of_eventuallyEq rhs_analytic (z₀ := 0) ?_
  -- `F'` is analytic on a box `V` around `1`, which contains `A s` for `|s| ≤ 1` and small `t`.
  have at_one : AnalyticAt ℂ F' fun _ ↦ 1 := by
    simpa using (hF' 1 1 (by simp [IsBorelMatrix, blockTriangular_one]) (by simp)).left
  obtain ⟨T, V, hV, V_analytic⟩ : ∃ (T : Finset Φ) (V : Φ → Set (Matrix n n ℂ)),
      (∀ τ, V τ ∈ 𝓝 1) ∧ Set.pi T V ⊆ {z | AnalyticAt ℂ F' z} :=
    mem_pi'.1 (nhds_pi.ge at_one.eventually_analyticAt)
  have factor_near (τ : Φ) : ∀ᶠ t in 𝓝 (0 : ℝ), ∃ (A : ℂ → Matrix n n ℂ) (b : Matrix n n ℂ),
      IsCircleFactorization ε' o (u τ) (c τ t) A b ∧ ∀ s ∈ closedBall (0 : ℂ) 1, A s ∈ V τ := by
    have c_tendsto : Tendsto (fun t ↦ (c τ t : Matrix n n ℂ)) (𝓝 0) (𝓝 1) :=
      (c_analytic τ 0).continuousAt.tendsto.mono_right (by simp [c_zero])
    filter_upwards [c_tendsto.eventually (eventually_exists_isCircleFactorization ho (hu τ) (hV τ))]
      with t ht using ht (c_mem τ t)
  filter_upwards [eventually_all.2 factor_near] with t ht
  choose A b factor A_mem using ht
  simpa only [lhs, rhs, weight, on_path] using circle_mean_of_isCircleFactorization ho
    (fun h b hb h_mem ↦ (hF' h b hb h_mem).2) (fun τ ↦ c_mem τ t) factor
    (fun s hs ↦ V_analytic fun τ _ ↦ A_mem τ s hs) hq

/-- Let `o` be injective. Let `F` on a single copy of `U(diag ε)` be continuous and holomorphic of
weight `w`, with blocks given by `ε` and `w` dominant within the blocks (`w j ≤ w i` whenever
`ε i = ε j` and `o i < o j`). Then the integral of `F k * conj (weightMinors w k)` against the Haar
probability measure `haarK ε` of `K = U(diag ε) ∩ U(n)` is `w.kTypeNormSq * F 1`, where
`w.kTypeNormSq = ∫ ‖weightMinors w k‖ ^ 2`. A case of Schur's orthogonality relations for `K`:
integration against `conj (weightMinors w) / w.kTypeNormSq` fixes the highest vectors of weight
`w`. -/
theorem IsHolOfWeight.integral_mul_conj_weightMinors {F : (Unit → USign ε) → ℂ} (ho : o.Injective)
    {w : HCParam ε} (hw : IsKDominant ε o w) (hF : IsHolOfWeight ε o (fun _ : Unit ↦ w) F ε)
    (F_cont : Continuous F) :
    ∫ k : maxCompactU ε, F (fun _ : Unit ↦ k) * conj (weightMinors w k) ∂haarK ε =
      w.kTypeNormSq * F 1 := by
  -- Average the integrand over left translation by the circle `s ^ o`, which preserves the Haar
  -- measure of `K`: the circle mean turns `F k` into `weightMinors w k * F 1`.
  let T (θ : UnitAddCircle) : maxCompactU ε := diagTorusK fun i ↦ θ.toCircle ^ o i
  have h_mean (k : maxCompactU ε) :
      ∫ θ, F (fun _ ↦ ↑(T θ * k)) * conj (weightMinors w (T θ * k).val) =
        conj (weightMinors w k.val) * weightMinors w k.val * F 1 := by
    -- translating `k` multiplies `conj (weightMinors w k)` by the inverse character
    have conj_translate (θ : UnitAddCircle) : conj (weightMinors w (T θ * k).val) =
        (∏ i : n, ((θ.toCircle : ℂ) ^ o i) ^ w i)⁻¹ * conj (weightMinors w k.val) := by
      simp [T, ← coe_inv_eq_conj, diagTorus, zpow_ne_zero, GeneralLinearGroup.det_ne_zero]
    have k_mem : (k.val : Matrix n n ℂ) ∈ blockDiagAlg ε := mem_maxCompactU.1 k.property
    simp only [conj_translate]
    simpa [T, diagTorus] using hF.circle_mean_weightMinors ho (g := fun _ ↦ k) (hε := .inr rfl)
      (hu := fun _ ↦ hw) (hg := fun _ ↦ k_mem) (q := fun _ ↦ conj (weightMinors w k.val))
      (hq := analyticOnNhd_const)
  calc ∫ k : maxCompactU ε, F (fun _ ↦ k) * conj (weightMinors w k) ∂haarK ε
      = ∫ k, conj (weightMinors w k.val) * weightMinors w k.val * F 1 ∂haarK ε :=
        integral_eq_of_circle_mean (T := fun θ k ↦ T θ * k) (Continuous.measurable (by fun_prop))
          (fun θ ↦ measurePreserving_mul_left _ (T θ))
          (integrable_of_compactSpace
            (by fun_prop (disch := simp [GeneralLinearGroup.det_ne_zero])))
          h_mean
    _ = w.kTypeNormSq * F 1 := by simp [← integral_complex_ofReal, integral_mul_const, conj_mul']

end New
