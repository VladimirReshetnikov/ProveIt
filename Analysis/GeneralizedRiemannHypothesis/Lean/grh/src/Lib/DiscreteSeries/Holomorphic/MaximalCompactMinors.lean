import Lib.DiscreteSeries.FlenstedJensen.RightDerivatives
import Lib.General.LinearAlgebra.MinorProducts

/-!
# Maximal compact subgroup, block diagonal matrices and equivariance of minors

For signs `ε`, let `J = New.signMatrix ε`. `New.USign ε` is the unitary group of `J`,
`New.maxCompactU ε` is its subgroup of unitary matrices, `New.blockDiagAlg ε` is the algebra of
matrices that commute with `J`, and `New.blockDiagPart ε x` is the block diagonal part of `x`.

## Main definitions and results

* `New.mem_blockDiagAlg`, `New.blockDiagPart_eq`: `New.blockDiagAlg ε` consists of the block
  diagonal matrices, and `New.blockDiagPart ε x` is `(x + J * x * J) / 2`.
* `New.mem_maxCompactU`: an element of the group is unitary exactly when it is block diagonal.
* `New.fderiv_eq_on_blockDiagAlg`: a complex derivative at `1` is determined on `New.blockDiagAlg ε`
  by the derivatives along one-parameter subgroups of `New.maxCompactU ε`.
* `New.IsKDominant.weightMinors_mul_borel`, `New.IsKDominant.weightMinors_oppBorel_mul`: let `o` be
  an injective order, `w` dominant within each block of `ε` (`New.IsKDominant`), `x` invertible and
  `b` invertible and block diagonal (`New.blockDiagAlg ε`). Multiplying `x` on the right by an upper
  triangular `b`, or on the left by a lower triangular `b`, multiplies `weightMinors w x` by
  `diagChar w b`.

Notions from other files:
* `New.weightMinors w g`: the coefficient of a highest vector of weight `w`, that is the product
  over all integers `t` of the principal minor of `g` on `{i | t ≤ w i}`, each factor with `t ≤ 0`
  divided by `det g`.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Holomorphic.HighestVectorExtension` for sources.
-/

namespace New

section MaximalCompact

open Matrix MeasureTheory Measure DiscreteSeries NormedSpace Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ}

theorem DiscreteSeries.mem_blockDiagAlg_iff_commute {x : Matrix n n ℂ} :
    x ∈ blockDiagAlg ε ↔ Commute (signMatrix ε) x := by
  simp [blockDiagAlg, Subalgebra.mem_centralizer_iff, commute_iff_eq]

theorem DiscreteSeries.diagonal_mem_blockDiagAlg (d : n → ℂ) : diagonal d ∈ blockDiagAlg ε :=
  mem_blockDiagAlg_iff_commute.mpr (commute_diagonal _ d)

/-- With `J = signMatrix ε`, the diagonal matrix with entries `ε i`, the block diagonal part of `x`,
that is the matrix of the entries `x i j` with `ε i = ε j`, is `(x + J * x * J) / 2`. -/
theorem blockDiagPart_eq (x : Matrix n n ℂ) :
    blockDiagPart ε x = (2⁻¹ : ℂ) • (x + signMatrix ε * x * signMatrix ε) := by
  -- entrywise: `(1 + ε i * ε j) / 2` is `1` if `ε i = ε j` and `0` otherwise
  ext i j
  have h_entry : (signMatrix ε * x * signMatrix ε) i j = (ε i : ℤ) * (ε j : ℤ) * x i j := by
    simp [signMatrix, mul_right_comm]
  rw [Matrix.smul_apply, Matrix.add_apply, h_entry]
  obtain hi | hi := Int.units_eq_one_or (ε i) <;> obtain hj | hj := Int.units_eq_one_or (ε j) <;>
    simp [blockDiagPart, hi, hj, ← two_mul]

/-- A matrix lies in `New.blockDiagAlg ε` exactly when its entry at `(i, j)` vanishes whenever
`ε i ≠ ε j`. -/
@[local simp]
theorem mem_blockDiagAlg {x : Matrix n n ℂ} :
    x ∈ blockDiagAlg ε ↔ ∀ i j : n, ε i ≠ ε j → x i j = 0 := by
  rw [mem_blockDiagAlg_iff_commute, commute_iff_eq]
  simp [← ext_iff, signMatrix, mul_comm, imp_iff_not_or, Units.ext_iff]

/-- For the constant signs `1` there is one block, so every matrix is block diagonal. -/
@[simp]
theorem mem_blockDiagAlg_one {x : Matrix n n ℂ} : x ∈ blockDiagAlg 1 := by simp

theorem blockDiagPart_mem (x : Matrix n n ℂ) : blockDiagPart ε x ∈ blockDiagAlg ε :=
  mem_blockDiagAlg.mpr fun i j h_sign ↦ by simp [blockDiagPart, h_sign]

/-- The matrix inverse of an element `g` of `U(diag ε)` is `J * gᴴ * J`, where
`J = signMatrix ε`. -/
theorem U.inv_coe_eq_mul_conjTranspose_mul (g : USign ε) :
    (g : Matrix n n ℂ)⁻¹ = signMatrix ε * (g : Matrix n n ℂ)ᴴ * signMatrix ε := by
  simp [← coe_inv IsHermitianInvolution.mul_self]

/-- The matrix inverse of an element `k` of `New.maxCompactU ε`, the group of unitary matrices in
`U(diag ε)`, is its conjugate transpose. -/
theorem maxCompactU.coe_inv (k : maxCompactU ε) :
    (k : Matrix n n ℂ)⁻¹ = (k : Matrix n n ℂ)ᴴ := by
  let k' : U (1 : Matrix n n ℂ) := ⟨k, Subgroup.mem_subgroupOf.mp k.prop⟩
  exact inv_eq_left_inv (mem_unitaryGroup_iff'.mp (U_one_mem_unitaryGroup k'))

/-- If `J` is an involution and `A` preserves the form of `J`, that is `Aᴴ * J * A = J`, then `A` is
unitary exactly when it commutes with `J`. -/
theorem conjTranspose_mul_self_eq_one_iff_commute {J A : Matrix n n ℂ} (h_invol : J * J = 1)
    (h_form : Aᴴ * J * A = J) : Aᴴ * A = 1 ↔ Commute J A := by
  constructor
  · intro h_left
    calc J * A = A * Aᴴ * (J * A) := by rw [mul_eq_one_comm.mp h_left, Matrix.one_mul]
      _ = A * (Aᴴ * J * A) := by simp only [Matrix.mul_assoc]
      _ = A * J := by rw [h_form]
  · intro h_comm
    calc Aᴴ * A = Aᴴ * (A * J) * J := by simp only [Matrix.mul_assoc, h_invol, Matrix.mul_one]
      _ = Aᴴ * J * A * J := by rw [← h_comm.eq, ← Matrix.mul_assoc]
      _ = 1 := by rw [h_form, h_invol]

/-- An element `g` of `U(diag ε)` lies in the subgroup `New.maxCompactU ε` of unitary matrices
exactly when it is block diagonal, that is, commutes with `signMatrix ε`. -/
theorem mem_maxCompactU {g : U (signMatrix ε)} :
    g ∈ maxCompactU ε ↔ (g : Matrix n n ℂ) ∈ blockDiagAlg ε := by
  rw [maxCompactU, Subgroup.mem_subgroupOf, mem_U, Matrix.mul_one, mem_blockDiagAlg_iff_commute]
  exact conjTranspose_mul_self_eq_one_iff_commute (signMatrix_mul_self ε) (mem_U.mp g.property)

/-- Let `Φ` have the complex derivative `D` at `1`, and let `φ` be a complex linear form. If for
every `Y` in the Lie algebra `unitaryLie (signMatrix ε)` of `U(diag ε)` whose one-parameter group
`expU (t • Y)` lies in `New.maxCompactU ε` the derivative of `t ↦ Φ (exp (t • Y))` at `0` is `φ Y`,
then `D` and `φ` agree on the block diagonal matrices `New.blockDiagAlg ε`. -/
theorem fderiv_eq_on_blockDiagAlg {Φ : Matrix n n ℂ → ℂ} {D : Matrix n n ℂ →L[ℂ] ℂ}
    (hΦ : HasFDerivAt Φ D 1) (φ : Matrix n n ℂ →ₗ[ℂ] ℂ)
    (h_deriv : ∀ Y : unitaryLie (signMatrix ε),
      (∀ t : ℝ, expU (t • Y) ∈ maxCompactU ε) →
      deriv (fun t : ℝ ↦ Φ (exp (t • Y.val))) (0 : ℝ) = φ Y.val)
    {x : Matrix n n ℂ} (hx_mem : x ∈ blockDiagAlg ε) :
    D x = φ x := by
  -- Every `x` is `Y₁ + i Y₂` with `Y₁, Y₂` in the Lie algebra of `U(diag ε)`, block diagonal if
  -- `x` is; both sides are `ℂ`-linear, so it is enough to compare them on such `Y`.
  have h_lie (Y : unitaryLie (signMatrix ε)) (hY : Y.val ∈ blockDiagAlg ε) :
      D Y.val = φ Y.val := by
    have h_mem (t : ℝ) : expU (t • Y) ∈ maxCompactU ε := by
      rw [mem_maxCompactU, mem_blockDiagAlg_iff_commute]
      exact ((mem_blockDiagAlg_iff_commute.mp hY).smul_right t).exp_right
    -- chain rule along the curve `t ↦ exp (t • Y)`, which starts at `1` with velocity `Y`
    rw [← h_deriv Y h_mem]
    exact ((hΦ.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ)
      (by simpa using hasDerivAt_exp_smul_const Y.val (0 : ℝ)) (by simp)).deriv.symm
  have h_part (y : Matrix n n ℂ) (hy : y ∈ blockDiagAlg ε) :
      D (unitaryLiePart ε y).val = φ (unitaryLiePart ε y).val := by
    refine h_lie _ (mem_blockDiagAlg.mpr fun i j h_sign ↦ ?_)
    simp [unitaryLiePart, signMatrix, inv_diagonal, mem_blockDiagAlg.mp hy i j h_sign,
      mem_blockDiagAlg.mp hy j i h_sign.symm]
  rw [eq_unitaryLiePart_add_I_smul ε x, map_add, map_add, map_smul, map_smul, h_part x hx_mem,
    h_part _ (Subalgebra.smul_mem _ hx_mem _)]

/-- For a tuple `t` of complex numbers of modulus one, the diagonal matrix `diag(t)` as an element
of the compact group `U(diag ε) ∩ U(n)`. -/
noncomputable abbrev diagTorusK (t : n → Circle) : maxCompactU ε :=
  (⟨diagTorus ε t, mem_maxCompactU.mpr (diagonal_mem_blockDiagAlg _)⟩ : maxCompactU ε)

/-- The map sending a tuple of complex numbers of modulus one to its diagonal matrix in
`U(diag ε)` is continuous. -/
@[fun_prop]
theorem continuous_diagTorus : Continuous (diagTorus ε) := continuous_U_iff_matrix.mpr (by fun_prop)

/-- The Haar measure `New.haarK ε` on `New.maxCompactU ε` has total mass one. -/
instance : IsProbabilityMeasure (haarK ε) := ⟨haarMeasure_self⟩

deriving instance IsHaarMeasure, IsMulRightInvariant for haarK


/-! ### Products with a block diagonal matrix -/

@[simp]
theorem blockDiagPart_of_mem {x : Matrix n n ℂ} (hx : x ∈ blockDiagAlg ε) :
    blockDiagPart ε x = x := by
  ext i j
  by_cases h_sign : ε i = ε j <;> simp [blockDiagPart, h_sign, mem_blockDiagAlg.mp hx i j]

/-- Taking the block diagonal part commutes with left multiplication by a block diagonal matrix
`x`. -/
@[simp]
theorem blockDiagPart_mul_left {x : Matrix n n ℂ} (hx : x ∈ blockDiagAlg ε) (y : Matrix n n ℂ) :
    blockDiagPart ε (x * y) = x * blockDiagPart ε y := by
  -- `x` commutes with `signMatrix ε`, so it comes out of the formula `blockDiagPart_eq`
  have hx_comm : signMatrix ε * x = x * signMatrix ε := mem_blockDiagAlg_iff_commute.mp hx
  rw [blockDiagPart_eq, blockDiagPart_eq, ← Matrix.mul_assoc (signMatrix ε) x y, hx_comm]
  simp only [Matrix.mul_assoc, mul_smul_comm, mul_add]

/-- Taking the block diagonal part commutes with right multiplication by a block diagonal matrix
`x`. -/
@[simp]
theorem blockDiagPart_mul_right {x : Matrix n n ℂ} (hx : x ∈ blockDiagAlg ε) (y : Matrix n n ℂ) :
    blockDiagPart ε (y * x) = blockDiagPart ε y * x := by
  -- `x` commutes with `signMatrix ε`, so it comes out of the formula `blockDiagPart_eq`
  simp only [blockDiagPart_eq, Matrix.mul_assoc, (mem_blockDiagAlg_iff_commute.mp hx).eq,
    smul_mul_assoc, add_mul]

/-- Taking the block diagonal part commutes with left and with right multiplication by a block
diagonal matrix `x`. -/
@[simp]
theorem blockDiagPart_mul {x : Matrix n n ℂ} (hx : x ∈ blockDiagAlg ε) (y : Matrix n n ℂ) :
    blockDiagPart ε (x * y) = x * blockDiagPart ε y ∧
    blockDiagPart ε (y * x) = blockDiagPart ε y * x :=
  ⟨blockDiagPart_mul_left hx y, blockDiagPart_mul_right hx y⟩

@[simp]
theorem blockDiagAlg.inv_mem {x : Matrix n n ℂ} (hx : x ∈ blockDiagAlg ε) :
    x⁻¹ ∈ blockDiagAlg ε := by
  rw [mem_blockDiagAlg_iff_commute, ← x.zpow_neg_one]
  exact Matrix.Commute.zpow_right (mem_blockDiagAlg_iff_commute.mp hx) (-1)

end MaximalCompact

/-!
## Holomorphic functions of a weight and products of minors

`New.IsHolOfWeight ε o u F` says that `F`, a function of a family of elements of `U(diag ε)` indexed
by `Φ`, extends analytically to the products `h * b` with `b` invertible and triangular for the
order `o` (`New.IsBorelMatrix`) and block diagonal for optional signs `ε'` (by default `1`, which
imposes no condition). The extension is `F h` times `∏ τ, New.diagChar (u τ) (b τ)`, where
`New.diagChar w b = ∏ i, b i i ^ w i`.
-/

section MinorEquivariance

open Matrix Finset DiscreteSeries Norms.L2Operator

variable {n : Type} [Fintype n] [DecidableEq n] {ε : n → ℤˣ} {o w : n → ℤ}

attribute [fun_prop] analyticAt_fst analyticAt_snd analyticAt_weightMinors
  ContinuousLinearMap.analyticAt

/-- A finite linear combination with complex coefficients of functions holomorphic of weight `u` for
the order `o` is holomorphic of weight `u`. Here `New.IsHolOfWeight ε o u F` says that some `F'` is
analytic at every product `g * b`, with each `b τ` invertible and upper triangular for `o`, block
diagonal for optional signs `ε'` (by default `1`, no condition), and equals
`(∏ τ, diagChar (u τ) (b τ)) * F g` there, where `diagChar w b = ∏ i, b i i ^ w i`. -/
theorem IsHolOfWeight.sum {Φ : Type} [Fintype Φ] {u : Φ → n → ℤ} {ι : Type*} {T : Finset ι}
    {f : ι → (Φ → USign ε) → ℂ} (c : ι → ℂ)
    (hf : ∀ i : ι, IsHolOfWeight ε o u (f i)) :
    IsHolOfWeight ε o u fun g : Φ → USign ε ↦ ∑ i ∈ T, c i * f i g := by
  -- the same linear combination of the extensions `f' i` of the `f i` is an extension
  choose f' hf' using hf
  refine ⟨∑ i ∈ T, c i • f' i, fun g b hb_borel hb_mem ↦ ⟨?_, ?_⟩⟩
  · exact analyticAt_sum T fun i _ ↦ (hf' i g b hb_borel hb_mem).left.const_smul
  · simp [Finset.sum_apply, (hf' _ g b hb_borel hb_mem).right, mul_sum, mul_left_comm]

/-- For an injective order `o`, the product of holomorphic functions of weights `u` and `v` is
holomorphic of weight `u + v`. Here `New.IsHolOfWeight ε o u F` says that some `F'` is analytic at
every product `h * b`, with each `b τ` invertible and upper triangular for `o`, block diagonal for
optional signs `ε'` (by default `1`, no condition), and equals `(∏ τ, diagChar (u τ) (b τ)) * F h`
there, where `diagChar w b = ∏ i, b i i ^ w i`. -/
theorem IsHolOfWeight.mul {Φ : Type} [Fintype Φ] {u v : Φ → n → ℤ} {F G : (Φ → USign ε) → ℂ}
    (ho : o.Injective) (hF : IsHolOfWeight ε o u F) (hG : IsHolOfWeight ε o v G) :
    IsHolOfWeight ε o (u + v) (F * G) := by
  -- multiply the extensions; `diagChar · b` is multiplicative, as `b` has nonzero diagonal
  obtain ⟨F', hF'⟩ := hF
  obtain ⟨G', hG'⟩ := hG
  refine ⟨F' * G', fun h b hb_borel hb_mem ↦ ?_⟩
  obtain ⟨hF_an, hF_eq⟩ := hF' h b hb_borel hb_mem
  obtain ⟨hG_an, hG_eq⟩ := hG' h b hb_borel hb_mem
  refine ⟨hF_an.mul hG_an, ?_⟩
  have h_char (τ : Φ) :
      diagChar ((u + v) τ) (b τ) = diagChar (u τ) (b τ) * diagChar (v τ) (b τ) := by
    simp [diagChar, zpow_add₀, (hb_borel τ).diag_ne_zero ho, prod_mul_distrib]
  simp_rw [Pi.mul_apply, hF_eq, hG_eq, h_char, prod_mul_distrib]
  ring


/-- Let `o` be injective and `w` dominant within each block of `ε` (`New.IsKDominant ε o w`:
`w j ≤ w i` whenever `ε i = ε j` and `o i < o j`). Here `weightMinors w g` is the product over
integers `t` of the principal minor of `g` on `{i | t ≤ w i}`, divided by `det g` when `t ≤ 0`.
Right multiplication of an invertible `x` by an invertible block diagonal `b`, upper triangular for
`o` (`New.IsBorelMatrix o b`), multiplies `weightMinors w x` by
`diagChar w b = ∏ i, b i i ^ w i`. -/
theorem IsKDominant.weightMinors_mul_borel (ho : o.Injective) (hw : IsKDominant ε o w)
    {x b : Matrix n n ℂ} (hx : x.det ≠ 0) (hb : b ∈ blockDiagAlg ε)
    (hb_borel : IsBorelMatrix o b) :
    weightMinors w (x * b) = weightMinors w x * diagChar w b := by
  -- `b` lies in `blockDiagAlg ε` and is triangular for `o`, so `b i j = 0` whenever `w i < w j`.
  have h_block (i j : n) (hij : w i < w j) : b i j = 0 := by
    by_cases h_sign : ε i = ε j
    · rcases lt_trichotomy (o i) (o j) with h_lt | h_eq | h_gt
      · exact absurd hij (hw i j h_sign h_lt).not_gt
      · simp [ho h_eq] at hij
      · exact hb_borel.left h_gt
    · exact mem_blockDiagAlg.mp hb i j h_sign
  -- The minors in `weightMinors w` are therefore multiplicative, and those of the triangular matrix
  -- `b` are those of its diagonal part `d`. So `x * b` has the same minors as `d * x`, for which
  -- `weightMinors_diagonal_mul` gives the character.
  let d : Matrix n n ℂ := diagonal fun i : n ↦ b i i
  have h_minor (t : ℤ) :
      principalMinor (x * b) (t ≤ w ·) = principalMinor (d * x) (t ≤ w ·) := by
    have h_zero (i j k : n) (_ : t ≤ w i) (hj : ¬t ≤ w j) (hk : t ≤ w k) :
        x i j = 0 ∨ b j k = 0 := Or.inr (h_block j k (by omega))
    have h_zero_diag (i j k : n) (hi : t ≤ w i) (hj : ¬t ≤ w j) (_ : t ≤ w k) :
        d i j = 0 ∨ x j k = 0 := Or.inl (diagonal_apply_ne _ (by grind))
    have h_det : principalMinor b (t ≤ w ·) = principalMinor d (t ≤ w ·) := by
      simp [d, principalMinor, toSquareBlockProp, toBlock, submatrix_diagonal,
        det_eq_prod_diag_of_blockTriangular _ hb_borel.left.submatrix, ho]
    rw [principalMinor_mul h_zero, principalMinor_mul h_zero_diag, h_det, mul_comm]
  have h_diag : weightMinors w (x * b) = weightMinors w (d * x) := by
    simp [weightMinors, h_minor, d, det_eq_prod_diag_of_blockTriangular ho hb_borel.left, mul_comm]
  rw [h_diag, weightMinors_diagonal_mul hx (hb_borel.diag_ne_zero ho), mul_comm, diagChar]

/-- Let `o` be injective and `w` dominant within each block of `ε` for `o`, not `-o`
(`New.IsKDominant ε o w`: `w j ≤ w i` whenever `ε i = ε j` and `o i < o j`). Left multiplication of
an invertible `x` by an invertible block diagonal `b`, lower triangular for `o`
(`New.IsBorelMatrix (-o) b`), multiplies the product of principal minors `weightMinors w` by
`diagChar w b = ∏ i, b i i ^ w i`. -/
lemma IsKDominant.weightMinors_oppBorel_mul (ho : o.Injective) (hw : IsKDominant ε o w)
    {x b : Matrix n n ℂ} (hx : x.det ≠ 0) (hb : b ∈ blockDiagAlg ε)
    (hb_borel : IsBorelMatrix (-o) b) :
    weightMinors w (b * x) = diagChar w b * weightMinors w x := by
  -- Transpose: `bᵀ` lies in `blockDiagAlg ε` and is triangular for `o`, so
  -- `IsKDominant.weightMinors_mul_borel` applies.
  have hb_mem : bᵀ ∈ blockDiagAlg ε :=
    mem_blockDiagAlg.mpr fun i j h_sign ↦ mem_blockDiagAlg.mp hb j i h_sign.symm
  have hb_tri : IsBorelMatrix o bᵀ :=
    ⟨fun i j hij ↦ hb_borel.left (neg_lt_neg hij), (det_transpose b).trans_ne hb_borel.right⟩
  have h_mul : weightMinors w (xᵀ * bᵀ) = weightMinors w xᵀ * diagChar w bᵀ :=
    hw.weightMinors_mul_borel ho ((det_transpose x).trans_ne hx) hb_mem hb_tri
  simpa [← transpose_mul, weightMinors_transpose, diagChar, mul_comm] using h_mul

end MinorEquivariance

end New
