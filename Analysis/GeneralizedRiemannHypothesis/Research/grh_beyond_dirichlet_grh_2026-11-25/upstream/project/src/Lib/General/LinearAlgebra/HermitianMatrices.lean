import Lib.General.Analysis.GaussianIntegral
import Lib.General.Groups.CongruenceSubgroups

/-!
# Determinants of positive semidefinite matrices, principal minors and hermitian involutions

The file proves inequalities and identities for complex matrices. The norm of a matrix is the `L²`
operator norm, and `≤` between matrices is the positive semidefinite order. It also studies a
hermitian involution `J` and its unitary group `New.U J`, the group of invertible matrices `g` with
`gᴴ * J * g = J`, with real coordinates on skew-hermitian matrices. For signs `ε i = ±1`,
`New.signMatrix ε` is their diagonal matrix and `New.USign ε` its unitary group.

## Main definitions and results

* `New.norm_det_le_norm_det_of_posSemidef`: `0 ≤ P ≤ Q` implies `|det P| ≤ |det Q|`.
* `New.norm_det_sq_le_of_posSemidef`: if the block matrix with rows `(P, A)` and `(B, Q)` is
  positive semidefinite, then `|det A|² ≤ |det P| |det Q|`.
* `New.principalMinor`: the principal minor on the indices satisfying a predicate `p`.
* `New.jacobi_complementary_minor`: Jacobi's theorem, the principal minors of `x⁻¹` from the
  complementary principal minors of `x`.
* `New.IsHermitianInvolution J`: `J` is hermitian and `J * J = 1`. Examples are `1` and the diagonal
  matrices of signs `New.signMatrix ε`.

## Relation to the literature

Known; see `Lib.DiscreteSeries.Haar.TotalMass` for sources.
-/

/-! ## Positive semidefinite matrices -/

section PosSemidefDet

open Matrix ComplexOrder MatrixOrder Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P Q : Matrix ι ι ℂ}

/-- If `P` and `Q - P` are positive semidefinite complex square matrices, that is `0 ≤ P ≤ Q` in
the Loewner order, then `|det P| ≤ |det Q|`. -/
lemma New.norm_det_le_norm_det_of_posSemidef (hP : P.PosSemidef) (h_le : (Q - P).PosSemidef) :
    ‖P.det‖ ≤ ‖Q.det‖ := by
  -- The Ostrowski–Taussky bound `|det H| ≤ 2 ^ card ι * |det Θ|` (for `0 ≤ H ≤ Θ + Θᴴ`) at
  -- `H = 2 P` and `Θ = Q`; the factors `2 ^ card ι` cancel.
  have h_sum : (Q + Qᴴ - (P + P)).PosSemidef := by
    simpa [hP.1.eq, sub_add_sub_comm] using h_le.add h_le.conjTranspose
  simpa [← two_smul ℂ P] using ostrowski_taussky (hP.add hP) h_sum

/-- Cauchy–Schwarz inequality for determinants: if the complex block matrix with rows `(P, A)` and
`(B, Q)`, all blocks square of the same size, is positive semidefinite, then
`|det A|² ≤ |det P| * |det Q|`. -/
lemma New.norm_det_sq_le_of_posSemidef {A B : Matrix ι ι ℂ} (h : (fromBlocks P A B Q).PosSemidef) :
    ‖A.det‖ ^ 2 ≤ ‖P.det‖ * ‖Q.det‖ := by
  by_cases hQ : Q.det = 0
  · -- A vector `v` killed by `Q` makes `(0, v)` isotropic for the block matrix, hence killed by it;
    -- so `A v = 0` and `det A = 0`.
    obtain ⟨v, hv, hQv⟩ := exists_mulVec_eq_zero_iff.2 hQ
    have h_kernel : fromBlocks P A B Q *ᵥ (0 ⊕ᵥ v) = 0 :=
      (h.dotProduct_mulVec_zero_iff (x := 0 ⊕ᵥ v)).1
        (by simp [fromBlocks_mulVec, hQv, dotProduct])
    have hAv : A *ᵥ v = 0 := by simpa [fromBlocks_mulVec, hQv, funext_iff] using h_kernel
    simp [hQ, exists_mulVec_eq_zero_iff.1 ⟨v, hv, hAv⟩]
  -- Otherwise `Q` is positive definite and the Schur complement `P - A Q⁻¹ Aᴴ` is semidefinite.
  have hQ_pos : Q.PosDef := (h.submatrix Sum.inr).posDef_iff_det_ne_zero.2 hQ
  let : Invertible Q := hQ_pos.isUnit.invertible
  obtain ⟨-, rfl, -, -⟩ := isHermitian_fromBlocks_iff.1 h.isHermitian
  have h_schur : (P - A * Q⁻¹ * Aᴴ).PosSemidef := (hQ_pos.fromBlocks₂₂ P A).1 h
  have h_det : ‖(A * Q⁻¹ * Aᴴ).det‖ ≤ ‖P.det‖ :=
    norm_det_le_norm_det_of_posSemidef (hQ_pos.inv.posSemidef.mul_mul_conjTranspose_same A) h_schur
  have h_left : ‖(A * Q⁻¹ * Aᴴ).det‖ = ‖A.det‖ ^ 2 / ‖Q.det‖ := by simp [field]
  rwa [h_left, div_le_iff₀ (norm_pos_iff.2 hQ)] at h_det

/-- Gram–Schmidt for a positive definite matrix `G`: there is a lower triangular matrix `Γ` whose
columns are orthonormal for `G`. -/
lemma New.exists_lowerTriangular_conjTranspose_mul_mul_eq_one {m : ℕ}
    {G : Matrix (Fin m) (Fin m) ℂ} (hG : G.PosDef) :
    ∃ Γ : Matrix (Fin m) (Fin m) ℂ, (∀ a b : Fin m, a < b → Γ a b = 0) ∧ Γᴴ * G * Γ = 1 := by
  -- Orthogonalise the standard basis from the last vector to the first, then normalise.
  let H : Matrix (Fin m) (Fin m) ℂ := G.submatrix Fin.revPerm Fin.revPerm
  have hH : H.PosDef := hG.submatrix Fin.revPerm.injective
  let L : Matrix (Fin m) (Fin m) ℂ := LDL.lowerInv hH
  let d : Fin m → ℂ := LDL.diagEntries hH
  have h_diag : diagonal d = L * H * Lᴴ := by simpa [LDL.diag] using LDL.diag_eq_lowerInv_conj hH
  have hd_pos (a : Fin m) : 0 < d a := by
    have h_pos : (diagonal d).PosDef := by
      simpa [h_diag] using hH.mul_mul_conjTranspose_same
        (vecMul_injective_of_isUnit (isUnit_of_invertible (LDL.lowerInv hH)))
    exact posDef_diagonal_iff.1 h_pos a
  let r (a : Fin m) : ℂ := (√(d a).re : ℝ)⁻¹
  have h_scale (a : Fin m) : star (r a) * d a * r a = 1 := by
    obtain ⟨h_re, h_im⟩ := Complex.pos_iff.1 (hd_pos a)
    simp [r, Complex.ext_iff, ← h_im, field, Real.sq_sqrt h_re.le]
  refine ⟨(Lᴴ * diagonal r).submatrix Fin.revPerm Fin.revPerm, fun a b hab ↦ ?_, ?_⟩
  · have hL_lower : L b.rev a.rev = 0 := LDL.isLowerTriangular_lowerInv hH (Fin.rev_lt_rev.2 hab)
    simp [mul_diagonal, hL_lower]
  · have h_rev : (Lᴴ * diagonal r)ᴴ * H * (Lᴴ * diagonal r) = 1 :=
      calc
        _ = (diagonal r)ᴴ * (L * H * Lᴴ) * diagonal r := by simp [Matrix.mul_assoc]
        _ = 1 := by simpa [← h_diag, funext_iff] using h_scale
    have hG_eq : G = H.submatrix Fin.revPerm Fin.revPerm := by simp [H, ← Matrix.ext_iff]
    simp only [hG_eq, conjTranspose_submatrix, submatrix_mul_equiv, h_rev, submatrix_one_equiv]

end PosSemidefDet

/-!
## Principal minors and Jacobi's complementary minor theorem

* `New.principalMinor_eq_det`: the principal minor of `x` on the indices satisfying `p` is the
  determinant of the matrix with the rows of `x` on `p` and those of `1` off `p`. Most identities of
  this section are reduced to determinants in this way.
* `New.U.principalMinor_coe_inv`, `New.U.principalMinor_compl`: inverse and complementary minors in
  `New.USign ε`. This is the group of `g` in `GL n ℂ` with `gᴴ J g = J`, for the diagonal matrix
  `J = New.signMatrix ε` of signs `ε i = ±1`.
-/

section PrincipalMinors

open Matrix ComplexOrder ComplexConjugate MatrixOrder Fintype Norms.L2Operator CStarAlgebra

namespace New

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-! ### Definition and the operator norm bound -/

/-- The principal minor of the complex matrix `y` on the set of indices satisfying `p`. -/
noncomputable def principalMinor (y : Matrix n n ℂ) (p : n → Prop) [DecidablePred p] : ℂ :=
  (toSquareBlockProp y p).det

variable {x b : Matrix n n ℂ} {p : n → Prop} [DecidablePred p] {ε : n → ℤˣ} (g : USign ε)

/-- The absolute value of the principal minor of a complex square matrix `x` on the indices
satisfying `p` is at most `‖x‖ ^ k`, where `‖x‖` is the operator norm and `k` is the number of
these indices. -/
theorem norm_principalMinor_le_pow : ‖principalMinor x p‖ ≤ ‖x‖ ^ card {i // p i} := by
  -- With `A` the block of `x` on `p`: `Aᴴ * A ≤ ‖x‖ ^ 2` in the Loewner order,
  -- and taking determinants gives the square of the claim.
  set A : Matrix {i // p i} {i // p i} ℂ := x.toBlock p p with hA
  set c : Matrix n n ℂ := algebraMap ℝ (Matrix n n ℂ) (‖x‖ ^ 2) with hc
  have h_le : Aᴴ * A ≤ c.toBlock p p :=
    calc
      _ ≤ Aᴴ * A + (x.toBlock (¬p ·) p)ᴴ * x.toBlock (¬p ·) p :=
        le_add_of_nonneg_right (posSemidef_conjTranspose_mul_self _).nonneg
      _ = (star x * x).toBlock p p := (toBlock_mul_eq_add p p p (star x) x).symm
      -- restrict `star x * x ≤ ‖x‖ ^ 2` to the block
      _ ≤ c.toBlock p p := (star_mul_le_algebraMap_norm_sq (a := x)).submatrix _
  refine le_of_sq_le_sq ?_ (by positivity)
  calc
    ‖principalMinor x p‖ ^ 2 = ‖(Aᴴ * A).det‖ := by simp [sq, principalMinor, toSquareBlockProp, hA]
    _ ≤ ‖(c.toBlock p p).det‖ :=
      norm_det_le_norm_det_of_posSemidef A.posSemidef_conjTranspose_mul_self h_le
    _ = (‖x‖ ^ card {i // p i}) ^ 2 := by
      simp [hc, algebraMap_eq_diagonal, toBlock_diagonal_self, pow_right_comm]

-- lets `aesop` reduce an equality of two determinants to an equality of the two matrices
attribute [local aesop 1%] congr

/-! ### Principal minors as determinants -/

/-- A principal minor is a full determinant: with `D` the diagonal projection onto the indices
satisfying `p`, the matrix `1 - D * (1 - x)` has the rows of `x` on `p` and the rows of `1` off
`p`, and its determinant is the principal minor of `x` on `p`. -/
@[local simp low]
theorem principalMinor_eq_det :
    principalMinor x p = (1 - diagonal (fun i : n ↦ if p i then 1 else 0) * (1 - x)).det := by
  -- The matrix is block triangular, with diagonal blocks the block of `x` on `p` and `1`.
  set A : Matrix n n ℂ := 1 - diagonal (fun i ↦ if p i then 1 else 0) * (1 - x) with hA
  have h_tri (i : n) (hi : ¬p i) (j : n) (hj : p j) : A i j = 0 := by
    aesop (add simp Matrix.one_apply)
  have h_on : A.toSquareBlockProp p = x.toSquareBlockProp p := by aesop
  have h_off : A.toSquareBlockProp (¬p ·) = 1 := by
    aesop (add simp [Matrix.one_apply, toSquareBlockProp])
  simp [twoBlockTriangular_det A p h_tri, h_on, h_off, principalMinor]

/-- A principal minor of the block diagonal matrix with blocks `x` and `y` is the product of the
principal minors of `x` and `y` on the indices of each block that satisfy `p`. -/
lemma principalMinor_fromBlocks {y : Matrix m m ℂ} {p : n ⊕ m → Prop} [DecidablePred p] :
    principalMinor (fromBlocks x 0 0 y) p =
      principalMinor x (fun i : n ↦ p (Sum.inl i)) *
        principalMinor y (fun j : m ↦ p (Sum.inr j)) := by
  -- by `principalMinor_eq_det` all three minors are determinants; the left matrix is block diagonal
  simp only [principalMinor_eq_det, ← det_fromBlocks_zero₂₁ _ 0]
  congr 1
  -- the two matrices agree entrywise
  aesop (add simp Matrix.one_apply)

/-- A principal minor of the block diagonal matrix with blocks `u τ` is the product over `τ` of the
principal minors of `u τ` on the indices `i` for which `(τ, i)` satisfies `p`. -/
@[simp]
theorem principalMinor_blockDiagonal (u : m → Matrix n n ℂ) (p : m × n → Prop) [DecidablePred p] :
    principalMinor ((blockDiagonal u).submatrix Prod.swap Prod.swap) p =
      ∏ τ : m, principalMinor (u τ) fun i : n ↦ p (τ, i) := by
  -- by `principalMinor_eq_det` all minors are determinants; the left matrix is block diagonal
  simp only [principalMinor_eq_det]
  rw [← det_blockDiagonal, ← det_reindex_self (.prodComm m n)]
  congr 1
  aesop (add simp [Matrix.one_apply, blockDiagonal_apply, Matrix.ext_iff.symm])

/-- Jacobi's complementary minor theorem: for a complex square matrix `x` with `det x ≠ 0`, the
principal minor of `x⁻¹` on the indices satisfying `p` equals the principal minor of `x` on the
complementary indices divided by `det x`. -/
theorem jacobi_complementary_minor (hx : x.det ≠ 0) :
    principalMinor x⁻¹ p = principalMinor x (fun i : n ↦ ¬p i) / x.det := by
  -- With `D` the projection onto `p`, write both minors by `principalMinor_eq_det` and clear
  -- `x.det`: `(1 - D (1 - x⁻¹)) x = x - D x + D = 1 - (1 - D) (1 - x)`.
  set D : Matrix n n ℂ := diagonal (fun i : n ↦ if p i then 1 else 0) with hD
  have h_compl : diagonal (fun i : n ↦ if ¬p i then (1 : ℂ) else 0) = 1 - D := by
    aesop (add simp [Matrix.one_apply, Matrix.ext_iff.symm])
  have h_mat : (1 - D * (1 - x⁻¹)) * x = 1 - (1 - D) * (1 - x) := by
    simp [sub_mul, mul_sub, mul_assoc, nonsing_inv_mul _ hx.isUnit]
    abel
  rw [eq_div_iff hx, principalMinor_eq_det, principalMinor_eq_det, ← det_mul, h_compl, ← hD, h_mat]

@[fun_prop]
theorem continuous_principalMinor : Continuous fun y : Matrix n n ℂ ↦ principalMinor y p := by
  simp only [principalMinor_eq_det]
  fun_prop

/-! ### Special cases, products and reindexing -/

theorem principalMinor_of_forall (hp : ∀ i : n, p i) : principalMinor x p = x.det := by
  simp [principalMinor_eq_det, hp]

theorem DiscreteSeries.principalMinor_of_forall_not (hp : ∀ i : n, ¬p i) :
    principalMinor x p = 1 := by
  simp [principalMinor_eq_det, hp]

@[simp]
theorem principalMinor_one : principalMinor 1 p = 1 := by simp

@[simp]
theorem principalMinor_transpose : principalMinor xᵀ p = principalMinor x p := det_transpose _

@[simp]
theorem principalMinor_conjTranspose : principalMinor xᴴ p = conj (principalMinor x p) :=
  det_conjTranspose _

/-- Suppose `x i j * b j k` has a zero factor whenever `i`, `k` satisfy `p` and `j` does not. This
holds, for instance, when `x i j = 0` whenever `i` satisfies `p` and `j` does not. It also holds
when `b j k = 0` whenever `j` does not satisfy `p` and `k` does. Then the principal minor on `p` of
`x * b` is the product of those of `x` and `b`. -/
theorem principalMinor_mul (h_zero : ∀ i j k : n, p i → ¬p j → p k → x i j = 0 ∨ b j k = 0) :
    principalMinor (x * b) p = principalMinor x p * principalMinor b p := by
  -- the block of `x * b` on `p` is the product of the blocks plus a cross term, zero by `h_zero`
  have h_cross : x.toBlock p (¬p ·) * b.toBlock (¬p ·) p = 0 := by
    aesop (add simp [mul_apply, Matrix.ext_iff.symm]) (add simp sum_eq_zero)
  simp [principalMinor, toBlock_mul_eq_add p p, ← det_mul, h_cross, toSquareBlockProp]

theorem principalMinor_submatrix (e : m ≃ n) :
    principalMinor (x.submatrix e e) (fun i : m ↦ p (e i)) = principalMinor x p :=
  det_submatrix_equiv_self e.subtypeEquivOfSubtype (x.toSquareBlockProp p)

/-! ### Indefinite unitary groups, and the bound for the determinant -/

/-- For `g` in `USign ε = U (signMatrix ε)`, the unitary group of the diagonal matrix of signs
`ε i = ±1`, each principal minor of the inverse of `g` is the complex conjugate of the same
principal minor of `g`. -/
theorem U.principalMinor_coe_inv : principalMinor ↑g⁻¹ p = conj (principalMinor g p) := by
  -- `g⁻¹ = J gᴴ J` with `J` diagonal, so the minor is multiplicative, and `J * J = 1`.
  set J : Matrix n n ℂ := signMatrix ε
  have h_off {i j : n} (hi : p i) (hj : ¬p j) : J i j = 0 ∧ J j i = 0 := by
    aesop (add simp [signMatrix, diagonal_apply])
  have h_left (y : Matrix n n ℂ) :
      principalMinor (J * y) p = principalMinor J p * principalMinor y p :=
    principalMinor_mul fun _ _ _ hi hj _ ↦ .inl (h_off hi hj).1
  have h_right (y : Matrix n n ℂ) :
      principalMinor (y * J) p = principalMinor y p * principalMinor J p :=
    principalMinor_mul fun _ _ _ _ hj hk ↦ .inr (h_off hk hj).2
  have h_sq : principalMinor J p * principalMinor J p = 1 := by
    rw [← h_left, signMatrix_mul_self, principalMinor_one]
  rw [coe_inv (signMatrix_mul_self _), h_right, h_left, principalMinor_conjTranspose]
  linear_combination conj (principalMinor g p) * h_sq

/-- For `g` in `USign ε = U (signMatrix ε)`, the unitary group of the diagonal matrix of signs
`ε i = ±1`, the principal minor on the complement of `p` is `det g` times the conjugate of the
principal minor on `p`. -/
theorem U.principalMinor_compl :
    principalMinor g (fun i : n ↦ ¬p i) = g.val.val.det * conj (principalMinor g p) := by
  -- Jacobi's identity for `g⁻¹`, whose minor on `p` is the conjugate of that of `g`.
  have h_inv : principalMinor (g.val.val : Matrix n n ℂ)⁻¹ p = conj (principalMinor g p) := by
    rw [← coe_units_inv, ← InvMemClass.coe_inv, principalMinor_coe_inv]
  rw [← h_inv, jacobi_complementary_minor g.val.det_ne_zero, mul_div_cancel₀ _ g.val.det_ne_zero]

theorem norm_det_le_norm_pow : ‖x.det‖ ≤ ‖x‖ ^ card n := by
  simpa using norm_principalMinor_le_pow (x := x) (p := fun _ ↦ True)

end New

end PrincipalMinors

namespace New

/-!
## Hermitian involutions and coordinates on skew-hermitian matrices

* `New.skewOfReal`, `New.skewCoords`: real coordinates on skew-hermitian matrices. The `n²`
  coordinates are held in a real `n × n` matrix.
-/

section HermitianInvolution

open Matrix Complex

variable {n : Type*} [Fintype n] [DecidableEq n] (J : Matrix n n ℂ) (ε : n → ℤˣ)

/-- The complex matrix J is a hermitian involution: J* = J and J² = 1. -/
class IsHermitianInvolution where
  /-- The matrix `J` is hermitian. -/
  isHermitian : J.IsHermitian
  /-- The matrix `J` is an involution: `J² = 1`. -/
  mul_self : J * J = 1

instance : IsHermitianInvolution (signMatrix ε) where
  isHermitian := by simp [signMatrix, IsHermitian]
  mul_self := signMatrix_mul_self ε

instance : IsHermitianInvolution (n := n) 1 where
  isHermitian := by simp
  mul_self := by simp

theorem IsHermitianInvolution.det_ne_zero [IsHermitianInvolution J] : J.det ≠ 0 :=
  det_ne_zero_of_left_inverse mul_self

/-- The skew-hermitian matrix `x` with real coordinates `y`: its entries are `I * y a a` on the
diagonal and `((1 + I) * y a b - (1 - I) * y b a) / √2` off it. The factor `√2` makes
`(y a b, y b a)` an orthogonal change of `(Re x a b, Im x a b)`, so Lebesgue measure in `y` is
Lebesgue measure in `Im x a a` and `Re x a b`, `Im x a b` for one of each pair `(a, b)`, `(b, a)`,
`a ≠ b`. -/
noncomputable def skewOfReal : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℂ where
  toFun y := of fun a b ↦ ((1 + I) * y a b - (1 - I) * y b a) / if a = b then 2 else √2
  map_add' := by
    simp [funext_iff]
    grind
  map_smul' := by
    simp [funext_iff]
    grind

/-- The real coordinates of a complex matrix `x`: the entries `Re x a b + Im x a b`, divided by `√2`
off the diagonal. It is a left inverse of `New.skewOfReal`, and a two-sided one on skew-hermitian
`x`. -/
noncomputable def skewCoords : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℝ where
  toFun x := of fun a b ↦ ((x a b).re + (x a b).im) / if a = b then 1 else √2
  map_add' := by
    simp [funext_iff]
    grind
  map_smul' := by
    simp [funext_iff]
    grind

end HermitianInvolution

/-!
## Norms and determinants in the unitary group of a hermitian involution

* `New.U.norm_det`: the determinant of `g` in `New.U J` has absolute value `1`.
-/

section UnitaryNorm

open Matrix CStarRing Norms.L2Operator IsHermitianInvolution

variable {n : Type*} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ}
  [IsHermitianInvolution (n := n) J] (g : U J)

theorem IsHermitianInvolution.isUnit : IsUnit J := .of_mul_eq_one _ mul_self

theorem IsHermitianInvolution.mem_unitary : J ∈ unitary (Matrix n n ℂ) := by
  simp [Unitary.mem_iff, isHermitian.star_eq, mul_self]

/-- For a hermitian involution `J`, the determinant of an element of `U J`, the group of `g` with
`gᴴ * J * g = J`, has absolute value `1`. -/
@[simp]
theorem U.norm_det : ‖g.val.val.det‖ = 1 :=
  -- `U.det` is the determinant as a homomorphism into the complex numbers of absolute value `1`
  norm_coe_unitary (U.det (det_ne_zero J).isUnit g)

/-- For a hermitian involution `J` and `g` in `U J`, the group of `g` with `gᴴ * J * g = J`, the
inverse of `g` has the operator norm of `g`. -/
theorem U.norm_inv : ‖g⁻¹.val.val‖ = ‖g.val.val‖ := by
  -- `g⁻¹ = J * gᴴ * J` with `J` unitary, and the conjugate transpose keeps the operator norm
  have hJ : J ∈ unitary (Matrix n n ℂ) := IsHermitianInvolution.mem_unitary
  calc
    ‖g⁻¹.val.val‖ = ‖J * g.val.valᴴ * J‖ := by rw [coe_inv mul_self]
    _ = ‖J * g.val.valᴴ‖ := norm_mul_mem_unitary (J * g.val.valᴴ) hJ
    _ = ‖g.val.valᴴ‖ := norm_mem_unitary_mul g.val.valᴴ hJ
    _ = ‖g.val.val‖ := l2_opNorm_conjTranspose g.val.val

/-- For a hermitian involution `J` in positive dimension, every element of `U J`, the group of `g`
with `gᴴ * J * g = J`, has operator norm at least `1`. -/
theorem U.one_le_norm [Nonempty n] : 1 ≤ ‖g.val.val‖ := by
  refine (one_le_sq_iff₀ (norm_nonneg _)).1 ?_
  calc
    (1 : ℝ) = ‖g⁻¹.val.val * g.val.val‖ := by simp
    _ ≤ ‖g.val.val‖ ^ 2 := (norm_mul_le _ _).trans_eq (by rw [norm_inv g, pow_two])

end UnitaryNorm

end New
