import Lib.Adelic.Witt.WittTheorem
import New.Appendix.DiscreteSeries.SteepParameters

/-!
# Positions of a smaller unitary group, and the two traces

A position of `U(η)` in `U(ε)` consists of independent vectors `v₁, …, v_{j₀}` and an isometry `i₀`
into their orthogonal complement. It is stationary for two weights `μ`, `μ'` if `μ` moves `v_j` to
`v_{j + 1}` for `j < j₀` and compresses to `μ'` on the image of `i₀`, and `i₀` is the identity on
the common coordinates `X`. For a matrix `Y` that lowers the flag of the `v_j` together with its
adjoint, and induces `Y'` on the image of `i₀`, we compute `tr Y - tr Y'` and `tr μ Y - tr μ' Y'`.

Notions from other files:
* `signMatrix ε` is the diagonal matrix of the signs `ε i = ±1`, and `USign ε` its unitary group.
* `HCParam ε` consists of the integer vectors on `n`, used as doubled Harish-Chandra parameters
  `l = 2 λ`; `l.lowestKType` is the weight of the lowest `K`-type and `intDiagonal w` the diagonal
  matrix of a weight `w`.
* `l.phase k (Y, Y')` is `tr μ Y - tr μ' Y'` for the weights `μ`, `μ'` of the lowest `K`-types of
  `l` and `k`.
-/

noncomputable section

open Finset Matrix ComplexConjugate

namespace New.DiscreteSeries

variable {n m X : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The adjoint `A†` of `A : (ℂ^m, η) → (ℂ^n, ε)` for the two hermitian forms. -/
def formAdjoint (ε : n → ℤˣ) (η : m → ℤˣ) (A : Matrix n m ℂ) : Matrix m n ℂ :=
  signMatrix η * Aᴴ * signMatrix ε

/-- The columns `v₁, …, v_{j₀ - 1}` of `v = (v₁, …, v_{j₀})`, where `j₀ = d + 1`. -/
def initCols {d : ℕ} (v : Matrix n (Fin (d + 1)) ℂ) : Matrix n (Fin d) ℂ :=
  v.submatrix id Fin.castSucc

/-- A position of `U(η)` in `U(ε)`, where the ranks differ by `2 j₀ - 1` and `j₀ = d + 1`. It
consists of independent vectors `v₁, …, v_{j₀}`, the columns of `v`, whose pairings for the form
`ε` vanish except that the pairing of `v_{j₀}` with itself is `±1`, and of an isometry `i₀` into
their orthogonal complement. -/
structure IsPosition (ε : n → ℤˣ) (η : m → ℤˣ) (d : ℕ) (v : Matrix n (Fin (d + 1)) ℂ)
    (i₀ : Matrix n m ℂ) : Prop where
  /-- The ranks differ by `2 j₀ - 1`. -/
  card_eq : Fintype.card n = Fintype.card m + 2 * d + 1
  /-- The vectors `v₁, …, v_{j₀}` are independent. -/
  independent : LinearIndependent ℂ v.col
  /-- The product of `v_i` and `v_j` vanishes unless `i = j = j₀`. -/
  gram_eq_zero (a b : Fin (d + 1)) :
    a ≠ Fin.last d ∨ b ≠ Fin.last d → (vᴴ * signMatrix ε * v) a b = 0
  /-- The pairing of `v_{j₀}` with itself, which can be negative, is `±1`. -/
  gram_last_eq_sign : (vᴴ * signMatrix ε * v) (Fin.last d) (Fin.last d) = 1 ∨
    (vᴴ * signMatrix ε * v) (Fin.last d) (Fin.last d) = -1
  /-- The map `i₀` is an isometry. -/
  isometry : i₀ᴴ * signMatrix ε * i₀ = signMatrix η
  /-- The image of `i₀` is orthogonal to `v₁, …, v_{j₀}`. -/
  orthogonal : i₀ᴴ * signMatrix ε * v = 0

/-- Let `A_{≤ j}` be the span of the columns `v₁, …, v_j` of `v`. Then `Y` maps `A_{≤ j}` into
`A_{≤ j - 1}` for `j ≤ j₀ = d + 1`, and `σ` is the sum of the coefficients of `v_j` in
`Y v_{j + 1}` over `j < j₀`, which is determined by `Y` if the `v_j` are independent. -/
def LowersFlag (d : ℕ) (v : Matrix n (Fin (d + 1)) ℂ) (Y : Matrix n n ℂ) (σ : ℂ) : Prop :=
  ∃ N : Matrix (Fin d) (Fin (d + 1)) ℂ,
    (∀ (a : Fin d) (b : Fin (d + 1)), b.val ≤ a.val → N a b = 0) ∧
    Y * v = initCols v * N ∧
    ∑ a : Fin d, N a a.succ = σ

/-- `Y` acts by `Y'` on the image of `i₀`, modulo the span `A_{≤ j₀ - 1}` of `v₁, …, v_{j₀ - 1}`. -/
def InducesOn (d : ℕ) (v : Matrix n (Fin (d + 1)) ℂ) (i₀ : Matrix n m ℂ) (Y : Matrix n n ℂ)
    (Y' : Matrix m m ℂ) : Prop :=
  ∃ C : Matrix (Fin d) m ℂ, Y * i₀ = i₀ * Y' + initCols v * C

/-- A stationary position. Let `μ`, `μ'` be the weights of the lowest `K`-types of `l`, `k`, as
diagonal matrices. Then `μ` moves `v_j` to `v_{j + 1}` for `j < j₀` and compresses to `μ'`, and `i₀`
is the identity on `ℂ^X`, where `e` and `e'` place `X` among the coordinates `n` and `m`. -/
structure IsStationary {ε : n → ℤˣ} {η : m → ℤˣ} (l : HCParam ε) (k : HCParam η) {L L' : ℕ}
    (e : X ⊕ Fin L ≃ n) (e' : X ⊕ Fin L' ≃ m) (d : ℕ) (v : Matrix n (Fin (d + 1)) ℂ)
    (i₀ : Matrix n m ℂ) : Prop extends IsPosition ε η d v i₀ where
  /-- `μ v_j = v_{j + 1}` for `j < j₀`. -/
  shift : intDiagonal l.lowestKType * initCols v = v.submatrix id Fin.succ
  /-- `i₀† μ i₀ = μ'`. -/
  adjoint_weight_mul_eq : formAdjoint ε η i₀ * intDiagonal l.lowestKType * i₀ = intDiagonal
    k.lowestKType
  /-- `i₀ = 1` on `ℂ^X`. -/
  apply_inl (i : n) (x : X) : i₀ i (e' (Sum.inl x)) = if i = e (Sum.inl x) then 1 else 0

variable {ε : n → ℤˣ} {η : m → ℤˣ} {d : ℕ} {v : Matrix n (Fin (d + 1)) ℂ} {i₀ : Matrix n m ℂ}

section Adjoint

/-- The adjoint for the forms reverses products: `(A A')† = A'† A†`. -/
lemma formAdjoint_mul {p : Type} [Fintype p] {κ : p → ℤˣ} [DecidableEq p] (A : Matrix n m ℂ)
    (A' : Matrix m p ℂ) : formAdjoint ε κ (A * A') = formAdjoint η κ A' * formAdjoint ε η A := by
  simp only [formAdjoint, conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (signMatrix η) (signMatrix η), signMatrix_mul_self, Matrix.one_mul]

lemma formAdjoint_sub (A A' : Matrix n m ℂ) :
    formAdjoint ε η (A - A') = formAdjoint ε η A - formAdjoint ε η A' := by
  simp only [formAdjoint, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]

lemma formAdjoint_formAdjoint (A : Matrix n m ℂ) : formAdjoint η ε (formAdjoint ε η A) = A := by
  simp [formAdjoint, conjTranspose_mul, IsHermitianInvolution.isHermitian.eq, Matrix.mul_assoc,
    signMatrix_mul_self, ← Matrix.mul_assoc (signMatrix ε) (signMatrix ε)]

lemma trace_formAdjoint (Y : Matrix n n ℂ) : (formAdjoint ε ε Y).trace = conj Y.trace := by
  rw [formAdjoint, trace_mul_cycle, signMatrix_mul_self, Matrix.one_mul, trace_conjTranspose,
    starRingEnd_apply]

lemma formAdjoint_intDiagonal (w : n → ℤ) : formAdjoint ε ε (intDiagonal w) = intDiagonal w := by
  have h_comm : signMatrix ε * (intDiagonal w)ᴴ = intDiagonal w * signMatrix ε := by
    simp [signMatrix, diagonal_conjTranspose, mul_comm]
  rw [formAdjoint, h_comm, Matrix.mul_assoc, signMatrix_mul_self, Matrix.mul_one]

lemma formAdjoint_one : formAdjoint ε ε (1 : Matrix n n ℂ) = 1 := by
  rw [formAdjoint, conjTranspose_one, Matrix.mul_one, signMatrix_mul_self]

/-- On the group `U(ε)` the adjoint for the form is the inverse. -/
lemma formAdjoint_val (g : USign ε) :
    formAdjoint ε ε ((g : GL n ℂ) : Matrix n n ℂ) = ((g⁻¹ : USign ε) : Matrix n n ℂ) :=
  (U.coe_inv IsHermitianInvolution.mul_self g).symm

/-- For `g` in `U(ε)` the adjoint of `g - 1` is `g⁻¹ - 1`. -/
lemma formAdjoint_sub_one (g : USign ε) :
    formAdjoint ε ε (((g : GL n ℂ) : Matrix n n ℂ) - 1) =
      ((g⁻¹ : USign ε) : Matrix n n ℂ) - 1 := by
  rw [formAdjoint_sub, formAdjoint_val, formAdjoint_one]

/-- A map `A` with `A† A = 1` is an isometry. -/
lemma isometry_of_formAdjoint_mul_self {A : Matrix n m ℂ} (hA : formAdjoint ε η A * A = 1) :
    Aᴴ * signMatrix ε * A = signMatrix η := by
  simpa [formAdjoint, ← Matrix.mul_assoc, signMatrix_mul_self] using
    congrArg (signMatrix η * ·) hA

/-- Let `τ` take values among the coordinates of sign `+1`. Then the adjoint for the forms `ε` and
`1` of the matrix with columns the standard vectors at `τ x` is its usual adjoint. -/
lemma formAdjoint_inclMatrix [Fintype X] [DecidableEq X] {τ : X → n} (hτ : ∀ x : X, ε (τ x) = 1) :
    formAdjoint ε 1 (inclMatrix ℂ τ) = (inclMatrix ℂ τ)ᴴ := by
  ext x i
  rcases eq_or_ne i (τ x) with rfl | hi
  · simp [formAdjoint, signMatrix, inclMatrix, one_apply, hτ]
  · simp [formAdjoint, signMatrix, inclMatrix, one_apply, hi, hi.symm]

end Adjoint

namespace IsPosition

lemma formAdjoint_mul_self (hP : IsPosition ε η d v i₀) : formAdjoint ε η i₀ * i₀ = 1 := by
  simpa [formAdjoint, Matrix.mul_assoc, signMatrix_mul_self] using
    congrArg (signMatrix η * ·) hP.isometry

lemma formAdjoint_mul_vec (hP : IsPosition ε η d v i₀) : formAdjoint ε η i₀ * v = 0 := by
  simpa [formAdjoint, Matrix.mul_assoc] using congrArg (signMatrix η * ·) hP.orthogonal

lemma vec_orthogonal (hP : IsPosition ε η d v i₀) : vᴴ * signMatrix ε * i₀ = 0 := by
  simpa [IsHermitianInvolution.isHermitian.eq, Matrix.mul_assoc] using
    congrArg conjTranspose hP.orthogonal

lemma initCols_orthogonal (hP : IsPosition ε η d v i₀) : (initCols v)ᴴ * signMatrix ε * i₀ = 0 :=
  show (vᴴ * signMatrix ε * i₀).submatrix Fin.castSucc id = 0 by simp [hP.vec_orthogonal]

/-- In a position (`hP : IsPosition ε η d v i₀`), the span of all the columns of `v` is orthogonal,
for the form `ε`, to the span of its first `d` columns `initCols v`:
`vᴴ * signMatrix ε * initCols v = 0`. -/
lemma orthogonal_initCols (hP : IsPosition ε η d v i₀) : vᴴ * signMatrix ε * initCols v = 0 :=
  Matrix.ext fun a b ↦ hP.gram_eq_zero a b.castSucc (Or.inr b.castSucc_ne_last)

/-- In a position (`hP : IsPosition ε η d v i₀`), the span of the first `d` columns `initCols v` of
`v` is orthogonal, for the form `ε`, to the span of all the columns of `v`:
`(initCols v)ᴴ * signMatrix ε * v = 0`. -/
lemma initCols_isotropic (hP : IsPosition ε η d v i₀) : (initCols v)ᴴ * signMatrix ε * v = 0 :=
  Matrix.ext fun a b ↦ hP.gram_eq_zero a.castSucc b (Or.inl a.castSucc_ne_last)

/-- Let `(v, i₀)` be a position (`IsPosition`): the columns `v₁, …, v_{j₀}` of `v`, where
`j₀ = d + 1`, are independent, and `i₀` is an isometry into their orthogonal complement for the
forms with signs `η` and `ε`. Then some matrix `Z` gives coordinates along all the `v_j` and
vanishes on the image of `i₀`: it satisfies `Z i₀ = 0` and `Z v = 1`. -/
lemma exists_mul_eq_zero_and_mul_eq_one (hP : IsPosition ε η d v i₀) :
    ∃ Z : Matrix (Fin (d + 1)) n ℂ, Z * i₀ = 0 ∧ Z * v = 1 := by
  obtain ⟨T, hT⟩ : HasLeftInv v := .of_ker_le_bot
    (LinearMap.ker_eq_bot.2 (mulVec_injective_iff.2 hP.independent) : v.mulVecLin.ker = ⊥).le
  -- Project away from the image of `i₀` first.
  refine ⟨T * (1 - i₀ * formAdjoint ε η i₀), ?_, ?_⟩
  · simp [Matrix.mul_assoc, Matrix.sub_mul, hP.formAdjoint_mul_self]
  · simp [Matrix.mul_assoc, Matrix.sub_mul, hP.formAdjoint_mul_vec, hT]

/-- Let `(v, i₀)` be a position (`IsPosition`): the columns `v₁, …, v_{j₀}` of `v`, where
`j₀ = d + 1`, are independent, and `i₀` is an isometry into their orthogonal complement for the
forms with signs `η` and `ε`. Then some matrix `Z` gives coordinates along the first `j₀ - 1` of
these vectors, the columns of `initCols v`, and vanishes on the image of `i₀`. -/
lemma exists_mul_eq_zero_and_mul_initCols_eq_one (hP : IsPosition ε η d v i₀) :
    ∃ Z : Matrix (Fin d) n ℂ, Z * i₀ = 0 ∧ Z * initCols v = 1 := by
  obtain ⟨Z, hZ_zero, hZ_one⟩ := hP.exists_mul_eq_zero_and_mul_eq_one
  refine ⟨Z.submatrix Fin.castSucc id, congrArg (·.submatrix Fin.castSucc id) hZ_zero, ?_⟩
  show (Z * v).submatrix Fin.castSucc Fin.castSucc = 1
  rw [hZ_one, submatrix_one _ (Fin.castSucc_injective d)]

/-- The columns of `i₀` and the vectors `v₁, …, v_{j₀}` of a position are independent. -/
lemma hasLeftInv (hP : IsPosition ε η d v i₀) : HasLeftInv (fromCols i₀ v) := by
  obtain ⟨Z, hZ_zero, hZ_one⟩ := hP.exists_mul_eq_zero_and_mul_eq_one
  exact ⟨fromRows (formAdjoint ε η i₀) Z, by
    simp [hP.formAdjoint_mul_self, hP.formAdjoint_mul_vec, hZ_zero, hZ_one]⟩

/-- Let `(v, i₀)` be a position of `U(η)` in `U(ε)` (`IsPosition`): the columns `v₁, …, v_{j₀}` of
`v`, where `j₀ = d + 1`, are independent, their pairings for the form with signs `ε` vanish except
that of `v_{j₀}` with itself, which is `±1`, and `i₀` is an isometry into their orthogonal
complement. Let `A` be the span of `v₁, …, v_{j₀ - 1}`, the columns of `initCols v`. If the columns
of `M` are orthogonal to `A`, then they are linear combinations, with coefficient matrix `T`, of
the columns of `i₀` and of `v`. -/
lemma exists_eq_of_orthogonal (hP : IsPosition ε η d v i₀) {p : Type} {M : Matrix n p ℂ}
    (hM : (initCols v)ᴴ * signMatrix ε * M = 0) :
    ∃ T : Matrix (m ⊕ Fin (d + 1)) p ℂ, M = fromCols i₀ v * T := by
  -- The span of the columns lies in the kernel of the pairing with `A`, and the dimensions agree.
  obtain ⟨W, hW⟩ : ∃ W : Matrix (m ⊕ Fin (d + 1)) n ℂ, W * fromCols i₀ v = 1 := hP.hasLeftInv
  obtain ⟨Z, -, hZ⟩ : ∃ Z : Matrix (Fin d) n ℂ, Z * i₀ = 0 ∧ Z * initCols v = 1 :=
    hP.exists_mul_eq_zero_and_mul_initCols_eq_one
  set combination : (m ⊕ Fin (d + 1) → ℂ) →ₗ[ℂ] n → ℂ := (fromCols i₀ v).mulVecLin
  set pairing : (n → ℂ) →ₗ[ℂ] Fin d → ℂ := ((initCols v)ᴴ * signMatrix ε).mulVecLin
  have h_inj : Function.Injective combination :=
    Function.LeftInverse.injective (g := W.mulVec) fun x ↦ by
      rw [mulVecLin_apply, mulVec_mulVec, hW, one_mulVec]
  have h_right : (initCols v)ᴴ * signMatrix ε * (signMatrix ε * Zᴴ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (signMatrix ε), signMatrix_mul_self, Matrix.one_mul,
      ← conjTranspose_mul, hZ, conjTranspose_one]
  have h_surj : Function.Surjective pairing :=
    Function.RightInverse.surjective (g := (signMatrix ε * Zᴴ).mulVec) fun x ↦ by
      rw [mulVecLin_apply, mulVec_mulVec, h_right, one_mulVec]
  have h_eq : LinearMap.range combination = LinearMap.ker pairing := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [LinearMap.range_le_ker_iff, ← mulVecLin_mul, mul_fromCols, hP.initCols_orthogonal,
        hP.initCols_isotropic, fromCols_zero, mulVecLin_zero]
    · have h_combination_rank :
          Module.finrank ℂ (LinearMap.range combination) = Fintype.card m + (d + 1) := by
        simp [LinearMap.finrank_range_of_inj h_inj]
      have h_pairing_rank : Module.finrank ℂ (LinearMap.range pairing) = d := by
        rw [LinearMap.range_eq_top.2 h_surj, finrank_top, Module.finrank_fin_fun]
      have h_rank : d + Module.finrank ℂ (LinearMap.ker pairing) = Fintype.card m + 2 * d + 1 := by
        simpa [h_pairing_rank, hP.card_eq] using pairing.finrank_range_add_finrank_ker
      omega
  have h_col (j : p) : ∃ x : m ⊕ Fin (d + 1) → ℂ, combination x = Mᵀ j := by
    rw [← LinearMap.mem_range, h_eq, LinearMap.mem_ker]
    exact funext fun a ↦ congrFun₂ hM a j
  choose T hT using h_col
  exact ⟨(of T)ᵀ, Matrix.ext fun i j ↦ (congrFun (hT j) i).symm⟩

/-- Let `(v, i₀)` be a position (`IsPosition`): the columns `v₁, …, v_{j₀}` of `v`, where
`j₀ = d + 1`, are independent with vanishing pairings for the form with signs `ε`, except that of
`v_{j₀}` with itself, and `i₀` is an isometry into their orthogonal complement. Let `Y` map the
span of the `v_j` into `A`, the span of the first `j₀ - 1` of them (the columns of `initCols v`),
with matrix `N`, and let it act by `Y'` on the image of `i₀` modulo `A` (`InducesOn`). If `M`
vanishes on `A` and has its image in the orthogonal complement of `A`, then
`tr M Y = tr (i₀† M i₀) Y'`, with `i₀†` the adjoint for the two forms. -/
lemma trace_mul_eq_of_mul_initCols_eq_zero (hP : IsPosition ε η d v i₀) {M Y : Matrix n n ℂ}
    {Y' : Matrix m m ℂ} {N : Matrix (Fin d) (Fin (d + 1)) ℂ} (hN : Y * v = initCols v * N)
    (hY' : InducesOn d v i₀ Y Y') (h_ker : M * initCols v = 0)
    (h_range : (initCols v)ᴴ * signMatrix ε * M = 0) :
    (M * Y).trace = (formAdjoint ε η i₀ * M * i₀ * Y').trace := by
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin d) m ℂ, Y * i₀ = i₀ * Y' + initCols v * C := hY'
  obtain ⟨W, hW⟩ := hP.hasLeftInv
  -- `T` gives the coordinates of the columns of `M` along `i₀` and `v₁, …, v_{j₀}`.
  obtain ⟨T, rfl⟩ : ∃ T : Matrix (m ⊕ Fin (d + 1)) n ℂ, M = fromCols i₀ v * T :=
    hP.exists_eq_of_orthogonal h_range
  have hT_coord : T = W * (fromCols i₀ v * T) := by rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  have hT_ker : T * initCols v = 0 := by
    rw [hT_coord, Matrix.mul_assoc, h_ker, Matrix.mul_zero]
  have hT_top : formAdjoint ε η i₀ * (fromCols i₀ v * T) = toRows₁ T := by
    rw [← Matrix.mul_assoc, mul_fromCols, hP.formAdjoint_mul_self, hP.formAdjoint_mul_vec,
      ← fromRows_toRows T, fromCols_mul_fromRows]
    simp
  have h_blocks : T * (Y * fromCols i₀ v) = fromCols (T * i₀ * Y') 0 := by
    rw [mul_fromCols, hN, hC, mul_fromCols]
    simp [Matrix.mul_add, ← Matrix.mul_assoc, hT_ker]
  calc (fromCols i₀ v * T * Y).trace = (T * (Y * fromCols i₀ v)).trace := by
        rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
    _ = (toRows₁ T * i₀ * Y').trace := by
        rw [h_blocks]
        simp [trace, Fintype.sum_sum_type, mul_apply]
    _ = (formAdjoint ε η i₀ * (fromCols i₀ v * T) * i₀ * Y').trace := by rw [hT_top]

/-- Let `(v, i₀)` be a position (`IsPosition`): the columns `v₁, …, v_{j₀}` of `v`, where
`j₀ = d + 1`, are independent with vanishing pairings for the form with signs `ε`, except that of
`v_{j₀}` with itself, and `i₀` is an isometry into their orthogonal complement. Let `i₀†` be its
adjoint for the two forms, and let `μ` be self-adjoint and send each `v_j`, for `j < j₀`, to
`v_{t j}`, where `t` is any map of indices. Let `Y` and its adjoint `Y†` map the span of all the
`v_j` into the span `A` of the first `j₀ - 1` of them, with the matrices `N` and `N'`, and let
`Y` act by `Y'` on the image of `i₀` modulo `A` (`InducesOn`). Then
`tr μ Y = tr (i₀† μ i₀) Y' + ∑ N j (t j) + conj (∑ N' j (t j))`. The terms come from a split of
`μ` into a self-adjoint rest that vanishes on `A`, its part `μ₁` on `A`, and the adjoint of
`μ₁`. -/
lemma trace_mul_eq_trace_add_sum_of_inducesOn (hP : IsPosition ε η d v i₀) {μ Y : Matrix n n ℂ}
    {Y' : Matrix m m ℂ} {t : Fin d → Fin (d + 1)} {N N' : Matrix (Fin d) (Fin (d + 1)) ℂ}
    (hμ : formAdjoint ε ε μ = μ) (ht : μ * initCols v = v.submatrix id t)
    (hY' : InducesOn d v i₀ Y Y') (hN : Y * v = initCols v * N)
    (hN' : formAdjoint ε ε Y * v = initCols v * N') :
    (μ * Y).trace = (formAdjoint ε η i₀ * μ * i₀ * Y').trace + ∑ a : Fin d, N a (t a) +
      conj (∑ a : Fin d, N' a (t a)) := by
  obtain ⟨Z, hZ_zero, hZ_one⟩ : ∃ Z : Matrix (Fin d) n ℂ, Z * i₀ = 0 ∧ Z * initCols v = 1 :=
    hP.exists_mul_eq_zero_and_mul_initCols_eq_one
  -- `μ₁` is `μ` on `A` and `0` on a complement of `A` that contains the image of `i₀`.
  set μ₁ : Matrix n n ℂ := μ * initCols v * Z with hμ₁
  have h_on_flag : μ₁ * initCols v = μ * initCols v := by simp [hμ₁, Matrix.mul_assoc, hZ_one]
  have h_on_range : μ₁ * i₀ = 0 := by simp [hμ₁, Matrix.mul_assoc, hZ_zero]
  -- The image of `μ₁` lies in `A_{≤ j₀}`, so `μ₁†` vanishes on `A` and on the image of `i₀`.
  have h_adj_zero {p : Type} {A : Matrix n p ℂ} (hA : vᴴ * signMatrix ε * A = 0) :
      formAdjoint ε ε μ₁ * A = 0 := by
    have h_zero : (v.submatrix id t)ᴴ * signMatrix ε * A = 0 := congrArg (·.submatrix t id) hA
    simp only [Matrix.mul_assoc] at h_zero
    simp only [formAdjoint, hμ₁, ht, conjTranspose_mul, Matrix.mul_assoc, h_zero, Matrix.mul_zero]
  have h_adj_flag : formAdjoint ε ε μ₁ * initCols v = 0 := h_adj_zero hP.orthogonal_initCols
  have h_adj_range : formAdjoint ε ε μ₁ * i₀ = 0 := h_adj_zero hP.vec_orthogonal
  -- The rest is self-adjoint and vanishes on `A`, so its image is orthogonal to `A`.
  set M : Matrix n n ℂ := μ - μ₁ - formAdjoint ε ε μ₁ with hM
  have hM_adj : formAdjoint ε ε M = M := by
    rw [hM, formAdjoint_sub, formAdjoint_sub, formAdjoint_formAdjoint, hμ, sub_right_comm]
  have hM_ker : M * initCols v = 0 := by simp [hM, Matrix.sub_mul, h_on_flag, h_adj_flag]
  have hM_range : (initCols v)ᴴ * signMatrix ε * M = 0 := by
    rw [← hM_adj, formAdjoint, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_assoc _ (signMatrix ε) (signMatrix ε), signMatrix_mul_self]
    simp [← conjTranspose_mul, hM_ker]
  have hM_on_range : M * i₀ = μ * i₀ := by simp [hM, Matrix.sub_mul, h_on_range, h_adj_range]
  have h_middle : (M * Y).trace = (formAdjoint ε η i₀ * μ * i₀ * Y').trace := by
    rw [hP.trace_mul_eq_of_mul_initCols_eq_zero hN hY' hM_ker hM_range, Matrix.mul_assoc _ M,
      hM_on_range, ← Matrix.mul_assoc]
  -- `Y μ₁` sends `v_j` to `Y v_{t j}` and vanishes on the complement.
  have h_trace_μ₁_mul {Y₀ : Matrix n n ℂ} {N₀ : Matrix (Fin d) (Fin (d + 1)) ℂ}
      (hN₀ : Y₀ * v = initCols v * N₀) : (μ₁ * Y₀).trace = ∑ a : Fin d, N₀ a (t a) := by
    have h_cols : Y₀ * v.submatrix id t = initCols v * N₀.submatrix id t :=
      congrArg (·.submatrix id t) hN₀
    calc (μ₁ * Y₀).trace = (initCols v * N₀.submatrix id t * Z).trace := by
          rw [trace_mul_comm, hμ₁, ht, ← Matrix.mul_assoc, h_cols]
      _ = (N₀.submatrix id t).trace := by rw [trace_mul_cycle, hZ_one, Matrix.one_mul]
      _ = ∑ a : Fin d, N₀ a (t a) := rfl
  have h_trace_adjoint_mul :
      (formAdjoint ε ε μ₁ * Y).trace = conj (∑ a : Fin d, N' a (t a)) := by
    rw [← h_trace_μ₁_mul hN', ← trace_formAdjoint (ε := ε), formAdjoint_mul (η := ε),
      formAdjoint_formAdjoint, trace_mul_comm]
  rw [← h_middle, ← h_trace_μ₁_mul hN, ← h_trace_adjoint_mul, hM, Matrix.sub_mul, Matrix.sub_mul,
    trace_sub, trace_sub]
  ring

/-- Let `(v, i₀)` be a position (`IsPosition`); only the independence of the columns
`v₁, …, v_{j₀}` of `v`, where `j₀ = d + 1`, matters here. Let `Y` lower their flag
(`LowersFlag`): it sends `v₁` to `0` and each `v_{j + 1}` into the span of `v₁, …, v_j`. Then the
sum `σ` of the coefficients of `v_j` in `Y v_{j + 1}` is determined by `Y`. -/
lemma lowersFlag_unique (hP : IsPosition ε η d v i₀) {Y : Matrix n n ℂ} {σ σ' : ℂ}
    (hσ : LowersFlag d v Y σ) (hσ' : LowersFlag d v Y σ') : σ = σ' := by
  obtain ⟨N, -, hN, rfl⟩ := hσ
  obtain ⟨N', -, hN', rfl⟩ := hσ'
  obtain ⟨Z, -, hZ⟩ := hP.exists_mul_eq_zero_and_mul_initCols_eq_one
  have h_eq : N = N' :=
    calc N = Z * (initCols v * N) := by rw [← Matrix.mul_assoc, hZ, Matrix.one_mul]
      _ = Z * (initCols v * N') := by rw [← hN, hN']
      _ = N' := by rw [← Matrix.mul_assoc, hZ, Matrix.one_mul]
  rw [h_eq]

end IsPosition

/-- Let `g₁ - 1` and `g₂ - 1` lower the flag of the columns `v₁, …, v_{d + 1}` of `v`
(`LowersFlag`): they send `v₁` to `0` and each `v_{j + 1}` into the span of `v₁, …, v_j`, and the
coefficients of `v_j` in the images of the `v_{j + 1}` add up to `σ₁` and to `σ₂`. Then
`g₁ g₂ - 1` lowers the flag with sum `σ₁ + σ₂`, as `(g₁ - 1) (g₂ - 1)` lowers it by two steps. -/
lemma LowersFlag.mul {g₁ g₂ : Matrix n n ℂ} {σ₁ σ₂ : ℂ} (h₁ : LowersFlag d v (g₁ - 1) σ₁)
    (h₂ : LowersFlag d v (g₂ - 1) σ₂) : LowersFlag d v (g₁ * g₂ - 1) (σ₁ + σ₂) := by
  have h_prod : g₁ * g₂ - 1 = g₁ - 1 + (g₂ - 1) + (g₁ - 1) * (g₂ - 1) := by noncomm_ring
  rw [h_prod]
  generalize g₁ - 1 = Y₁, g₂ - 1 = Y₂ at h₁ h₂ ⊢
  obtain ⟨N₁, hN₁_tri, hN₁, rfl⟩ := h₁
  obtain ⟨N₂, hN₂_tri, hN₂, rfl⟩ := h₂
  have h_two_steps (a : Fin d) (b : Fin (d + 1)) (hba : b.val ≤ a.val + 1) :
      (N₁.submatrix id Fin.castSucc * N₂) a b = 0 := by
    rw [Matrix.mul_apply]
    refine sum_eq_zero fun (t : Fin d) _ ↦ mul_eq_zero.2 ?_
    exact (le_or_gt t.val a.val).imp (hN₁_tri a t.castSucc) fun hat ↦ hN₂_tri t b (by omega)
  have hN₁_init : Y₁ * initCols v = initCols v * N₁.submatrix id Fin.castSucc :=
    congrArg (·.submatrix id Fin.castSucc) hN₁
  refine ⟨N₁ + N₂ + N₁.submatrix id Fin.castSucc * N₂, fun a b hba ↦ ?_, ?_, ?_⟩
  · simp [hN₁_tri a b hba, hN₂_tri a b hba, h_two_steps a b (by omega)]
  · show (Y₁ + Y₂ + Y₁ * Y₂) * v =
      initCols v * (N₁ + N₂ + N₁.submatrix id Fin.castSucc * N₂)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hN₁, hN₂]
    rw [← Matrix.mul_assoc, hN₁_init, Matrix.mul_assoc]
  · -- The product term vanishes next to the diagonal.
    simp [sum_add_distrib, h_two_steps]

variable {l : HCParam ε} {k : HCParam η} {L L' : ℕ} {e : X ⊕ Fin L ≃ n} {e' : X ⊕ Fin L' ≃ m}

/-- In a stationary position `(v, i₀)` for the parameters `l` and `k` let `μ` be the weight of the
lowest `K`-type of `l`, as a diagonal matrix. Then `μ ^ a v₁ = v_{a + 1}` for `a < j₀ = d + 1`. -/
lemma IsStationary.pow_mulVec_col_zero (hP : IsStationary l k e e' d v i₀) (a : Fin (d + 1)) :
    intDiagonal l.lowestKType ^ a.val *ᵥ v.col 0 = v.col a := by
  induction a using Fin.induction with
  | zero => simp
  | succ a ih =>
    rw [Fin.val_succ, pow_succ', ← mulVec_mulVec, ← Fin.val_castSucc, ih]
    exact congrArg (·.col a) hP.shift

/-- Let `μ`, `μ'` be the weights of the lowest `K`-types of the parameters `l` of `U(ε)` and `k` of
`U(η)`, as diagonal matrices. Let `(v, i₀)` be a stationary position (`IsStationary`): a position in
which `μ v_j = v_{j + 1}` for `j < j₀ = d + 1`, and `i₀† μ i₀ = μ'`. If `a + b ≤ 2 d`, the pairing
of `μ ^ a v₁` and `μ ^ b v₁` for the hermitian form with signs `ε` is the pairing of `v_{j₀}` with
itself (which is `±1`) if `a + b = 2 d`, and `0` otherwise. -/
lemma IsStationary.gram_pow_mulVec (hP : IsStationary l k e e' d v i₀) {a b : ℕ}
    (hab : a + b ≤ 2 * d) :
    star (intDiagonal l.lowestKType ^ a *ᵥ v.col 0) ⬝ᵥ
        signMatrix ε *ᵥ intDiagonal l.lowestKType ^ b *ᵥ v.col 0 =
      if a + b = 2 * d then (vᴴ * signMatrix ε * v) (Fin.last d) (Fin.last d) else 0 := by
  -- As `μ` is self-adjoint, the product depends only on `a + b`.
  set μ : Matrix n n ℂ := intDiagonal l.lowestKType with hμ
  have h_gram_eq_pow_add (a b : ℕ) :
      star (μ ^ a *ᵥ v.col 0) ⬝ᵥ signMatrix ε *ᵥ μ ^ b *ᵥ v.col 0 =
      star (v.col 0) ⬝ᵥ (signMatrix ε * μ ^ (a + b)) *ᵥ v.col 0 := by
    have h_adj : (μ ^ a)ᴴ * signMatrix ε = signMatrix ε * μ ^ a := by
      simp [hμ, signMatrix, diagonal_pow, diagonal_conjTranspose, mul_comm]
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, h_adj, pow_add,
      Matrix.mul_assoc]
  -- Write `a + b = a' + b'` with `a', b' ≤ d`; then the product is that of two of the `v_j`.
  obtain ⟨a', b', h_split⟩ : ∃ a' b' : Fin (d + 1), a + b = a'.val + b'.val :=
    ⟨⟨min (a + b) d, by omega⟩, ⟨a + b - min (a + b) d, by omega⟩, by simp⟩
  have h_gram : star (v.col a') ⬝ᵥ signMatrix ε *ᵥ v.col b' = (vᴴ * signMatrix ε * v) a' b' :=
    (congrFun₂ (Matrix.mul_assoc vᴴ (signMatrix ε) v) a' b').symm
  rw [h_gram_eq_pow_add, h_split, ← h_gram_eq_pow_add, hP.pow_mulVec_col_zero,
    hP.pow_mulVec_col_zero, h_gram]
  split_ifs with h_eq
  · rw [Fin.eq_last_of_not_lt (i := a') (by omega), Fin.eq_last_of_not_lt (i := b') (by omega)]
  · exact hP.gram_eq_zero a' b' (by grind)

/-- Let `(v, i₀)` be a position of `U(η)` in `U(ε)` (`IsPosition`): the columns `v₁, …, v_{j₀}` of
`v`, where `j₀ = d + 1`, are independent with vanishing pairings for the form with signs `ε`,
except that of `v_{j₀}` with itself, and `i₀` is an isometry into their orthogonal complement. Let
`Y` and its adjoint `Y†` for the form lower the flag of the `v_j` (`LowersFlag`: each `v_j` goes
into the span of the earlier ones), and let `Y` act by `Y'` on the image of `i₀` modulo the span of
`v₁, …, v_{j₀ - 1}` (`InducesOn`). Then `tr Y = tr Y'`. -/
lemma IsPosition.trace_eq (hP : IsPosition ε η d v i₀) {Y : Matrix n n ℂ} {Y' : Matrix m m ℂ}
    {σ σ' : ℂ} (hY : LowersFlag d v Y σ) (hY' : InducesOn d v i₀ Y Y')
    (hYadj : LowersFlag d v (formAdjoint ε ε Y) σ') : Y.trace = Y'.trace := by
  obtain ⟨N, hN_tri, hN, -⟩ := hY
  obtain ⟨N', hN'_tri, hN', -⟩ := hYadj
  -- Split the identity, which keeps each `v_j`: the three terms are the traces of `Y` on `A^⊥ / A`,
  -- on `A = A_{≤ j₀ - 1}` and on `ℂ^n / A^⊥`. The last two vanish, as `Y`, `Y†` lower the flag.
  have h_split : ((1 : Matrix n n ℂ) * Y).trace =
      (formAdjoint ε η i₀ * (1 : Matrix n n ℂ) * i₀ * Y').trace +
        ∑ a : Fin d, N a a.castSucc + conj (∑ a : Fin d, N' a a.castSucc) :=
    hP.trace_mul_eq_trace_add_sum_of_inducesOn formAdjoint_one (Matrix.one_mul (initCols v)) hY' hN
      hN'
  have hN_diag (a : Fin d) : N a a.castSucc = 0 := hN_tri a a.castSucc le_rfl
  have hN'_diag (a : Fin d) : N' a a.castSucc = 0 := hN'_tri a a.castSucc le_rfl
  simpa [hP.formAdjoint_mul_self, hN_diag, hN'_diag] using h_split

/-- Let `μ`, `μ'` be the weights of the lowest `K`-types of the parameters `l` of `U(ε)` and `k` of
`U(η)`, as diagonal matrices. Let `(v, i₀)` be a stationary position (`IsStationary`): a position in
which `μ v_j = v_{j + 1}` for `j < j₀ = d + 1`, and `i₀† μ i₀ = μ'`. Let `Y` and its adjoint `Y†`
lower the flag of the `v_j` (`LowersFlag`), with sums `σ` and `σ'` of the coefficients next to the
diagonal, and let `Y` act by `Y'` on the image of `i₀` modulo the span of `v₁, …, v_{j₀ - 1}`
(`InducesOn`). Then the phase `l.phase k (Y, Y') = tr μ Y - tr μ' Y'` equals `σ + conj σ'`. -/
lemma IsStationary.phase_eq (hP : IsStationary l k e e' d v i₀) {Y : Matrix n n ℂ}
    {Y' : Matrix m m ℂ} {σ σ' : ℂ} (hY : LowersFlag d v Y σ) (hY' : InducesOn d v i₀ Y Y')
    (hYadj : LowersFlag d v (formAdjoint ε ε Y) σ') : l.phase k (Y, Y') = σ + conj σ' := by
  obtain ⟨N, -, hN, hσ⟩ := hY
  obtain ⟨N', -, hN', hσ'⟩ := hYadj
  -- The weight moves `v_j` to `v_{j + 1}`.
  have h_split : (intDiagonal l.lowestKType * Y).trace =
      (formAdjoint ε η i₀ * intDiagonal l.lowestKType * i₀ * Y').trace +
        ∑ a : Fin d, N a a.succ + conj (∑ a : Fin d, N' a a.succ) :=
    hP.trace_mul_eq_trace_add_sum_of_inducesOn (formAdjoint_intDiagonal l.lowestKType) hP.shift hY'
      hN hN'
  rw [HCParam.phase, h_split, hP.adjoint_weight_mul_eq, hσ, hσ']
  ring

/-- **Two traces.** Let `μ`, `μ'` be the weights of the lowest `K`-types of the parameters `l` of
`U(ε)` and `k` of `U(η)`, as diagonal matrices. Let `(v, i₀)` be a stationary position
(`IsStationary`): the columns `v₁, …, v_{j₀}` of `v`, where `j₀ = d + 1`, and an isometry `i₀`
into their orthogonal complement, with `μ v_j = v_{j + 1}` for `j < j₀` and `i₀† μ i₀ = μ'`. Let
`Y` and its adjoint `Y†` lower the flag of the `v_j` (`LowersFlag`), with sums `σ` and `σ'` of the
coefficients next to the diagonal, and let `Y` induce `Y'` on the image of `i₀` modulo the span of
`v₁, …, v_{j₀ - 1}` (`InducesOn`). Then `Y` and `Y'` have the same trace, and the phase
`tr μ Y - tr μ' Y'` is `σ + conj σ'`. -/
theorem IsStationary.trace_eq_and_phase_eq (hP : IsStationary l k e e' d v i₀) {Y : Matrix n n ℂ}
    {Y' : Matrix m m ℂ} {σ σ' : ℂ} (hY : LowersFlag d v Y σ) (hY' : InducesOn d v i₀ Y Y')
    (hYadj : LowersFlag d v (formAdjoint ε ε Y) σ') :
    Y.trace = Y'.trace ∧ l.phase k (Y, Y') = σ + conj σ' :=
  ⟨hP.trace_eq hY hY' hYadj, hP.phase_eq hY hY' hYadj⟩

end New.DiscreteSeries

end
