import Lib.Adelic.Witt.WittTheorem
import Lib.GLn.SchurModule.WeylKernel

/-!
# Fock pairing, Hermitian norm and Cartan products for the Gram matrix of the Weyl kernel

This file uses the Fock pairing `⟨P, Q⟩ = P(∂) Q (0)` (`New.fockPairing`) and Schur's lemma to show
that the Gram matrix `G = New.weylGram` times the matrix of the Fock pairings of the basis
`b_i = New.nablaBasis` (products of minors) of the semi-invariants `New.nablaFamily` is the hook
number `New.hookNumber κ N = ⟨f, f⟩`, the Fock pairing of `f = New.highestPoly` with itself.
It treats weights with one row at each place. It defines the squared
norm `New.weylNormSq ξ = re (ξ* G ξ)` and builds a tight frame of integral vectors. It shows that
this norm is submultiplicative under Cartan multiplication of polynomials of weights `κ` and `κ'`,
and defines the products of determinants `New.pairedDetProd`.

## Main definitions and results

* `New.weylGram_mul_fockPairing`, `New.fockPairing_toPoly_nablaBasis`: by Schur's lemma, `G` times
  the matrix of the Fock pairings `⟨b_i, b_j⟩` is the hook number `New.hookNumber`.
* `New.GL.comulMatrix`: the matrix `C`, in the bases `New.nablaBasis`, of multiplication of
  polynomials of weights `κ` and `κ'` into those of weight `κ + κ'`;
  `New.GL.vecMul_comulMatrix_eq_iff`: acting on row vectors, `C` multiplies polynomials;
  `New.GL.comulMatrix_mulVec_weylEval`: acting on columns, it sends an evaluation vector to a tensor
  product of two.
* `New.GL.comulMatrix_isometry`, `New.GL.comulMatrix_equivariant`, `New.GL.hasLeftInv_comulMatrix`:
  `C` is an isometry for the Gram matrices, intertwines the Schur matrices, and has a left inverse
  over `ℤ`.

Notions from other files:
* `New.WeylIndexFamily n κ`: families that choose, for each place `τ`, a standard filling with rows
  `n τ`; they index the basis `b_i`.
* `New.schur κ z`: the Schur matrix `S_κ(z)` of matrices `z τ` of size `n' τ × n τ`. Row `i`
  holds the coordinates of `b'_i(z y)` in the products `b_j(y) · ∏_τ det(y_τ)^{d_τ}`, where `b'` is
  the basis for the rows `n'` and `d = New.schurDetExp n n' κ`.
* `New.mem_range_scalar_of_commute_schur` (`Lib.GLn.SchurModule.WeylKernel`): Schur's lemma, a
  matrix that commutes with `New.schur κ g` for all unitary `g` is scalar.

## Relation to the literature

Known; see `Lib.GLn.SchurModule.SchurNorm` and `Lib.GLn.Dual` for sources.
-/

/-!
## The Fock form and the Gram matrix

A vector `ξ` pairs with a polynomial `P = ∑ c_k b_k` in two ways, by `ξ(P) = ∑ ξ_k c_k` and by the
Fock pairing `⟨ξ̂, P⟩` with `ξ̂ = New.toPoly n κ ξ`. By Schur's lemma the two are proportional, and
the factor is the hook number.
-/

section FockForm

namespace New

open MvPolynomial «GL» Fintype Finset Matrix

variable {Φ : Type} {R : Type _} [CommRing R] [Fintype Φ] [DecidableEq Φ]
  {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] {κ : Φ → ℕ → ℕ}
  (ξ η : WeylIndexFamily n κ → R)

/-- The Fock pairing of the polynomial Σ_i (Gξ)_i b_i attached to ξ with b_k is the coordinate k of
HᵀGξ, where G is the Gram matrix and H the integer matrix of the Fock pairings ⟨b_i, b_j⟩. -/
lemma fockPairing_toPoly_nablaBasis_eq_mulVec (k : WeylIndexFamily n κ) :
    fockPairing R (toPoly n κ ξ) (nablaBasis R n κ k) =
      (((of fun i j : WeylIndexFamily n κ ↦
          fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j))ᵀ * weylGram n κ).map
        (Int.cast : ℤ → R) *ᵥ ξ) k := by
  have h_entry (i : WeylIndexFamily n κ) :
      (fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ k) : R) =
        fockPairing R (nablaBasis R n κ i) (nablaBasis R n κ k) := by
    simpa using map_fockPairing (Int.castRingHom R) (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ k)
  rw [map_mul_intCast, ← mulVec_mulVec, ← nablaCombination_weylGramOver_mulVec]
  simp [Fintype.linearCombination_apply, mulVec.eq_1 _ (weylGramOver *ᵥ ξ), dotProduct, h_entry,
    mul_comm]

omit [DecidableEq Φ] in
/-- The kernel at the permutation array of the row numbering `rowEquivFin` is the product of the
leading minors with the rows renamed, so its Fock pairing with itself is the hook number. -/
lemma fockPairing_weylKernel_permArray_self :
    fockPairing R (weylKernel n κ (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ)))
        (weylKernel n κ (permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ))) =
      hookNumber κ (rankAt n) := by
  let p (τ : Φ) : Matrix (Fin (rankAt n τ)) (n τ) R :=
    of fun i a ↦ permArray (fun (σ : Φ) (b : n σ) ↦ (rowEquivFin n σ b : ℕ)) (⟨τ, a⟩, i)
  have h_orth (τ : Φ) : p τ * (p τ)ᵀ = 1 := by
    ext i j
    rw [mul_apply, ← (rowEquivFin n τ).symm.sum_comp]
    simp [p, permArray, Fin.val_inj, one_apply, eq_comm]
  let f : MatrixPoly (Σ τ : Φ, Fin (rankAt n τ)) R := highestPoly R κ (rankAt n)
  calc fockPairing R (rowSubst p f) (rowSubst p f)
    _ = fockPairing R f f := by
      simp only [fockPairing_rowSubst p, rowSubst_rowSubst, h_orth, rowSubst_one]
    _ = hookNumber κ (rankAt n) := by
      simpa [f, hookNumber] using (map_fockPairing (Int.castRingHom R) (highestPoly ℤ κ (rankAt n))
        (highestPoly ℤ κ (rankAt n))).symm

/-- The Gram matrix `weylGram n κ` has as entries the integer coefficients of the generic kernel
`weylKernel` in the products b_i(x)·b_j(y), where b = `nablaBasis` are the basis minor products. It
times the matrix of Fock pairings ⟨b_i,b_j⟩ = b_i(∂)b_j(0) equals the hook number
`hookNumber κ (rankAt n)` times the identity matrix. -/
lemma weylGram_mul_fockPairing :
    (weylGram n κ * of fun i j : WeylIndexFamily n κ ↦
        fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j)) =
      hookNumber κ (rankAt n) • 1 := by
  -- Over `ℂ` let `T` be the map with `⟨ξ̂, P⟩ = (T ξ)(P)`. Both pairings make the Schur matrix of
  -- `g` adjoint to the substitution `P ↦ P(g ·)`, so `T` commutes with it and is a scalar `c`.
  let H : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℤ :=
    of fun i j : WeylIndexFamily n κ ↦ fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j)
  let T : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℂ := (Hᵀ * weylGram n κ).map Int.cast
  have hT (ξ : WeylIndexFamily n κ → ℂ) (k : WeylIndexFamily n κ) :
      (T *ᵥ ξ) k = fockPairing ℂ (toPoly n κ ξ) (nablaBasis ℂ n κ k) :=
    (fockPairing_toPoly_nablaBasis_eq_mulVec ξ k).symm
  have h_comm (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) : T * schur κ g = schur κ g * T := by
    refine ext_iff_mulVec.2 fun ξ ↦ funext fun k ↦ ?_
    have h_expand : rowSubst g (nablaBasis ℂ n κ k) =
        ∑ j : WeylIndexFamily n κ, schur κ g k j • nablaBasis ℂ n κ j := by
      simp [← sum_schur_smul_nablaBasis FitsRanks.refl, detPow]
    calc ((T * schur κ g) *ᵥ ξ) k
      _ = fockPairing ℂ (rowSubst (fun τ : Φ ↦ (g τ)ᵀ) (toPoly n κ ξ)) (nablaBasis ℂ n κ k) := by
        simp [← mulVec_mulVec, hT, toPoly_schur FitsRanks.refl, detPow]
      _ = fockPairing ℂ (toPoly n κ ξ) (rowSubst g (nablaBasis ℂ n κ k)) :=
        fockPairing_rowSubst _ _ _
      _ = ((schur κ g * T) *ᵥ ξ) k := by
        simp [h_expand, ← hT, ← mulVec_mulVec, mulVec.eq_1 (schur κ g), dotProduct]
  obtain ⟨c, hc⟩ : T ∈ Set.range (scalar (WeylIndexFamily n κ)) :=
    mem_range_scalar_of_commute_schur fun g _ ↦ h_comm g
  -- The frame vector `v` has the polynomial `K` with `v(K) = 1` and `⟨K, K⟩` the hook number.
  let w : (Σ τ : Φ, n τ) × ℕ → ℂ := permArray fun (τ : Φ) (i : n τ) ↦ (rowEquivFin n τ i : ℕ)
  let v : WeylIndexFamily n κ → ℂ := weylEval n κ w
  have h_const : (hookNumber κ (rankAt n) : ℂ) = c :=
    calc (hookNumber κ (rankAt n) : ℂ)
      _ = fockPairing ℂ (toPoly n κ v) (nablaCombination κ (weylGramOver *ᵥ v)) := by
        rw [nablaCombination_weylGramOver_mulVec, toPoly_weylEval,
          fockPairing_weylKernel_permArray_self]
      _ = (T *ᵥ v) ⬝ᵥ weylGramOver *ᵥ v := by
        simp [Fintype.linearCombination_apply, hT, dotProduct, mul_comm]
      _ = c * eval w (weylKernel n κ w) := by
        rw [← toPoly_weylEval, eval_toPoly, ← hc]
        simp [v]
      _ = c := by rw [eval_weylKernel_permArray, mul_one]
  -- This is an identity of integer matrices; transpose it, using that `G` is symmetric.
  have h_int : Hᵀ * weylGram n κ = hookNumber κ (rankAt n) • 1 := by
    refine map_injective (Int.cast_injective (α := ℂ)) (hc.symm.trans ?_)
    simp [← h_const, Matrix.map_intCast, diagonal_intCast]
  simpa [weylGram_isSymm.eq] using congrArg transpose h_int

/-- Let ξ be a vector of the Weyl module `WeylIndexFamily n κ → R` over any commutative ring `R`,
and let `toPoly n κ ξ` be its polynomial Σ_i (Gξ)_i b_i. Here G is the Gram matrix `weylGramOver`
and b_i = `nablaBasis R n κ i` are the basis minor products. For each index k, the Fock pairing
⟨P,Q⟩ = P(∂)Q(0) of `toPoly n κ ξ` with b_k equals `hookNumber κ (rankAt n)` times the coordinate
ξ_k. -/
@[simp]
lemma fockPairing_toPoly_nablaBasis (k : WeylIndexFamily n κ) :
    fockPairing R (toPoly n κ ξ) (nablaBasis R n κ k) = hookNumber κ (rankAt n) * ξ k := by
  rw [fockPairing_toPoly_nablaBasis_eq_mulVec, ← weylGram_isSymm.eq, ← transpose_mul,
    weylGram_mul_fockPairing]
  simp [Matrix.map_intCast, mulVec_diagonal]

/-- For vectors ξ, η of the Weyl module over a commutative ring `R` (functions on
`WeylIndexFamily n κ`), the Fock pairing ⟨P,Q⟩ = P(∂)Q(0) of the polynomials
`toPoly n κ ξ = Σ_i (Gξ)_i b_i` and `toPoly n κ η` equals the hook number times ξᵀ G η. Here the b_i
are the basis products of minors `nablaBasis`, indexed by `WeylIndexFamily n κ`. G is the integer
Gram matrix `weylGram`, the coefficients of the generic kernel `weylKernel` in the products b_i(x)
b_j(y), mapped into `R`. The hook number is ⟨f,f⟩, where f is the product over places τ of the
leading principal h×h minors raised to κ_τ(h), for h < |n_τ|. -/
@[simp]
lemma fockPairing_toPoly_toPoly :
    fockPairing R (toPoly n κ ξ) (toPoly n κ η) =
      hookNumber κ (rankAt n) * ξ ⬝ᵥ weylGramOver *ᵥ η := by
  simp [← nablaCombination_weylGramOver_mulVec η, mul_rotate', linearCombination_apply, dotProduct,
    mul_sum]

/-- The orthogonal projection of an integral tensor `v` to the Weyl module becomes integral after
multiplication by the hook number: some integral vector has the same pairings with the Weyl module
as that multiple of `v`. -/
lemma exists_weylGram_mulVec_eq_hookNumber_smul (v : ColumnFilling n κ → ℤ) :
    ∃ η : WeylIndexFamily n κ → ℤ,
      weylGram n κ *ᵥ η = hookNumber κ (rankAt n) • ((fillingMatrix n κ)ᵀ *ᵥ v) := by
  -- The matrix of Fock pairings is the hook number times the inverse of the Gram matrix.
  refine ⟨(of fun i j ↦ fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j)) *ᵥ
    (fillingMatrix n κ)ᵀ *ᵥ v, ?_⟩
  rw [mulVec_mulVec, weylGram_mul_fockPairing, smul_mulVec, one_mulVec]

end New

end FockForm

/-!
## Weights with one row at each place

If only columns of height one occur, with `κ τ 1` of them at `τ`, the basis polynomials are
monomials in the first columns `z_τ` of variables.
-/

section OneRow

namespace New

open MvPolynomial Finset Matrix Nat

variable {Φ R : Type} [Fintype Φ] {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] {κ : Φ → ℕ → ℕ}

/-- The exponent of the monomial `∏ z_τ ^ α_τ`, where `z_τ` is the first column of variables at
`τ`. -/
noncomputable def firstColumnExponent (α : ∀ τ : Φ, n τ → ℕ) : ((τ : Φ) × n τ) × ℕ →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm fun x : (τ : Φ) × n τ ↦ α x.1 x.2).embDomain
    (Function.Embedding.sectL ((τ : Φ) × n τ) 0)

lemma firstColumnExponent_injective : Function.Injective (firstColumnExponent (n := n)) := by
  intro α β h_eq
  funext τ b
  exact congrFun (Finsupp.equivFunOnFinite.symm.injective (Finsupp.embDomain_injective _ h_eq))
    ⟨τ, b⟩

/-- A product over the exponent `firstColumnExponent α` runs over the variables in the first
columns. -/
lemma prod_firstColumnExponent {M : Type} [CommMonoid M] (α : ∀ τ : Φ, n τ → ℕ)
    (f : ((τ : Φ) × n τ) × ℕ → ℕ → M) (hf : ∀ x : ((τ : Φ) × n τ) × ℕ, f x 0 = 1) :
    (firstColumnExponent α).prod f = ∏ τ : Φ, ∏ b : n τ, f (⟨τ, b⟩, 0) (α τ b) := by
  rw [firstColumnExponent, Finsupp.prod_embDomain, Finsupp.prod_fintype _ _ fun x ↦ hf _,
    Fintype.prod_sigma]
  rfl

/-- The polynomial `∏_τ (|α_τ|! / α_τ!) z_τ ^ α_τ` in the first columns `z_τ` of variables, where
`|α_τ|` is the sum of the exponents at `τ` and `α_τ!` the product of their factorials. -/
noncomputable def multinomialMonomial (R : Type) [CommRing R] (α : ∀ τ : Φ, n τ → ℕ) :
    MatrixPoly ((τ : Φ) × n τ) R :=
  monomial (firstColumnExponent α) (∏ τ : Φ, multinomial univ (α τ) : ℕ)

variable [∀ τ : Φ, DecidableEq (n τ)]

/-- Suppose only columns of height at most one occur (`κ τ h = 0` for 1 < h < `N τ`). Then the
product over τ of the polynomials `tableauPoly` of the fillings `T τ` (products of minors on the
rows given by the columns' entries) is a monomial in the first column of variables at each τ. Its
exponent at (τ, b) is the number of height-one columns of `T τ` with entry b. -/
lemma prod_tableauPoly_one_row [CommRing R] {N : Φ → ℕ} (hN : ∀ τ : Φ, 1 < N τ)
    (hκ : ∀ (τ : Φ) (h : ℕ), 1 < h → h < N τ → κ τ h = 0)
    (T : ∀ τ : Φ, Tableau (n τ) (N τ) (κ τ)) :
    ∏ τ : Φ, tableauPoly (m := (τ : Φ) × n τ) R (Sigma.mk τ) (T τ) =
      monomial (firstColumnExponent fun τ b ↦ #{j | T τ ⟨1, hN τ⟩ j (0 : Fin 1) = b}) 1 := by
  rw [monomial_eq, C_1, one_mul, prod_firstColumnExponent _ _ fun x ↦ pow_zero _]
  refine prod_congr rfl fun τ _ ↦ ?_
  rw [tableauPoly, Fintype.prod_eq_single ⟨1, hN τ⟩]
  · -- A minor of size one is a variable; sort the columns of height one by their entry.
    simp [minor, ← prod_fiberwise' univ (fun j ↦ T τ ⟨1, hN τ⟩ j (0 : Fin 1))
      fun b ↦ (X (⟨τ, b⟩, 0) : MatrixPoly ((τ : Φ) × n τ) R)]
  · -- Minors of size zero are `1`, and there are no columns of height above one.
    rintro ⟨_ | _ | h, h_lt⟩ h_ne
    · simp [minor]
    · exact (h_ne rfl).elim
    · exact prod_eq_one fun j _ ↦ (Fin.cast (hκ τ (h + 2) (by omega) h_lt) j).elim0

/-- The hook number of a weight with one row at each place is the product of the factorials of the
row lengths. -/
lemma hookNumber_one_row [DecidableEq Φ] {N : Φ → ℕ} (hN : ∀ τ : Φ, 1 < N τ)
    (hκ : ∀ (τ : Φ) (h : ℕ), 1 < h → h < N τ → κ τ h = 0) :
    hookNumber κ N = (∏ τ : Φ, (κ τ 1)! : ℕ) := by
  rw [hookNumber, highestPoly, prod_tableauPoly_one_row hN hκ, fockPairing_monomial,
    prod_firstColumnExponent _ _ fun _ ↦ by simp, coeff_monomial, ite_eq_left rfl]
  simp only [mul_one, cast_prod]
  refine prod_congr rfl fun τ _ ↦ ?_
  rw [Fintype.prod_eq_single (Fin.castLE (hN τ).le 0) fun b hb ↦ by simp [hb.symm]]
  simp

variable [DecidableEq Φ] [Field R] [CharZero R]

/-- Over a field `R` of characteristic zero, assume every row type `n τ` has more than one element
(`1 < rankAt n τ`) and `κ τ h = 0` for `1 < h < rankAt n τ`, so the weight is one row of length
`κ τ 1` at each place. Then there is an injective assignment `α` from basis indices
`i : WeylIndexFamily n κ` to exponent families, with `∑ b, α i τ b = κ τ 1` for every τ. For every
vector ξ, its polynomial `toPoly n κ ξ = Σ_i (Gξ)_i b_i` (G the Gram matrix, b_i the basis minor
products) equals `∑ i, ξ i • multinomialMonomial R (α i)`, where `multinomialMonomial R α = ∏_τ
(|α_τ|!/α_τ!) z_τ^{α_τ}` in the first columns `z_τ` of the variables. -/
lemma exists_toPoly_eq_sum_multinomialMonomial (h_card : ∀ τ : Φ, 1 < rankAt n τ)
    (hκ : ∀ (τ : Φ) (h : ℕ), 1 < h → h < rankAt n τ → κ τ h = 0) :
    ∃ α : WeylIndexFamily n κ → ∀ τ : Φ, n τ → ℕ,
      Function.Injective α ∧
      (∀ (i : WeylIndexFamily n κ) (τ : Φ), ∑ b : n τ, α i τ b = κ τ 1) ∧
      ∀ ξ : WeylIndexFamily n κ → R,
        toPoly n κ ξ = ∑ i : WeylIndexFamily n κ, ξ i • multinomialMonomial R (α i) := by
  -- The basis products are distinct monomials. The Fock pairing with them gives the coefficients
  -- of `toPoly n κ ξ`.
  let α (i : WeylIndexFamily n κ) (τ : Φ) (b : n τ) : ℕ :=
    #{j | (i τ).1 ⟨1, h_card τ⟩ j (0 : Fin 1) = b}
  have h_basis (i : WeylIndexFamily n κ) :
      nablaBasis R n κ i = monomial (firstColumnExponent (α i)) 1 :=
    prod_tableauPoly_one_row h_card hκ fun τ ↦ (i τ).1
  have h_inj : Function.Injective α := fun i j hij ↦
    (linearIndependent_nablaBasis (R := R)).injective (by rw [h_basis, h_basis, hij])
  have h_sum (i : WeylIndexFamily n κ) (τ : Φ) : ∑ b : n τ, α i τ b = κ τ 1 := by
    rw [← card_eq_sum_card_fiberwise fun _ _ ↦ mem_coe.2 (mem_univ _), Finset.card_fin]
  refine ⟨α, h_inj, h_sum, fun ξ ↦ ?_⟩
  obtain ⟨c, h_expand⟩ : ∃ c : WeylIndexFamily n κ → R, toPoly n κ ξ =
      ∑ i : WeylIndexFamily n κ, c i • monomial (firstColumnExponent (α i)) (1 : R) :=
    ⟨weylGramOver *ᵥ ξ, by simp [toPoly, Fintype.linearCombination_apply, h_basis]⟩
  -- Pairing with a basis monomial gives `α! * c i = (∏ (κ τ 1)!) * ξ i`.
  have h_coeff (i : WeylIndexFamily n κ) :
      c i = ξ i * (∏ τ : Φ, multinomial univ (α i τ) : ℕ) := by
    let d : R := ∏ τ : Φ, ∏ b : n τ, ((α i τ b)! : R)
    have h_value : (toPoly n κ ξ).coeff (firstColumnExponent (α i)) = c i := by
      simp [h_expand, firstColumnExponent_injective.eq_iff, h_inj.eq_iff]
    have h_factorial : (∏ τ : Φ, (κ τ 1)!) =
        (∏ τ : Φ, ∏ b : n τ, (α i τ b)!) * ∏ τ : Φ, multinomial univ (α i τ) := by
      simp only [← prod_mul_distrib, multinomial_spec, h_sum]
    refine mul_left_cancel₀ (a := d) (by simp [d, prod_ne_zero_iff, factorial_ne_zero]) ?_
    calc d * c i = fockPairing R (toPoly n κ ξ) (nablaBasis R n κ i) := by
          rw [fockPairing_comm, h_basis, fockPairing_monomial,
            prod_firstColumnExponent _ _ fun _ ↦ by simp]
          simp [d, h_value]
      _ = (∏ τ : Φ, (κ τ 1)! : ℕ) * ξ i := by
          rw [fockPairing_toPoly_nablaBasis, hookNumber_one_row h_card hκ, Int.cast_natCast]
      _ = d * (ξ i * (∏ τ : Φ, multinomial univ (α i τ) : ℕ)) := by
          simp only [h_factorial, d, cast_mul, cast_prod]
          ring
  simp [h_expand, h_coeff, multinomialMonomial, smul_monomial]

/-- Over a field `R` of characteristic zero, assume every row type `n τ` has more than one element
(`1 < rankAt n τ`) and `κ τ h = 0` for `1 < h < rankAt n τ`, so the weight is one row of length
`κ τ 1` at each place. Let `A` be a subring of `R`. A vector ξ has all coordinates `ξ i` in `A` if
and only if its polynomial `toPoly n κ ξ = Σ_i (Gξ)_i b_i` (G the Gram matrix, b_i the basis minor
products) lies in the `A`-span of the `multinomialMonomial R α` with `∑ b, α τ b = κ τ 1` for all τ.
Here `multinomialMonomial R α = ∏_τ (|α_τ|!/α_τ!) z_τ^{α_τ}` in the first columns `z_τ` of the
variables. -/
lemma toPoly_mem_span_multinomialMonomial_iff (h_card : ∀ τ : Φ, 1 < rankAt n τ)
    (hκ : ∀ (τ : Φ) (h : ℕ), 1 < h → h < rankAt n τ → κ τ h = 0) (A : Subring R)
    (ξ : WeylIndexFamily n κ → R) :
    toPoly n κ ξ ∈ Submodule.span A
        (multinomialMonomial R '' {α | ∀ τ : Φ, ∑ b : n τ, α τ b = κ τ 1}) ↔
      ∀ i : WeylIndexFamily n κ, ξ i ∈ A := by
  obtain ⟨α, h_inj, h_sum, h_eq⟩ := exists_toPoly_eq_sum_multinomialMonomial (R := R) h_card hκ
  rw [h_eq]
  refine ⟨fun h_mem i ↦ ?_, fun h_int ↦ Submodule.sum_mem _ fun i _ ↦
    Submodule.smul_mem _ (⟨ξ i, h_int i⟩ : A) (Submodule.subset_span ⟨α i, h_sum i, rfl⟩)⟩
  let w : R := (∏ τ : Φ, multinomial univ (α i τ) : ℕ)
  have hw_ne : w ≠ 0 := cast_ne_zero.2 (prod_ne_zero_iff.2 fun τ _ ↦ (multinomial_pos _ _).ne')
  -- On the span, the coefficient at the exponent `α i` lies in `A * w`.
  have h_coeff {f : MatrixPoly ((τ : Φ) × n τ) R} (hf : f ∈ Submodule.span A
      (multinomialMonomial R '' {α | ∀ τ : Φ, ∑ b : n τ, α τ b = κ τ 1})) :
      f.coeff (firstColumnExponent (α i)) / w ∈ A := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨β, -, rfl⟩ := hf
      rw [multinomialMonomial, coeff_monomial]
      split_ifs with hβ
      · simp only [firstColumnExponent_injective hβ, w, div_self hw_ne, A.one_mem]
      · simp
    | zero => simp
    | add f g _ _ hf hg => simpa [add_div] using A.add_mem hf hg
    | smul a f _ hf => simpa [mul_div_assoc, Subring.smul_def] using A.mul_mem a.prop hf
  have h_value : (∑ j : WeylIndexFamily n κ, ξ j • multinomialMonomial R (α j)).coeff
      (firstColumnExponent (α i)) = ξ i * w := by
    simp [multinomialMonomial, firstColumnExponent_injective.eq_iff, h_inj.eq_iff, w]
  simpa only [h_value, mul_div_cancel_right₀ _ hw_ne] using h_coeff h_mem

end New

end OneRow

/-!
## The Hermitian norm

* `New.weylNormSq`: the squared norm `re (ξ* G ξ)` of a complex coordinate vector `ξ`.
* `New.GL.weylNormSq_weylEval_permArray`: the evaluation vector `New.weylEval` at the permutation
  array of enumerations of the rows has norm `1`.
* `New.GL.exists_tightFrame`: the hook number times the orthogonal projections of the basis tensors
  to the Weyl module form a tight frame of integral vectors; `New.GL.card_columnFilling_le` bounds
  the number of basis tensors.
-/

namespace New

open MvPolynomial Matrix Complex ComplexOrder

variable {Φ : Type} {R : Type} [CommRing R] [Fintype Φ] [DecidableEq Φ]
  {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)]
  {κ : Φ → ℕ → ℕ} (ξ : WeylIndexFamily n κ → ℂ)

/-- For a complex coordinate vector ξ, the real part of ξ* G ξ, where G is the integer Gram
matrix. It is the squared norm of ξ for the Hermitian form of G, which is positive definite. -/
noncomputable def weylNormSq : ℝ :=
  re (star ξ ⬝ᵥ (weylGram n κ).map (Int.cast : ℤ → ℂ) *ᵥ ξ)

@[simp]
lemma weylNormSq_nonneg : 0 ≤ weylNormSq ξ := weylGramOver_posDef.posSemidef.re_dotProduct_nonneg ξ

lemma weylNormSq_smul (t : ℂ) : weylNormSq (t • ξ) = ‖t‖ ^ 2 * weylNormSq ξ := by
  simp [weylNormSq, mulVec_smul, ← mul_assoc, mul_conj', sq]

/-- The squared Gram norm of `σ ∘ (t • ξ)` is `‖σ t‖ ^ 2` times that of `σ ∘ ξ`, for multiplicative
`σ`. -/
@[simp]
lemma weylNormSq_comp_smul {F : Type*} [FunLike F ℂ ℂ] [MulHomClass F ℂ ℂ] (σ : F) (t : ℂ) :
    weylNormSq (σ ∘ (t • ξ)) = ‖σ t‖ ^ 2 * weylNormSq (σ ∘ ξ) := by
  have h_comp : σ ∘ (t • ξ) = σ t • (σ ∘ ξ) := funext fun i ↦ map_mul σ t (ξ i)
  rw [h_comp, weylNormSq_smul]

namespace «GL»

/-- Cauchy–Schwarz for the Hermitian form of a positive definite complex matrix M:
`‖x* M y‖ ^ 2 ≤ re (y* M y) * re (x* M x)`. -/
lemma posDef_cauchy_schwarz {ι : Type*} [Fintype ι] {M : Matrix ι ι ℂ} (h_posDef : PosDef M)
    (x y : ι → ℂ) :
    ‖star x ⬝ᵥ M *ᵥ y‖ ^ 2 ≤ (star y ⬝ᵥ M *ᵥ y).re * (star x ⬝ᵥ M *ᵥ x).re := by
  -- the Cauchy–Schwarz inequality of the inner product `⟪u, v⟫ = u* M v` that `M` defines
  let _ : SeminormedAddCommGroup (ι → ℂ) := M.toSeminormedAddCommGroup h_posDef.posSemidef
  let _ : InnerProductSpace ℂ (ι → ℂ) := M.toInnerProductSpace h_posDef.posSemidef
  have h_inner (u v : ι → ℂ) : inner ℂ u v = star u ⬝ᵥ M *ᵥ v := dotProduct_comm _ _
  have h_cs : ‖inner ℂ y x‖ * ‖inner ℂ x y‖ ≤ re (inner ℂ y y) * re (inner ℂ x x) :=
    inner_mul_inner_self_le y x
  rwa [norm_inner_symm y x, ← sq, h_inner, h_inner, h_inner] at h_cs

/-- As a complex number, the squared Gram norm `weylNormSq ξ` is `ξ* G ξ` itself: its imaginary part
is zero because G is positive semidefinite. -/
lemma coe_weylNormSq : weylNormSq ξ = star ξ ⬝ᵥ weylGramOver *ᵥ ξ :=
  (eq_re_of_ofReal_le (weylGramOver_posDef.posSemidef.dotProduct_mulVec_nonneg ξ)).symm

omit [DecidableEq Φ] in
/-- The complex conjugate of the evaluation vector at y (the values `b_i y` of the basis minor
products) is the evaluation vector at the conjugate array, since the `b_i` have integer
coefficients. -/
lemma star_weylEval (y : ((τ : Φ) × n τ) × ℕ → ℂ) :
    star (weylEval n κ y) = weylEval n κ (star y) := by
  ext i
  simp [weylEval, map_eval, Function.comp_def, Pi.star_def]

/-- For enumerations `e τ` of the rows, the evaluation vector at the permutation array of e (entry
1 at row `(τ, a)` and column `e τ a`, and 0 elsewhere) has Gram norm 1. -/
lemma weylNormSq_weylEval_permArray (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) :
    weylNormSq (weylEval n κ (permArray e)) = 1 := by
  -- The array `y = permArray e` is real, so the vector is its own conjugate; its Gram form is the
  -- kernel at `y` evaluated at `y`, which is `1`.
  set y : ((τ : Φ) × n τ) × ℕ → ℂ := permArray e with hy_def
  have h_star : star (weylEval n κ y) = weylEval n κ y := by
    rw [star_weylEval]
    congr 1
    ext x
    simp [hy_def, permArray, apply_ite]
  have h_form : star (weylEval n κ y) ⬝ᵥ weylGramOver *ᵥ weylEval n κ y = 1 := by
    rw [h_star, ← eval_toPoly, toPoly_weylEval]
    exact eval_weylKernel_permArray e
  show re (star (weylEval n κ y) ⬝ᵥ weylGramOver *ᵥ weylEval n κ y) = 1
  rw [h_form, one_re]

/-- A tight frame of integral vectors. Let `hk` be the hook number and `⟨ξ, ξ'⟩ = ξ* G ξ'` the form
of the Gram matrix. There are integral vectors `η T`, one for each basis tensor `T`
(`New.ColumnFilling`), with `∑ T, ⟨η T, ξ⟩ η T = hk² ξ` for all `ξ` and of norm at most `hk`. -/
lemma exists_tightFrame : ∃ η : ColumnFilling n κ → WeylIndexFamily n κ → ℤ,
    (∀ ξ : WeylIndexFamily n κ → ℂ,
      ∑ T : ColumnFilling n κ, (star (Int.cast ∘ η T) ⬝ᵥ weylGramOver *ᵥ ξ) • (Int.cast ∘ η T) =
        (hookNumber κ (rankAt n) : ℂ) ^ 2 • ξ) ∧
    ∀ T : ColumnFilling n κ,
      weylNormSq (Int.cast ∘ η T) ≤ (hookNumber κ (rankAt n) : ℝ) ^ 2 := by
  -- Take for `η T` the hook number times the orthogonal projection of `T` to the Weyl module.
  -- With `F` the embedding into tensors and `G = Fᵀ F`, this means `G (η T) = hk Fᵀ T`, so
  -- `⟨η T, ξ⟩` is `hk` times the coordinate `T` of the tensor `F ξ`.
  classical
  set hk : ℤ := hookNumber κ (rankAt n)
  let F : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) ℂ := fillingMatrixOver ℂ n κ
  have h_exists (T : ColumnFilling n κ) :
      ∃ η : WeylIndexFamily n κ → ℤ, weylGram n κ *ᵥ η = hk • fillingMatrix n κ T := by
    simpa [hk, row] using exists_weylGram_mulVec_eq_hookNumber_smul (Pi.single T 1)
  choose η hη using h_exists
  refine ⟨η, fun ξ ↦ ?_, fun T ↦ ?_⟩
  · have h_gram (T : ColumnFilling n κ) : weylGramOver *ᵥ (Int.cast ∘ η T) = (hk : ℂ) • F T := by
      funext i
      simpa [F, mulVec, dotProduct] using congrArg (Int.cast : ℤ → ℂ) (congrFun (hη T) i)
    have h_pair (T : ColumnFilling n κ) :
        star (Int.cast ∘ η T) ⬝ᵥ weylGramOver *ᵥ ξ = hk * F T ⬝ᵥ ξ := by
      have h_real : star (Int.cast ∘ η T : WeylIndexFamily n κ → ℂ) = Int.cast ∘ η T :=
        funext fun i ↦ by simp
      rw [h_real, dotProduct_mulVec, ← mulVec_transpose, (weylGram_isSymm.map _).eq, h_gram,
        smul_dotProduct, smul_eq_mul]
    refine mulVec_injective_iff_isUnit.2 weylGramOver_posDef.isUnit ?_
    calc weylGramOver *ᵥ ∑ T : ColumnFilling n κ,
          (star (Int.cast ∘ η T) ⬝ᵥ weylGramOver *ᵥ ξ) • (Int.cast ∘ η T : WeylIndexFamily n κ → ℂ)
      _ = ∑ T : ColumnFilling n κ, (hk * F T ⬝ᵥ ξ) • (hk : ℂ) • F T := by
        simp only [mulVec_sum, mulVec_smul, h_pair, h_gram]
      _ = (hk : ℂ) ^ 2 • Fᵀ *ᵥ F *ᵥ ξ := by
        rw [mulVec_transpose, vecMul_eq_sum, Finset.smul_sum]
        simp only [smul_smul, mul_right_comm (hk : ℂ), ← sq, mulVec]
      _ = weylGramOver *ᵥ ((hk : ℂ) ^ 2 • ξ) := by
        rw [mulVec_smul, mulVec_mulVec, ← weylGramOver_eq_transpose_mul]
  · -- The squared norm is `hk * w T` and also `w ⬝ᵥ w ≥ w T ^ 2`, for the tensor `w` of `η T`.
    let w : ColumnFilling n κ → ℤ := fillingMatrix n κ *ᵥ η T
    have h_coord : η T ⬝ᵥ weylGram n κ *ᵥ η T = hk * w T := by
      rw [hη, dotProduct_smul, smul_eq_mul, dotProduct_comm]
      rfl
    have h_sum : η T ⬝ᵥ weylGram n κ *ᵥ η T = w ⬝ᵥ w := by
      rw [← fillingMatrix_transpose_mul_self, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    have h_single : w T * w T ≤ w ⬝ᵥ w :=
      Finset.single_le_sum (fun S _ ↦ mul_self_nonneg (w S)) (Finset.mem_univ T)
    have h_le : η T ⬝ᵥ weylGram n κ *ᵥ η T ≤ hk ^ 2 := by nlinarith [sq_nonneg (hk - w T)]
    simpa [weylNormSq, dotProduct, mulVec] using (Int.cast_le (R := ℝ)).2 h_le

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] in
/-- If all ranks are at most `t ≥ 1` and the diagrams have at most `L` boxes in total, there are at
most `t ^ L` basis tensors (`New.ColumnFilling`). -/
lemma card_columnFilling_le {t L : ℕ} (ht : 1 ≤ t) (h_rank : ∀ τ : Φ, rankAt n τ ≤ t)
    (h_degree : ∑ τ : Φ, ∑ h ∈ Finset.range (rankAt n τ), h * κ τ h ≤ L) :
    Nat.card (ColumnFilling n κ) ≤ t ^ L := by
  have h_column (τ : Φ) (h : ℕ) : Nat.card (IncreasingMap (rankAt n τ) h) ≤ t ^ h := by
    grw [Finite.card_subtype_le, Nat.card_fun, Nat.card_fin, Nat.card_fin, h_rank]
  calc Nat.card (ColumnFilling n κ)
    _ = ∏ τ : Φ, ∏ h : Fin (rankAt n τ), Nat.card (IncreasingMap (rankAt n τ) h) ^ κ τ h := by
      simp only [Nat.card_pi, Finset.prod_const, Finset.card_fin]
    _ ≤ t ^ ∑ τ : Φ, ∑ h ∈ Finset.range (rankAt n τ), h * κ τ h := by
      grw [h_column]
      simp only [← pow_mul, Finset.prod_pow_eq_pow_sum, Finset.sum_range, le_refl]
    _ ≤ t ^ L := Nat.pow_le_pow_right ht h_degree

/-- Over any commutative ring, let f be a Borel semi-invariant of the weight given by κ
(`New.nablaFamily`). Then the hook number times f is `toPoly n κ ζ` for some coordinate vector ζ,
where `New.toPoly` sends ζ to `∑ i, (G ζ) i • b i` (G the Gram matrix, b the basis minor
products). -/
lemma exists_toPoly_eq_hookNumber_smul {f : MatrixPoly (Sigma n) R} (hf : f ∈ nablaFamily R n κ) :
    ∃ ζ : WeylIndexFamily n κ → R, toPoly n κ ζ = hookNumber κ (rankAt n) • f := by
  -- With `c` the coordinates of `f` in `nablaBasis` and `F` the matrix of Fock pairings of
  -- `nablaBasis`, take `ζ = F *ᵥ c`: the Gram matrix times `F` is the hook number times the
  -- identity.
  obtain ⟨c, rfl⟩ : f ∈ (nablaCombination κ).range := range_nablaCombination.ge hf
  let F : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℤ :=
    of fun i j ↦ fockPairing ℤ (nablaBasis ℤ n κ i) (nablaBasis ℤ n κ j)
  refine ⟨F.map (↑) *ᵥ c, ?_⟩
  rw [← nablaCombination_weylGramOver_mulVec, mulVec_mulVec, ← map_mul_intCast,
    weylGram_mul_fockPairing]
  simp [Matrix.map_intCast, ← Int.cast_smul_eq_zsmul R]

end «GL»

end New

/-!
## Cartan multiplication and norms of products

`New.WeylIndexFamily n κ` indexes the basis, and `New.weylEval n κ y` is the vector of values of the
basis at `y`. The tensor product `(p, q) ↦ a p * b q` is written `(vecMulVec b a).vec`, since
`Matrix.vec` swaps the two indices.
-/

section Cartan

open Matrix Kronecker SetLike

namespace New.GL

variable {Φ R : Type} [CommRing R] [Fintype Φ] [DecidableEq Φ]
  {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] {κ κ' : Φ → ℕ → ℕ}

variable (R n κ κ') in
/-- The matrix of multiplication: row `(p, q)` holds the integer coordinates of the product of the
basis elements `nablaBasis ℤ n κ p` and `nablaBasis ℤ n κ' q` in the basis for `κ + κ'`, cast to
`R`. -/
noncomputable def comulMatrix :
    Matrix (WeylIndexFamily n κ × WeylIndexFamily n κ') (WeylIndexFamily n (κ + κ')) R :=
  of fun (p, q) k ↦
    (Function.invFun (nablaCombination (κ + κ')) (nablaBasis ℤ n κ p * nablaBasis ℤ n κ' q) k : ℤ)

/-- The multiplication matrix sends the evaluation vector at `y` for `κ + κ'` to the tensor product
of those for `κ` and `κ'`: the right side is `(p, q) ↦ weylEval n κ' y q * weylEval n κ y p`. -/
lemma comulMatrix_mulVec_weylEval (y : (Σ τ : Φ, n τ) × ℕ → R) :
    comulMatrix R n κ κ' *ᵥ weylEval n (κ + κ') y =
      (vecMulVec (weylEval n κ' y) (weylEval n κ y)).vec := by
  -- Expand the product of two basis elements in the basis for `κ + κ'` over `ℤ`, then map to `R`
  -- and evaluate at `y`.
  funext ⟨p, q⟩
  have h_mem : nablaBasis ℤ n κ p * nablaBasis ℤ n κ' q ∈ nablaFamily ℤ n (κ + κ') := by
    rw [nablaFamily, diagramWeight_add]
    exact mul_mem_graded prod_tableauPoly_mem_nabla prod_tableauPoly_mem_nabla
  have h_expand : ∑ k : WeylIndexFamily n (κ + κ'), comulMatrix ℤ n κ κ' (p, q) k •
      nablaBasis ℤ n (κ + κ') k = nablaBasis ℤ n κ p * nablaBasis ℤ n κ' q :=
    sum_coords_nablaBasis h_mem
  simpa [comulMatrix, mulVec, dotProduct, weylEval, vecMulVec_apply, mul_comm] using
    congrArg (fun P ↦ (P.map (algebraMap ℤ R)).eval y) h_expand

variable [IsDomain R] [Infinite R]

/-- Work over an infinite domain, and let `a ⊗ b` be the row vector `(vecMulVec b a).vec`, with
entry `b q * a p` at `(p, q)`. Then `a ⊗ b` times the multiplication matrix is `x` exactly when the
product of the polynomials with coordinates `a` (basis for `κ`) and `b` (basis for `κ'`) has
coordinates `x` (basis for `κ + κ'`). -/
lemma vecMul_comulMatrix_eq_iff {a : WeylIndexFamily n κ → R} {b : WeylIndexFamily n κ' → R}
    {x : WeylIndexFamily n (κ + κ') → R} :
    (vecMulVec b a).vec ᵥ* comulMatrix R n κ κ' = x ↔
      nablaCombination κ a * nablaCombination κ' b = nablaCombination (κ + κ') x := by
  -- Both sides say that the polynomials agree at every `y`: pair with `weylEval n (κ + κ') y` and
  -- use `comulMatrix_mulVec_weylEval`.
  have h_eval_product (y : ((τ : Φ) × n τ) × ℕ → R) :
      MvPolynomial.eval y
          (nablaCombination (κ + κ') ((vecMulVec b a).vec ᵥ* comulMatrix R n κ κ')) =
        MvPolynomial.eval y (nablaCombination κ a * nablaCombination κ' b) := by
    simp [comulMatrix_mulVec_weylEval, ← weylEval.eq_1, Fintype.linearCombination,
      ← dotProduct.eq_1,
      ← dotProduct_mulVec, mul_comm (a ⬝ᵥ _), vec_dotProduct_vec, mul_vecMulVec, vecMulVec_mulVec]
  rw [← nablaCombination_injective.eq_iff, MvPolynomial.funext_iff, MvPolynomial.funext_iff]
  simp only [h_eval_product]

/-- Over an infinite domain, the multiplication matrix `C` is an isometry for the Gram forms:
`Cᵀ (G κ ⊗ G κ') C = G (κ + κ')`, where `G` is the Gram matrix `weylGram` mapped into `R`. -/
lemma comulMatrix_isometry :
    (comulMatrix R n κ κ')ᵀ * ((weylGram n κ).map (Int.cast : ℤ → R) ⊗ₖ
        (weylGram n κ').map (Int.cast : ℤ → R) * comulMatrix R n κ κ') = weylGramOver := by
  -- Test on the evaluation vectors, which `C` sends to tensor products
  -- (`comulMatrix_mulVec_weylEval`).
  refine toLin'.injective (ext_weylEval 0 (fun y _ _ ↦ ?_) Set.infinite_univ)
  -- The kernel for `κ + κ'` is the product of the kernels for `κ` and `κ'`.
  simp [comulMatrix_mulVec_weylEval, vecMul_comulMatrix_eq_iff,
    nablaCombination_weylGramOver_mulVec,
    pow_add, kronecker_mulVec_vec, mul_vecMulVec, vecMulVec_mul, vecMul_transpose,
    mulVec_transpose, weylKernel, highestPoly, tableauPoly, Finset.prod_mul_distrib]

/-- Over an infinite domain, the multiplication matrix `C` is equivariant: for the Schur matrices
`S` of a family `g` of square matrices, `(S κ g ⊗ S κ' g) C = C * S (κ + κ') g`. -/
lemma comulMatrix_equivariant (g : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    schur κ g ⊗ₖ schur κ' g * comulMatrix R n κ κ' =
      comulMatrix R n κ κ' * schur (κ + κ') g := by
  -- Test on the evaluation vectors, which `C` sends to tensor products
  -- (`comulMatrix_mulVec_weylEval`).
  refine toLin'.injective (ext_weylEval 0 (fun y _ _ ↦ ?_) Set.infinite_univ)
  simp [comulMatrix_mulVec_weylEval, schur_mulVec_weylEval_of_schurDetExp_eq_zero,
    kronecker_mulVec_vec,
    mul_vecMulVec, vecMulVec_mul, vecMul_transpose]

/-- Over an infinite domain, let `C` be the multiplication matrix.
(a) `Cᵀ (G κ ⊗ G κ') C = G (κ + κ')` for the Gram matrices `G`; this part does not involve `g`.
(b) `(S κ g ⊗ S κ' g) C = C * S (κ + κ') g` for the Schur matrices `S` of any family `g` of square
matrices. -/
lemma comulMatrix_isometry_and_equivariant (g : ∀ τ : Φ, Matrix (n τ) (n τ) R) :
    let C := comulMatrix R n κ κ'
    -- (a) the matrix is an isometry for the Gram forms
    Cᵀ * ((weylGram n κ).map (↑) ⊗ₖ (weylGram n κ').map (Int.cast : ℤ → R) * C) = weylGramOver ∧
    -- (b) the matrix is equivariant
    schur κ g ⊗ₖ schur κ' g * C = C * schur (κ + κ') g :=
  ⟨comulMatrix_isometry, comulMatrix_equivariant g⟩

/-- The integer matrix whose row (p, q) lists the coordinates of the product of the basis minor
products b_p for κ and b_q for κ', in the basis for κ + κ', has an integer left inverse. -/
lemma hasLeftInv_comulMatrix : HasLeftInv (comulMatrix ℤ n κ κ') := by
  -- A basis tableau for `κ + κ'` splits into its first `κ` and last `κ'` columns of each height.
  -- `f k` and `g k` are the minor products of these columns; `f k * g k` is the basis element.
  let f (k : WeylIndexFamily n (κ + κ')) : MatrixPoly ((τ : Φ) × n τ) ℤ :=
    ∏ τ : Φ, tableauPoly ℤ (Sigma.mk τ)
      (fun h j ↦ (k τ).val h (Fin.castAdd _ j) : Tableau (n τ) (rankAt n τ) (κ τ))
  let g (k : WeylIndexFamily n (κ + κ')) : MatrixPoly ((τ : Φ) × n τ) ℤ :=
    ∏ τ : Φ, tableauPoly ℤ (Sigma.mk τ)
      (fun h j ↦ (k τ).val h (Fin.natAdd _ j) : Tableau (n τ) (rankAt n τ) (κ' τ))
  have hf (k : WeylIndexFamily n (κ + κ')) : f k ∈ nablaFamily ℤ n κ := prod_tableauPoly_mem_nabla
  have hg (k : WeylIndexFamily n (κ + κ')) : g k ∈ nablaFamily ℤ n κ' := prod_tableauPoly_mem_nabla
  have hfg (k : WeylIndexFamily n (κ + κ')) : f k * g k = nablaBasis ℤ n (κ + κ') k := by
    simp [f, g, nablaBasis, Fin.prod_univ_add, tableauPoly, Finset.prod_mul_distrib]
  -- Row `k` of the left inverse is the tensor product of the coordinates of the two factors.
  refine ⟨fun k ↦ (vecMulVec (Function.invFun (nablaCombination κ') (g k))
      (Function.invFun (nablaCombination κ) (f k))).vec,
    ext_row fun k ↦ vecMul_comulMatrix_eq_iff.mpr ?_⟩
  simp [Fintype.linearCombination_apply, ↓sum_coords_nablaBasis, hf, hg, hfg, one_apply]

/-- Let ξ, η, ζ be complex vectors of the Weyl modules of weights κ, κ' and κ+κ'. Assume the
polynomial of ζ is the product of those of ξ and η, where the polynomial `toPoly` of a vector ξ is
Σ_i (Gξ)_i b_i, with G the integer Gram matrix and b_i the basis minor products. Then
`weylNormSq ζ ≤ weylNormSq ξ * weylNormSq η`, where `weylNormSq ξ` is the real part of ξ* G ξ, the
squared norm for the positive definite Hermitian form of G. -/
lemma _root_.New.weylNormSq_le_mul_of_toPoly_eq {ξ : WeylIndexFamily n κ → ℂ}
    {η : WeylIndexFamily n κ' → ℂ} {ζ : WeylIndexFamily n (κ + κ') → ℂ}
    (h_toPoly_eq : toPoly n (κ + κ') ζ = toPoly n κ ξ * toPoly n κ' η) :
    weylNormSq ζ ≤ weylNormSq ξ * weylNormSq η := by
  -- Cauchy–Schwarz for the form `B = G κ ⊗ G κ'` on `C *ᵥ ζ` and `v = ξ ⊗ η`: their pairing is
  -- `weylNormSq ζ` by `h_toPoly_eq`, and `C` is an isometry by `comulMatrix_isometry`.
  let C := comulMatrix ℂ n κ κ'
  let B := (weylGram n κ).map (Int.cast : ℤ → ℂ) ⊗ₖ (weylGram n κ').map (Int.cast : ℤ → ℂ)
  let v : WeylIndexFamily n κ × WeylIndexFamily n κ' → ℂ := (vecMulVec η ξ).vec
  have hC_real : Cᴴ = Cᵀ := by
    ext i j
    simp [C, comulMatrix]
  -- The hypothesis in coordinates: multiplication sends `G ξ ⊗ G η` to `G ζ`.
  have h_coord : (vecMulVec (weylGramOver *ᵥ η) (weylGramOver *ᵥ ξ)).vec ᵥ* C = weylGramOver *ᵥ ζ :=
    vecMul_comulMatrix_eq_iff.mpr h_toPoly_eq.symm
  have h_pair : star (C *ᵥ ζ) ⬝ᵥ B *ᵥ v = weylNormSq ζ := by
    simp [B, v, star_mulVec, ← dotProduct_mulVec, h_coord, ← coe_weylNormSq, hC_real,
      vecMul_transpose _ ξ, kronecker_mulVec_vec, mul_vecMulVec, vecMulVec_mul, mulVec_transpose]
  have h_tensor : (star v ⬝ᵥ B *ᵥ v).re = weylNormSq η * weylNormSq ξ := by
    simp [B, v, ← coe_weylNormSq, ↓map_vecMulVec_star, ← dotProduct_mulVec,
      vecMul_transpose _ ξ, kronecker_mulVec_vec, mul_vecMulVec, vecMulVec_mul, star_vec,
      vec_dotProduct_vec, vecMulVec_mulVec]
  have h_isom : (star (C *ᵥ ζ) ⬝ᵥ B *ᵥ (C *ᵥ ζ)).re = weylNormSq ζ := by
    simp [B, C, star_mulVec, ← dotProduct_mulVec, hC_real, mulVec_mulVec, comulMatrix_isometry,
      ← coe_weylNormSq]
  have h_sq : weylNormSq ζ ^ 2 ≤ weylNormSq η * weylNormSq ξ * weylNormSq ζ := by
    simpa only [h_pair, h_tensor, h_isom, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
      posDef_cauchy_schwarz (M := B) (weylGramOver_posDef.kronecker weylGramOver_posDef) (C *ᵥ ζ) v
  -- Cancel one factor `weylNormSq ζ`; if it is not positive, the right side is still nonnegative.
  nlinarith [mul_nonneg (weylNormSq_nonneg ξ) (weylNormSq_nonneg η)]

end New.GL

end Cartan

/-!
## Products of determinants

* `New.pairedDetProd`: the product of the determinants `det (η τ k * Y τ)`, with one matrix `Y τ`
  for each `τ : Φ`.
-/

namespace New

open Matrix

variable {Φ n a S : Type} [Fintype Φ] [Fintype n] [CommRing S] [Algebra ℂ S] [Fintype a]
  [DecidableEq a] {ι : Φ → Type} [∀ τ : Φ, Fintype (ι τ)]
  (Y : Φ → n → a → S) (η : ∀ τ : Φ, ι τ → Matrix a n ℂ)

/-- The element ∏_τ ∏_k det(η_{τk} Y_τ) of the ℂ-algebra S, for n×a matrices Y_τ over S and
complex a×n matrices η_{τk}. -/
noncomputable def pairedDetProd : S :=
  ∏ τ : Φ, ∏ k : ι τ, ((η τ k).map (algebraMap ℂ S) * of (Y τ)).det

end New
