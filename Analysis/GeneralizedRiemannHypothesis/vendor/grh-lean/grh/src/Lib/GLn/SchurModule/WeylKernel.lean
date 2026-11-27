import Lib.Adelic.Unitary.Defs
import Lib.GLn.SchurModule.TensorModel
import Lib.Shimura.ComplexTheta.AppellHumbertData

/-!
# The Weyl kernel and its Gram matrix: the hook number bound, positivity, Schur's lemma

This file studies the reproducing kernel `K(x, y) = f(yᵀ x)` (`New.weylKernel`), where
`f = New.highestPoly` is the product of leading principal minors. `G = New.weylGram` is the integer
Gram matrix of `K` in the basis `b_i = New.nablaBasis` (products of minors) of the semi-invariants
`New.nablaFamily`. The hook number `New.hookNumber κ N = ⟨f, f⟩ = f(∂) f(0)` is the Fock pairing
of `f` with itself. It is positive and at most `(L ^ L) ^ 3` when the diagrams have at most `L`
boxes in total (`New.hookNumber_pos`, `New.hookNumber_le`). This file also proves that the unitary
group is Zariski dense, and derives Schur's lemma for the Schur matrices.

## Main definitions and results

* `New.toPoly_weylEval`, `New.toPoly_schur`: `New.toPoly`, `ξ ↦ ∑ (G ξ)_i b_i`, sends the vector
  `ev_y = (b_i(y))` (`New.weylEval`) to `K(·, y)`. It turns the Schur matrix of `z` into
  substitution of `zᵀ`, applied after multiplying by the determinant powers `New.detPow` with
  exponents `New.schurDetExp`.
* `New.fillingMatrix_transpose_mul_self`: `G` is the matrix of the form restricted from tensors.
  Hence `G` is symmetric, positive definite, and makes the Schur matrices of `g` and `gᵀ` adjoint
  (`New.weylGram_isSymm`, `New.weylGramOver_posDef`, `New.weylGramOver_mul_schur`).
* `New.mem_range_scalar_of_commute_schur`: a matrix that commutes with `New.schur κ g` for all
  unitary `g` is scalar.

Notions from other files:
* `New.WeylIndexFamily n κ`: families that choose, for each place `τ`, a standard filling with rows
  `n τ`; they index the basis `b_i`.
* `New.schur κ z`: the Schur matrix `S_κ(z)` of matrices `z τ` of size `n' τ × n τ`. Row `i`
  holds the coordinates of `b'_i(z y)` in the products `b_j(y) · ∏_τ det(y_τ)^{d_τ}`, where `b'` is
  the basis for the rows `n'` and `d = New.schurDetExp n n' κ`.

## Relation to the literature

Known; see `Lib.GLn.SchurModule.SchurNorm` and `Lib.GLn.Dual` for sources.
-/

/-!
## Positivity and a bound for the hook number

* `New.hookNumber_pos`, `New.hookNumber_le`: the hook number is positive, and at most
  `(L ^ L) ^ 3` when the diagrams have at most `L` boxes in total.
-/

section Hook

open MvPolynomial Finset Matrix Finsupp Nat RingHom

namespace New

variable {Φ : Type} [Fintype Φ] {κ : Φ → ℕ → ℕ} {N : Φ → ℕ} {L : ℕ}

/-- The hook number, the Fock pairing of `New.highestPoly ℤ κ N` with itself, is positive. -/
@[simp]
lemma hookNumber_pos : 0 < hookNumber κ N := by
  -- `highestPoly ℤ κ N` is nonzero, since its value at the identity array is `1`.
  have h_eval : eval (permArray fun τ (i : Fin (N τ)) ↦ (i : ℕ)) (highestPoly ℤ κ N) = 1 := by
    simp [highestPoly, tableauPoly, minor, map_det, Matrix.map, permArray, Fin.val_inj,
      ← diagonal.eq_1]
  have h_ne : highestPoly ℤ κ N ≠ 0 := fun h_zero ↦ by simp [h_zero] at h_eval
  -- Over `ℤ` conjugation is trivial, so `fockPairing_star_self_pos` is the claim.
  have h_star : MvPolynomial.map (starRingEnd ℤ) (highestPoly ℤ κ N) = highestPoly ℤ κ N :=
    MvPolynomial.ext _ _ fun d ↦ by simp
  simpa only [hookNumber, h_star] using fockPairing_star_self_pos h_ne

@[simp]
lemma hookNumber_ne_zero : hookNumber κ N ≠ 0 := hookNumber_pos.ne'

lemma prod_factorial_le_factorial_sum {ι : Type} (s : Finset ι) (a : ι → ℕ) :
    ∏ i ∈ s, (a i)! ≤ (∑ i ∈ s, a i)! :=
  le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s a)

/-- Two monomials with coefficients `± 1` have Fock pairing at most `d !`, where `d` is the degree
of the first. -/
lemma fockPairing_monomial_monomial_le {σ : Type} (α β : σ →₀ ℕ) (ε ε' : ℤˣ) :
    fockPairing ℤ (monomial α (ε : ℤ)) (monomial β (ε' : ℤ)) ≤ (α.degree)! := by
  classical
  have h_factorial : (α.prod fun _ a ↦ a !) ≤ (α.degree)! :=
    prod_factorial_le_factorial_sum α.support α
  have h_unit : (ε : ℤ) * ε' ≤ 1 := Int.le_of_dvd one_pos (ε.isUnit.mul ε'.isUnit).dvd
  have h_coeff : (ε : ℤ) * (monomial β (ε' : ℤ)).coeff α ≤ 1 := by grind [coeff_monomial]
  grw [fockPairing_monomial, h_coeff, mul_one, h_factorial]

/-- Take at each place `τ` a filling `T τ` with `κ τ h` columns of height `h` for `h < N τ`, and
multiply the minors of all columns. If the degree `∑ τ, ∑ h < N τ, h * κ τ h` of this product is at
most `L`, then its Fock pairing with itself is at most `L ^ (3 * L)`. -/
lemma fockPairing_tableauPoly_le {n : Φ → Type} (T : ∀ τ : Φ, Tableau (n τ) (N τ) (κ τ))
    (h_degree : ∑ τ : Φ, ∑ h ∈ range (N τ), h * κ τ h ≤ L) :
    fockPairing ℤ (∏ τ : Φ, tableauPoly ℤ (Sigma.mk τ) (T τ))
      (∏ τ : Φ, tableauPoly ℤ (Sigma.mk τ) (T τ)) ≤ (L : ℤ) ^ (3 * L) := by
  classical
  -- Expand each minor over permutations. The product becomes a sum of signed monomials of degree
  -- `d`, one for each choice `s : S` of a permutation for every column, and `card S ≤ d !`.
  let S : Type := ∀ (τ : Φ) (h : Fin (N τ)), Fin (κ τ h) → Equiv.Perm (Fin h)
  let α (s : S) : (Σ τ : Φ, n τ) × ℕ →₀ ℕ :=
    ∑ τ : Φ, ∑ h : Fin (N τ), ∑ j : Fin (κ τ h), ∑ i : Fin h, single (⟨τ, T τ h j (s τ h j i)⟩, i) 1
  let ε (s : S) : ℤˣ := ∏ τ : Φ, ∏ h : Fin (N τ), ∏ j : Fin (κ τ h), (s τ h j).sign
  let d : ℕ := ∑ τ : Φ, ∑ h : Fin (N τ), κ τ h * h
  have h_expand :
      ∏ τ : Φ, tableauPoly ℤ (Sigma.mk τ) (T τ) = ∑ s : S, monomial (α s) (ε s : ℤ) := by
    simp_rw [tableauPoly, minor, det_apply, prod_univ_sum, prod_smul, of_apply, X,
      ← monomial_sum_one, smul_monomial]
    simp [α, ε, S, Units.smul_def]
  have h_degree_eq (s : S) : (α s).degree = d := by simp [α, d]
  have h_card : Fintype.card S ≤ d ! := by
    -- the product over all columns of (height)! is at most the factorial of the sum of the heights
    let height : (Σ (τ : Φ) (h : Fin (N τ)), Fin (κ τ h)) → ℕ := fun ⟨_, h, _⟩ ↦ h
    simpa [S, d, height, Fintype.card_perm, Fintype.prod_sigma, Fintype.sum_sigma] using
      prod_factorial_le_factorial_sum univ height
  have h_d_le : d ≤ L := by simpa only [d, sum_range, mul_comm] using h_degree
  rw [h_expand]
  calc
    _ = ∑ s : S, ∑ t : S, fockPairing ℤ (monomial (α s) (ε s : ℤ)) (monomial (α t) (ε t : ℤ)) := by
      simp_rw [LinearMap.map_sum₂, map_sum]
    _ ≤ ∑ _s : S, ∑ _t : S, (d ! : ℤ) := by
      gcongr with s _ t
      grw [fockPairing_monomial_monomial_le, h_degree_eq]
    _ = Fintype.card S * (Fintype.card S * (d ! : ℤ)) := by simp
    _ ≤ (d ! : ℤ) ^ 3 := by grw [h_card, h_card, pow_three]
    _ ≤ ((L : ℤ) ^ L) ^ 3 := by grw [h_d_le, factorial_le_pow, cast_pow]
    _ = (L : ℤ) ^ (3 * L) := by rw [← pow_mul, mul_comm]

/-- Suppose the diagrams with `κ τ h` columns of height `h < N τ` have at most `L` boxes in total,
that is, Σ_τ Σ_{h<N τ} h·κ τ h ≤ L. Then `hookNumber κ N` is at most `(L ^ L) ^ 3`. Here
`hookNumber κ N` is the integer ⟨f,f⟩ = f(∂)f(0), where f is the product over places τ and heights
h < N τ of the leading principal h×h minors raised to the power κ τ h. -/
lemma hookNumber_le (h_degree : ∑ τ : Φ, ∑ h ∈ range (N τ), h * κ τ h ≤ L) :
    hookNumber κ N ≤ ((L : ℤ) ^ L) ^ 3 := by
  -- `highestPoly ℤ κ N` is the product of minors for the fillings `T` with `i` in row `i`.
  let T : ∀ τ : Φ, Tableau (Fin (N τ)) (N τ) (κ τ) := fun _ h _ ↦ Fin.castLE h.is_le'
  rw [← pow_mul, mul_comm, hookNumber, highestPoly]
  exact fockPairing_tableauPoly_le T h_degree

end New

end Hook

/-!
## The kernel and the Gram matrix

Linear identities are tested on the vectors `weylEval n κ y` (`New.GL.ext_weylEval`). An array `y`
has rows `(τ, a)` and columns in `ℕ`; `New.diagramWeight` is the partition with `κ τ h` columns of
height `h`.
-/

section Gram

open MvPolynomial Module New «GL» ComplexOrder Sigma Function Fintype Equiv Finset Matrix

variable {Φ : Type}
  {R S : Type _} [CommRing R] [CommRing S] [Fintype Φ] [DecidableEq Φ]
  {n n' : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)]
  [∀ τ : Φ, Fintype (n' τ)] [∀ τ : Φ, DecidableEq (n' τ)] {κ : Φ → ℕ → ℕ}
  (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) (φ : R →+* S)
  (N : Φ → ℕ) (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ n' τ) (g : ∀ τ : Φ, Matrix (n τ) (n τ) R)
  (ξ η : WeylIndexFamily n κ → R) (s : Φ → R) (y : (Σ τ : Φ, n τ) × ℕ → R)

namespace New.GL

/-! ### Evaluation vectors and the kernel -/

/-- For an array `y` and enumerations `e τ` of the rows, the square matrix at the place `τ` with
`(a, b)` entry `y((τ, a), e τ b)`: the columns of block `τ` numbered below `|n τ|`. -/
def squarePart (τ : Φ) : Matrix (n τ) (n τ) R := of fun a b : n τ ↦ y (⟨τ, a⟩, e τ b)

/-- Every evaluation vector `ev_y` is the image of the evaluation vector at the permutation array
of `e` under the Schur matrix of the square part `New.GL.squarePart e y` of `y`. -/
lemma schur_squarePart_mulVec :
    schur κ (squarePart e y) *ᵥ weylEval n κ (permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ)) =
      weylEval n κ y := by
  -- `squarePart e y` times the permutation array `permArray e` agrees with `y` in the columns below
  -- `rankAt n τ`, the only ones that the basis minors read.
  set w : (Σ τ : Φ, n τ) × ℕ → R := permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ)
  have h_frame : schur κ (squarePart e y) *ᵥ weylEval n κ w =
      weylEval n κ fun ⟨⟨τ, i⟩, k⟩ ↦ ∑ a : n τ, squarePart e y τ i a * w (⟨τ, a⟩, k) := by
    simpa only [schurDetExp_self, detPow_zero, map_one, one_smul] using
      schur_mulVec_weylEval (FitsRanks.refl (κ := κ)) (squarePart e y) w
  have h_agree (τ : Φ) (i : n τ) (k : ℕ) (hk : k < rankAt n τ) :
      ∑ a : n τ, squarePart e y τ i a * w (⟨τ, a⟩, k) = y (⟨τ, i⟩, k) := by
    lift k to Fin (rankAt n τ) using hk
    simp [squarePart, w, permArray, Fin.val_inj, ← eq_symm_apply]
  rw [h_frame]
  ext i
  simp (disch := omega) only [weylEval, nablaBasis, tableauPoly, minor, map_prod, RingHom.map_det,
    RingHom.mapMatrix_apply, Matrix.map, of_apply, eval_X, Function.comp_apply, h_agree]

/-- Two linear maps `L`, `L'` into a free module over a domain are equal if they agree on the
evaluation vectors `weylEval n κ y`. It is enough to take the arrays `y` whose entries lie in an
infinite set `s` and at which `detPow R n d`, the product of the powers `d τ` of the determinants
of the square blocks, does not vanish. -/
lemma ext_weylEval [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    {L L' : (WeylIndexFamily n κ → R) →ₗ[R] M} {s : Set R} (d : Φ → ℕ)
    (h_agree : ∀ y : (Σ τ : Φ, n τ) × ℕ → R, (∀ p : (Σ τ : Φ, n τ) × ℕ, y p ∈ s) →
      eval y (detPow R n d) ≠ 0 → L (weylEval n κ y) = L' (weylEval n κ y))
    (hs_infinite : s.Infinite) : L = L' := by
  -- As `M` is free, it suffices to compare `ℓ (L eᵢ)` and `ℓ (L' eᵢ)` for linear forms `ℓ`.
  ext i
  refine eval_apply_injective R (LinearMap.ext fun ℓ ↦ ?_)
  -- These are the coefficients of two combinations `P L`, `P L'` of the independent `b_j * D`, with
  -- `D = detPow R n d`, which agree at every `y` with entries in the infinite set `s`: by
  -- `h_agree` if `D y ≠ 0`, and trivially if `D y = 0`.
  let P (F : (WeylIndexFamily n κ → R) →ₗ[R] M) : MatrixPoly (Σ τ : Φ, n τ) R :=
    ∑ j : WeylIndexFamily n κ, ℓ (F (Pi.single j 1)) • (nablaBasis R n κ j * detPow R n d)
  have h_value (F : (WeylIndexFamily n κ → R) →ₗ[R] M) (y : (Σ τ : Φ, n τ) × ℕ → R) :
      eval y (P F) = ℓ (F (weylEval n κ y)) * eval y (detPow R n d) := by
    rw [pi_eq_sum_univ' (weylEval n κ y)]
    simp [P, ← mul_assoc, sum_mul, mul_comm _ (ℓ _), weylEval]
  have h_poly : P L = P L' := funext_set (fun _ ↦ s) (fun _ ↦ hs_infinite) fun y hy ↦ by
    by_cases hD : eval y (detPow R n d) = 0
    · simp [h_value, hD]
    · rw [h_value, h_value, h_agree y (fun p ↦ hy p (Set.mem_univ p)) hD]
  exact (linearIndependent_nablaBasis_mul_detPow d).eq_coords_of_eq h_poly i

section

omit [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)]

lemma map_weylKernel : MvPolynomial.map φ (weylKernel n κ y) = weylKernel n κ (φ ∘ y) := by
  simp [weylKernel, rowSubst, map_bind₁, ← C_mul']

/-- `f(yᵀ x)` as a polynomial in `x`: the product of the leading minors of `yᵀ x`. -/
lemma rowSubst_highestPoly :
    rowSubst (fun τ : Φ ↦ of fun (i : Fin (N τ)) (a : n τ) ↦ y (⟨τ, a⟩, i)) (highestPoly R κ N) =
      ∏ τ : Φ, ∏ h ∈ range (N τ),
        (of fun s t : Fin h ↦ ∑ a : n τ, y (⟨τ, a⟩, s) • X (⟨τ, a⟩, ↑t)).det ^ κ τ h := by
  simp [highestPoly, prod_range, rowSubst, tableauPoly, minor, AlgHom.map_det, Matrix.map]

/-- The kernel is symmetric in `x` and `y`: `K(·, y)` is the generic kernel, whose coefficients are
polynomials in the variables for `y`, with `y` put in for its variables `x`, and the coefficient
variables kept as the new variables. -/
lemma weylKernel_symm :
    weylKernel n κ y = MvPolynomial.eval (C ∘ y)
      (weylKernel n κ (X : (Σ τ : Φ, n τ) × ℕ → MatrixPoly (Σ τ : Φ, n τ) R)) := by
  simp [weylKernel, rowSubst_highestPoly, ← C_mul', mul_comm, RingHom.map_det, Matrix.map]
  -- The minors of `yᵀ X` and `Xᵀ y` are determinants of transposed matrices.
  refine prod_congr rfl fun τ _ ↦ prod_congr rfl fun k _ ↦ ?_
  exact congrArg (fun M ↦ M ^ κ τ k) (det_transpose _).symm

end

omit [∀ τ : Φ, DecidableEq (n τ)] in
/-- Multiplying `y` on the right by the upper triangular part of `b` scales the kernel `K(·, y)`
by `∏ b(τ, i, i) ^ λ(τ, i)`, with `λ = New.diagramWeight (rankAt n) κ`. -/
lemma weylKernel_borelMul (b : Φ × ℕ × ℕ → R) :
    weylKernel n κ (borelMul fst b y) =
      ((diagramWeight (rankAt n) κ).prod fun (p : Φ × ℕ) (k : ℕ) ↦ b (p.1, p.2, p.2) ^ k) •
        weylKernel n κ y := by
  -- By symmetry of the kernel, `weylKernel n κ y` is the generic kernel `K` with `y` put in for its
  -- polynomial variables, and in these variables `K` is semi-invariant.
  let A : Type _ := MatrixPoly (Σ τ : Φ, n τ) R
  let K : MatrixPoly (Σ τ : Φ, n τ) A := weylKernel n κ (X : (Σ τ : Φ, n τ) × ℕ → A)
  have h_semi : aeval (borelMul fst (C ∘ b) (C ∘ y) : (Σ τ : Φ, n τ) × ℕ → A) K =
      ((diagramWeight (rankAt n) κ).prod fun p k ↦ C (b (p.1, p.2, p.2)) ^ k) * aeval (C ∘ y) K :=
    mem_nabla.mp (weylKernel_mem_nablaFamily X) A (C ∘ b) (C ∘ y)
  have h_C_borelMul :
      (borelMul fst (C ∘ b) (C ∘ y) : (Σ τ : Φ, n τ) × ℕ → A) = C ∘ borelMul fst b y :=
    funext fun x ↦ by simp [borelMul]
  simp only [MvPolynomial.aeval_eq_eval, h_C_borelMul] at h_semi
  simpa [K, ← C_mul', map_finsuppProd, weylKernel_symm (R := R), comp_def] using h_semi

/-- For a vector ξ of the Weyl module over a commutative ring `R` and an array `y` over `R`, the
value at `y` of the polynomial `toPoly n κ ξ = Σ_i (Gξ)_i b_i` equals ev_yᵀ G ξ. Here the b_i are
the basis products of minors `nablaBasis`, indexed by `WeylIndexFamily n κ`, and
ev_y = `weylEval n κ y` is the vector of values b_i(y). G is the integer Gram matrix `weylGram`, the
coefficients of the generic kernel in the products b_i(x) b_j(y), mapped into `R`. -/
@[simp ←]
lemma eval_toPoly : MvPolynomial.eval y (toPoly n κ ξ) = weylEval n κ y ⬝ᵥ weylGramOver *ᵥ ξ := by
  simp [toPoly, mul_comm, linearCombination_apply, dotProduct, weylEval]

lemma nablaCombination_weylGramOver_mulVec :
    nablaCombination κ (weylGramOver *ᵥ ξ) = toPoly n κ ξ := rfl

/-- For square matrices `g τ` and scalars `s τ`, the block diagonal matrix `diag(g τ, s τ)`,
reindexed by `n' τ` through the bijection `ι τ : n τ ⊕ Unit ≃ n' τ`. -/
noncomputable def blockScalar (τ : Φ) : Matrix (n' τ) (n' τ) R :=
  ((g τ).fromBlocks 0 0 (diagonal fun _ ↦ s τ)).reindex (ι τ) (ι τ)

omit [DecidableEq Φ] in
/-- The weight at `(τ, i)` is the weight at `(τ, i + 1)` plus `κ τ (i + 1)` when `i + 1 < N τ`:
the columns of height `i + 1` are counted at `i` but not at `i + 1`. -/
@[grind]
lemma diagramWeight_eq_succ_add (τ : Φ) (i : ℕ) :
    diagramWeight N κ (τ, i) =
      diagramWeight N κ (τ, i + 1) + if i + 1 < N τ then κ τ (i + 1) else 0 := by
  grind [diagramWeight_apply, =_ Ico_add_one_left_eq_Ioo, sum_eq_sum_Ico_succ_bot, Ico_eq_empty]

/-- The kernel `weylKernel n κ y` is the polynomial f(yᵀx) in x, with f the product of leading
minors; here y is the permutation array of `e` (entry 1 at row (τ,a), column `e τ a`, else 0). If
`g τ a b = 0` whenever `e τ a < e τ b`, substituting x ↦ g x in the kernel (`rowSubst g`) scales it
by `∏ g τ a a ^ λ(τ, e τ a)`, with `λ = New.diagramWeight (rankAt n) κ`. -/
lemma rowSubst_weylKernel_permArray (hg_tri : ∀ τ : Φ, (g τ)ᵀ.BlockTriangular (e τ)) :
    rowSubst g (weylKernel n κ (permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ))) =
      (∏ τ : Φ, ∏ a : n τ, g τ a a ^ diagramWeight (rankAt n) κ (τ, e τ a)) •
        weylKernel n κ (permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ)) := by
  -- Substituting `g` multiplies the array on the right by the triangular array `t` of the entries
  -- of `g` in the numbering `e`; by `weylKernel_borelMul` this scales the kernel by a monomial in
  -- the diagonal entries. In the product defining `t` the condition selects at most one factor.
  set w : (Σ τ : Φ, n τ) × ℕ → R := permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ)
  let t (x : Φ × ℕ × ℕ) : R :=
    ∏ τ : Φ, ∏ a : n τ, ∏ b : n τ, if x = (τ, (e τ a : ℕ), (e τ b : ℕ)) then g τ b a else 1
  have h_sub : rowSubst g (weylKernel n κ w) = weylKernel n κ (borelMul fst t w) := by
    have h_tri (τ : Φ) (a b : n τ) (hab : e τ a < e τ b) : g τ a b = 0 := hg_tri τ hab
    rw [weylKernel, rowSubst_rowSubst, weylKernel]
    congr 2
    -- Entrywise, `borelMul` keeps only the entries on one side of the diagonal; the others vanish.
    simpa +instances [t, w, funext_iff, ← ext_iff, (e _).surjective.forall, borelMul, permArray,
      Fin.val_inj, ite_and, Matrix.mul_apply] using h_tri
  have h_diag : ((diagramWeight (rankAt n) κ).prod fun p k ↦ t (p.1, p.2, p.2) ^ k) =
      ∏ τ, ∏ a, g τ a a ^ diagramWeight (rankAt n) κ (τ, e τ a) := by
    simp [t, ← prod_pow, Finsupp.prod_finsetProd_comm, ← and_assoc,
      ← Prod.ext_iff (y := (_, _)), ite_and, Fin.val_inj]
    -- Outside the support of the weight the exponent is zero.
    exact prod_congr rfl fun τ _ ↦ prod_congr rfl fun a _ ↦
      ite_eq_right_iff.2 fun h_zero ↦ by rw [h_zero, pow_zero]
  rw [h_sub, weylKernel_borelMul, h_diag]

omit [Fintype Φ] [DecidableEq Φ] [∀ τ : Φ, DecidableEq (n τ)] [∀ τ : Φ, DecidableEq (n' τ)] in
lemma rankAt_eq_succ (ι : ∀ τ : Φ, n τ ⊕ Unit ≃ n' τ) (τ : Φ) : rankAt n' τ = rankAt n τ + 1 := by
  simp [← card_congr (ι τ)]

end «GL»

/-! ### The kernel formula -/

/-- The polynomial attached by the Gram matrix to the evaluation vector ev_y is the kernel x ↦
f(yᵀx), f the highest weight product of leading minors. -/
@[simp]
lemma toPoly_weylEval : toPoly n κ (weylEval n κ y) = weylKernel n κ y := by
  -- Expand the generic kernel `K` in the basis, with coefficients `c i` in `A = ℤ[Y]`; expand the
  -- `c i` in the basis again, which gives the Gram matrix; then specialise `Y` to `y`.
  let A : Type := MatrixPoly (Σ τ : Φ, n τ) ℤ
  let K : MatrixPoly (Σ τ : Φ, n τ) A := weylKernel n κ (X : (Σ τ : Φ, n τ) × ℕ → A)
  let c : WeylIndexFamily n κ → A := invFun (nablaCombination κ) K
  have hK : ∑ i, c i • nablaBasis A n κ i = K :=
    sum_coords_nablaBasis (weylKernel_mem_nablaFamily X)
  -- The monomial coefficients of `K` are semi-invariant in `Y` (`weylKernel_borelMul`), hence so is
  -- `c i`: the coordinates lie in any subgroup that holds all coefficients.
  have h_coeff (d : (Σ τ : Φ, n τ) × ℕ →₀ ℕ) : K.coeff d ∈ (nablaFamily ℤ n κ).toAddSubgroup := by
    simp [A, K, mem_nabla, aeval_eq_eval₂Hom, ← coeff_map, map_weylKernel, weylKernel_borelMul,
      comp_def]
  have hc (i : WeylIndexFamily n κ) : c i ∈ nablaFamily ℤ n κ :=
    coord_mem_of_coeff_mem _ 0 (by simpa [detPow_zero] using hK) h_coeff i
  have h_gram (i : WeylIndexFamily n κ) : ∑ j, weylGram n κ i j • nablaBasis ℤ n κ j = c i :=
    sum_coords_nablaBasis (hc i)
  -- Put `y` in for the variables `Y` of the coefficients.
  have hK_at_y : ∑ i, aeval y (c i) • nablaBasis R n κ i = weylKernel n κ y := by
    simpa [A, K, map_weylKernel, ← C_mul', comp_def] using congrArg (mapAlgHom (aeval y)) hK
  have hc_at_y (i : WeylIndexFamily n κ) :
      aeval y (c i) = (weylGramOver *ᵥ weylEval n κ y) i := by
    simp [← h_gram, ← eval_map, aeval_def, mulVec, dotProduct, weylEval]
  simp [← hK_at_y, hc_at_y, toPoly, linearCombination_apply]

/-- The Gram matrix `New.weylGram` does not depend on the labelling of the places: for a bijection
`p` from `Φ` to `Ψ`, the Gram matrix of `(n, κ)` is that of the data transported to `Ψ`, with rows
and columns reindexed along `p`. -/
lemma GL.weylGram_eq_submatrix {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] (κ : Φ → ℕ → ℕ) (p : Φ ≃ Ψ) :
    weylGram n κ =
      (weylGram (fun σ : Ψ ↦ n (p.symm σ)) fun σ : Ψ ↦ κ (p.symm σ)).submatrix
        (p.piCongrLeft' fun τ : Φ ↦ BasisTableau (n τ) (rankAt n τ) (κ τ))
        (p.piCongrLeft' fun τ : Φ ↦ BasisTableau (n τ) (rankAt n τ) (κ τ)) := by
  -- Compare the two matrices on the vectors `weylEval n κ y`, through the injective
  -- `nablaCombination κ`. For `Φ` this gives the kernel at `y` (`toPoly_weylEval`); for `Ψ` the
  -- same after renaming the variables.
  let e : (Σ σ, n (p.symm σ)) × ℕ → (Σ τ, n τ) × ℕ := Prod.map p.symm.sigmaCongrLeft id
  refine toLin'.injective (ext_weylEval 0 (fun y _ _ ↦ ?_) Set.infinite_univ)
  refine nablaCombination_injective ((toPoly_weylEval y).trans ?_)
  simpa [toPoly, rowSubst, nablaBasis, e, weylKernel, highestPoly, reindex_equiv p.symm,
    reindex_equiv (p.piCongrLeft' _).symm, tableauPoly, minor, AlgHom.map_det, Matrix.map,
    linearCombination_apply, mulVec, dotProduct, weylEval, RingHom.map_det] using
    congrArg (rename (R := ℤ) e) (toPoly_weylEval (y ∘ e)).symm

@[simp]
lemma map_toPoly : MvPolynomial.map φ (toPoly n κ ξ) = toPoly n κ (φ ∘ ξ) := by
  simp [toPoly, ← C_mul', linearCombination_apply, mulVec, dotProduct]

/-! ### The form restricted from tensors -/

omit [∀ τ : Φ, DecidableEq (n τ)] in
/-- The kernel at `y` is the pairing of the tensor of `y` with the tensor of the variables. -/
lemma weylKernel_eq_sum_fillingPoly (y : (Σ τ : Φ, n τ) × ℕ → R) :
    weylKernel n κ y = ∑ T : ColumnFilling n κ, eval y (fillingPoly R T) • fillingPoly R T := by
  -- the Cauchy–Binet formula for one leading minor of `yᵀ x`
  let m (τ : Φ) (h : ℕ) (I : IncreasingMap (rankAt n τ) h) : MatrixPoly (Σ τ : Φ, n τ) R :=
    minor R (Sigma.mk τ ∘ (rowEquivFin n τ).symm ∘ I.1)
  have hminor (τ : Φ) (h : ℕ) :
      (of fun s t : Fin h ↦ ∑ a : n τ, y (⟨τ, a⟩, s) • X (⟨τ, a⟩, ↑t)).det =
        ∑ I : IncreasingMap (rankAt n τ) h, eval y (m τ h I) • m τ h I := by
    refine (det_sum_smul_X τ (of fun s a ↦ y (⟨τ, a⟩, s))).trans (sum_congr rfl fun I _ ↦ ?_)
    rw [← det_transpose]
    simp only [m, minor, RingHom.map_det]
    congr 2
    exact Matrix.ext fun s t ↦ by simp
  simp_rw [weylKernel, rowSubst_highestPoly, prod_range, ← Fin.prod_const, hminor, Fintype.prod_sum]
  refine sum_congr rfl fun T _ ↦ ?_
  simp [prod_smul, fillingPoly, tableauPoly, m, fillingRows, comp_def]

/-- Let F = `fillingMatrix n κ` be the integral matrix of the embedding of the Weyl module into
tensors, whose row `T` holds the coordinates of the product of minors of `T` in the standard basis.
Then FᵀF = `weylGram n κ`: the Gram matrix is that of the form on tensors for which the basis
tensors are orthonormal, restricted to the Weyl module. -/
lemma fillingMatrix_transpose_mul_self :
    (fillingMatrix n κ)ᵀ * fillingMatrix n κ = weylGram n κ := by
  -- Compare the polynomials of both matrices applied to an evaluation vector: each is the kernel.
  refine toLin'.injective
    (ext_weylEval 0 (fun y _ _ ↦ nablaCombination_injective ?_) Set.infinite_univ)
  have h_int : weylGramOver (R := ℤ) = weylGram n κ := Matrix.ext fun i j ↦ by simp
  have h_gram : nablaCombination κ (weylGram n κ *ᵥ weylEval n κ y) = weylKernel n κ y := by
    rw [← h_int, nablaCombination_weylGramOver_mulVec, toPoly_weylEval]
  rw [toLin'_apply, toLin'_apply, h_gram, weylKernel_eq_sum_fillingPoly, ← mulVec_mulVec,
    ← fillingMatrixOver_int, nablaCombination_transpose_mulVec]
  simp only [fillingMatrixOver_mulVec_weylEval]

/-- The Gram matrix `weylGramOver` over `R`, which is the integer matrix `New.weylGram` mapped into
`R`, equals FᵀF. Here F = `fillingMatrixOver R n κ` is the integer matrix `fillingMatrix` mapped
into `R`. Thus the Gram matrix is that of the form restricted from tensors. -/
lemma weylGramOver_eq_transpose_mul :
    (weylGramOver : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) R) =
      (fillingMatrixOver R n κ)ᵀ * fillingMatrixOver R n κ := by
  rw [weylGramOver, ← fillingMatrix_transpose_mul_self]
  exact Matrix.map_mul (f := Int.castRingHom R)

/-- The polynomial of a vector is the pairing of its tensor with the tensor of the variables. -/
lemma toPoly_eq_sum_fillingPoly (ξ : WeylIndexFamily n κ → R) :
    toPoly n κ ξ = ∑ T : ColumnFilling n κ, (fillingMatrixOver R n κ *ᵥ ξ) T • fillingPoly R T := by
  rw [← nablaCombination_weylGramOver_mulVec, weylGramOver_eq_transpose_mul, ← mulVec_mulVec,
    nablaCombination_transpose_mulVec]

/-- The integer Gram matrix `weylGram n κ` is symmetric. Its entries are the chosen coefficients of
the generic kernel `weylKernel n κ` in the products b_i(x) b_j(y) of the basis minor products
b = `nablaBasis`, indexed by `WeylIndexFamily n κ`. -/
lemma weylGram_isSymm : (weylGram n κ).IsSymm := by
  rw [← fillingMatrix_transpose_mul_self, IsSymm, transpose_mul, transpose_transpose]

/-- The Gram matrix `weylGram n κ` of the Weyl module, indexed by `WeylIndexFamily n κ` and with
entries mapped into `ℂ` (`weylGramOver`), is positive definite. It is the Gram matrix of the
restriction to the Weyl module of the form on tensors for which the standard basis tensors are
orthonormal (see `fillingMatrix_transpose_mul_self`). -/
lemma weylGramOver_posDef :
    (weylGramOver : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℂ).PosDef := by
  -- The form is restricted from tensors along a real matrix `F` with a left inverse.
  let F : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) ℂ := fillingMatrixOver ℂ n κ
  obtain ⟨Q, hQ⟩ := exists_fillingMatrix_leftInverse (n := n) (κ := κ)
  have h_left : Q.map (Int.cast : ℤ → ℂ) * F = 1 :=
    (Matrix.map_mul (f := Int.castRingHom ℂ)).symm.trans (by simp [hQ])
  have h_inj : Injective F.mulVec := LeftInverse.injective (g := (Q.map Int.cast).mulVec) fun ξ ↦ by
    rw [mulVec_mulVec, h_left, one_mulVec]
  have h_real : Fᵀ = Fᴴ := Matrix.ext fun i T ↦ by simp [F]
  rw [weylGramOver_eq_transpose_mul, h_real]
  exact PosDef.conjTranspose_mul_self F h_inj

/-- For a family `g` of square matrices `g τ`, let `G = weylGramOver` be the integer Gram matrix
`New.weylGram` for rows `n` and column counts `κ`, mapped into `R` and indexed by
`WeylIndexFamily n κ`. Let `schur κ g` be the Schur matrix S_κ(g) of `g` acting on the Weyl module.
Then G·S_κ(g) = S_κ(gᵀ)ᵀ·G, so the Schur matrices of `g` and of the transposes `(g τ)ᵀ` are adjoint
for the form with Gram matrix G. -/
lemma weylGramOver_mul_schur :
    weylGramOver * schur κ g = (schur κ fun τ : Φ ↦ (g τ)ᵀ)ᵀ * weylGramOver := by
  -- Adjointness is inherited from the action on tensors.
  let F : Matrix (ColumnFilling n κ) (WeylIndexFamily n κ) R := fillingMatrixOver R n κ
  calc weylGramOver * schur κ g
    _ = Fᵀ * (minorsMatrix κ g * F) := by
      rw [weylGramOver_eq_transpose_mul, Matrix.mul_assoc, fillingMatrixOver_mul_schur]
    _ = (minorsMatrix κ (fun τ : Φ ↦ (g τ)ᵀ) * F)ᵀ * F := by
      rw [minorsMatrix_transpose, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    _ = (schur κ fun τ : Φ ↦ (g τ)ᵀ)ᵀ * weylGramOver := by
      rw [← fillingMatrixOver_mul_schur, transpose_mul, weylGramOver_eq_transpose_mul,
        Matrix.mul_assoc]

/-! ### Schur matrices and substitution -/

/-- If the ranks fit `κ`, then `c ᵥ* S_κ(z) = x` if and only if the substitution `y ↦ z y` sends
`Σ_i c_i b'_i` to `(Σ_j x_j b_j) · ∏_τ det(y_τ)^{d_τ}`, with `d = New.schurDetExp n n' κ`. -/
lemma GL.vecMul_schur_eq_iff (h_fits : FitsRanks n n' κ) (z : ∀ τ : Φ, Matrix (n' τ) (n τ) R)
    {c : WeylIndexFamily n' κ → R} {x : WeylIndexFamily n κ → R} :
    c ᵥ* schur κ z = x ↔
      rowSubst z (nablaCombination κ c) =
        nablaCombination κ x * detPow R n (schurDetExp n n' κ) := by
  have h_subst : rowSubst z (nablaCombination κ c) =
      nablaCombination κ (c ᵥ* schur κ z) * detPow R n (schurDetExp n n' κ) := by
    simp [← sum_schur_smul_nablaBasis h_fits, vecMul_eq_sum, sum_mul, linearCombination_apply]
  -- The determinant factor cancels, and `nablaCombination κ` is injective.
  rw [h_subst, isRegular_detPow.right.eq_iff, nablaCombination_injective.eq_iff]

/-- Let `R` be a domain of characteristic zero, and assume `FitsRanks n n' κ`: at each place τ,
|n_τ| ≤ |n'_τ| and `κ τ h = 0` for |n_τ| < h < |n'_τ|. For a family `z τ` of `n' τ × n τ` matrices
and a Weyl module vector ξ, the polynomial `toPoly n' κ` of S_κ(z)ξ, where S_κ(z) = `schur κ z` is
the Schur matrix, is x ↦ (ξ̂·D)(zᵀx). Here ξ̂ = `toPoly n κ ξ` = Σ_i (Gξ)_i b_i (G the Gram matrix,
b_i the basis minor products), and D = ∏_τ det_τ^{d_τ}, with det_τ the determinant of the variables
in block τ and its first |n_τ| columns. The exponent is d_τ = `schurDetExp n n' κ τ`, equal to
`κ τ |n_τ|` if |n_τ| < |n'_τ| and 0 otherwise. -/
@[simp]
lemma toPoly_schur (h_fits : FitsRanks n n' κ) [IsDomain R] [CharZero R]
    (z : (τ : Φ) → Matrix (n' τ) (n τ) R) (ξ : WeylIndexFamily n κ → R) :
    toPoly n' κ (schur κ z *ᵥ ξ) =
      rowSubst (fun τ : Φ ↦ (z τ)ᵀ) (toPoly n κ ξ * detPow R n (schurDetExp n n' κ)) := by
  -- Both sides are linear in `ξ`, so by `ext_weylEval` take `ξ = ev_y` with `D y ≠ 0`, and multiply
  -- by `D y`: the left side becomes the kernel at `z y`, that is `highestPoly` of rank `n'` at
  -- `yᵀ zᵀ x`.
  let D : MatrixPoly (Σ τ : Φ, n τ) R := detPow R n (schurDetExp n n' κ)
  -- The minors of `yᵀ x` of size below `rankAt n τ` give the kernel in rank `n`, the minor of size
  -- `rankAt n τ` is `det y * det x`, and the larger ones have exponent `0` by `h_fits`.
  have h_minors (y : (Σ τ : Φ, n τ) × ℕ → R) :
      ∏ τ : Φ, ∏ k ∈ range (rankAt n' τ),
        (of fun s t : Fin k ↦ ∑ a : n τ, y (⟨τ, a⟩, s) • X (⟨τ, a⟩, ↑t)).det ^ κ τ k =
      D.eval y • (weylKernel n κ y * D) := by
    simp only [D, smul_eq_C_mul, detPow, minor, map_prod, map_pow, RingHom.map_det, weylKernel,
      rowSubst_highestPoly, ← prod_mul_distrib]
    congr with τ
    -- split the product at `k = rankAt n τ`; the factors after that one are `1`
    rw [← prod_range_mul_prod_Ico _ (h_fits τ).1, schurDetExp, mul_left_comm, ← mul_pow,
      (Ico ..).prod_eq_ite (rankAt n τ) (by simp_all [FitsRanks, Ne.lt_of_le']),
      ← (C.mapMatrix _).det_transpose, ← det_mul]
    simp [-det_mul, ← (equivFin (n τ)).symm.sum_comp, Matrix.map]
    rfl
  suffices h_lin : toPoly n' κ ∘ₗ toLin' (schur κ z) =
      (rowSubst fun τ ↦ (z τ)ᵀ).toLinearMap ∘ₗ LinearMap.mulRight R D ∘ₗ toPoly n κ from
    LinearMap.congr_fun h_lin ξ
  refine ext_weylEval (schurDetExp n n' κ) (fun y _ (hy : D.eval y ≠ 0) ↦ ?_) Set.infinite_univ
  change toPoly n' κ (schur κ z *ᵥ weylEval n κ y) =
    rowSubst (fun τ ↦ (z τ)ᵀ) (toPoly n κ (weylEval n κ y) * D)
  rw [← smul_right_inj hy, ← map_smul, ← map_smul, schur_mulVec_weylEval h_fits, toPoly_weylEval,
    toPoly_weylEval, ← h_minors, ← rowSubst_highestPoly, rowSubst_rowSubst, weylKernel]
  simp [mul_comm (z ..)]
  rfl

variable [IsDomain R] [CharZero R]

/-- Over a domain of characteristic zero, the map sending a coordinate vector ξ to the
polynomial ∑ (Gξ)_i b_i, G the Gram matrix, is injective. -/
lemma toPoly_injective : Function.Injective (toPoly (R := R) n κ) := by
  -- The integer `det G` is not zero, since `G` is positive definite over `ℂ`.
  have h_int : (weylGram n κ).det ≠ 0 := by
    simpa [weylGramOver, ← Int.cast_det] using (weylGramOver_posDef (n := n) (κ := κ)).det_pos.ne'
  have h_det : (weylGramOver : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) R).det ≠ 0 := by
    rwa [weylGramOver, ← Int.cast_det, Int.cast_ne_zero]
  refine (injective_iff_map_eq_zero _).2 fun ξ hξ ↦
    eq_zero_of_mulVec_eq_zero h_det (nablaCombination_injective ?_)
  rw [nablaCombination_weylGramOver_mulVec, hξ, map_zero]

/-- Let `toPoly n κ` be the map on the Weyl module `WeylIndexFamily n κ → ℂ` sending ξ to Σ_i (Gξ)_i
b_i. Here G is the Gram matrix `weylGramOver` (the integer matrix `New.weylGram` mapped into ℂ), and
b_i = `nablaBasis ℂ n κ i` are the basis minor products. Over ℂ, its range is exactly the module
`New.nablaFamily ℂ n κ` of Borel semi-invariant polynomials of the weight given by κ. -/
lemma range_toPoly : (toPoly n κ).range = nablaFamily ℂ n κ :=
  -- The Gram matrix is invertible, so the range is that of `nablaCombination κ`, the span of the
  -- basis.
  ((toLinearEquiv' _ weylGramOver_posDef.isUnit.invertible).range_comp _).trans
    range_nablaCombination

end New

end Gram

/-!
## Zariski density of the unitary group and Schur's lemma

`New.weylEval n κ y` is the vector of the values at the array `y` of the basis minor products.
-/

section SchurLemma

namespace New

open MvPolynomial Matrix «GL» RingHom Function

variable {Φ : Type} {K : Type _} [Field K] [CharZero K] [Fintype Φ]
  {n : Φ → Type} [∀ τ : Φ, Fintype (n τ)] [∀ τ : Φ, DecidableEq (n τ)] {κ : Φ → ℕ → ℕ}

section Density

open Complex Norms.L2Operator NormedSpace ComplexStarModule

/-- For a complex polynomial P in the entries of a family of square matrices, its value
`evalMatrix g P` at the family `g` is an entire function of `g`. -/
lemma GL.analyticOnNhd_evalMatrix {P : MvPolynomial ((τ : Φ) × n τ × n τ) ℂ} :
    AnalyticOnNhd ℂ (fun g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ ↦ evalMatrix g P) ⊤ :=
  -- `evalMatrix g P` is `P` evaluated at the entries of `g`, which are linear functions of `g`.
  .eval_linearMap ⟨⟨_, by tauto⟩, by tauto⟩ P

/-- The unitary group is Zariski dense. Let P be a complex polynomial in the entries of a family
of square matrices `g τ`, and write `evalMatrix g P` for its value at `g`. If P vanishes at every
family of unitary matrices (`(g τ)ᴴ * g τ = 1` for all τ), then it vanishes at every family x. -/
lemma GL.zariski_dense_unitary (x : (τ : Φ) → Matrix (n τ) (n τ) ℂ)
    (P : MvPolynomial ((τ : Φ) × n τ × n τ) ℂ)
    (hP : ∀ g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ, (∀ τ : Φ, (g τ)ᴴ * g τ = 1) → evalMatrix g P = 0) :
    evalMatrix x P = 0 := by
  -- `P` is entire and `exp` is a submersion at `0`, so it is enough that `P` vanish at each
  -- `exp y`.
  -- The entire function `s ↦ P (exp (I • (s • -ℜ y + ℑ y)))` vanishes for real `s`, where the
  -- exponential is unitary, hence everywhere; and at `s = I` the exponent is `y`.
  refine eq_zero_of_submersion analyticOnNhd_evalMatrix hasStrictFDerivAt_exp_zero (by bound)
    (.of_forall fun y ↦ ?_) x
  let path (s : ℂ) : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ := I • (s • (-ℜ y).val + ℑ y)
  have h_entire : AnalyticOnNhd ℂ (fun s : ℂ ↦ evalMatrix (NormedSpace.exp (path s)) P) Set.univ :=
    analyticOnNhd_evalMatrix.comp (fun _ _ ↦ .comp (exp_analytic _) (f := path) (by fun_prop))
      (by simp)
  have h_real (t : ℝ) : evalMatrix (NormedSpace.exp (path t)) P = 0 := by
    -- at real `s` the exponent is skew-adjoint, so its exponential is unitary
    have h_unitary : star (NormedSpace.exp (path t)) * NormedSpace.exp (path t) = 1 :=
      Unitary.star_mul_self_of_mem (selfAdjoint.expUnitary (t • -ℜ y + ℑ y)).prop
    exact hP _ (congrFun h_unitary)
  -- The real points accumulate at `0`, so the identity theorem applies.
  have h_zero : (fun s : ℂ ↦ evalMatrix (NormedSpace.exp (path s)) P) = fun _ ↦ 0 :=
    h_entire.eq_of_frequently_eq analyticOnNhd_const
      (((hasDerivAt_id 0).ofReal_comp.tendsto_nhdsNE one_ne_zero).frequently (.of_forall h_real))
  have h_path_I : path I = y := by simp [path, smul_smul, realPart_add_I_smul_imaginaryPart]
  simpa [h_path_I] using congrFun h_zero I

end Density

variable [DecidableEq Φ]

/-- Over a field `K` of characteristic zero, let `v₀` be the frame vector of the enumerations `e`,
the evaluation vector at the permutation array of `e`. Two linear maps that agree on
`schur κ g *ᵥ v₀` for all tuples `g` of invertible matrices are equal.

So the translates of the frame vector under the product of general linear groups span the module.
The reason is duality: they are the evaluation vectors at invertible arrays, and a polynomial that
vanishes on invertible matrices is zero.

In other words, the frame vector is cyclic for the product of the general linear groups. -/
lemma GL.ext_schur_weylEval (e : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ))
    {M : Type*} [AddCommGroup M] [Module K M] {L L' : (WeylIndexFamily n κ → K) →ₗ[K] M}
    (h_agree : ∀ g : ∀ τ : Φ, GL (n τ) K,
      L (schur κ (fun τ : Φ ↦ (g τ).val) *ᵥ
          weylEval n κ (permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ))) =
        L' (schur κ (fun τ : Φ ↦ (g τ).val) *ᵥ
          weylEval n κ (permArray fun (τ : Φ) (i : n τ) ↦ (e τ i : ℕ)))) : L = L' := by
  -- By `ext_weylEval` it suffices to treat the vectors `weylEval n κ y` with `detPow K n 1`, the
  -- product of the determinants of the square blocks, non-zero at `y`. Such a vector is
  -- `schur κ g` applied to the frame vector, with `g = squarePart e y` invertible.
  refine ext_weylEval 1 (fun y _ hy ↦ ?_) Set.infinite_univ
  have h_unit (τ : Φ) : IsUnit (squarePart e y τ) := by
    -- After renumbering rows and columns, its determinant is the factor of `detPow` at `τ`.
    apply (isUnit_submatrix_equiv (rowEquivFin n τ).symm (e τ).symm).1
    simp_all [squarePart, detPow, minor, det_apply, isUnit_iff_isUnit_det, Finset.prod_eq_zero_iff]
  rw [← schur_squarePart_mulVec e y]
  exact h_agree fun τ ↦ (h_unit τ).unit

/-- Schur's lemma for the unitary group: a complex matrix `T` that commutes with `schur κ g` for
every tuple `g` of unitary matrices is a scalar matrix.

A form of Weyl's theorem on irreducibility of the complex Schur module: the commutant of the Schur
matrices of all tuples of unitary matrices consists of scalars. -/
lemma mem_range_scalar_of_commute_schur {T : Matrix (WeylIndexFamily n κ) (WeylIndexFamily n κ) ℂ}
    (hT : ∀ g : (τ : Φ) → Matrix (n τ) (n τ) ℂ,
      (∀ τ : Φ, (g τ)ᴴ * g τ = 1) → Commute T (schur κ g)) :
    T ∈ Set.range (scalar (WeylIndexFamily n κ)) := by
  classical
  -- The frame vector `v` spans the highest weight space, which `T` preserves, so `T v = c • v`.
  -- The translates of `v` are then eigenvectors for the same `c`, and they span the whole space.
  let v : WeylIndexFamily n κ → ℂ := weylEval n κ (permArray fun τ i ↦ (rowEquivFin n τ i : ℕ))
  -- The entries of the commutator are polynomials in `g`, and unitary tuples are Zariski dense.
  have h_comm (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
      schur κ g *ᵥ T *ᵥ v = T *ᵥ schur κ g *ᵥ v := by
    ext i
    simpa +contextual [Ring.lie_def, ↓map_mulVec, Matrix.map_sub, (hT ..).eq, comp_def,
      ← mulVec_mulVec, sub_eq_zero, sub_mulVec] using!
      zariski_dense_unitary (n := n) g ((⁅schur κ (genericMatrixAt ℂ n), T.map C⁆ *ᵥ C ∘ v) i)
  -- The diagonal tuple `D` with `2` at `(τ, a)` and `1` elsewhere scales coordinate `i` by
  -- `2 ^ tableauWeight i τ a`, and `v`, hence `T v`, by `2` to the highest weight.
  have h_weight (i : WeylIndexFamily n κ) (hi : (T *ᵥ v) i ≠ 0) (τ : Φ) (a : n τ) :
      tableauWeight i τ a = diagramWeight (rankAt n) κ (τ, rowEquivFin n τ a) := by
    let D (σ : Φ) : Matrix (n σ) (n σ) ℂ := diagonal fun b ↦ if σ = τ ∧ b ≍ a then 2 else 1
    let m : ℕ := diagramWeight (rankAt n) κ (τ, rowEquivFin n τ a)
    have hD : schur κ D *ᵥ v = (2 : ℂ) ^ m • v := toPoly_injective (by
      simp [v, D, m, rowSubst_weylKernel_permArray, ite_and, blockTriangular_diagonal])
    have h_norm : ‖(schur κ D *ᵥ T *ᵥ v) i‖ = ‖(T *ᵥ (2 : ℂ) ^ m • v) i‖ := by rw [h_comm, hD]
    simp_all [D, m, schur_diagonal, ite_and, mulVec_diagonal, mulVec_smul]
  -- As the `b_i` are independent, a linear form `φ` on polynomials has the values `(T v)_i` on
  -- them. It sees only the highest weight, so on the `b_i` it is `c` times evaluation at the frame.
  obtain ⟨L, hL⟩ : ∃ L : MatrixPoly (Σ τ : Φ, n τ) ℂ →ₗ[ℂ] WeylIndexFamily n κ → ℂ,
      L ∘ₗ nablaCombination κ = .id :=
    LinearMap.exists_leftInverse_of_injective _ (LinearMap.ker_eq_bot.2 nablaCombination_injective)
  let φ : MatrixPoly (Σ τ : Φ, n τ) ℂ →ₗ[ℂ] ℂ := dotProductBilin ℂ ℂ (T *ᵥ v) ∘ₗ L
  have hφ (i : WeylIndexFamily n κ) : φ (nablaBasis ℂ n κ i) = (T *ᵥ v) i := by
    simpa [φ] using congrArg (dotProduct (T *ᵥ v)) (LinearMap.congr_fun hL (Pi.single i 1))
  let c : ℂ := φ (weylKernel n κ (permArray fun τ i ↦ (rowEquivFin n τ i : ℕ)))
  have h_eigen : T *ᵥ v = c • v := by
    ext i
    rw [← hφ]
    exact map_nablaBasis_eq_map_weylKernel_mul_weylEval (rowEquivFin n) i φ fun hi τ a ↦
      (h_weight i (by rwa [← hφ]) τ a).ge
  have h_translate (g : ∀ τ : Φ, Matrix (n τ) (n τ) ℂ) :
      T *ᵥ schur κ g *ᵥ v = c • schur κ g *ᵥ v := by rw [← h_comm, h_eigen, mulVec_smul]
  refine ⟨c, toLin'.injective (ext_schur_weylEval (rowEquivFin n) fun g ↦ ?_)⟩
  simpa [v, ← mulVec_mulVec] using (h_translate fun τ ↦ (g τ).val).symm

end New

end SchurLemma
