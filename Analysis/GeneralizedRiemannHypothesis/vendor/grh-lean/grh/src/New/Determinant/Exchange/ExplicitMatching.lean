import Lib.GLn.SchurModule.Polarisation
import New.Determinant.Exchange.TheoremForPartners
import New.OneLift.ComparisonOperator.DeterminantProducts
import New.OneLift.ComparisonOperator.OneExchange

/-!
# Explicit real data: the exchange identity for a definite space with determinant data

`New.Rows.exists_stdClassSum_eq_mul_integral_modKernel` follows from the identity
`New.Exchange.exchange_identity` for the positive definite standard space `I_a` of rank `card a`,
with the real data made explicit as products of determinants.

Its archimedean step, `New.Rows.exists_mul_apply_eq_apply_matchedPoly`, takes an identity between
functionals on two Fock spaces that holds for one polynomial and its translates, and moves it to
explicit products of determinants.

## Main definitions and results

* `New.Rows.matchedPoly`: the explicit polynomial for the pair of signs on `b` and on `n`.
* `New.Rows.realPairWeil_stackedDetProd`, `New.Rows.realPairWeil_matchedPoly`: the laws of
  `New.Rows.stackedDetProd` and `New.Rows.matchedPoly` under the real Weil representation
  `New.realPairWeil`.
* `New.Rows.exists_mul_apply_eq_apply_matchedPoly`: the matching of `New.Rows.stackedDetProd` with
  `New.Rows.matchedPoly`.
* `New.Rows.exists_stdClassSum_eq_mul_integral_modKernel`: a multiple, possibly zero, of the class
  sum equals a non-zero multiple of the integral over the group of the complementary space.
* `New.Rows.exists_mul_stdClassSum_eq_integral_modKernel`: the same identity divided by its non-zero
  constant, with the characters absorbed into the kernels and a free character for `I_a`.

Notions from other files:
* `New.GInf`: The archimedean unitary group G_∞ for signs s: one copy of the complex unitary group
  U(diag s) for each infinite place of E.
* `New.PairFock`, `New.Fock.polyVector`, `New.realPairWeil`: the Fock space of a pair of signs, the
  vector in it attached to a polynomial, and the real Weil representation of the pair on it.
* `New.Rows.stackedDetProd`: The product over τ and k of the determinants of M_{τk} stacked over the
  variable matrix x_τ (`New.Rows.stackedDet`), columns ordered by e.
* `New.AreMatched`: Φ lives on the rows `a` of k⁻¹ and Ψ on the columns `b` of k, for k in GL_n(O),
  and there the values differ by the factor χ(det k). Here the subring O is always `⊤`.
* `New.Exchange.lValueProd`: The number (∏_{w ∈ S} Nw)^(e²) · ∏_{z=1}^{e} |L^S(z, ν)|², for a
  natural number e.

## Relation to the literature

A multiple of a theta kernel summed over a definite unitary group equals a kernel integrated over a
unitary group of no larger rank, with explicit determinant polynomials on both sides. The size of
the multiple is given by Hecke L-values and the conductor up to one fixed factor, which may be zero.
The first term identity between theta integrals of complementary spaces and the harmonic polynomials
given by determinants are known in the literature. Related work: Gan–Qiu–Takeda, The regularized
Siegel–Weil formula, 2014 (after Kudla–Rallis, 1994; Ichino, 2004); Kashiwara–Vergne, On the
Segal–Shale–Weil representations and harmonic polynomials, 1978; Böcherer–Schulze-Pillot, Siegel
modular forms and theta series attached to quaternion algebras, 1991.
-/

noncomputable section

/-!
## Archimedean step for products of determinants in Fock space

Let the pair be U(signs on `n`) × U(`a`). As seen by functionals invariant under U(`a`), a mean over
a circle in the torus removes all variables but one square block, and averaging over U(`a`)
(`New.exists_forall_eq_mul_map_det_pow`) leaves a multiple of the product of determinants for the
standard frame `(1 0)`. Polarisation passes from the unitary translates of that frame to all
matrices, since the products of determinants lie in a module that is irreducible under the unitary
group (`New.exists_pairedDetProd_eq_sum_unitary`).
-/

section RealMatching

namespace New.Rows

open NumberField Finset Matrix MvPolynomial Sum Fock Fintype Function Real ComplexOrder

variable {E n m a b p l : Type} [Field E] [NumberField E] [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] [Fintype a] [DecidableEq a] [Fintype b] [Fintype p] [DecidableEq p] [Fintype l]
  [DecidableEq l]

section Blocks

variable (f : p ⊕ l ≃ b) (j : m ⊕ l ≃ n) (e : p ⊕ a ≃ m)
  {ι : InfinitePlace E → Type} [∀ τ : InfinitePlace E, Fintype (ι τ)]

/-- The signs on `b ≃ p ⊕ l` that are `+1` on `p` and `-1` on `l`. -/
abbrev blockSigns : b → ℤˣ := (1 ⊕ᵥ -1) ∘ f.symm

/-- The embedding of the compact groups `U(m)`, one for each infinite place, as the positive block
of the unitary group of signs `blockSigns j`. -/
@[simps!]
def posBlockEmb : GInf E (1 : m → ℤˣ) →* GInf E (blockSigns j) :=
  ((U.reindex j (by simp [signMatrix])).toMonoidHom.comp (U.inl 1 (-1))).compLeft (InfinitePlace E)

omit [NumberField E] in
/-- At each place, the inverse of the image of `k` has the matrix of the image of `k⁻¹`. -/
lemma coe_inv_posBlockEmb (τ : InfinitePlace E) (k : GInf E (1 : m → ℤˣ)) :
    (((posBlockEmb j k τ)⁻¹ : U (signMatrix (blockSigns j))) : Matrix n n ℂ) =
      (posBlockEmb j k⁻¹ τ : Matrix n n ℂ) := by
  simp

omit [NumberField E] in
/-- At each place, the image of `k` lies in `blockDiagAlg (blockSigns j)`, the algebra of matrices
that commute with the diagonal matrix of the signs, that is, are block diagonal for them. -/
lemma posBlockEmb_mem_blockDiagAlg (τ : InfinitePlace E) (k : GInf E (1 : m → ℤˣ)) :
    (posBlockEmb j k τ : Matrix n n ℂ) ∈ blockDiagAlg (blockSigns j) := by
  simp [mem_blockDiagAlg, reindex_equiv j]

omit [NumberField E] in
/-- At each place `τ`, the principal minor of `posBlockEmb j k τ` on the indices `i` with
`blockSigns j i = 1` (the positive block) equals the determinant of `k τ`. -/
lemma principalMinor_posBlockEmb_eq_det (τ : InfinitePlace E) (k : GInf E (1 : m → ℤˣ)) :
    principalMinor (posBlockEmb j k τ) (fun i : n ↦ blockSigns j i = 1) =
      (k τ : Matrix m m ℂ).det := by
  simp [← principalMinor_submatrix j, principalMinor_fromBlocks, principalMinor_of_forall,
    DiscreteSeries.principalMinor_of_forall_not]

omit [NumberField E] in
/-- At each place, the negative block of the image of `k` has determinant `1`. -/
lemma principalMinor_posBlockEmb_eq_one (τ : InfinitePlace E) (k : GInf E (1 : m → ℤˣ)) :
    principalMinor (posBlockEmb j k τ) (fun i : n ↦ blockSigns j i = -1) = 1 := by
  simp [← principalMinor_submatrix j, principalMinor_fromBlocks, principalMinor_of_forall,
    DiscreteSeries.principalMinor_of_forall_not]

omit [DecidableEq p] [DecidableEq l] in
@[simp↓]
lemma card_neg_blockSigns : card {i : b // blockSigns f i = -1} = card l := by
  simp [Fintype.card_subtype, card_filter, reindex_equiv f, -sum_boole]

omit [NumberField E] in
lemma continuous_posBlockEmb : Continuous (posBlockEmb (E := E) j) := by
  simp only [continuous_pi_iff, continuous_U_iff_matrix, val_posBlockEmb_apply_coe]
  fun_prop

/-- The polynomial `∏_τ det (y⁻_τ) ^ (card (ι τ) + card n - 2 * card l) ∏_{τ, k} det (η_{τ k} y_τ)`,
where `y⁻_τ` is the `l × l` block of variables with both signs negative and `y_τ` the `m × p` block
with both signs positive. The first determinant is `variableMinor` (a minor of the matrix of
variables at `τ`) and the last product is `pairedDetProd`. The subtraction in the exponent is
truncated; it is exact when `2 * card l ≤ card n`. -/
def matchedPoly (η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ) :
    MvPolynomial (InfinitePlace E × n × b) ℂ :=
  (∏ τ : InfinitePlace E,
      variableMinor τ (j ∘ inr) (f ∘ inr) ^ (card (ι τ) + card n - 2 * card l)) *
    pairedDetProd (fun τ i k ↦ X (τ, j (inl i), f (inl k))) η

omit [DecidableEq n] [Fintype b] [DecidableEq m] in
/-- Scaling all matrices by `w` multiplies `matchedPoly` by `(w ^ card p) ^ card (ι τ)` for each
place `τ`, as each factor that depends on the matrices is a `p × p` determinant. -/
lemma matchedPoly_smul (η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ) (w : ℂ) :
    matchedPoly f j (fun (τ : InfinitePlace E) (i : ι τ) ↦ w • η τ i) =
      (∏ τ : InfinitePlace E, (w ^ Fintype.card p) ^ Fintype.card (ι τ)) • matchedPoly f j η := by
  simp [matchedPoly, pairedDetProd, Matrix.map_smul, ↓C_mul', ↓prod_smul]

/-- The Fock vector of a polynomial in the variables `a × m`. The map `renameRowsCols` reads them as
variables `a × n` through the positive block of `j`, and `polyVector` sends a polynomial to its
product with the Gaussian in the Fock space `fockSpace`. The signs of the variables are the products
`homSigns` of a row sign and a column sign, repeated at every infinite place by `realSigns`. -/
abbrev posFockVector :
    MvPolynomial (InfinitePlace E × a × m) ℂ →ₗ[ℂ]
      fockSpace (realSigns E (homSigns (blockSigns j) (1 : a → ℤˣ))) :=
  polyVector (realSigns E (homSigns (n' := a) (blockSigns j) 1)) ∘ₗ
    (renameRowsCols id (j ∘ inl)).toLinearMap

/-- For a linear form `L` on polynomials and exponents `w`, the value of `L` at `P` with each
variable `x` multiplied by `s ^ w x` is differentiable in `s`. -/
lemma differentiable_apply_bind₁_pow_smul {σ : Type} (L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (w : σ → ℕ)
    (P : MvPolynomial σ ℂ) :
    Differentiable ℂ fun s : ℂ ↦ L (P.bind₁ fun x : σ ↦ s ^ w x • X x) := by
  simp only [← aeval_eq_bind₁, aeval_def, eval₂_eq, algebraMap_eq, C_mul', smul_pow, prod_smul,
    map_sum, map_smul, smul_eq_mul]
  fun_prop

/-- Fix `j : m ⊕ l ≃ n`, with signs `blockSigns j` equal to `+1` on `m` and `-1` on `l`, and fix
`e : p ⊕ a ≃ m`. `ι τ` indexes `p × m` matrices `η τ i` at each infinite place `τ`. The polynomial
`stackedDetProd e η` is the product of the determinants of `η τ i` stacked over the `a × m` matrix
of variables, with columns ordered by `e`. `posFockVector j` turns it into a vector in the Fock
space of the pair U(`blockSigns j`) × U(`a`).

Let `γ τ = card l - card (ι τ)`, so that `realPairWeil γ 0` is the real Weil representation in which
`(x, u)` is twisted by `∏_τ (det u_τ) ^ γ τ` and not by `det x`. Let `k` be in the group `GInf E 1`,
one copy of U(`m`) for each infinite place, and let `posBlockEmb j k` be its image in the block with
signs `+1`. Then `(posBlockEmb j k, u)` carries this vector for the matrices `η * (kᵀ)⁻¹` to that
for `η`, times the factor `∏_τ (det k_τ) ^ (- card (ι τ))`, which does not depend on `u`. -/
lemma realPairWeil_stackedDetProd {γ : InfinitePlace E → ℤ}
    (hγ : γ = fun τ : InfinitePlace E ↦ (card l - card (ι τ) : ℤ))
    (η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ)
    (k : GInf E (1 : m → ℤˣ)) (u : GInf E (1 : a → ℤˣ)) :
    realPairWeil γ 0 (posBlockEmb j k, u)
        (posFockVector j (stackedDetProd e fun (τ : InfinitePlace E) (i : ι τ) ↦
          η τ i * (k τ : Matrix m m ℂ)⁻¹ᵀ)) =
      (∏ τ : InfinitePlace E, (k τ : Matrix m m ℂ).det ^ Fintype.card (ι τ))⁻¹ •
        posFockVector j (stackedDetProd e η) := by
  -- The pair acts by the substitution of `twoSidedSubst_stackedDetProd` and the vacuum character
  -- `det u ^ (γ τ - card l) = det u ^ (-card (ι τ))`, which cancels the powers of `det u`.
  have h_act (P : MvPolynomial (InfinitePlace E × a × m) ℂ) :
      realPairWeil γ 0 (posBlockEmb j k, u) (posFockVector j P) =
        (∏ τ, (u τ : Matrix a a ℂ).det ^ card (ι τ))⁻¹ • posFockVector j
          (twoSidedSubst (fun τ ↦ (u τ : Matrix a a ℂ)) (fun τ ↦ (k⁻¹ τ : Matrix m m ℂ)) P) := by
    simp [hγ, rename_eq_aeval, reindex_equiv j, principalMinor_of_forall,
      DiscreteSeries.principalMinor_of_forall_not, ↓bind₁_bind₁, ↓coe_inv_posBlockEmb,
      ↓posBlockEmb_mem_blockDiagAlg, ↓principalMinor_posBlockEmb_eq_det,
      ↓principalMinor_posBlockEmb_eq_one, ↓realPairWeil_polyVector, ↓prod_pair,
      ↓Nat.card_eq_fintype_card, ↓val_posBlockEmb_apply_coe]
  have h_inv (τ : InfinitePlace E) : (k τ : Matrix m m ℂ)⁻¹ = (k⁻¹ τ : Matrix m m ℂ) := by simp
  simp only [h_act, h_inv, twoSidedSubst_stackedDetProd, map_smul, smul_smul]
  simp [mul_pow, prod_mul_distrib, ↓prod_ne_zero_iff, GeneralLinearGroup.det_ne_zero]

/-- Let `γ τ = card l - card (ι τ)` and take the real Weil representation `realPairWeil γ 0` of the
pair of unitary groups with signs `blockSigns f`, `blockSigns j`, in which `(x, y)` is twisted by
`∏_τ (det y_τ) ^ γ τ` and not by `det x`. For `k` in U(`m`) at each place, the point
`posBlockEmb j k`, its image in the positive block of the second group, carries the Fock vector
(`polyVector`) of `matchedPoly` for `η` to that for `η * kᵀ`, times the factor
`∏_τ (det k_τ) ^ (- card (ι τ))`. -/
lemma realPairWeil_matchedPoly [DecidableEq b] {γ : InfinitePlace E → ℤ}
    (hγ : γ = fun τ : InfinitePlace E ↦ (card l - card (ι τ) : ℤ))
    (η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ) (k : GInf E (1 : m → ℤˣ)) :
    realPairWeil (s := blockSigns f) γ 0 (1, posBlockEmb j k)
        (polyVector (realSigns E (homSigns (blockSigns f) (blockSigns j))) (matchedPoly f j η)) =
      (∏ τ : InfinitePlace E, (k τ : Matrix m m ℂ).det ^ card (ι τ))⁻¹ •
        polyVector (realSigns E (homSigns (blockSigns f) (blockSigns j)))
          (matchedPoly f j fun (τ : InfinitePlace E) (i : ι τ) ↦
            η τ i * (k τ : Matrix m m ℂ)ᵀ) := by
  -- The vacuum character gives `det k ^ (γ τ - card l)`. The substitution fixes the block of
  -- variables with negative signs and multiplies the block `y` with positive signs by `kᵀ`.
  simp [hγ, Matrix.map, reindex_equiv j, ↓posBlockEmb_mem_blockDiagAlg,
    ↓principalMinor_posBlockEmb_eq_det, ↓principalMinor_posBlockEmb_eq_one,
      ↓realPairWeil_polyVector,
    ↓prod_pair, ↓Nat.card_eq_fintype_card, ↓val_posBlockEmb_apply_coe, Matrix.one_apply,
    ↓matchedPoly, ↓variableMinor, ↓pairedDetProd, ↓AlgHom.map_det, ↓prod_ne_zero_iff,
    GeneralLinearGroup.det_ne_zero]
  -- Entry by entry, `η * (kᵀ * y) = (η * kᵀ) * y`.
  congr! with τ _ i _
  refine Matrix.ext fun r s ↦ ?_
  trans ∑ x : m, ∑ x' : m, (η τ i r x * (k τ : Matrix m m ℂ) x' x) • X (τ, j (inl x'), f (inl s))
  · simp [Matrix.mul_apply, ↓C_mul', smul_sum, smul_smul]
  · rw [sum_comm]
    simp only [Matrix.mul_apply, of_apply, transpose_apply, C_mul', sum_smul]

/-- The standard frame `(1 0)` for `m ≃ p ⊕ a`: the `p × m` matrix whose row `k` is the standard
basis vector at `e (inl k)`. -/
def standardFrame : Matrix p m ℂ := (1 : Matrix m m ℂ).submatrix (e ∘ inl) id

variable (E) in
/-- For `|z| = 1`, the point of `U(m)` that is, at every infinite place, the diagonal matrix with
entries `z⁻¹ ^ 2` on `p` and `z⁻¹` on `a`, for `m ≃ p ⊕ a`. -/
def frameTorus (z : Circle) : GInf E (1 : m → ℤˣ) :=
  fun _ : InfinitePlace E ↦ diagTorus 1 fun i : m ↦ z⁻¹ ^ (if (e.symm i).isLeft then 2 else 1)

omit [NumberField E] [DecidableEq a] [DecidableEq p] in
/-- At each place, `frameTorus E e z` has determinant `z⁻¹ ^ (2 * card p + card a)`. -/
lemma det_frameTorus (z : Circle) (τ : InfinitePlace E) :
    (frameTorus E e z τ : Matrix m m ℂ).det = ((z⁻¹ : Circle) : ℂ) ^ (2 * card p + card a) := by
  simp [frameTorus, diagTorus, reindex_equiv e, pow_add, pow_mul]

omit [NumberField E] [Fintype m] in
/-- For the standard frame `(1 0)`, the stacked determinant at `τ` is the minor of the variables in
the columns `e ∘ inr`. -/
lemma stackedDet_standardFrame (τ : InfinitePlace E) :
    stackedDet τ (standardFrame e) e = variableMinor τ id (e ∘ inr) := by
  trans det (fromBlocks 1 0 (of fun i k ↦ X (τ, i, e (inl k))) (of fun i k ↦ X (τ, i, e (inr k))))
  · refine congrArg det (Matrix.ext ?_)
    rintro (i | i) (k | k) <;> simp [standardFrame, Matrix.one_apply, apply_ite C]
  · simp [variableMinor]

end Blocks

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `γ τ = card l - card (ι τ)` and let `y` lie in `PairFock`, the Fock space of the pair
U(signs on `n`) × U(`a`), on which `(x, u)` acts by the real Weil representation `realPairWeil γ 0`,
twisted by `∏_τ (det u_τ) ^ γ τ` and not by `det x`.

For `|z| = 1`, `frameTorus E e z` is the diagonal point of U(`m`) with entries `z⁻²` on `p` and
`z⁻¹` on `a`, put by `posBlockEmb j` in the positive block, and `diagTorus 1 t` is the diagonal
matrix with entries `t`. The vector `Ω z` is `y` moved by the pair of this point and the scalar
`z⁻¹` in U(`a`), times `z⁻¹ ^ (card a * ∑ τ, card (ι τ))`. There is a number `κ` such that, for
every functional `ℓ` invariant under U(`a`), the mean of `ℓ (Ω z)` over the circle is `κ` times `ℓ`
at the Fock vector (`posFockVector`) of `stackedDetProd e` for the standard frame. -/
lemma exists_mul_eq_circle_mean (j : m ⊕ l ≃ n) (e : p ⊕ a ≃ m)
    {ι : InfinitePlace E → Type} [∀ τ : InfinitePlace E, Fintype (ι τ)] {γ : InfinitePlace E → ℤ}
    (hγ : γ = fun τ : InfinitePlace E ↦ (Fintype.card l - Fintype.card (ι τ) : ℤ))
    (y : PairFock E (blockSigns j) (1 : a → ℤˣ))
    {Ω : Circle → PairFock E (blockSigns j) (1 : a → ℤˣ)}
    (hΩ : ∀ z : Circle, Ω z = (z⁻¹ : ℂ) ^ (card a * ∑ τ : InfinitePlace E, card (ι τ)) •
      realPairWeil γ 0 (posBlockEmb j (frameTorus E e z),
        fun _ : InfinitePlace E ↦ diagTorus 1 (const a z⁻¹)) y) :
    ∃ κ : ℂ, ∀ ℓ : PairFock E (blockSigns j) (1 : a → ℤˣ) →L[ℂ] ℂ,
      (∀ (u : GInf E (1 : a → ℤˣ)) (w : PairFock E (blockSigns j) (1 : a → ℤˣ)),
        ℓ (realPairWeil γ 0 (1, u) w) = ℓ w) →
      κ * ℓ (posFockVector j
          (stackedDetProd e fun (τ : InfinitePlace E) (_ : ι τ) ↦ standardFrame e)) =
        (2 * π)⁻¹ • ∫ θ : ℝ in 0..2 * π, ℓ (Ω (Circle.exp θ)) := by
  -- `orbit y` is `Ω`, with the scalar written through determinants; `mean y ℓ` is the right side.
  let η (τ : InfinitePlace E) (_ : ι τ) : Matrix p m ℂ := standardFrame e
  let orbit (y : PairFock E (blockSigns j) (1 : a → ℤˣ)) (z : Circle) :
      PairFock E (blockSigns j) 1 :=
    (∏ τ : InfinitePlace E, (diagTorus 1 (const a z⁻¹) : Matrix a a ℂ).det ^ card (ι τ)) •
      realPairWeil γ 0 (posBlockEmb j (frameTorus E e z), fun _ ↦ diagTorus 1 (const a z⁻¹)) y
  obtain rfl : Ω = orbit y := by
    funext z
    simp [hΩ, orbit, diagTorus, pow_mul, prod_pow_eq_pow_sum]
  let cols : a → n := j ∘ inl ∘ e ∘ inr
  let mean (y : PairFock E (blockSigns j) 1)
      (ℓ : {ℓ : PairFock E (blockSigns j) 1 →L[ℂ] ℂ //
        ∀ u w, ℓ (realPairWeil γ 0 (1, u) w) = ℓ w}) : ℂ :=
    (2 * π)⁻¹ • ∫ θ : ℝ in 0..2 * π, ℓ.val (orbit y (Circle.exp θ))
  suffices h_mem : mean y ∈
      Set.range fun κ : ℂ ↦ κ • fun ℓ ↦ ℓ.val (posFockVector j (stackedDetProd e η)) by
    exact h_mem.imp fun κ hκ ℓ hℓ ↦ congrFun hκ ⟨ℓ, hℓ⟩
  -- A line of functions of `ℓ` is closed and `mean` is continuous, so it is enough to treat Fock
  -- vectors of polynomials.
  have h_cont := continuous_posBlockEmb (E := E) j
  have h_cont_torus : Continuous (frameTorus E e) := by fun_prop [frameTorus]
  refine isClosed_property denseRange_polyVector
    ((isClosedMap_smul_left _).isClosed_range.preimage_of_continuous (f := mean)) (fun P ↦ ?_) y
  -- `P₀` is `P` with variables outside the columns `cols` set to zero. Averaged over U(`a`) with
  -- the weight `∏ τ, det (u τ) ^ (-card (ι τ))`, it is `κ` times `∏ τ, det ^ card (ι τ)`.
  let P₀ : MvPolynomial (InfinitePlace E × a × a) ℂ :=
    P.bind₁ fun (τ, i, k) ↦ extend cols (fun k' ↦ X (τ, i, k')) 0 k
  obtain ⟨κ, hκ⟩ := exists_forall_eq_mul_map_det_pow (fun τ ↦ card (ι τ)) P₀
  refine ⟨κ, funext fun ⟨ℓ, hℓ⟩ ↦ ?_⟩
  -- The torus scales the variables outside the columns `cols` by `z`; the result is polynomial in
  -- `z`, so its circle mean is the value `scaled 0`.
  let scaled (s : ℂ) : ℂ :=
    ℓ (polyVector _ (P.bind₁ fun (τ, i, k) ↦ s ^ extend cols 0 1 k • X (τ, i, k)))
  have h_torus (z : Circle) : ℓ (orbit (polyVector _ P) z) = scaled z := by
    simp [orbit, hγ, principalMinor_of_forall, DiscreteSeries.principalMinor_of_forall_not,
      ↓coe_inv_posBlockEmb, ↓posBlockEmb_mem_blockDiagAlg, ↓principalMinor_posBlockEmb_eq_det,
      ↓principalMinor_posBlockEmb_eq_one, ↓realPairWeil_polyVector, ↓prod_pair,
      ↓Nat.card_eq_fintype_card, ↓val_posBlockEmb_apply_coe, ↓prod_ne_zero_iff,
      GeneralLinearGroup.det_ne_zero]
    -- The scalars cancel; it remains to compare the substitutions variable by variable.
    congr
    simp [cols, frameTorus, extend, reindex_equiv j, reindex_equiv e, inv_diagonal, Ring.inverse,
      Pi.isUnit_iff, sq, ↓_root_.funext_iff, ↓diagTorus, ↓diagonal_apply, Matrix.one_apply]
  have h_diff : Differentiable ℂ scaled :=
    differentiable_apply_bind₁_pow_smul (ℓ.toLinearMap ∘ₗ polyVector _) _ P
  have mean_eq : mean (polyVector _ P) ⟨ℓ, hℓ⟩ = scaled 0 := by
    simp [mean, h_torus, ← h_diff.diffContOnCl.circleAverage (c := 0) (R := 1), circleAverage,
      circleMap]
  -- `evalCols` reads a polynomial in square matrices in the columns `cols` and applies `ℓ`. As `ℓ`
  -- is invariant, its value at the translate of `P₀` by `u` is `scaled 0` times powers of `det u`.
  let evalCols : MvPolynomial (InfinitePlace E × a × a) ℂ →ₗ[ℂ] ℂ :=
    ℓ.toLinearMap ∘ₗ polyVector _ ∘ₗ (renameRowsCols id cols).toLinearMap
  have h_average : scaled 0 = κ * evalCols (∏ τ, variableMinor τ id id ^ card (ι τ)) := by
    refine hκ evalCols (scaled 0) fun u ↦ ?_
    unfold scaled
    rw [← hℓ u]
    have h_det : ∏ τ, (u τ : Matrix a a ℂ).det ^ card (ι τ) ≠ 0 :=
      prod_ne_zero_iff.2 fun τ _ ↦ pow_ne_zero _ (GeneralLinearGroup.det_ne_zero _)
    simp [hγ, field, rename_eq_aeval, evalCols, P₀, principalMinor_of_forall,
      DiscreteSeries.principalMinor_of_forall_not, ↓bind₁_bind₁, ↓realPairWeil_polyVector,
      ↓prod_pair, ↓Nat.card_eq_fintype_card, Matrix.one_apply]
    -- Both substitutions keep the columns `cols`, mixed by `u`, and kill the other variables.
    congr
    simp [reindex_equiv j, reindex_equiv e, cols, extend, ↓_root_.funext_iff]
  -- For the standard frame, `det (η; x)` is the minor of `x` in the columns `e ∘ inr`.
  simpa [mean_eq, η, stackedDet_standardFrame, stackedDetProd, det_apply', evalCols, cols,
    ↓variableMinor] using h_average.symm

omit [NumberField E] in
/-- At each point `x` there are an `m × p` matrix `Y` and a number `d` with
`det (ξ; x τ) = d * det (ξ * Y)` for all `p × m` matrices `ξ`; here `ξ` is stacked over `x τ`, with
columns ordered by `e`. -/
lemma exists_eval_stackedDet_eq (e : p ⊕ a ≃ m) (τ : InfinitePlace E)
    (x : InfinitePlace E × a × m → ℂ) :
    ∃ (Y : m → p → ℂ) (d : ℂ), ∀ ξ : Matrix p m ℂ,
      (stackedDet τ ξ e).eval x = d * (ξ * of Y).det := by
  obtain ⟨Z, d, hZ⟩ := exists_det_fromCols_eq_mul_det e.symm fun i k ↦ x (τ, k, i)
  refine ⟨of.symm Zᵀ, d, fun ξ ↦ ?_⟩
  have h_eval : (stackedDet τ ξ e).eval x =
      ((ξ.fromRows (of fun i k ↦ x (τ, i, k))).submatrix id e).det := by
    rw [stackedDet, RingHom.map_det]
    congr 1
    ext (i | i) k <;> simp
  rw [h_eval, Equiv.apply_symm_apply, ← transpose_transpose ξ, ← transpose_mul, ← hZ ξᵀ,
    ← det_transpose, ← det_submatrix_equiv_self e]
  simp [det_apply', fromCols]

omit [DecidableEq n] [Fintype b] in
/-- Let `a` be non-empty and fix `f : p ⊕ l ≃ b`, `j : m ⊕ l ≃ n`, `e : p ⊕ a ≃ m`. For `p × m`
matrices `ξ τ i`, indexed by `ι τ` at each infinite place `τ`, `stackedDetProd e ξ` is the product
of the determinants of `ξ τ i` stacked over an `a × m` matrix of variables, and `matchedPoly f j ξ`
the product of the `det (ξ τ i * y_τ)`, with `y_τ` an `m × p` block of variables, and a fixed
polynomial. Both are finite combinations, with the same coefficients, of the same polynomials for
the unitary translates `frame k τ i = standardFrame e * (k τ)ᵀ` of `standardFrame e`, the `p × m`
matrix `(1 0)`, with `k τ` in U(`m`). -/
lemma exists_stackedDetProd_eq_sum_unitary (f : p ⊕ l ≃ b) (j : m ⊕ l ≃ n) (e : p ⊕ a ≃ m)
    {ι : InfinitePlace E → Type} [∀ τ : InfinitePlace E, Fintype (ι τ)] [Nonempty a]
    (ξ : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ) :
    let frame (k : GInf E (1 : m → ℤˣ)) (τ : InfinitePlace E) (_ : ι τ) : Matrix p m ℂ :=
      standardFrame e * (k τ : Matrix m m ℂ)ᵀ
    ∃ c : GInf E (1 : m → ℤˣ) →₀ ℂ,
      (stackedDetProd e ξ =
        c.sum fun (k : GInf E (1 : m → ℤˣ)) (z : ℂ) ↦ z • stackedDetProd e (frame k)) ∧
      matchedPoly f j ξ =
        c.sum fun (k : GInf E (1 : m → ℤˣ)) (z : ℂ) ↦ z • matchedPoly f j (frame k) := by
  -- By irreducibility, `∏ det (ξ τ i * Y τ)` is such a combination, the same for all `Y`.
  intro frame
  have h_card : card p < card m := by simp [← card_congr e, Fintype.card_pos]
  obtain ⟨c, hc⟩ : ∃ c : GInf E (1 : m → ℤˣ) →₀ ℂ,
      ∀ (S : Type) [CommRing S] [Algebra ℂ S] (Y : InfinitePlace E → m → p → S),
        pairedDetProd Y ξ = c.sum fun k z ↦ z • pairedDetProd Y (frame k) :=
    exists_pairedDetProd_eq_sum_unitary h_card (e.injective.comp inl_injective) ξ
  refine ⟨c, MvPolynomial.funext fun x ↦ ?_, ?_⟩
  · -- At the point `x`, `stackedDetProd e` is a fixed multiple of the product for complex `Y τ`.
    have h_point (τ : InfinitePlace E) : ∃ (Y : m → p → ℂ) (d : ℂ), ∀ ζ : Matrix p m ℂ,
        (stackedDet τ ζ e).eval x = d * (ζ * of Y).det := exists_eval_stackedDet_eq e τ x
    choose Y d hY using h_point
    have h_eval (ζ : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ) :
        (stackedDetProd e ζ).eval x =
          (∏ τ : InfinitePlace E, d τ ^ card (ι τ)) * pairedDetProd Y ζ := by
      simp [stackedDetProd, pairedDetProd, hY, prod_mul_distrib]
    simp [h_eval, hc ℂ Y, Finsupp.sum, mul_sum, mul_left_comm]
  · -- `matchedPoly f j` is a fixed polynomial times the product for the matrices of variables.
    simp only [matchedPoly, hc, Finsupp.mul_sum, mul_smul_comm]

/-- Let `a` be non-empty, fix `f : p ⊕ l ≃ b`, `j : m ⊕ l ≃ n`, which give signs `+1` on `p`, `m`
and `-1` on `l` (`blockSigns`), and `e : p ⊕ a ≃ m`, and let `γ τ = card l - card (ι τ)`.

There is a polynomial `Q₀` such that every vector `v` has a number `κ` with the following property.
Let `ℓ g` be continuous functionals and `ℓ'` a linear form on polynomials such that (a)
`ℓ g (realPairWeil γ 0 (x₁, x₂) w) = ℓ (g x₁) w`; (b) `ℓ x v = ℓ' Q` whenever `x` carries the Fock
vector of `Q₀` to that of a polynomial `Q`. Then `κ * ℓ 1` at the Fock vector of
`stackedDetProd e η` is `ℓ' (matchedPoly f j η)` for all matrices `η`. -/
lemma exists_mul_apply_eq_apply_matchedPoly (f : p ⊕ l ≃ b) (j : m ⊕ l ≃ n) (e : p ⊕ a ≃ m)
    {ι : InfinitePlace E → Type} [∀ τ : InfinitePlace E, Fintype (ι τ)] {γ : InfinitePlace E → ℤ}
    (hγ : γ = fun τ : InfinitePlace E ↦ (Fintype.card l - Fintype.card (ι τ) : ℤ))
    [DecidableEq b] [Nonempty a] :
    ∃ Q₀ : MvPolynomial (InfinitePlace E × n × b) ℂ, ∀ v : PairFock E (blockSigns j) (1 : a → ℤˣ),
      ∃ κ : ℂ,
      ∀ (ℓ : GInf E (blockSigns j) → PairFock E (blockSigns j) (1 : a → ℤˣ) →L[ℂ] ℂ)
        (ℓ' : MvPolynomial (InfinitePlace E × n × b) ℂ →ₗ[ℂ] ℂ),
      -- (a) `ℓ` is equivariant under the first group and invariant under the second
      (∀ (g : GInf E (blockSigns j)) (x : GInf E (blockSigns j) × GInf E (1 : a → ℤˣ))
          (w : PairFock E (blockSigns j) 1),
        ℓ g (realPairWeil γ 0 x w) = ℓ (g * x.1) w) →
      -- (b) `ℓ` at `v` matches `ℓ'` on the polynomial translates of `Q₀`
      (∀ (x : GInf E (blockSigns j)) (Q : MvPolynomial (InfinitePlace E × n × b) ℂ),
        realPairWeil (s := blockSigns f) γ 0 (1, x)
            (polyVector (realSigns E (homSigns (blockSigns f) (blockSigns j))) Q₀) =
          polyVector (realSigns E (homSigns (blockSigns f) (blockSigns j))) Q →
        ℓ x v = ℓ' Q) →
      ∀ η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ,
        κ * ℓ 1 (posFockVector j (stackedDetProd e η)) = ℓ' (matchedPoly (ι := ι) f j η) := by
  -- Take `Q₀ = matchedPoly η` for the standard frame `η`. On functionals invariant under the second
  -- group, the circle mean of `Ω v` is a multiple `κ` of the value at `stackedDetProd η`. This
  -- gives the identity for the unitary translates of `η`, and polarisation
  -- (`exists_stackedDetProd_eq_sum_unitary`) extends it to all matrices.
  let η (τ : InfinitePlace E) (_ : ι τ) : Matrix p m ℂ := standardFrame e
  let t : Circle → GInf E (1 : m → ℤˣ) := frameTorus E e
  let Ω (y : PairFock E (blockSigns j) (1 : a → ℤˣ)) (z : Circle) : PairFock E (blockSigns j) 1 :=
    (z⁻¹ : ℂ) ^ (card a * ∑ τ, card (ι τ)) •
      realPairWeil γ 0 (posBlockEmb j (t z), fun _ ↦ diagTorus 1 (const a z⁻¹)) y
  let c (τ : InfinitePlace E) : ℕ := card (ι τ)
  refine ⟨matchedPoly f j η, fun v ↦
    (exists_mul_eq_circle_mean j e hγ v (Ω := Ω v) fun _ ↦ rfl).imp
      fun κ hκ ℓ ℓ' hℓ h_match ↦ ?_⟩
  -- The identity for the translate of `η` by a unitary `k`.
  have h_unitary (k : GInf E (1 : m → ℤˣ)) :
      let ξ (τ : InfinitePlace E) (i : ι τ) : Matrix p m ℂ := η τ i * (k τ : Matrix m m ℂ)ᵀ
      κ * ℓ 1 (posFockVector j (stackedDetProd e ξ)) = ℓ' (matchedPoly f j ξ) := by
    intro ξ
    -- By `realPairWeil_matchedPoly`, `posBlockEmb j (k * t z)` carries `matchedPoly η` to a
    -- multiple of `matchedPoly (z⁻¹ ^ 2 • ξ)`, so `h_match` applies.
    have h_frame (z : Circle) (τ : InfinitePlace E) (i : ι τ) :
        η τ i * ((k * t z) τ : Matrix m m ℂ)ᵀ = (z⁻¹ : Circle).val ^ 2 • ξ τ i := by
      simp [η, ξ, ← ext_iff, Matrix.mul_apply, t, standardFrame, frameTorus, mul_comm, ↓diagTorus,
        Matrix.one_apply, ↓diagonal_apply]
    have h_transl (z : Circle) : ℓ (posBlockEmb j (k * t z)) v =
        ℓ' ((∏ τ, ((k * t z) τ : Matrix m m ℂ).det ^ c τ)⁻¹ •
          matchedPoly f j fun τ i ↦ (z⁻¹ : Circle).val ^ 2 • ξ τ i) := by
      exact h_match _ _ (by simp only [realPairWeil_matchedPoly f j hγ, h_frame, map_smul, c])
    calc
      _ = κ * ((∏ τ, (k τ : Matrix m m ℂ).det ^ c τ) • ℓ (posBlockEmb j k))
            (posFockVector j (stackedDetProd e η)) := by
        simpa [hℓ, c] using congrArg (fun w ↦ κ * ℓ (posBlockEmb j k) w)
          (realPairWeil_stackedDetProd j e hγ η k⁻¹ 1)
      _ = (2 * π)⁻¹ • ∫ θ in 0..2 * π,
            ((∏ τ, (k τ : Matrix m m ℂ).det ^ c τ) • ℓ (posBlockEmb j k)) (Ω v (.exp θ)) :=
        hκ _ (by simp [hℓ])
      _ = ℓ' (matchedPoly f j ξ) := by
        -- The integrand is constant: the powers of `z` and of `det k` cancel.
        have h_integrand (z : Circle) :
            ((∏ τ, (k τ : Matrix m m ℂ).det ^ c τ) • ℓ (posBlockEmb j k)) (Ω v z) =
              ℓ' (matchedPoly f j ξ) := by
          simp [Ω, hℓ, h_transl, matchedPoly_smul, t, det_frameTorus, c, pow_mul,
            ← prod_pow_eq_pow_sum, ← map_mul, mul_pow, prod_mul_distrib]
          -- What is left is an equation between powers of `z` and of `det k τ ≠ 0`.
          field_simp [↓prod_ne_zero_iff, GeneralLinearGroup.det_ne_zero]
          simp [pow_add, ← pow_mul, mul_pow, prod_mul_distrib, mul_comm, mul_left_comm, mul_assoc]
        simp [field, h_integrand]
  -- Both sides are linear in the polynomials, so the identity passes to combinations.
  intro ξ
  obtain ⟨w, h_stacked, h_matched⟩ := exists_stackedDetProd_eq_sum_unitary f j e ξ
  simp only [h_stacked, h_matched, map_finsuppSum, map_smul, Finsupp.mul_sum, mul_smul_comm]
  exact Finsupp.sum_congr fun k _ ↦ congrArg (w k • ·) (h_unitary k)

end New.Rows

end RealMatching

section ExplicitMatching

open MeasureTheory New WeilData Exchange Fock Fintype Space NumberField

namespace New.Rows

variable {E : Type} [Field E] [CMType E] [WeilData E] {n m a b p l : Type}
  [Fintype n] [DecidableEq n] [Fintype m] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype p] [DecidableEq p] [Fintype l] [DecidableEq l]

/-- Let `I_a` be the positive definite standard space `stdSpace E a` and let `Φ` be a function on
matrices modulo `𝔪`. The theta integral over `U(I_a)` with characters `α`, `β`, at a point `g` of
`U(S)`, is a continuous linear functional of the real part `w` of the datum `modDatum`, whose finite
part is given by `Φ`. -/
lemma exists_clm_eq_thetaIntegral_modDatum {s : n → ℤˣ} (S : Space E n s) (α β : AutChar E)
    {𝔪 : Modulus E} (Φ : Matrix a n 𝔪.ResidueRing → ℂ) :
    ∃ L : G E s → PairFock E s (1 : a → ℤˣ) →L[ℂ] ℂ,
      ∀ (g : G E s) (w : PairFock E s (1 : a → ℤˣ)),
        L g w = thetaIntegral S (stdSpace E a) α β (modDatum S (stdSpace E a) 𝔪 Φ w) g := by
  -- The theta integral is the lift of the constant function `1`, which is of rapid decay on a
  -- definite group; the datum is `w` tensored with a fixed finite part `φ`.
  have h_one : (fun _ : G E (1 : a → ℤˣ) ↦ (1 : ℂ)) ∈ (stdSpace E a).rapidFunctions :=
    (isAutomorphic_const _ 1).mem_rapidFunctions fun _ _ ↦ rfl
  obtain ⟨L, hL⟩ : ∃ L : G E s → 𝒮 (S.hom (stdSpace E a)) →L[ℂ] ℂ, ∀ f g,
      lift (pairThetaKer S (stdSpace E a) α β).swap f (fun _ ↦ (1 : ℂ)) g = L g f :=
    (pairThetaKer S (stdSpace E a) α β).swap.exists_clm_lift h_one
  let φ : 𝒮 (S.hom (stdSpace E a)) :=
    schrodingerOp (S.hom (stdSpace E a)) 𝔪.places (𝔪.liftFn (Φ ∘ vecToMatrix)) (vacElem _)
  refine ⟨fun g ↦ L g ∘L (integrated (S.hom (stdSpace E a))).flip φ, fun g w ↦ ?_⟩
  show L g (integrated _ w φ) = thetaIntegral S (stdSpace E a) α β (integrated _ w φ) g
  simp [← hL, lift, thetaIntegral, pairTheta]

omit [Fintype a] [DecidableEq a] in
/-- Let `𝔪` not be the unit ideal, and let `Φ`, `Ψ` be matched functions for `χ` (`AreMatched`). Fix
`g` in `G E t`. Integrate over the quotient of `G E s` by the rational points of `S`
(`quotMeasure`). The integrand is the theta kernel `modKernel` of `(S, T)` at `(x, g)`, twisted by
`α`, `β`, with data `Ψ`, `Q`. The integral is a linear form `ℓ` in the polynomial `Q`. -/
lemma exists_linearMap_eq_integral_modKernel {s : b → ℤˣ} {t : n → ℤˣ} (S : Space E b s)
    (T : Space E n t) (α β : AutChar E) {𝔪 : Modulus E} (h𝔪 : Nonempty 𝔪.places) {σ : b ⊕ a ≃ n}
    {χ : MulChar 𝔪.ResidueRing ℂ} {Φ : Matrix a n 𝔪.ResidueRing → ℂ}
    {Ψ : Matrix n b 𝔪.ResidueRing → ℂ} (h_matched : AreMatched ⊤ σ χ Φ Ψ) (g : G E t) :
    ∃ ℓ : MvPolynomial (InfinitePlace E × n × b) ℂ →ₗ[ℂ] ℂ,
      ∀ Q : MvPolynomial (InfinitePlace E × n × b) ℂ,
        ℓ Q = ∫ x : G E s, modKernel S T α β 𝔪 Ψ Q x g ∂S.quotMeasure := by
  -- `Ψ` lives on left invertible matrices, so the kernels are rapidly decreasing, hence integrable.
  have hΨ (y : Matrix n b 𝔪.ResidueRing) (hy : Ψ y ≠ 0) : HasLeftInv y := by
    obtain ⟨k, -, rfl⟩ := h_matched.supp_right y hy -- `y` is the matrix of first columns of `k`
    exact ⟨invFirstRows σ k, invFirstRows_mul_firstCols σ k⟩
  have h_int (Q : MvPolynomial (InfinitePlace E × n × b) ℂ) :
      Integrable (fun x : G E s ↦ modKernelBilin S T α β 𝔪 x g Ψ Q) S.quotMeasure :=
    (isRapid_modKernel S T α β h𝔪 hΨ Q g).integrable (by fun_prop [modKernel])
  exact ⟨{ toFun Q := ∫ x : G E s, modKernelBilin S T α β 𝔪 x g Ψ Q ∂S.quotMeasure
           map_add' Q Q' := by simp only [map_add, integral_add (h_int Q) (h_int Q')]
           map_smul' c Q := by simp [integral_const_mul] },
    fun Q ↦ rfl⟩ -- by definition of `modKernelBilin`

/-- Let `W` have `card l` negative signs and let `I_a` be the positive definite standard space
`stdSpace E a`. Let the character `α` be tame for `(𝔪, χ)` of weight `card l - card (ι τ)`. Let `Φ`
have a matched function `Ψ` for `χ⁻¹` (`AreMatched`): for invertible `k` modulo `𝔪` they vanish off
the rows `a` of `k⁻¹` and the columns `b` of `k` respectively, with `Φ = χ⁻¹ (det k) Ψ` there. Take
the theta kernel `modKernel` of `(W, I_a)` with the characters `α`, `1` and the data `Φ`,
`stackedDetProd e η`; `modKernelStdSpace` is its restriction to the finite points `h` of `U(I_a)`.
The integral of the kernel over `U(I_a)` is the class sum of this restriction: the sum of its values
over the double cosets of the rational points and of the integral finite points `stdLevel E a`, each
divided by the number of automorphisms of the class. -/
lemma integral_modKernel_stackedDetProd (j : m ⊕ l ≃ n) (W : Space E n (blockSigns j))
    (σ : b ⊕ a ≃ n) (e : p ⊕ a ≃ m)
    {ι : InfinitePlace E → Type} [∀ τ : InfinitePlace E, Fintype (ι τ)]
    {𝔪 : Modulus E} {α : AutChar E} {χ : MulChar 𝔪.ResidueRing ℂ}
    (h_tame : IsTameFor 𝔪 α (fun τ : InfinitePlace E ↦ card l - card (ι τ)) χ)
    (η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ)
    {Φ : Matrix a n 𝔪.ResidueRing → ℂ} {Ψ : Matrix n b 𝔪.ResidueRing → ℂ}
    (h_matched : AreMatched ⊤ σ χ⁻¹ Φ Ψ) (g : G E (blockSigns j)) :
    ∫ h : G E (1 : a → ℤˣ), modKernel W (stdSpace E a) α 1 𝔪 Φ
        (renameRowsCols id (j ∘ Sum.inl) (stackedDetProd e η)) g h ∂(stdSpace E a).quotMeasure =
      stdClassSum (stdLevel E a) fun h : Gf E a ↦
        modKernelStdSpace W α 1 𝔪 Φ (renameRowsCols id (j ∘ Sum.inl) (stackedDetProd e η)) g h := by
  classical
  set Q : MvPolynomial (InfinitePlace E × a × n) ℂ :=
    renameRowsCols id (j ∘ Sum.inl) (stackedDetProd e η)
  set K : G E (1 : a → ℤˣ) → ℂ := modKernel W (stdSpace E a) α 1 𝔪 Φ Q g with hK
  -- The kernel is invariant under right translation by the real points and by `stdLevel E a`, so
  -- its integral is a class sum. `h_weight` is the instance that `pairWeil_integrated_right` reads.
  obtain ⟨ψ, (h_weight : α.HasWeight _ ψ), -⟩ := h_tame.2
  -- The kernel does not depend on the real part of `h`, since `U(I_a)(ℝ)` fixes the vector of `Q`.
  have h_real (u : GInf E (1 : a → ℤˣ)) (h : Gf E a) : K (u, h) = K (1, h) := by
    have h_fixed : realPairWeil (s := blockSigns j)
        (fun τ : InfinitePlace E ↦ (card l - card (ι τ) : ℤ)) 0 (1, u) (polyVector _ Q) =
        polyVector _ Q := by
      simpa using realPairWeil_stackedDetProd j e rfl η 1 u
    simp only [hK, modKernel, modDatum]
    conv_rhs => rw [← h_fixed, ← pairWeil_integrated_right α, ← pairTheta_mul]
    simp
  -- Translation by `k` in `stdLevel E a` replaces `Φ` by `α (det k) Φ (k⁻¹ ·)`, which is `Φ` since
  -- `α (det k) = χ (det k)` and `Φ (k⁻¹ y) = χ (det k)⁻¹ Φ y`.
  have h_level : stdLevel E a ≤ rightStabilizer fun h : Gf E a ↦ K (1, h) := by
    intro k hk h
    have h_datum : ((α.val (detFin (1 : a → ℤˣ) k) : ℂ) •
        fun y : Matrix a n 𝔪.ResidueRing ↦ Φ ((𝔪.reductionGL ⟨k, hk⟩)⁻¹.val * y)) = Φ :=
          funext fun y ↦
      by simpa [h_tame.apply_det ⟨k, hk⟩, χ.inv_apply, Ring.inverse_inverse] using
        h_matched.left_mul (g := (𝔪.reductionGL ⟨k, hk⟩)⁻¹) (x := y) (by simp [mem_intGL])
    simp only [hK, modKernel_mul_stdLevel_right W (stdSpace E a) α 1 𝔪 ⟨k, hk⟩ Φ Q g 1 h, h_datum]
  have h_left : (stdSpace E a).Γ.FixesLeft K := (pairThetaKer W _ α 1).swap.theta_rat_mul
  rw [integral_quotMeasure_eq_classSum h_left (fun h ↦ integral_eq_const (.of_forall (h_real · h)))
    (stdLevel E a) h_level (by fun_prop [modKernel])]
  simp [hK]

/-- Let `W` and `V'` both have `card l` negative signs (`j` and `f` split their bases by sign), let
`I_a` be the positive definite standard space `stdSpace E a` with `a` non-empty, and let `σ` give
`n = b ⊕ a`; `e` orders the columns of the determinants, of which `ι τ` indexes those at the place
`τ`. There is a polynomial `Q₀` such that every real datum `v`, a vector in the Fock space
`PairFock` of `(W, I_a)`, has a number `c'` with the following property. Let the character `α` be
tame for `(𝔪, χ)` of weight `card l - card (ι τ)`, let `Φ`, `Ψ` be matched functions for `χ⁻¹`, and
suppose that at every point the theta integral over `U(I_a)` with datum `Φ`, `v` is `c` times the
integral over `U(V')` of the kernel with data `Ψ`, `Q₀`. Then `c'` times the class sum for `Φ`,
`stackedDetProd e η` is `c` times the integral for `Ψ`, `matchedPoly f j η`. Here
`stackedDetProd e η` is the product of the determinants of the `p × m` matrices `η τ i` stacked over
the variables `a × m`, and `matchedPoly f j η` the product of the `det (η τ i * y_τ)`, with `y_τ`
the block of `n × b` variables with both signs `+1`, and of powers of the determinants of the blocks
with both signs `-1`. The class sum `stdClassSum` runs over the double cosets of the finite points
of `U(I_a)` by the rational points and the integral points `stdLevel E a`, each weighted by the
inverse of its number of automorphisms. -/
lemma exists_stdClassSum_eq_of_exchange (f : p ⊕ l ≃ b) (V' : Space E b (blockSigns f))
    (σ : b ⊕ a ≃ n) (e : p ⊕ a ≃ m) (j : m ⊕ l ≃ n) (W : Space E n (blockSigns j))
    (ι : InfinitePlace E → Type) [∀ τ : InfinitePlace E, Fintype (ι τ)] [Nonempty a] :
    ∃ Q₀ : MvPolynomial (InfinitePlace E × n × b) ℂ,
      ∀ v : PairFock E (blockSigns j) (1 : a → ℤˣ), ∃ c' : ℂ,
      ∀ {𝔪 : Modulus E} {α : AutChar E} {χ : MulChar 𝔪.ResidueRing ℂ},
      IsTameFor 𝔪 α (fun τ : InfinitePlace E ↦ card l - card (ι τ)) χ →
      ∀ {Φ : Matrix a n 𝔪.ResidueRing → ℂ} {Ψ : Matrix n b 𝔪.ResidueRing → ℂ},
        AreMatched ⊤ σ χ⁻¹ Φ Ψ →
      ∀ c : ℂ,
        (∀ y : G E (blockSigns j),
          thetaIntegral W (stdSpace E a) α 1 (modDatum W (stdSpace E a) 𝔪 Φ v) y =
            c * ∫ x : G E (blockSigns f), modKernel V' W α α 𝔪 Ψ Q₀ x y ∂V'.quotMeasure) →
        ∀ (η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ) (g : G E (blockSigns j)),
          c' * stdClassSum (stdLevel E a) (fun h : Gf E a ↦
              modKernelStdSpace W α 1 𝔪 Φ (renameRowsCols id (j ∘ Sum.inl) (stackedDetProd e η)) g
                h) =
            c * ∫ x : G E (blockSigns f),
              modKernel V' W α α 𝔪 Ψ (matchedPoly f j η) x g ∂V'.quotMeasure := by
  -- Both sides of the hypothesis are functionals of the real datum, so
  -- `exists_mul_apply_eq_apply_matchedPoly` moves it from `v`, `Q₀` to the products of
  -- determinants. The integral over `U(I_a)` is then a class sum.
  classical
  obtain ⟨Q₀, h_match_real⟩ := exists_mul_apply_eq_apply_matchedPoly f j e (ι := ι) rfl
  refine ⟨Q₀, fun v ↦ (h_match_real v).imp fun c' hc' ↦ ?_⟩
  intro 𝔪 α χ h_tame Φ Ψ h_matched c h_exchange η g
  -- The two functionals: `L (g * (y, 1))` of the real datum on the left and `ℓ'` of the polynomial
  -- on the right. `h_weight` is the instance that `pairWeil_integrated` reads.
  obtain ⟨ψ, (h_weight : α.HasWeight _ ψ), -⟩ := h_tame.2
  obtain ⟨L, hL⟩ := exists_clm_eq_thetaIntegral_modDatum (a := a) W α 1 Φ
  obtain ⟨ℓ', hℓ'⟩ := exists_linearMap_eq_integral_modKernel V' W α α h_tame.1 h_matched g
  have h_equivariant (y : GInf E (blockSigns j))
      (z : GInf E (blockSigns j) × GInf E (1 : a → ℤˣ)) (w : PairFock E (blockSigns j) 1) :
      L (g * (y, 1)) (realPairWeil (fun τ ↦ card l - card (ι τ)) 0 z w) =
        L (g * (y * z.1, 1)) w := by
    simp [hL, modDatum, ← pairWeil_integrated W (stdSpace E a) α 1, thetaIntegral_pairWeil,
      mul_assoc]
  have h_match : c' * L (g * (1, 1)) (posFockVector j (stackedDetProd e η)) =
      (c • ℓ') (matchedPoly f j η) := by
    refine hc' (fun y ↦ L (g * (y, 1))) (c • ℓ') h_equivariant (fun y Q hQ ↦ ?_) η
    -- If `y` carries `Q₀` to `Q`, this is the hypothesis at `g * (y, 1)`.
    have h_translate (x : G E (blockSigns f)) :
        modKernel V' W α α 𝔪 Ψ Q₀ x (g * (y, 1)) = modKernel V' W α α 𝔪 Ψ Q x g := by
      simp [modKernel, modDatum, ← hQ, ← pairWeil_integrated_right α α, ← pairTheta_mul]
    show L (g * (y, 1)) v = c * ℓ' Q
    rw [hL, h_exchange, hℓ']
    simp only [h_translate]
  rw [← integral_modKernel_stackedDetProd j W σ e h_tame η h_matched g, ← hℓ']
  rw [hL, Prod.mk_one_one, mul_one] at h_match
  exact h_match

/-- Explicit exchange of theta kernels. Index types stand for their cardinalities. Let `W` of rank
`n` and `V'` of rank `b` both have `l` negative signs (`j : m ⊕ l ≃ n` and `f : p ⊕ l ≃ b` split
their bases by sign), let `I_a` be the positive definite standard space, and let `n = b + a` (by
`σ`), `a = b + 2 d` and `n = 2 l + 2 s₀` with `s₀ ≥ 1`; `e : p ⊕ a ≃ m` orders the columns of the
determinants, of which `ι τ` indexes those at the place `τ`. The kernels carry the standard
characters: `υ ^ l` for `W` and `V'`, and `1` for `I_a`, where `υ` is `upsilonU1`, the character of
the Weil data on `U(1)`.

There are numbers `C > 0` and `c'`, possibly `c' = 0`, such that every character `α` of weight
`-card (ι τ)` that is tamely ramified exactly at the places of `𝔪 ≠ 1`, with character `χ` of the
residue ring, has a number `c` with (a) and (b). (a) `‖c‖² = C * lValueProd 𝔪.places ν⁻¹ d ≠ 0` for
`ν = α / υ ^ s₀`. Here `lValueProd 𝔪.places μ d`, for a character `μ`, is the norm factor
`(∏_{w ∣ 𝔪} Nw) ^ (d ^ 2)` times `∏_{1 ≤ z ≤ d} |L^S(z, μ)| ^ 2`, where `L^S(z, μ)` is the Euler
product at `z` of the base change of `μ` outside the places `S` of `𝔪` and their conjugates.
(b) For all matrices `η`, all `g` and all matched functions `Φ`, `Ψ` for `χ⁻¹` (`AreMatched`: for
invertible `k` modulo `𝔪` they vanish off the rows `a` of `k⁻¹` and the columns `b` of `k`
respectively, with `Φ = χ⁻¹ (det k) Ψ` there), the number `c'` times the class sum at the level
`stdLevel E a` over finite points `h` of `U(I_a)` of `α (det h)` times the kernel of `(W, I_a)` with
data `Φ`, `stackedDetProd e η` (read in the variables `a × n` through `j`) equals `c α (det g)`
times the integral over `x` in `U(V')` of `α (det x)⁻¹` times the kernel of `(V', W)` with data `Ψ`,
`matchedPoly f j η`. The first polynomial is the product of the determinants of `η τ k` stacked over
the `a × m` matrix of variables; the second is the product of the `det (η τ k * y_τ)`, for `y_τ` the
`m × p` block of variables with positive signs, and of powers of the determinants of the `l × l`
blocks with negative signs. -/
theorem exists_stdClassSum_eq_mul_integral_modKernel (j : m ⊕ l ≃ n) (W : Space E n (blockSigns j))
    (f : p ⊕ l ≃ b) (V' : Space E b (blockSigns f)) (σ : b ⊕ a ≃ n) (e : p ⊕ a ≃ m)
    {d s₀ : ℕ} (hd : card a = card b + 2 * d)
    (hs₀ : card n = 2 * card l + 2 * s₀) (hs₀_pos : 1 ≤ s₀)
    (ι : InfinitePlace E → Type) [∀ τ : InfinitePlace E, Fintype (ι τ)] :
    ∃ C : ℝ, 0 < C ∧ ∃ c' : ℂ,
      ∀ {𝔪 : Modulus E} {α : AutChar E} {χ : MulChar 𝔪.ResidueRing ℂ},
      IsTameFor 𝔪 α (fun τ : InfinitePlace E ↦ -card (ι τ)) χ →
      ∃ c : ℂ,
        -- (a) the size of `c`
        ‖c‖ ^ 2 = C * lValueProd 𝔪.places (α / upsilonU1 ^ s₀)⁻¹ d ∧
        C * lValueProd 𝔪.places (α / upsilonU1 ^ s₀)⁻¹ d ≠ 0 ∧
        -- (b) the class sum for `I_a` against the integral over the group of `V'`
        ∀ (η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ) (g : G E (blockSigns j))
          (Φ : Matrix a n 𝔪.ResidueRing → ℂ) (Ψ : Matrix n b 𝔪.ResidueRing → ℂ),
            AreMatched ⊤ σ χ⁻¹ Φ Ψ →
          c' * stdClassSum (stdLevel E a) (fun h : Gf E a ↦
              α.val (detFin (1 : a → ℤˣ) h) *
                modKernelStdSpace W (upsilonU1 ^ card l) 1 𝔪 Φ
                  (renameRowsCols id (j ∘ Sum.inl) (stackedDetProd e η)) g h) =
            c * α.val g.det *
              ∫ x : G E (blockSigns f),
                (α.val x.det : ℂ)⁻¹ *
                  modKernel V' W (upsilonU1 ^ card l) (upsilonU1 ^ card l) 𝔪 Ψ
                    (matchedPoly f j η) x g ∂V'.quotMeasure := by
  -- The exchange identity for the polynomial `Q₀` of `exists_stdClassSum_eq_of_exchange` gives `C`,
  -- a real datum `v` and `c`. That lemma moves it from `v`, `Q₀` to the products of determinants,
  -- at the cost of the factor `c'`.
  classical
  have h_card : card n = card b + card a := by rw [← card_congr σ, card_sum]
  have h_neg : negCount (blockSigns j) = card l := by simp [negCount]
  have h_nonempty : Nonempty a := card_pos_iff.1 (by omega)
  obtain ⟨Q₀, h_transfer⟩ := exists_stdClassSum_eq_of_exchange f V' σ e j W ι
  obtain ⟨C, hC, v, -, h_exch⟩ :=
    exchange_identity W (stdSpace E a) V' σ (by simp [negCount]) hd
      (μ := fun τ : InfinitePlace E ↦ card (ι τ) + s₀) (by omega) (fun τ ↦ by omega)
      fun k : ℕ ↦ fockMoment_polyVector_ne_top k Q₀
  obtain ⟨c', hc'⟩ := h_transfer v
  refine ⟨C, hC, c', fun {𝔪 α χ} hα ↦ ?_⟩
  set ν : AutChar E := α / upsilonU1 ^ s₀ with hν
  have h_tame_inv : IsTameFor 𝔪 ν⁻¹ (fun τ : InfinitePlace E ↦ card (ι τ) + s₀) χ⁻¹ := by
    rw [hν, inv_div, div_eq_inv_mul]
    simpa [Pi.add_def, Pi.neg_def] using hα.inv.mul (hasWeight_upsilonU1_pow s₀)
  obtain ⟨c, hc_norm, h_size_ne, hc⟩ := h_exch 𝔪 ν⁻¹ χ⁻¹ h_tame_inv
  refine ⟨c, hc_norm, h_size_ne, fun η g Φ Ψ h_matched ↦ ?_⟩
  -- In the exchange identity `W` and `V'` have the character `γ = υ ^ l α`, and `I_a` has `1`.
  set γ : AutChar E := upsilonU1 ^ card l * α with hγ
  have h_tame : IsTameFor 𝔪 γ (fun τ : InfinitePlace E ↦ card l - card (ι τ)) χ := by
    rw [hγ, mul_comm]
    simpa [Pi.add_def, neg_add_eq_sub] using hα.mul (hasWeight_upsilonU1_pow (card l))
  have h_rank : rankTwist ν⁻¹⁻¹ n = γ := by
    rw [inv_inv, rankTwist, show card n / 2 = s₀ + card l by omega, pow_add, ← mul_assoc, hν,
      div_mul_cancel, mul_comm]
  have h_split : (1 : AutChar E).spaceChar (card a) * γ.spaceChar (card b) = ν⁻¹.baseChange⁻¹ := by
    rw [← map_inv, ← spaceChar_rankTwist (n := n) ⟨card l + s₀, by omega⟩, h_rank, h_card]
    simp [AutChar.spaceChar, pow_add, mul_comm (υ ^ card a)⁻¹, mul_assoc]
  have h_exchange (y : G E (blockSigns j)) :
      thetaIntegral W (stdSpace E a) γ 1 (modDatum W (stdSpace E a) 𝔪 Φ v) y =
        c * ∫ x : G E (blockSigns f), modKernel V' W γ γ 𝔪 Ψ Q₀ x y ∂V'.quotMeasure := by
    simpa only [h_rank, modKernel] using hc 1 γ h_split Φ Ψ h_matched y
  -- Twisting the standard characters by `α` multiplies the kernels by values of `α`.
  have h_left (Q : MvPolynomial (InfinitePlace E × a × n) ℂ) (h : Gf E a) :
      α.val (detFin (1 : a → ℤˣ) h) * modKernelStdSpace W (upsilonU1 ^ card l) 1 𝔪 Φ Q g h =
        modKernelStdSpace W γ 1 𝔪 Φ Q g h := by
    simpa using (modKernel_twist W (stdSpace E a) (upsilonU1 ^ card l) 1 𝔪 α 1 Φ Q g (1, h)).symm
  have h_right (Q : MvPolynomial (InfinitePlace E × n × b) ℂ) (x : G E (blockSigns f)) :
      α.val g.det * ((α.val x.det : ℂ)⁻¹ *
          modKernel V' W (upsilonU1 ^ card l) (upsilonU1 ^ card l) 𝔪 Ψ Q x g) =
        modKernel V' W γ γ 𝔪 Ψ Q x g := by
    rw [modKernel_twist, div_eq_mul_inv, mul_assoc]
  rw [mul_assoc c, ← integral_const_mul]
  simp only [h_left, h_right]
  exact hc' h_tame h_matched c h_exchange η g

/-- Index types stand for their cardinalities. Let `W` of rank `n` and `V'` of rank `b` both have
`l` negative signs, let `I_a` be the positive definite standard space, and let `n = b + a` (by `σ`),
`a = b + 2 d` and `2 l + 2 ≤ n`; `e : p ⊕ a ≃ m` orders the columns of the determinants. The finite
sets `ι τ` index the determinants at the infinite place `τ`, and `η` gives one `p × m` matrix for
each of them.

There is a number `C`, which may be `0`, with the following property. Every character `α` of weight
`l - card (ι τ)` that is tame for `(𝔪, χ)` has a number `c` with (a) and (b). (a)
`‖c‖² = C / lValueProd 𝔪.places μ d` for `μ = α⁻¹ υ ^ (b + d)`, where `υ` is `upsilonU1`, the
character of the Weil data on `U(1)`, and the denominator, which is non-zero here, is `(∏_{w ∣ 𝔪}
Nw) ^ (d ^ 2) * ∏_{1 ≤ z ≤ d} |L^S(z, μ)| ^ 2`, with `L^S` the Euler product of the base change of
`μ` outside the places `S` of `𝔪` and their conjugates. (b) Let `η`, `β`, `g` be given and let `Φ`,
`Ψ` be matched functions for `χ⁻¹` (`AreMatched`: for invertible `k` modulo `𝔪` they vanish off the
rows `a` of `k⁻¹` and the columns `b` of `k` respectively, with `Φ = χ⁻¹ (det k) Ψ` there). Then `c`
times the class sum over `U(I_a)` of the kernel of `(W, I_a)` with characters `α`, `β` and data `Φ`,
`stackedDetProd e η` equals the integral over `U(V')` of the kernel of `(V', W)` with characters
`α / β`, `α` and data `Ψ`, `matchedPoly f j η`. -/
lemma exists_mul_stdClassSum_eq_integral_modKernel {s : n → ℤˣ} (W : Space E n s) (f : p ⊕ l ≃ b)
    (V' : Space E b (blockSigns f)) (σ : b ⊕ a ≃ n) (e : p ⊕ a ≃ m) (j : m ⊕ l ≃ n)
    (hj : s = blockSigns j) {d : ℕ} (hd : card a = card b + 2 * d) (hn : 2 * card l + 2 ≤ card n)
    (ι : InfinitePlace E → Type) [∀ τ : InfinitePlace E, Fintype (ι τ)] :
    ∃ C : ℝ,
      ∀ {𝔪 : Modulus E} {α : AutChar E} {χ : MulChar 𝔪.ResidueRing ℂ},
      IsTameFor 𝔪 α (fun τ : InfinitePlace E ↦ card l - card (ι τ)) χ →
      ∃ c : ℂ,
        -- (a) the size of the constant
        ‖c‖ ^ 2 = C / lValueProd 𝔪.places (α⁻¹ * upsilonU1 ^ (card b + d)) d ∧
        -- (b) `c` times the class sum for `I_a` is the integral over the group of `V'`
        ∀ (η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ)
          {Φ : Matrix a n 𝔪.ResidueRing → ℂ} {Ψ : Matrix n b 𝔪.ResidueRing → ℂ},
            AreMatched ⊤ σ χ⁻¹ Φ Ψ →
          ∀ (β : AutChar E) (g : G E s),
          c * stdClassSum (stdLevel E a) (fun h : Gf E a ↦
              modKernelStdSpace W α β 𝔪 Φ (renameRowsCols id (j ∘ Sum.inl) (stackedDetProd e η)) g
                h) =
            ∫ x : G E (blockSigns f),
              modKernel V' W (α / β) α 𝔪 Ψ (matchedPoly f j η) x g ∂V'.quotMeasure := by
  -- Apply `exists_stdClassSum_eq_mul_integral_modKernel` to `α₀ = α / υ ^ l` and divide by `c₀`;
  -- both kernels differ from the standard ones by values of `α₀` and by `β (det g)⁻¹`.
  subst hj
  have h_card : card n = card b + card a := by rw [← card_congr σ, card_sum]
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℕ, card b + d = s₀ + card l := ⟨card b + d - card l, by omega⟩
  obtain ⟨C, -, c', h_data⟩ :=
    exists_stdClassSum_eq_mul_integral_modKernel j W f V' σ e hd (s₀ := s₀) (by omega) (by omega) ι
  refine ⟨‖c'‖ ^ 2 / C, fun {𝔪 α χ} hα ↦ ?_⟩
  obtain ⟨α₀, rfl⟩ : ∃ α₀, α = upsilonU1 ^ card l * α₀ := ⟨_, (mul_inv_cancel_left _ α).symm⟩
  have h_tame : IsTameFor 𝔪 α₀ (fun τ : InfinitePlace E ↦ -card (ι τ)) χ := by
    -- Multiplying `α` by `υ ^ (-l)` lowers its weight by `l` and leaves the tame part.
    simpa [Pi.add_def, sub_add_eq_add_sub, zpow_neg, mul_comm (upsilonU1 ^ card l) α₀] using
      hα.mul (hasWeight_upsilonU1_zpow (-card l))
  obtain ⟨c₀, hc₀_norm, h_size_ne, hc₀⟩ := h_data h_tame
  have h_char : (upsilonU1 ^ card l * α₀)⁻¹ * upsilonU1 ^ (card b + d) =
      (α₀ / upsilonU1 ^ s₀)⁻¹ := by
    rw [hs₀, pow_add, inv_div, mul_inv, mul_comm (upsilonU1 ^ s₀), mul_mul_mul_comm,
      inv_mul_cancel, one_mul, div_eq_inv_mul]
  have hc₀_ne : c₀ ≠ 0 := fun h_zero ↦ h_size_ne (hc₀_norm.symm.trans (by simp [h_zero]))
  refine ⟨c' / c₀, ?_, fun η Φ Ψ h_matched β g ↦ ?_⟩
  · rw [norm_div, div_pow, hc₀_norm, div_div, h_char]
  have h_left (Q : MvPolynomial (InfinitePlace E × a × n) ℂ) (h : Gf E a) :
      modKernelStdSpace W (upsilonU1 ^ card l * α₀) β 𝔪 Φ Q g h =
        (β.val g.det : ℂ)⁻¹ *
          (α₀.val (detFin (1 : a → ℤˣ) h) * modKernelStdSpace W (upsilonU1 ^ card l) 1 𝔪 Φ Q g
            h) := by
    simpa [div_eq_inv_mul, mul_assoc] using
      modKernel_twist W (stdSpace E a) (upsilonU1 ^ card l) 1 𝔪 α₀ β Φ Q g (1, h)
  have h_right (Q : MvPolynomial (InfinitePlace E × n × b) ℂ) (x : G E (blockSigns f)) :
      modKernel V' W (upsilonU1 ^ card l * α₀ / β) (upsilonU1 ^ card l * α₀) 𝔪 Ψ Q x g =
        (β.val g.det : ℂ)⁻¹ * α₀.val g.det * ((α₀.val x.det : ℂ)⁻¹ *
          modKernel V' W (upsilonU1 ^ card l) (upsilonU1 ^ card l) 𝔪 Ψ Q x g) := by
    rw [mul_div_assoc, modKernel_twist, div_eq_mul_inv]
    simp [div_eq_inv_mul, mul_assoc]
  simp only [h_left, h_right, ← mul_classSum, integral_const_mul]
  -- By `hc₀` the class sum, times `c'`, is `c₀ α₀ (det g)` times the integral, and `c₀` cancels.
  calc
    _ = (β.val g.det : ℂ)⁻¹ / c₀ * (c' * classSum (stdSpace E a).Γf (stdLevel E a) fun h : Gf E a ↦
          α₀.val (detFin (1 : a → ℤˣ) h) * modKernelStdSpace W (upsilonU1 ^ card l) 1 𝔪 Φ
            (renameRowsCols id (j ∘ Sum.inl) (stackedDetProd e η)) g h) := by ring
    _ = (β.val g.det : ℂ)⁻¹ / c₀ * (c₀ * α₀.val g.det * ∫ x : G E (blockSigns f),
          (α₀.val x.det : ℂ)⁻¹ * modKernel V' W (upsilonU1 ^ card l) (upsilonU1 ^ card l) 𝔪 Ψ
            (matchedPoly f j η) x g ∂V'.quotMeasure) := by rw [hc₀ η g Φ Ψ h_matched]
    _ = _ := by field_simp

/-- Let `b` be empty, so that `σ` identifies `a` with `n`. The functions `χ ∘ det` on `a × n`
matrices and `1` on `n × b` matrices are matched functions for `χ⁻¹` (`AreMatched`): they live on
the rows of the inverses and on the columns of invertible matrices, with values differing by `χ⁻¹`
of the determinant. -/
lemma areMatched_det_one [IsEmpty b] (σ : b ⊕ a ≃ n) {R : Type} [CommRing R] (χ : MulChar R ℂ) :
    AreMatched ⊤ σ χ⁻¹ (fun x : Matrix a n R ↦ χ (x.submatrix id (σ ∘ Sum.inr)).det)
      (1 : Matrix n b R → ℂ) := by
  -- These are the matched functions of `areMatched_block` for the constant function `1`.
  have h_row : (fun x : Matrix a n R ↦ χ (x.submatrix id (σ ∘ Sum.inr)).det) =
      blockRowDatum σ χ⁻¹ 1 := by
    simp [funext_iff, blockRowDatum, Matrix.toCols₂, Matrix.submatrix]
  have h_col : (1 : Matrix n b R → ℂ) = blockColDatum σ χ⁻¹ 1 := by
    simp [funext_iff, blockColDatum, Matrix.det_isEmpty]
  simpa only [h_row, h_col] using areMatched_block σ χ⁻¹ 1

omit [WeilData E] in
/-- Let `V'` be a hermitian space over the CM field `E` of rank zero (`b` is empty), with signs `t`
at the infinite places. The quotient of its adelic unitary group `G E t` by the rational points,
with the measure `quotMeasure`, has volume `1`. -/
lemma integral_one_quotMeasure_of_isEmpty [IsEmpty b] {t : b → ℤˣ} (V' : Space E b t) :
    ∫ _ : G E t, (1 : ℂ) ∂V'.quotMeasure = 1 := by
  -- The space is definite, so the volume is a class sum; the group is trivial, so there is one
  -- class, with one automorphism.
  obtain rfl : t = 1 := Subsingleton.elim t 1
  have h_sub : Subsingleton (DoubleCoset.Quotient (V'.Γf : Set (Gf E b)) (stdLevel E b)) :=
    Quotient.mk''_surjective.subsingleton
  have h_class : Unique (DoubleCoset.Quotient (V'.Γf : Set (Gf E b)) (stdLevel E b)) :=
    uniqueOfSubsingleton (DoubleCoset.mk V'.Γf (stdLevel E b) 1)
  have h_left : V'.Γ.FixesLeft (fun _ : G E (1 : b → ℤˣ) ↦ (1 : ℂ)) := fun _ _ _ ↦ rfl
  have h_level : stdLevel E b ≤ rightStabilizer fun _ : Gf E b ↦ (1 : ℂ) := fun _ _ _ ↦ rfl
  rw [integral_quotMeasure_eq_classSum h_left (by simp) (stdLevel E b) h_level
    continuous_const, classSum, finsum_unique, Nat.card_unique]
  simp

omit [WeilData E] [DecidableEq n] [Fintype b] [DecidableEq b] in
/-- For `b` empty the polynomial `matchedPoly` is `1`, being a product of empty determinants. -/
lemma matchedPoly_of_isEmpty [IsEmpty b] (f : p ⊕ l ≃ b) (j : m ⊕ l ≃ n)
    {ι : InfinitePlace E → Type} [∀ τ : InfinitePlace E, Fintype (ι τ)]
    (η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ) :
    matchedPoly f j η = 1 := by
  have hp : IsEmpty p := Function.isEmpty (f ∘ Sum.inl)
  have hl : IsEmpty l := Function.isEmpty (f ∘ Sum.inr)
  simp [matchedPoly, pairedDetProd, variableMinor, Matrix.det_isEmpty]

/-- Let `V'`, `W` be hermitian spaces over the CM field `E` with signs `t`, `s` at the infinite
places, and let `V'` have rank zero. The theta kernel `modKernel` of `(V', W)` twisted by the
characters `α`, `β` of the norm-one ideles, for the constant function `1` modulo `𝔪` and the
constant polynomial `1`, takes the value `α (det g)` at `(x, g)`: the theta series is a sum over
the zero space. -/
lemma modKernel_one_of_isEmpty [IsEmpty b] {t : b → ℤˣ} {s : n → ℤˣ} (V' : Space E b t)
    (W : Space E n s) (α β : AutChar E) (𝔪 : Modulus E) (x : G E t) (g : G E s) :
    modKernel V' W α β 𝔪 1 1 x g = α.val g.det := by
  obtain rfl : x = 1 := Subsingleton.eq_one x
  have h_triv : G.onHom ((1 : G E t), g) = 1 := Subsingleton.eq_one _
  have h_coe (z : Circle) : Circle.coeHom z = (z : ℂ) := rfl
  have h_char : pairChar α β ((1 : G E t), g) = (α.val g.det : ℂ) := by
    simp [pairChar, h_coe]
  -- The datum is the vacuum, and the only lattice vector is `0`.
  have h_vac : (V'.hom W).vacElem 0 = 1 := by
    simp [vacElem_apply_eq_prod_lineTheta, funext_iff, Fintype.prod_empty]
  simp [modKernel, modDatum, pairTheta, pairWeil, h_triv, h_vac, Modulus.liftFn_one,
    schrodingerOp_boxIndicator, Modulus.isConjDisjoint_places]

/-- For a space `V'` of rank zero and a hermitian space `W` with signs `s`, the integral over the
quotient of `U(V')` by its rational points (`quotMeasure`) of `α (det x)⁻¹` times the theta kernel
`modKernel` of `(V', W)` at `(x, g)`, with both characters `υ ^ l` (`upsilonU1` is `υ`) and data the
constant function `1` modulo `𝔪` and `matchedPoly f j η` (here the constant polynomial `1`), is
`1`. -/
lemma integral_modKernel_matchedPoly_of_isEmpty [IsEmpty b] {s : n → ℤˣ} (W : Space E n s)
    (f : p ⊕ l ≃ b) (V' : Space E b (blockSigns f)) (j : m ⊕ l ≃ n) {𝔪 : Modulus E}
    (α : AutChar E) {ι : InfinitePlace E → Type} [∀ τ : InfinitePlace E, Fintype (ι τ)]
    (η : (τ : InfinitePlace E) → ι τ → Matrix p m ℂ) (g : G E s) :
    ∫ x : G E (blockSigns f),
        (α.val x.det : ℂ)⁻¹ *
          modKernel V' W (upsilonU1 ^ card l) (upsilonU1 ^ card l) 𝔪 1 (matchedPoly f j η) x g
        ∂V'.quotMeasure = 1 := by
  have hl : IsEmpty l := Function.isEmpty (f ∘ Sum.inr)
  have h_integrand (x : G E (blockSigns f)) : (α.val x.det : ℂ)⁻¹ *
      modKernel V' W (upsilonU1 ^ card l) (upsilonU1 ^ card l) 𝔪 1 (matchedPoly f j η) x g = 1 := by
    simp [matchedPoly_of_isEmpty, modKernel_one_of_isEmpty, Subsingleton.eq_one x]
  simpa only [h_integrand] using integral_one_quotMeasure_of_isEmpty V'

end New.Rows

end ExplicitMatching

end
