import Lib.SiegelWeil.Tower.LineGaussSums

/-!
# Matched functions, sections over GL cosets and same-section pairs of matrix functions

This file studies functions on matrices over a finite product F of non-archimedean local fields with
integers O (`New.SemilocalField`). For k in GL_n(F) and n = b ⊔ a, write y_k = `New.firstCols e k`
for the block of columns b of k and x_k = `New.invLastRows e k` for the block of rows a of k⁻¹. A
matrix is primitive (`New.IsPrimitiveMatrix O`) if it is integral with an integral left inverse.

## Main definitions and results

* `New.Rows.areMatched_block`: the block determinant functions `New.Rows.blockRowDatum` and
  `New.Rows.blockColDatum` are matched functions.
* `New.localSection χ y`: a linear functional that is the sum of χ(det g) Ψ(y g) over
  representatives g of GL_b(F)/GL_b(O) (`New.IsCommonCosetRep`,
  `New.exists_linearMap_eq_sum_and_isCommonCosetRep`) when that sum is finite;
  `New.exists_isPrimitiveMatrix_localSection_eq` computes it for Ψ with primitive support.
* `New.sameSectionPairs`: the pairs (Φ, Ψ) of Schwartz–Bruhat functions, Φ(x) zero unless xᵀ has a
  left inverse and Ψ(y) zero unless y has one, such that the section of y ↦ Φ(yᵀ) at x_kᵀ is χ(det
  k) times that of Ψ at y_k; GL_n(F) acts on them (`New.sameSectionPairs.translate_mem`).
* `New.sameSectionPairs.exists_linear_factor`: a linear map of Φ that is invariant under Φ ↦ χ(det
  g) Φ(g ·) depends, on same-section pairs, only on Ψ.
* `New.AreMatched.mem_sameSectionPairs`: for tame `χ` (`New.TameLocalChar`) and locally constant
  `Ψ`, matched functions over O form a same-section pair (`New.sameSectionPairs`).

Notions from other files:
* `New.AreMatched`: Φ vanishes off the matrices x_k = `New.invLastRows` (last rows of k⁻¹), Ψ off
  the y_k = `New.firstCols` (first columns of k), k in GL_n(O), and Φ(x_k) = χ(det k) Ψ(y_k).
* `New.TameLocalChar`: A finite ring R, a surjection π: O → R with kernel ϖO, and a primitive
  character η (`New.Exchange.IsPrimitiveMulChar`) with η∘π equal to χ⁻¹ on units, 0 on non-units.
* `New.SemilocalField`: Conditions met by a finite product of non-archimedean local fields: a
  locally compact ring with Haar measure, compact open subring O of volume one, a topologically
  nilpotent ϖ in O that is invertible in F, and `New.IsValuationPair O`.

## Relation to the literature

See `New.Determinant.Exchange.ExplicitMatching` and `New.Determinant.Exchange.TheoremForPartners`
for related work. See `Lib.Adelic.Hecke.ClassSums` for sources.
-/

noncomputable section

/-!
## Matched functions from block determinant functions

On the open cell of matrices with invertible square block, Jacobi's identity for complementary
minors makes the block determinant functions matched functions.
-/

section BlockPartners

open Matrix MulChar Function

/-- Cut the `a × n` matrix `x = (x₁ x₂)` by columns along `e`, with `x₂` square. The value of this
function at `x` is `χ⁻¹(det x₂) f(x₂⁻¹ x₁)`; it is zero unless `x₂` is invertible. -/
def New.Rows.blockRowDatum {n a b R : Type} [Fintype a] [DecidableEq a] [CommRing R]
    (e : b ⊕ a ≃ n) (χ : MulChar R ℂ) (f : Matrix a b R → ℂ) (x : Matrix a n R) : ℂ :=
  χ⁻¹ (x.submatrix id e).toCols₂.det *
    f ((x.submatrix id e).toCols₂⁻¹ * (x.submatrix id e).toCols₁)

/-- Cut the `n × b` matrix `y = (y₁; y₂)` by rows along `e`, with `y₁` square. The value of this
function at `y` is `χ⁻¹(det y₁) f(-(y₂ y₁⁻¹))`; it is zero unless `y₁` is invertible. -/
def New.Rows.blockColDatum {n a b R : Type} [Fintype b] [DecidableEq b] [CommRing R]
    (e : b ⊕ a ≃ n) (χ : MulChar R ℂ) (f : Matrix a b R → ℂ) (y : Matrix n b R) : ℂ :=
  χ⁻¹ (y.submatrix e id).toRows₁.det *
    f (-((y.submatrix e id).toRows₂ * (y.submatrix e id).toRows₁⁻¹))

/-- The block determinant functions `Φ (x₁ x₂) = χ⁻¹(det x₂) f(x₂⁻¹ x₁)` (`blockRowDatum`) and
`Ψ (y₁; y₂) = χ⁻¹(det y₁) f(-(y₂ y₁⁻¹))` (`blockColDatum`) are matched functions for `χ` over the
whole ring `R` (`AreMatched ⊤`): `Φ` vanishes off the matrices `x_k` formed by the rows `a` of
`k⁻¹`, `Ψ` off the matrices `y_k` formed by the columns `b` of `k`, for `k` in `GL_n(R)`, and
`Φ(x_k) = χ(det k) Ψ(y_k)`. -/
lemma New.Rows.areMatched_block {n a b R : Type} [Fintype n] [DecidableEq n] [Fintype a]
    [DecidableEq a] [Fintype b] [DecidableEq b] [CommRing R] (e : b ⊕ a ≃ n) (χ : MulChar R ℂ)
    (f : Matrix a b R → ℂ) :
    AreMatched ⊤ e χ (blockRowDatum e χ f) (blockColDatum e χ f) := by
  -- The support conditions hold because a datum with invertible square block completes to an
  -- invertible block triangular matrix. For the equation of matched functions at `k`, split
  -- `invLastRows e k = (x₁ x₂)` into columns and `firstCols e k = (y₁; y₂)` into rows: then
  -- `det y₁ = det x₂ * det k` and `x₁ y₁ + x₂ y₂ = 0`.
  refine ⟨fun x hx ↦ ?_, fun y hy ↦ ?_, (reindexGL e).surjective.forall.2 fun k _ ↦ ?_⟩
  · -- `x = (x₁ x₂)` forms the last rows of `k⁻¹` for `k = (1 0; x₁ x₂)⁻¹`
    have h_unit :
        IsUnit (fromBlocks 1 0 (x.submatrix id e).toCols₁ (x.submatrix id e).toCols₂).det := by
      simpa [apply_eq_zero_iff] using left_ne_zero_of_mul hx
    exact ⟨reindexGL e (.mk'' _ h_unit)⁻¹, by simp [mem_intGL, ← ext_iff, e.surjective.forall]⟩
  · -- `y = (y₁; y₂)` forms the first columns of `k = (y₁ 0; y₂ 1)`
    have h_unit :
        IsUnit (fromBlocks (y.submatrix e id).toRows₁ 0 (y.submatrix e id).toRows₂ 1).det := by
      simpa [apply_eq_zero_iff] using left_ne_zero_of_mul hy
    exact ⟨reindexGL e (.mk'' _ h_unit), by simp [mem_intGL, ← ext_iff, e.surjective.forall]⟩
  · -- relabel the basis, so that `e` becomes the identity
    set x : Matrix a (b ⊕ a) R := invLastRows (.refl _) k with hx
    set y : Matrix (b ⊕ a) b R := firstCols (.refl _) k with hy
    suffices h_blocks : χ⁻¹ x.toCols₂.det * f (x.toCols₂⁻¹ * x.toCols₁) =
        χ k.val.det * (χ⁻¹ y.toRows₁.det * f (-(y.toRows₂ * y.toRows₁⁻¹))) by
      simpa [blockRowDatum, blockColDatum, hx, hy, invLastRows, firstCols, ← Function.comp_assoc]
        using h_blocks
    -- Jacobi's identity: `det (s; x) * det k = det (s y)`, here for the rows `s = (1 0)`
    have h_det : y.toRows₁.det = x.toCols₂.det * k.val.det := by
      set s : Matrix b (b ⊕ a) R := fromCols 1 0 with hs
      have jacobi : (fromRows s x).det * k.val.det = (s * y).det :=
        det_fromRows_invLastRows (.refl _) k s
      rwa [hs, ← x.fromCols_toCols, fromRows_fromCols_eq_fromBlocks, det_fromBlocks_zero₁₂, det_one,
        one_mul, ← y.fromRows_toRows, fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul,
        add_zero, eq_comm] at jacobi
    -- the relation `x y = 0` in blocks
    have h_ker : x.toCols₁ * y.toRows₁ + x.toCols₂ * y.toRows₂ = 0 := by
      simpa [← fromCols_mul_fromRows] using invLastRows_mul_firstCols (.refl _) k
    by_cases hx₂ : IsUnit x.toCols₂.det
    · -- then `y₁` is invertible and `y₂ = -x₂⁻¹ x₁ y₁`
      have hy₁ : IsUnit y.toRows₁.det := by simp [h_det, hx₂]
      have hy₂ : y.toRows₂ = -(x.toCols₂⁻¹ * x.toCols₁ * y.toRows₁) := by
        simp [add_eq_zero_iff_eq_neg.1 h_ker, Matrix.mul_assoc, hx₂]
      have h_arg : x.toCols₂⁻¹ * x.toCols₁ = -(y.toRows₂ * y.toRows₁⁻¹) := by simp [hy₂, hy₁]
      have h_cancel : χ k.val.det * χ⁻¹ k.val.det = 1 := by
        simp [inv_apply_eq_inv', apply_eq_zero_iff]
      rw [h_arg, h_det, map_mul, ← mul_assoc, mul_left_comm (χ k.val.det), h_cancel, mul_one]
    · -- both sides vanish
      simp [h_det, χ⁻¹.map_nonunit hx₂]

end BlockPartners

/-! ## Sections over GL cosets and the space of same-section pairs -/

namespace New

open Matrix schwartzBruhat SemilocalField Finsupp

variable {F : Type} [SemilocalField F]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]

/-- On the complex functions on a type `ι` there is a linear functional equal to `f ↦ ∑ i, f i` on
the functions with finitely many nonzero values. -/
lemma exists_linearMap_eq_sum (ι : Type*) :
    ∃ ℓ : (ι → ℂ) →ₗ[ℂ] ℂ,
      ∀ (t : Finset ι) (f : ι → ℂ), (∀ i : ι, f i ≠ 0 → i ∈ t) → ℓ f = ∑ i ∈ t, f i := by
  -- Extend the sum of all values from finitely supported functions to all functions.
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : (ι → ℂ) →ₗ[ℂ] ℂ, ℓ ∘ₗ lcoeFun = linearCombination ℂ 1 :=
    lcoeFun.dualMap_surjective_of_injective DFunLike.coe_injective (linearCombination ℂ 1)
  refine ⟨ℓ, fun t f hf ↦ ?_⟩
  simpa [linearCombination_onFinset] using LinearMap.congr_fun hℓ (onFinset t f hf)

variable (n) in
/-- Let `O` be the ring of integers of the semilocal field `F` (`SemilocalField.O`), and `intGL b O`
the subgroup `GL_b(O)` of `GL_b(F)`. The matrices `r q` represent the cosets `q` in
`GL_b(F)/GL_b(O)`, and each `n × b` matrix `y` with a left inverse has `y * r q` primitive (entries
in `O`, with a left inverse over `O`) for exactly one `q`, and likewise `y * (r q)⁻¹`. -/
structure IsCommonCosetRep (r : GL b F ⧸ intGL b (O : Subring F) → GL b F) : Prop where
  /-- `r q` lies in the coset `q`. -/
  coe_eq (q : GL b F ⧸ intGL b O) : (r q : GL b F ⧸ intGL b O) = q
  /-- If `y` has a left inverse, exactly one representative makes `y * r q` primitive. -/
  existsUnique_mul (y : Matrix n b F) (hy : HasLeftInv y) :
    ∃! q : GL b F ⧸ intGL b O, IsPrimitiveMatrix O (y * (r q).val)
  /-- If `y` has a left inverse, exactly one representative makes `y * (r q)⁻¹` primitive. -/
  existsUnique_mul_inv (y : Matrix n b F) (hy : HasLeftInv y) :
    ∃! q : GL b F ⧸ intGL b O, IsPrimitiveMatrix O (y * (r q).val⁻¹)

variable (F b n) in
/-- For a semilocal field `F` with ring of integers `O` there are representatives `r q` of the
cosets `q` in `GL_b(F)/GL_b(O)` such that, for every `n × b` matrix `y` with a left inverse, exactly
one `q` makes `y * r q` primitive and exactly one makes `y * (r q)⁻¹` primitive
(`IsCommonCosetRep n r`). -/
lemma exists_isCommonCosetRep : ∃ r : GL b F ⧸ intGL b O → GL b F, IsCommonCosetRep n r := by
  -- Each left coset has a symmetric representative `r q` (`exists_invTransposeGL_inv_eq`). On
  -- these, inversion agrees with the inverse transpose `invTransposeGL`, which permutes the left
  -- cosets.
  have exists_symm (q : GL b F ⧸ intGL b O) :
      ∃ g : GL b F, (g : GL b F ⧸ intGL b O) = q ∧ (invTransposeGL g)⁻¹ = g := by
    obtain ⟨k, hk, h_symm⟩ :
        ∃ k ∈ intGL b O, invTransposeGL q.out⁻¹ = invTransposeGL k * q.out * k :=
      exists_invTransposeGL_inv_eq isValuationPair q.out
    refine ⟨q.out * k, by simp [hk], ?_⟩
    rw [map_mul, _root_.mul_inv_rev, ← map_inv _ q.out, h_symm, mul_assoc, inv_mul_cancel_left]
  choose r r_mk r_symm using exists_symm
  -- Some `y * u` is primitive, and then `y * g` is primitive exactly for `g` in the coset of `u`.
  have exists_coset (y : Matrix n b F) (hy : HasLeftInv y) : ∃ u : GL b F, ∀ g : GL b F,
      IsPrimitiveMatrix O (y * g.val) ↔ u⁻¹ * g ∈ intGL b O := by
    obtain ⟨u, -, hu⟩ := isValuationPair.exists_isPrimitiveMatrix_mul hy
    refine ⟨u, fun g ↦ ?_⟩
    simpa [y.mul_assoc] using hu.mul_iff.trans (isPrimitiveMatrix_iff_mem_intGL (u⁻¹ * g))
  refine ⟨r, r_mk, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · obtain ⟨u, prim_iff⟩ := exists_coset y hy
    have mul_iff (q : GL b F ⧸ intGL b O) : IsPrimitiveMatrix O (y * (r q).val) ↔ q = ↑u := by
      rw [prim_iff, ← QuotientGroup.eq, r_mk, eq_comm]
    simp only [mul_iff, existsUnique_eq]
  · -- Apply `invTransposeGL` to `u⁻¹ * (r q)⁻¹`: the condition says that `r q` lies in the coset
    -- of `invTransposeGL u`.
    obtain ⟨u, prim_iff⟩ := exists_coset y hy
    have mul_inv_iff (q : GL b F ⧸ intGL b O) :
        IsPrimitiveMatrix O (y * (r q).val⁻¹) ↔ q = ↑(invTransposeGL u) := by
      rw [← coe_units_inv, prim_iff, ← invTransposeGL_mem_intGL, map_mul, map_inv, map_inv, r_symm,
        ← QuotientGroup.eq, r_mk, eq_comm]
    simp only [mul_inv_iff, existsUnique_eq]

/-- There are representatives `r q` of the cosets `q` in `GL_b(F)/GL_b(O)` and a linear functional
`ℓ` on the complex functions on `GL_b(F)` such that `ℓ f = ∑ q, f (r q)` when only finitely many of
the values `f (r q)` are nonzero, and, for every `n × b` matrix `y` with a left inverse, exactly one
`q` makes `y * r q` primitive and exactly one makes `y * (r q)⁻¹` primitive. -/
lemma exists_linearMap_eq_sum_and_isCommonCosetRep :
    ∃ (ℓ : (GL b F → ℂ) →ₗ[ℂ] ℂ) (r : GL b F ⧸ intGL b O → GL b F),
      (∀ (t : Finset (GL b F ⧸ intGL b O)) (f : GL b F → ℂ),
        (∀ q : GL b F ⧸ intGL b O, f (r q) ≠ 0 → q ∈ t) → ℓ f = ∑ q ∈ t, f (r q)) ∧
      IsCommonCosetRep n r := by
  obtain ⟨ℓ, hℓ⟩ := exists_linearMap_eq_sum (GL b F ⧸ intGL b O)
  obtain ⟨r, hr⟩ := exists_isCommonCosetRep (F := F) (b := b) (n := n)
  exact ⟨ℓ ∘ₗ LinearMap.funLeft ℂ ℂ r, r, fun t f hf ↦ hℓ t (fun q ↦ f (r q)) hf, hr⟩

variable (F b n) in
/-- A linear functional on all functions on `GL b F`, chosen from
`exists_linearMap_eq_sum_and_isCommonCosetRep`. It extends the finite sum of the values at the
representatives `commonCosetRep` (`commonCosetSum_eq_sum`). -/
def commonCosetSum : (GL b F → ℂ) →ₗ[ℂ] ℂ :=
  (exists_linearMap_eq_sum_and_isCommonCosetRep (F := F) (b := b) (n := n)).choose

variable (F b n) in
/-- The representatives of the cosets of `GL b O` in `GL b F` that are chosen from
`exists_linearMap_eq_sum_and_isCommonCosetRep` together with `commonCosetSum`
(`isCommonCosetRep_commonCosetRep`). -/
def commonCosetRep : GL b F ⧸ intGL b O → GL b F :=
  (exists_linearMap_eq_sum_and_isCommonCosetRep (F := F) (b := b) (n := n)).choose_spec.choose

/-- `commonCosetSum f` is the sum of the values of `f` at the representatives, when the nonzero
values are indexed by a finite set `t` of cosets. -/
lemma commonCosetSum_eq_sum (f : GL b F → ℂ) (t : Finset (GL b F ⧸ intGL b O))
    (ht : ∀ q : GL b F ⧸ intGL b O, f (commonCosetRep F b n q) ≠ 0 → q ∈ t) :
    commonCosetSum F b n f = ∑ q ∈ t, f (commonCosetRep F b n q) :=
  (exists_linearMap_eq_sum_and_isCommonCosetRep (n := n)).choose_spec.choose_spec.left t f ht

/-- The chosen matrices `commonCosetRep` represent the cosets of `GL_b(O)` in `GL_b(F)`. For each
`n × b` matrix `y` with a left inverse, exactly one of them, `r`, makes `y * r` primitive, and
exactly one makes `y * r⁻¹` primitive (`IsCommonCosetRep`). -/
lemma isCommonCosetRep_commonCosetRep : IsCommonCosetRep n (commonCosetRep F b n) :=
  exists_linearMap_eq_sum_and_isCommonCosetRep.choose_spec.choose_spec.right

/-- For `y` with a left inverse, exactly one of the chosen coset representatives `r` makes `y * r`
primitive (integral with an integral left inverse). -/
lemma existsUnique_isPrimitiveMatrix_mul_commonCosetRep {y : Matrix n b F} (hy : HasLeftInv y) :
    ∃! q : GL b F ⧸ intGL b O, IsPrimitiveMatrix O (y * (commonCosetRep F b n q).val) :=
  isCommonCosetRep_commonCosetRep.existsUnique_mul y hy

/-- For `y` with a left inverse (`HasLeftInv y`), exactly one coset `q` of `GL b O` in `GL b F`
makes `y * (commonCosetRep F b n q)⁻¹` primitive (entries in `O`, with a left inverse that has
entries in `O`). -/
lemma existsUnique_isPrimitiveMatrix_mul_inv_commonCosetRep {y : Matrix n b F} (hy : HasLeftInv y) :
    ∃! q : GL b F ⧸ intGL b O, IsPrimitiveMatrix O (y * (commonCosetRep F b n q).val⁻¹) :=
  isCommonCosetRep_commonCosetRep.existsUnique_mul_inv y hy

/-- For a character `χ` of `F` and an `n × b` matrix `y`, the section at `y` is the functional
sending `Ψ` to `commonCosetSum` of `g ↦ χ (det g) * Ψ (y * g)` on `GL b F`, that is, to the sum of
this function over representatives of `GL_b(F)/GL_b(O)` when the sum is finite
(`localSection_eq_sum`). -/
def localSection (χ : MulChar F ℂ) (y : Matrix n b F) : (Matrix n b F → ℂ) →ₗ[ℂ] ℂ :=
  commonCosetSum F b n ∘ₗ LinearMap.mulLeft ℂ (fun g : GL b F ↦ χ g.val.det) ∘ₗ
    LinearMap.funLeft ℂ ℂ fun g : GL b F ↦ y * g.val

/-- The section of `Ψ` at `y` is the sum of `χ (det r) * Ψ (y * r)` over the chosen matrices `r`
indexed by `GL_b(F)/GL_b(O)` (`commonCosetRep`), when the indices with `Ψ (y * r) ≠ 0` lie in a
finite set `t`. -/
lemma localSection_eq_sum (χ : MulChar F ℂ) (y : Matrix n b F) (Ψ : Matrix n b F → ℂ)
    (t : Finset (GL b F ⧸ intGL b O))
    (ht : ∀ q : GL b F ⧸ intGL b O, Ψ (y * (commonCosetRep F b n q).val) ≠ 0 → q ∈ t) :
    localSection χ y Ψ =
      ∑ q ∈ t, χ (commonCosetRep F b n q).val.det * Ψ (y * (commonCosetRep F b n q).val) :=
  commonCosetSum_eq_sum (fun g : GL b F ↦ χ g.val.det * Ψ (y * g.val)) t fun q hq ↦
    ht q (right_ne_zero_of_mul hq)

/-- Same-section pairs (compare matched functions, `AreMatched`): pairs `(Φ, Ψ)` of
Schwartz–Bruhat functions, on the matrices `x` such that `xᵀ` has a left inverse and on the matrices
with a left inverse, such that for every `k` the section of `y ↦ Φ yᵀ` at `(invLastRows e k)ᵀ` is
`χ (det k)` times the section of `Ψ` at `firstCols e k` (`mem_sameSectionPairs_iff`). -/
def sameSectionPairs (χ : MulChar F ℂ) (e : b ⊕ a ≃ n) :
    Submodule ℂ ((Matrix a n F → ℂ) × (Matrix n b F → ℂ)) :=
  Submodule.prod (schwartzBruhat fun x : Matrix a n F ↦ HasLeftInv xᵀ)
      (schwartzBruhat HasLeftInv) ⊓
    (LinearMap.pi fun k : GL n F ↦
      (localSection χ (invLastRows e k)ᵀ ∘ₗ LinearMap.funLeft ℂ ℂ transpose).coprod
        (-(χ k.val.det • localSection χ (firstCols e k)))).ker

/-- `(Φ, Ψ)` is a same-section pair if and only if both functions are locally constant with compact
support, `Φ` in the `x` such that `xᵀ` has a left inverse and `Ψ` in the `y` with a left inverse,
and for each `k` the coset sum `localSection` of `y ↦ Φ yᵀ` at the transposed last rows of `k⁻¹` is
`χ (det k)` times that of `Ψ` at the first columns of `k`. -/
lemma mem_sameSectionPairs_iff {χ : MulChar F ℂ} {e : b ⊕ a ≃ n} {Φ : Matrix a n F → ℂ}
    {Ψ : Matrix n b F → ℂ} :
    (Φ, Ψ) ∈ sameSectionPairs χ e ↔
      Φ ∈ schwartzBruhat (fun x : Matrix a n F ↦ HasLeftInv xᵀ) ∧
      Ψ ∈ schwartzBruhat HasLeftInv ∧
      ∀ k : GL n F, localSection χ (invLastRows e k)ᵀ (fun y : Matrix n a F ↦ Φ yᵀ) =
        χ k.val.det * localSection χ (firstCols e k) Ψ := by
  simp [sameSectionPairs, LinearMap.ker_pi, add_neg_eq_zero, LinearMap.funLeft, Function.comp_def,
    and_assoc]

omit [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] in
/-- Multiplying the columns `b` of `k` on the left by `g` gives the columns `b` of `g * k`. -/
lemma mul_firstCols (e : b ⊕ a ≃ n) (g k : GL n F) :
    g.val * firstCols e k = firstCols e (g * k) := rfl

/-- Translation by `g` in `GL n F` preserves the same-section pairs of a character `χ` of `F` and a
splitting `e` of the indices: if `(Φ, Ψ)` is one, then so is
`(x ↦ χ (det g) * Φ (x * g), y ↦ Ψ (g⁻¹ * y))`. -/
lemma sameSectionPairs.translate_mem (χ : MulChar F ℂ) (e : b ⊕ a ≃ n)
    {Φ : Matrix a n F → ℂ} {Ψ : Matrix n b F → ℂ}
    (h_pair : (Φ, Ψ) ∈ sameSectionPairs χ e) (g : GL n F) :
    (χ g.val.det • fun x : Matrix a n F ↦ Φ (x * g.val),
      fun y : Matrix n b F ↦ Ψ (g⁻¹.val * y)) ∈ sameSectionPairs χ e := by
  obtain ⟨hΦ, hΨ, h_match⟩ := mem_sameSectionPairs_iff.1 h_pair
  refine mem_sameSectionPairs_iff.2 ⟨Submodule.smul_mem _ _ ?_, ?_, fun k ↦ ?_⟩
  · -- If `L` is a left inverse of `xᵀ`, then `L gᵀ` is one of `(x g⁻¹)ᵀ`.
    exact schwartzBruhat.comp hΦ (fun x ↦ x * g⁻¹.val) (fun x ↦ by simp) fun x ⟨L, hL⟩ ↦
      ⟨L * g.valᵀ, by simpa [← transpose_mul, Matrix.mul_assoc] using hL⟩
  · -- If `L` is a left inverse of `y`, then `L g⁻¹` is one of `g y`.
    exact schwartzBruhat.comp hΨ (fun y ↦ g.val * y) (fun y ↦ by simp) fun y ⟨L, hL⟩ ↦
      ⟨L * g⁻¹.val, by simpa [Matrix.mul_assoc] using hL⟩
  · -- The matching identity at `k` is `χ (det g)` times that of `(Φ, Ψ)` at `g⁻¹ k`.
    have h_det : χ g.val.det * χ (g⁻¹ * k).val.det = χ k.val.det := by
      simp [← map_mul, ← det_mul]
    calc localSection χ (invLastRows e k)ᵀ (χ g.val.det • fun y ↦ Φ (yᵀ * g.val))
      _ = χ g.val.det * localSection χ (invLastRows e (g⁻¹ * k))ᵀ (fun y ↦ Φ yᵀ) := by
        simp [invLastRows, localSection, Pi.mul_def, Matrix.mul_assoc]
      _ = χ k.val.det * localSection χ (firstCols e (g⁻¹ * k)) Ψ := by
        rw [h_match, ← mul_assoc, h_det]
      _ = χ k.val.det * localSection χ (firstCols e k) fun y ↦ Ψ (g⁻¹.val * y) := by
        simp [← mul_firstCols, localSection, Pi.mul_def, Matrix.mul_assoc]

/-- Let `y` have a left inverse. There is `g` in `GL b F` such that `y * g` is primitive and, for
every `Ψ` that vanishes off the primitive matrices, the section of `Ψ` at `y` is the one term
`χ (det g) * Ψ (y * g)`. -/
lemma exists_isPrimitiveMatrix_localSection_eq (χ : MulChar F ℂ) (y : Matrix n b F)
    (hy : HasLeftInv y) :
    ∃ g : GL b F, IsPrimitiveMatrix O (y * g.val) ∧
      ∀ Ψ : Matrix n b F → ℂ, (∀ x : Matrix n b F, Ψ x ≠ 0 → IsPrimitiveMatrix O x) →
        localSection χ y Ψ = χ g.val.det * Ψ (y * g.val) := by
  -- Exactly one representative `r` makes `y * r` primitive, and only it counts in the sum.
  obtain ⟨q, hq, hq_unique⟩ := existsUnique_isPrimitiveMatrix_mul_commonCosetRep (n := n) hy
  refine ⟨commonCosetRep F b n q, hq, fun Ψ hΨ ↦ ?_⟩
  simpa using localSection_eq_sum χ y Ψ {q} fun p hp ↦ by simp [hq_unique p (hΨ _ hp)]

/-- In a semilocal field with ring of integers `O` and uniformiser `ϖ`, the element `1 - ϖ t` is a
unit of `O` for every `t` in `O`. -/
lemma isIntegralUnit_one_sub_uniformizer_mul {t : F} (ht : t ∈ O) :
    IsIntegralUnit (1 - (ϖ : Fˣ) * t) := by
  -- With `x = ϖ t`, the multiples of `1 - x` by `O` form a compact set. It contains the
  -- `1 - x ^ k`, and so their limit `1`.
  set x : F := (ϖ : Fˣ) * t with hx
  have hx_mem : x ∈ O := mul_mem ϖ_mem ht
  have h_closed : IsClosed ((fun s : F ↦ s * (1 - x)) '' (O : Subring F)) :=
    (isCompact_O.image (continuous_mul_const (1 - x))).isClosed
  have h_geom (k : ℕ) : 1 - x ^ k ∈ (fun s : F ↦ s * (1 - x)) '' (O : Subring F) :=
    ⟨∑ i ∈ Finset.range k, x ^ i, sum_mem fun i _ ↦ pow_mem hx_mem i, geom_sum_mul_neg x k⟩
  -- The powers `x ^ k = ϖ ^ k * t ^ k` tend to zero, because `t ^ k` stays in the compact `O`.
  have h_pow : Filter.Tendsto (fun k : ℕ ↦ x ^ k) Filter.atTop (nhds 0) := by
    refine Filter.tendsto_def.2 fun U hU ↦ ?_
    have h_tube : ∀ᶠ c : F in nhds 0, ∀ u ∈ (O : Subring F), c * u ∈ U :=
      isCompact_O.eventually_forall_of_forall_eventually fun u _ ↦
        (continuous_mul.tendsto' (0, u) 0 (zero_mul u)).eventually_mem hU
    filter_upwards [isTopologicallyNilpotent_ϖ.eventually h_tube] with k hk
    simpa [hx, mul_pow] using hk (t ^ k) (pow_mem ht k)
  have h_lim : Filter.Tendsto (fun k : ℕ ↦ 1 - x ^ k) Filter.atTop (nhds 1) := by
    simpa using h_pow.const_sub 1
  exact ⟨sub_mem (one_mem O) hx_mem, h_closed.mem_of_tendsto h_lim (.of_forall h_geom)⟩

/-- The units of the ring of integers `O` of a semilocal field `F` form an open subset of `F`. -/
lemma isOpen_setOf_isIntegralUnit : IsOpen {x : F | IsIntegralUnit x} := by
  -- If `s * x = 1`, then `s * z` lies in `1 - ϖ O` for integral `z` near `x`.
  refine isOpen_iff_mem_nhds.2 fun x ⟨x_int, s, s_int, hs⟩ ↦ ?_
  let τ (z : F) : F := (ϖ⁻¹ : Fˣ) * (1 - s * z)
  have hτ : τ ⁻¹' (O : Subring F) ∈ nhds x :=
    (isOpen_O.preimage (by fun_prop)).mem_nhds (by simp [τ, hs])
  filter_upwards [isOpen_O.mem_nhds x_int, hτ] with z z_int hz
  obtain ⟨-, w, w_int, hw⟩ : IsIntegralUnit (s * z) := by
    simpa [τ] using isIntegralUnit_one_sub_uniformizer_mul hz
  exact ⟨z_int, w * s, mul_mem w_int s_int, by rwa [mul_assoc]⟩

omit [DecidableEq n] in
/-- The primitive `n × a` matrices over a semilocal field (entries in the ring of integers `O`, with
a left inverse over `O`) form a closed and open set. -/
lemma isClopen_setOf_isPrimitiveMatrix : IsClopen {y : Matrix n a F | IsPrimitiveMatrix O y} := by
  constructor
  · -- The set is the projection of the compact set of integral pairs `(y, L)` with `L * y = 1`.
    let K : Set (Matrix n a F × Matrix a n F) :=
      {y | IsIntMatrix O y} ×ˢ {L | IsIntMatrix O L} ∩ {p | p.2 * p.1 = 1}
    have hK : IsCompact K := (isCompact_O.matrix.prod isCompact_O.matrix).inter_right
      (isClosed_eq (by fun_prop) (by fun_prop))
    have h_image : {y : Matrix n a F | IsPrimitiveMatrix O y} = Prod.fst '' K :=
      Set.ext fun y ↦ by simp [K, IsPrimitiveMatrix, and_assoc]
    simpa only [h_image] using (hK.image continuous_fst).isClosed
  · -- If `L * y = 1`, then for integral `z` near `y` the determinant of `L * z` is a unit of `O`.
    refine isOpen_iff_mem_nhds.2 fun y ⟨y_int, L, L_int, hL⟩ ↦ ?_
    have h_int : IsOpen {z : Matrix n a F | IsIntMatrix O z} := isOpen_O.matrix
    have h_det : IsOpen {z : Matrix n a F | IsIntegralUnit (L * z).det} :=
      isOpen_setOf_isIntegralUnit.preimage (by fun_prop)
    filter_upwards [h_int.mem_nhds y_int, h_det.mem_nhds (by simp [hL])] with z z_int hz
    obtain ⟨-, L', L'_int, hL'⟩ : IsPrimitiveMatrix O (L * z) :=
      isPrimitiveMatrix_iff_int_and_unit_det.2 ⟨L_int.mul z_int, hz⟩
    exact ⟨z_int, L' * L, L'_int.mul L_int, by rwa [L'.mul_assoc]⟩

/-- A matrix `x` consists of the rows `a` of `k⁻¹` (`invLastRows`) for some `k` in `GL n O` exactly
when `xᵀ` is primitive (integral, with an integral left inverse). -/
lemma exists_eq_invLastRows_iff_isPrimitiveMatrix (e : b ⊕ a ≃ n) (x : Matrix a n F) :
    (∃ k ∈ intGL n O, x = invLastRows e k) ↔ IsPrimitiveMatrix O xᵀ :=
  (exists_invLastRows_iff_transpose e).trans (isValuationPair.exists_firstCols_iff _)

/-- Let `Φ` be locally constant with compact support in the `x` such that `xᵀ` has a left inverse.
There is a finite set `t` of cosets `q` in `GL_a(F)/GL_a(O)` such that each `x` in the support has
`xᵀ * r⁻¹` primitive for the chosen representative `r = commonCosetRep F a n q` of some `q` in
`t`. -/
lemma exists_finset_isPrimitiveMatrix_mul_inv_commonCosetRep {Φ : Matrix a n F → ℂ}
    (hΦ : Φ ∈ schwartzBruhat fun x : Matrix a n F ↦ HasLeftInv xᵀ) :
    ∃ t : Finset (GL a F ⧸ intGL a O), ∀ x : Matrix a n F, Φ x ≠ 0 →
      ∃ q ∈ t, IsPrimitiveMatrix O (xᵀ * (commonCosetRep F a n q).val⁻¹) := by
  obtain ⟨hΦ_const, hΦ_compact, hΦ_supp⟩ := hΦ
  let U (q : GL a F ⧸ intGL a O) : Set (Matrix a n F) :=
    {x | IsPrimitiveMatrix O (xᵀ * (commonCosetRep F a n q).val⁻¹)}
  have h_compact : IsCompact Φ.support :=
    hΦ_compact.of_isClosed_subset (hΦ_const {0}).isClosed_compl (subset_tsupport Φ)
  obtain ⟨t, ht⟩ := h_compact.elim_finite_subcover U
    (fun q ↦ isClopen_setOf_isPrimitiveMatrix.isOpen.preimage (by fun_prop))
    fun x hx ↦ Set.mem_iUnion.2
      (existsUnique_isPrimitiveMatrix_mul_inv_commonCosetRep (hΦ_supp hx)).exists
  exact ⟨t, fun x hx ↦ by simpa [U] using ht hx⟩

/-- Let `χ` be a character of `F`, and let `Λ` be a linear map on functions of `a × n` matrices with
`χ (det g) • Λ (x ↦ Φ (g * x)) = Λ Φ` for all `g` in `GL a F` and all locally constant `Φ` with
compact support in the `x` such that `xᵀ` has a left inverse. Then on same-section pairs `(Φ, Ψ)`
the value `Λ Φ` is a linear function `T` of `Ψ`. -/
lemma sameSectionPairs.exists_linear_factor (χ : MulChar F ℂ) (e : b ⊕ a ≃ n) {X : Type*}
    (Λ : (Matrix a n F → ℂ) →ₗ[ℂ] X → ℂ)
    (hΛ : ∀ g : GL a F, ∀ Φ ∈ schwartzBruhat fun x : Matrix a n F ↦ HasLeftInv xᵀ,
      χ g.val.det • Λ (fun x : Matrix a n F ↦ Φ (g.val * x)) = Λ Φ) :
    ∃ T : (Matrix n b F → ℂ) →ₗ[ℂ] X → ℂ, ∀ (Φ : Matrix a n F → ℂ) (Ψ : Matrix n b F → ℂ),
      (Φ, Ψ) ∈ sameSectionPairs χ e → T Ψ = Λ Φ := by
  classical
  -- For primitive `xᵀ` write `x = invLastRows e (k x)`; let `T Ψ` be `Λ` of the function on such
  -- `x` read from the sections of `Ψ`. For a same-section pair, cut `Φ` into finitely many pieces,
  -- by the coset `q` that makes `xᵀ (r q)⁻¹` primitive, and move each piece to primitive `xᵀ` by
  -- `hΛ`.
  have exists_rows (x : Matrix a n F) (hx : IsPrimitiveMatrix O xᵀ) :
      ∃ k ∈ intGL n O, x = invLastRows e k :=
    (exists_eq_invLastRows_iff_isPrimitiveMatrix e x).2 hx
  choose! k _ hk using exists_rows
  let recover : (Matrix n b F → ℂ) →ₗ[ℂ] Matrix a n F → ℂ := LinearMap.pi fun x ↦
    if IsPrimitiveMatrix O xᵀ then χ (k x).det • localSection χ (firstCols e (k x)) else 0
  refine ⟨Λ ∘ₗ recover, fun Φ Ψ h_pair ↦ ?_⟩
  obtain ⟨hΦ, -, h_match⟩ := mem_sameSectionPairs_iff.1 h_pair
  have ⟨hΦ_const, hΦ_compact, hΦ_supp⟩ := hΦ
  let r : GL a F ⧸ intGL a O → GL a F := commonCosetRep F a n
  let piece (q : GL a F ⧸ intGL a O) (x : Matrix a n F) : ℂ :=
    if IsPrimitiveMatrix O (xᵀ * (r q).val⁻¹) then Φ x else 0
  have piece_mem (q : GL a F ⧸ intGL a O) :
      piece q ∈ schwartzBruhat fun x : Matrix a n F ↦ HasLeftInv xᵀ := by
    have h_const : IsLocallyConstant (piece q) :=
      (LocallyConstant.indicator ⟨Φ, hΦ_const⟩ <| isClopen_setOf_isPrimitiveMatrix.preimage
        (f := fun x : Matrix a n F ↦ xᵀ * (r q).val⁻¹) (by fun_prop)).isLocallyConstant
    have h_support : (piece q).support ⊆ Φ.support := by simp [piece]
    exact ⟨h_const, hΦ_compact.mono h_support, h_support.trans hΦ_supp⟩
  have h_coset (x : Matrix a n F) (hx : Φ x ≠ 0) :
      ∃! q : GL a F ⧸ intGL a O, IsPrimitiveMatrix O (xᵀ * (r q).val⁻¹) :=
    existsUnique_isPrimitiveMatrix_mul_inv_commonCosetRep (hΦ_supp hx)
  obtain ⟨t, ht⟩ := exists_finset_isPrimitiveMatrix_mul_inv_commonCosetRep hΦ
  have h_pieces : Φ = ∑ q ∈ t, piece q := by
    ext x
    by_cases hx : Φ x = 0
    · simp [piece, hx]
    obtain ⟨q, hq, h_prim⟩ := ht x hx
    rw [Finset.sum_apply, Finset.sum_eq_single_of_mem q hq
      fun q' _ hq' ↦ ite_eq_right fun h ↦ hq' ((h_coset x hx).unique h h_prim)]
    simp [r, h_prim]
  -- The section of `Φ` at a primitive `xᵀ` is a sum over the same cosets.
  have h_section (x : Matrix a n F) (hx : IsPrimitiveMatrix O xᵀ) :
      localSection χ xᵀ (fun y ↦ Φ yᵀ) = ∑ q ∈ t, χ (r q).val.det * Φ ((r q).valᵀ * x) := by
    rw [localSection_eq_sum χ xᵀ (fun y ↦ Φ yᵀ) t fun q h_ne ↦ ?_]
    · simp only [r, transpose_mul, transpose_transpose]
    · obtain ⟨q', hq', h_prim⟩ := ht _ h_ne
      rwa [(h_coset _ h_ne).unique (y₁ := q) (by simpa [r] using hx) h_prim]
  -- The recovered function is the sum of the pieces, each moved to primitive `xᵀ` and weighted by
  -- `χ (det (r q))`: `moved q x` is `Φ ((r q)ᵀ * x)` if `xᵀ` is primitive, and `0` otherwise.
  let moved (q : GL a F ⧸ intGL a O) (x : Matrix a n F) : ℂ := piece q ((r q).valᵀ * x)
  have h_recover : recover Ψ = ∑ q ∈ t, χ (transposeGL (r q)).val.det • moved q := by
    ext x
    by_cases hx : IsPrimitiveMatrix O xᵀ
    · calc recover Ψ x
        _ = χ (k x).val.det * localSection χ (firstCols e (k x)) Ψ := by simp [recover, hx]
        _ = localSection χ xᵀ (fun y ↦ Φ yᵀ) := by rw [← h_match, ← hk x hx]
        _ = (∑ q ∈ t, χ (transposeGL (r q)).val.det • moved q) x := by
          simp [h_section x hx, moved, piece, hx]
    · simp [recover, moved, piece, hx]
  calc Λ (recover Ψ)
    _ = ∑ q ∈ t, χ (transposeGL (r q)).val.det • Λ (moved q) := by simp [h_recover]
    _ = ∑ q ∈ t, Λ (piece q) := Finset.sum_congr rfl fun q _ ↦ hΛ _ _ (piece_mem q)
    _ = Λ Φ := by rw [← map_sum, ← h_pieces]

end New

/-! ## Matched functions as same-section pairs -/

namespace New.AreMatched

open Matrix SemilocalField schwartzBruhat

/-- Let `Φ` and `Ψ` be matched for `χ` over the subring `O` (`AreMatched`): they vanish off the
matrices `invLastRows e k` and `firstCols e k` respectively, and `Φ (invLastRows e k) = χ (det k) *
Ψ (firstCols e k)` for `k` in `intGL n O`. Let `i` be in `intGL n O` and `j` in `GL n R`. Suppose
`invLastRows e j = invLastRows e i`. Suppose also that `firstCols e j`, the columns of `j` in the
block `b`, is primitive. Then `Φ (invLastRows e j) = χ (det j) * Ψ (firstCols e j)`. -/
lemma apply_invLastRows_eq_of_isPrimitiveMatrix {R a b n : Type} [CommRing R] [Fintype a]
    [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] {O : Subring R} {e : b ⊕ a ≃ n}
    {χ : MulChar R ℂ} {Φ : Matrix a n R → ℂ} {Ψ : Matrix n b R → ℂ} (hΦΨ : AreMatched O e χ Φ Ψ)
    {i j : GL n R} (hi : i ∈ intGL n O) (h_rows : invLastRows e j = invLastRows e i)
    (hj_prim : IsPrimitiveMatrix O (firstCols e j)) :
    Φ (invLastRows e j) = χ j.val.det * Ψ (firstCols e j) := by
  classical
  -- Both blocks of columns span the kernel of the common rows, so they differ by some `g`.
  have h_span {k l : GL n R} (hkl : invLastRows e l = invLastRows e k) :
      firstCols e l * (invFirstRows e l * firstCols e k) = firstCols e k :=
    firstCols_mul_invFirstRows_mul e l (by rw [hkl, invLastRows_mul_firstCols])
  have h_inv {k l : GL n R} (hkl : invLastRows e l = invLastRows e k) :
      invFirstRows e k * firstCols e l * (invFirstRows e l * firstCols e k) = 1 := by
    rw [Matrix.mul_assoc, h_span hkl, invFirstRows_mul_firstCols]
  let g : GL b R := ⟨invFirstRows e j * firstCols e i, invFirstRows e i * firstCols e j,
    h_inv h_rows.symm, h_inv h_rows⟩
  have h_cols : firstCols e j * g.val = firstCols e i := h_span h_rows
  -- `g` is integral, since it carries primitive columns to primitive columns.
  have hg : g ∈ intGL b O := by
    rw [← isPrimitiveMatrix_iff_mem_intGL, ← hj_prim.mul_iff, h_cols]
    exact isPrimitiveMatrix_firstCols e hi
  -- By `det_fromRows_invLastRows`, the determinant of the rows `invFirstRows e j` stacked on the
  -- common rows times `det j` is `1`, and times `det i` is `det g`.
  have h_det : i.val.det = j.val.det * g.val.det := by
    let s : Matrix n n R := ((invFirstRows e j).fromRows (invLastRows e i)).submatrix e.symm id
    have h_j : s.det * j.val.det = 1 := by
      simp only [s, ← h_rows, det_fromRows_invLastRows, invFirstRows_mul_firstCols, det_one]
    have h_i : s.det * i.val.det = g.val.det := det_fromRows_invLastRows e i (invFirstRows e j)
    rw [← h_i, ← mul_assoc, mul_comm j.val.det, h_j, one_mul]
  calc Φ (invLastRows e j)
    _ = χ j.val.det * (Ψ (firstCols e j * g.val) * χ g.val.det) := by
      rw [h_rows, hΦΨ.apply_eq i hi, h_cols, h_det, map_mul, mul_right_comm, mul_assoc]
    _ = χ j.val.det * Ψ (firstCols e j) := by rw [hΦΨ.right_mul g hg]

variable {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n]
  [DecidableEq n] {F : Type} [SemilocalField F] {χ : MulChar F ℂ} {e : b ⊕ a ≃ n}
  {Φ : Matrix a n F → ℂ} {Ψ : Matrix n b F → ℂ}

/-- If `Φ` and `Ψ` are matched functions over the ring of integers `O` of `F` (`AreMatched`), then
`y ↦ Φ yᵀ` vanishes off the primitive matrices (integral, with an integral left inverse). -/
lemma isPrimitiveMatrix_of_apply_transpose_ne_zero (hΦΨ : AreMatched O e χ Φ Ψ) (y : Matrix n a F)
    (hy : Φ yᵀ ≠ 0) : IsPrimitiveMatrix O y :=
  (exists_eq_invLastRows_iff_isPrimitiveMatrix e yᵀ).1 (hΦΨ.supp_left yᵀ hy)

/-- Let `F` be a semilocal field with ring of integers `O` (`SemilocalField.O`), and `χ` a tame
character of `F`. Let `e : b ⊕ a ≃ n` mark `b` as the first and `a` as the last indices. Let `Φ` and
`Ψ` be matched functions over `O` (`AreMatched`): they vanish off the rows `a` of `k⁻¹`
(`invLastRows e k`) and off the columns `b` of `k` (`firstCols e k`), for `k` in `GL n O`, and `Φ
(invLastRows e k) = χ (det k) * Ψ (firstCols e k)`. If `Ψ` is locally constant, so is `y ↦ Φ yᵀ`. -/
lemma isLocallyConstant_comp_transpose (hχ : TameLocalChar χ) (hΦΨ : AreMatched O e χ Φ Ψ)
    (hΨ : IsLocallyConstant Ψ) : IsLocallyConstant fun y : Matrix n a F ↦ Φ yᵀ := by
  -- The function vanishes off the primitive matrices. These form an open set, the image of the
  -- compact `intGL n O` under `k ↦ (invLastRows e k)ᵀ`, and the pullback of the function to
  -- `intGL n O` is the locally constant `G`.
  intro s
  let G : GL n F → ℂ := fun k ↦ Ψ (firstCols e k) / invOnUnits χ k.val.det
  have hG : IsLocallyConstant G := (hΨ.comp_continuous (by fun_prop)).div
    (hχ.isLocallyConstant_invOnUnits.comp_continuous Units.continuous_val.matrix_det)
  have hΦG (k : GL n F) (hk : k ∈ intGL n O) : Φ (invLastRows e k) = G k := by
    obtain ⟨-, h_unit⟩ :=
      isPrimitiveMatrix_iff_int_and_unit_det.1 ((isPrimitiveMatrix_iff_mem_intGL k).2 hk)
    have h_inv : invOnUnits χ k.val.det = (χ k.val.det)⁻¹ := by rw [invOnUnits, ite_eq_left h_unit]
    simp only [G, h_inv, hΦΨ.apply_eq k hk, div_inv_eq_mul, mul_comm]
  -- The preimage of `s` is the open set `U` less the closed set `C` of primitive matrices at which
  -- the value lies outside `s`.
  let U : Set (Matrix n a F) := {y | IsPrimitiveMatrix O y} ∪ (fun _ ↦ (0 : ℂ)) ⁻¹' s
  let C : Set (Matrix n a F) := (fun k ↦ (invLastRows e k)ᵀ) '' ({k | k ∈ intGL n O} \ G ⁻¹' s)
  have hU : IsOpen U := isClopen_setOf_isPrimitiveMatrix.isOpen.union (IsLocallyConstant.zero s)
  have h_compact : IsCompact ({k : GL n F | k ∈ intGL n O} \ G ⁻¹' s) :=
    (isCompact_intGL isCompact_O).diff (hG s)
  have hC : IsClosed C := (h_compact.image_of_continuous fun k ↦ (invLastRows e k)ᵀ).isClosed
  have mem_C (y : Matrix n a F) : y ∈ C ↔ IsPrimitiveMatrix O y ∧ Φ yᵀ ∉ s := by
    constructor
    · rintro ⟨k, ⟨hk, hks⟩, rfl⟩
      refine ⟨(exists_eq_invLastRows_iff_isPrimitiveMatrix e _).1 ⟨k, hk, rfl⟩, ?_⟩
      rwa [transpose_transpose, hΦG k hk]
    · rintro ⟨hy, hys⟩
      obtain ⟨k, hk, hyk⟩ : ∃ k ∈ intGL n O, yᵀ = invLastRows e k :=
        (exists_eq_invLastRows_iff_isPrimitiveMatrix e yᵀ).2 hy
      refine ⟨k, ⟨hk, ?_⟩, by simp only [← hyk, transpose_transpose]⟩
      rwa [hyk, hΦG k hk] at hys
  have h_preimage : (fun y : Matrix n a F ↦ Φ yᵀ) ⁻¹' s = U \ C := by
    ext y
    by_cases hy : IsPrimitiveMatrix O y
    · simp [U, mem_C, hy]
    · have h_zero : Φ yᵀ = 0 :=
        not_not.1 (mt (hΦΨ.isPrimitiveMatrix_of_apply_transpose_ne_zero y) hy)
      simp [U, mem_C, hy, h_zero]
  simpa only [h_preimage] using hU.sdiff hC

/-- Let `F` be a semilocal field with ring of integers `O` (`SemilocalField.O`) and `χ` a tame
character of `F`. Let `Φ`, on `a × n` matrices, and a locally constant `Ψ`, on `n × b` matrices, be
matched functions over `O`. Then `(Φ, Ψ)` is a same-section pair (`sameSectionPairs`): both
functions are Schwartz–Bruhat, and for every `k` in `GL n F` the coset sum `localSection` of
`y ↦ Φ yᵀ` at `(invLastRows e k)ᵀ` is `χ (det k)` times that of `Ψ` at `firstCols e k`. -/
lemma mem_sameSectionPairs (hχ : TameLocalChar χ) (hΦΨ : AreMatched (O : Subring F) e χ Φ Ψ)
    (hΨ : IsLocallyConstant Ψ) : (Φ, Ψ) ∈ sameSectionPairs χ e := by
  -- Both functions are locally constant and vanish off the primitive matrices.
  have hΦ_prim : ∀ y : Matrix n a F, Φ yᵀ ≠ 0 → IsPrimitiveMatrix O y :=
    hΦΨ.isPrimitiveMatrix_of_apply_transpose_ne_zero
  have hΨ_prim (y : Matrix n b F) (hy : Ψ y ≠ 0) : IsPrimitiveMatrix O y :=
    (isValuationPair.exists_firstCols_iff e).1 (hΦΨ.supp_right y hy)
  refine mem_sameSectionPairs_iff.2 ⟨(mem_of_support_isPrimitiveMatrix
    (hΦΨ.isLocallyConstant_comp_transpose hχ hΨ) hΦ_prim).transpose_mem_schwartzBruhat,
    mem_of_support_isPrimitiveMatrix hΨ hΨ_prim, fun k ↦ ?_⟩
  -- Each section is one value (`exists_isPrimitiveMatrix_localSection_eq`), at the primitive
  -- matrices `(invLastRows e k)ᵀ * g` and `firstCols e k * u`. These are the blocks (the first
  -- transposed) of one `j ∈ GL_n(F)` with `det j * det g = det k * det u`, and the rows
  -- `invLastRows e j` are also those of an integral `i`.
  obtain ⟨g, hg, section_left⟩ := exists_isPrimitiveMatrix_localSection_eq χ (invLastRows e k)ᵀ
    (hasLeftInv_invLastRows_transpose e k)
  obtain ⟨u, hu, section_right⟩ := exists_isPrimitiveMatrix_localSection_eq χ (firstCols e k)
    ⟨invFirstRows e k, invFirstRows_mul_firstCols e k⟩
  -- Over the subring `⊤` every invertible matrix is integral.
  obtain ⟨j, -, hj_cols, hj_rows, hj_det⟩ : ∃ j ∈ intGL n (⊤ : Subring F),
      firstCols e j = firstCols e k * u.val ∧
      invLastRows e j = (transposeGL g).val * invLastRows e k ∧
      j.val.det * (transposeGL g).val.det = k.val.det * u.val.det :=
    exists_firstCols_eq_mul e k ⊤ u (by simp [mem_intGL]) (transposeGL g) (by simp [mem_intGL])
      (by simp [mem_intGL])
  have hj_rowsT : (invLastRows e j)ᵀ = (invLastRows e k)ᵀ * g.val := by simp [hj_rows]
  obtain ⟨i, hi, hji⟩ :=
    (exists_eq_invLastRows_iff_isPrimitiveMatrix e (invLastRows e j)).2 (by rwa [hj_rowsT])
  calc localSection χ (invLastRows e k)ᵀ (fun y ↦ Φ yᵀ)
    _ = χ g.val.det * Φ (invLastRows e j) := by
      rw [section_left _ hΦ_prim, ← hj_rowsT, transpose_transpose]
    _ = χ (j.val.det * (transposeGL g).val.det) * Ψ (firstCols e j) := by
      simp [hΦΨ.apply_invLastRows_eq_of_isPrimitiveMatrix hi hji (by rwa [hj_cols]), mul_assoc,
        mul_left_comm]
    _ = χ k.val.det * localSection χ (firstCols e k) Ψ := by
      rw [section_right Ψ hΨ_prim, hj_det, hj_cols, map_mul, mul_assoc]

end New.AreMatched

end
