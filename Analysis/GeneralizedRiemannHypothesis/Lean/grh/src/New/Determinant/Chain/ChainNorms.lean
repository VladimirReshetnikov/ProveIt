import New.Determinant.Chain.Moduli
import New.Determinant.Chain.TriangleLifts
import New.Determinant.Chain.TriangleNorms
import New.Determinant.Exchange.OneSquare

/-!
# Norms along the chain of theta lifts and injectivity of ι_ϑ

This file proves the two commutation relations in the squares of the triangle of lifts and
computes the adjoints of descents. With these, the lifts satisfy the conditions
`New.Exchange.IsTriangle`. This file then compares the chain ι_ϑ (`New.Data.lowerChainAtLevel`)
with the weighted chain of the triangle `z = false`. Here J_M is the principal level at the chosen
places `New.Data.chosenPlace`, and Q is the product of the places of the twist ϑ. The weighted
chain `New.Exchange.weightedChain` is the composite of the lifts `New.Data.triangleLift`, the n-th
multiplied by N_n = `New.Data.triangleGLCard` false ϑ n, an order of GL over a residue ring.

The node `(i, n)` of a triangle is the space of the interval `[i + 1, i + n]`: it has the stem and
the blocks `i + 1, …, i + n`. The nodes `(i, 0)` are the empty intervals; they carry the space at
`(0, 0)` negated `i` times. The lift `triangleLift` goes along a right pair and adds the last block.
The descent `triangleTransposedLift` is a transposed lift along a left pair and removes the first
block; it stands for the adjoint of the map that adds this block. The ascent `triangleReversedLift`
is a transposed lift along the reversed pair and adds the first block. The flag `z = false` selects
the chain Y₀, …, Y_m, and `z = true` the second chain, which is untwisted, has blocks of length
`t - 1` and starts from Y₀ plus a line.

## Main definitions and results

* `New.Data.exists_triangleLift_triangleTransposedLift_comm`,
  `New.Data.exists_triangleTransposedLift_adjoint_comm`: the two commutation relations, with the
  moduli of their constants.
* `New.Data.exists_isTriangle`: with suitable descents these data satisfy the conditions
  `New.Exchange.IsTriangle`; for `z = false` also `New.Exchange.HasSquareModuli`, with the ratios of
  Hecke values `New.Data.quotientRatio` as moduli.
* `New.Data.inner_lowerChainAtLevel`: inner products of lifts are a multiple of those along the
  chain.
* `New.Data.lowerChainAtLevel_injective`: ι_ϑ is injective, because the chain is.

Notions from other files:
* `New.Data.RowIndex`, `New.Data.Y`: The basis index set of Y₀: e₁, …, e_ϱ, the indices of X₀, a
  middle vector, and e*₁, …, e*_ϱ. The basis index set of Y_j: the block `RowIndex`, then j blocks
  of t indices each.
* `New.Data.MFoldTwist`: a twist ϑ whose tame part ψ has ψ_wⁿ non-trivial for all places w in its
  set Q and 1 ≤ n ≤ m.
* `New.Data.chosenLevel`, `New.Data.lastLevel`: The level J_M consists of the elements of
  K₀ = `New.stdLevel` that are 1 modulo the chosen places `New.Data.chosenPlace`. The level J_ϑ(Y_m)
  on Y_m consists of those elements of J_M that are block upper triangular modulo Q.
* `New.Data.triangleModulus`, `New.Data.triangleGLCard`: the modulus 𝔪 of the triangle, and the
  order of the general linear group of a node modulo 𝔪. A lift times this order is the lift for the
  measure that gives the principal level of 𝔪 the volume 1.
* `New.Data.HasAbsUpToNormPower c f`: `‖c ϑ‖²` is `(f ϑ)²` times a constant, possibly zero, and a
  fixed integral power of the norm of Q.

## Relation to the literature

The chain of m theta lifts from U(Y_0) to the definite U(Y_m), mostly outside the range of Rallis's
formula, is injective at level J_M. On target forms its Gram form is that of a product of m Hecke
operators times a scalar whose modulus is a product of ratios of Hecke values. The norm and
injectivity of a single cuspidal theta lift, also below Weil's range, are known in the literature.
Related work: Gan–Qiu–Takeda, Regularized Siegel–Weil formula and Rallis inner product formula (Thm
1.3), 2014; Bruinier–Funke, Injectivity of the Kudla–Millson lift, 2010; He, Compositions of theta
correspondences, 2005.
-/

noncomputable section

section TriangleArrows

open MeasureTheory Matrix Complex ComplexConjugate Fintype LinearMap

namespace New

open Rows Exchange WeilData Space Modulus SiegelWeil ComplexInnerProductSpace

namespace Data

attribute [local implicit_reducible] Data.GridIndex BlockIndex kernelPair

/-! ### The two squares -/

/-- The two diagonals of the square with nodes `(i, n + 1)`, `(i, n + 2)`, `(i + 1, n)` and
`(i + 1, n + 1)` have the same number of negative signs. -/
lemma negCount_gridSigns_add {P : Parameters} (D : Data P) (z : Bool) {i n : ℕ} :
    negCount (D.gridSigns z i 0 (n + 1)) + negCount (D.gridSigns z (i + 1) 0 (n + 1)) =
      negCount (D.gridSigns z i 0 (n + 1 + 1)) + negCount (D.gridSigns z (i + 1) 0 n) := by
  simp_rw [negCount_gridSigns_eq_sum, ← Finset.sum_add_distrib]
  -- compare the parities of the exponents of `-1` entry by entry
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  grind [entrySign_eq_ite]

/-- Fewer than half of the signs `gridSigns` at the node `(0, n + 1)`, taken with the offsets `i`
and `i + 1`, are negative; both have the index set `GridIndex z 0 (n + 1)`. Only base entries can be
negative: the added blocks have sign `+1`. -/
lemma negCount_gridSigns_add_lt {P : Parameters} (D : Data P) (z : Bool) {i n : ℕ} :
    negCount (D.gridSigns z i 0 (n + 1)) + negCount (D.gridSigns z (i + 1) 0 (n + 1)) <
      card (D.GridIndex z 0 (n + 1)) := by
  have h_neg (j : ℕ) : negCount (D.gridSigns z j 0 (n + 1)) ≤ D.r + z.toNat := by
    simpa [negCount_gridSigns_eq_sum] using Finset.card_filter_le (.range (D.r + z.toNat)) _
  have h_block : D.r + z.toNat < D.t - z.toNat := by grind [D.r_add_six_le_t, z.toNat_le]
  rw [card_gridIndex]
  nlinarith [h_neg i, h_neg (i + 1)]

/-- The ranks along a row of the triangle form an arithmetic progression. -/
lemma card_gridIndex_add_card_gridIndex {P : Parameters} (D : Data P) (z : Bool) (n : ℕ) :
    card (D.GridIndex z 0 n) + card (D.GridIndex z 0 (n + 1 + 1)) =
      2 * card (D.GridIndex z 0 (n + 1)) := by
  simp +arith [card_gridIndex, add_mul]

/-- Let `1 ≤ j ≤ D.m` (`LiftIndex`), and let `quotientPair j` be the pair of the quotient of two
characters of the chain at distance `j`, of weight `-c τ = -j * D.gap` at the place `τ`. The rank in
column `j` of the triangle is at most `c τ`. -/
lemma card_gridIndex_le_quotientPair_negWeight {P : Parameters} (D : Data P) (z : Bool)
    (j : D.LiftIndex) (τ : NumberField.InfinitePlace D.E) :
    card (D.GridIndex z 0 j) ≤ (D.quotientPair j).negWeight τ := by
  change card (D.GridIndex z 0 j) ≤ j.val * (2 * D.halfGap)
  rw [card_gridIndex]
  nlinarith [D.k_add_t_add_one_le_halfGap, D.r_add_six_le_t, j.prop.1, z.toNat_le,
    D.t.sub_le z.toNat]

/-- The character of a square of the triangle `z`. Let `1 ≤ n + 1 ≤ D.m` (`LiftIndex`), and let `p`,
`q`, `r` be index types of hermitian spaces, with `card p + card q = card r` even. The character
`gridChar` of U(1)(𝔸) that the lift adding the block `n + i + 2` has at an end of index type `p`,
times the character `leftPairChar` of the left pairs of row `i` at an end of index type `q`, is
`ν * ϑ ^ (n + 1)` times the splitting character `upsilonU1` to the power `card r / 2` (`rankTwist`).
Here `ν`, the character of `quotientPair (n + 1)`, is the quotient of `untwistedLiftChar` at
`j + n + 1` by that at `j`, for any `j`, and `ϑ` is replaced by the trivial twist if `z = true`
(`triangleTwist`). -/
lemma gridChar_mul_leftPairChar {P : Parameters} (D : Data P) (z : Bool) (ϑ : D.MFoldTwist)
    {i n : ℕ} (hn : n + 1 ∈ D.LiftIndex) {p q r : Type} [Fintype p] [Fintype q] [Fintype r]
    (h_card : card p + card q = card r) (h_even : Even (card r)) :
    D.gridChar ϑ (!z) (n + i + 1) p * D.leftPairChar z ϑ i q =
      rankTwist ((D.quotientPair ⟨n + 1, hn⟩).character * (triangleTwist ϑ z).toAutChar ^ (n + 1))
        r := by
  -- Written additively, the identity compares the exponent of each basic character.
  apply_fun Additive.ofMul
  cases z
  all_goals
    simp [quotientPair, leftPairChar, rankTwist, gridChar, liftChar, untwistedLiftChar,
      TameChar.pow,
      toAutChar_one_and_toTwist_one_and_Q_one]
    match_scalars <;> grind

/-- The square law for point data around the square with nodes `(i, n + 1)`, `(i, n + 2)`,
`(i + 1, n)` and `(i + 1, n + 1)` of the triangle `z`, for `i + n + 1 < D.m`. The transposed lifts
`triangleTransposedLift` go from `(i, j + 1)` to `(i + 1, j)` and are formed with polynomials `Φ₀`,
`Φ₁` that make edges along the left pairs at `(i, n)`, `(i, n + 1)` (`IsLeftPair`). Let `ν` be the
character of `quotientPair (n + 1)`, of weight `-negWeight`, replace `ϑ` by the trivial twist if
`z = true`, and let `(ν * ϑ ^ (n + 1))⁻¹` be tamely ramified exactly at the modulus, where it is
given by the character `χ ϑ` of the residue ring (`IsTameFor`). Apply a linear form `L` to the two
composites around the square, each edge having as datum the indicator function of a block of the
matrix `ξ` or `η`. These functions `A ξ`, `B η` satisfy `SquareLaw` with constant `κ / c`: both
transform by `χ ϑ ∘ det`, and `∑ g B = κ / c * ∑ f A` whenever `f`, `g` are supported on the last
rows of `k⁻¹` and the first columns of `k`, for invertible `k`, with values there in the ratio
`χ ϑ (det k)` (`AreMatched`); `swapFirstTwo` reorders the blocks of indices. Here `‖c‖ ^ 2` is a
constant times `lValueProd`, the product of the `|L(k, (ν * ϑ ^ (n + 1))⁻¹)| ^ 2` off the modulus
for `k` from `1` to the block length `D.t - z.toNat`, times a power of the residue cardinalities at
the modulus. -/
lemma exists_squareLaw_triangleTransposedLift {P : Parameters} (D : Data P) (z : Bool) {i n : ℕ}
    (h_lt : i + (n + 1) < D.m) (hn : n + 1 ∈ D.LiftIndex)
    {Φ₀ : D.EdgePoly z n (n + 1)} {Φ₁ : D.EdgePoly z (n + 1) (n + 1 + 1)}
    (h_pair₀ : D.IsLeftPair z i n Φ₀) (h_pair₁ : D.IsLeftPair z i (n + 1) Φ₁)
    {χ : ∀ ϑ : D.MFoldTwist, MulChar (triangleModulus z ϑ).ResidueRing ℂ}
    (h_tame : ∀ ϑ : D.MFoldTwist, IsTameFor (triangleModulus z ϑ)
      ((D.quotientPair ⟨n + 1, hn⟩).character * (triangleTwist ϑ z).toAutChar ^ (n + 1))⁻¹
      (fun τ : NumberField.InfinitePlace D.E ↦ (D.quotientPair ⟨n + 1, hn⟩).negWeight τ) (χ ϑ)) :
    ∃ (C : ℝ) (κ : ℂ), ∀ ϑ : D.MFoldTwist, ∃ c ≠ (0 : ℂ),
      ‖c‖ ^ 2 = C * lValueProd (triangleModulus z ϑ).places
        ((D.quotientPair ⟨n + 1, hn⟩).character * (triangleTwist ϑ z).toAutChar ^ (n + 1))⁻¹
        (D.t - z.toNat) ∧
      ∀ (y : D.TriangleForm z i (n + 1)) (L : D.TriangleForm z (i + 1) (n + 1) →ₗ[ℂ] ℂ),
        SquareLaw (χ ϑ)
          (swapFirstTwo : D.GridIndex z 0 n ⊕ D.GridIndex z 0 (n + 1 + 1) ≃
            D.GridIndex z 0 (n + 1) ⊕ D.GridIndex z 0 (n + 1)) (κ / c)
          (fun ξ ↦ L (D.triangleTransposedLift z ϑ i (n + 1) Φ₁ (Pi.single ξ.toCols₂ 1)
            (D.triangleDatumLift z ϑ i (n + 1) (Pi.single ξ.toCols₁ 1) y)))
          (fun η ↦ L (D.triangleDatumLift z ϑ (i + 1) n (Pi.single η.toRows₂ 1)
            (D.triangleTransposedLift z ϑ i n Φ₀ (Pi.single η.toRows₁ 1) y))) := by
  have h_upper := D.isEdgeFamily_triangleKernel z h_lt
  -- the upper and the lower lift have the same character, of index `n + i + 1`
  simp only [triangleDatumLift, n.succ_add] at h_upper ⊢
  refine one_square_identity_of_isEdgeFamily _ _ _ _ h_pair₁ h_upper
    (D.isEdgeFamily_triangleKernel z (i := i + 1) (by lia)) h_pair₀ swapFirstTwo ?signs
    (D.t - z.toNat) ?rank ?range (fun τ ↦ ?weight) h_tame ?chars
  case signs => rw [negCount_sumElim, negCount_gridSigns_add]
  case rank => simp +arith [card_gridIndex, add_mul]
  case range => grind [negCount_sumElim, card_sum, D.negCount_gridSigns_add_lt z (i := i) (n := n)]
  case weight =>
    grind [card_sum, D.card_gridIndex_le_quotientPair_negWeight z ⟨n + 1, hn⟩ τ,
      D.card_gridIndex_add_card_gridIndex z n]
  case chars =>
    intro ϑ p q _ _ h_card
    rw [inv_inv]
    exact D.gridChar_mul_leftPairChar z ϑ hn (by simpa using h_card) (by simp)

/-- The first commutation relation, in the square with nodes `(i, n + 1)`, `(i, n + 2)`,
`(i + 1, n)`, `(i + 1, n + 1)` of the triangle `z`, for `i + n + 1 < D.m`, the number of lifts of
the data `D`. The transposed lifts `triangleTransposedLift` go from `(i, j + 1)` to `(i + 1, j)` and
are formed with polynomials at infinity `Φ₀`, `Φ₁` that make edges along the left pairs at `(i, n)`,
`(i, n + 1)` (`IsLeftPair`). For every twist `ϑ` and function `Ψ` on matrices modulo the modulus,
the transposed lift with datum `Ψ` followed by the lift, weighted by the group order
`triangleGLCard z ϑ n`, is a multiple of the lift followed by the transposed lift with datum
`nextDatum Ψ`, weighted by `triangleGLCard z ϑ (n + 2)`. The factor is `conj (β ϑ)⁻¹`, which is `0`
where `β ϑ = 0`. For `z = false`, `‖β ϑ‖²` is the square of `quotientRatio`, a product of ratios of
Hecke values, times a constant and a fixed power of the norm of the modulus Q of `ϑ`. -/
theorem exists_triangleLift_triangleTransposedLift_comm {P : Parameters} (D : Data P) (z : Bool)
    {i n : ℕ} (h_lt : i + (n + 1) < D.m) {Φ₀ : D.EdgePoly z n (n + 1)}
    {Φ₁ : D.EdgePoly z (n + 1) (n + 1 + 1)} (h_pair₀ : D.IsLeftPair z i n Φ₀)
    (h_pair₁ : D.IsLeftPair z i (n + 1) Φ₁) :
    ∃ β : D.MFoldTwist → ℂ,
      (∀ (ϑ : D.MFoldTwist) (Ψ : D.EdgeDatum z ϑ n (n + 1)) (y : D.TriangleForm z i (n + 1))
          (x : D.TriangleForm z (i + 1) (n + 1)),
        triangleGLCard z ϑ n * ⟪x, D.triangleLift z ϑ (i + 1) n
          (D.triangleTransposedLift z ϑ i n Φ₀ Ψ y)⟫ =
          conj (β ϑ)⁻¹ * triangleGLCard z ϑ (n + 2) *
            ⟪x, D.triangleTransposedLift z ϑ i (n + 1) Φ₁ (nextDatum Ψ)
              (D.triangleLift z ϑ i (n + 1) y)⟫) ∧
      (z = false → D.HasAbsUpToNormPower β (D.quotientRatio (i + 1) (i + 1 + n + 1))) := by
  -- Expand both finite data in point data, for which the square law holds, and apply
  -- `SquareLaw.sum_eq_nextDatum`.
  let dist : D.LiftIndex := ⟨n + 1, n.succ_pos, by omega⟩
  let ν : D.CriticalPair := D.quotientPair dist
  choose C κ c _hc_ne hc_norm h_law using
    D.exists_squareLaw_triangleTransposedLift z h_lt dist.prop h_pair₀ h_pair₁
      fun ϑ : D.MFoldTwist ↦ ν.isTameFor_inv_mul_pow (isRamified_quotientPair dist)
        (D.triangleExponent z) dist (triangleTwist ϑ z)
  refine ⟨fun ϑ ↦ conj (c ϑ / κ), fun ϑ Ψ y x ↦ ?_, ?_⟩
  · let R : Type := (triangleModulus z ϑ).ResidueRing
    have h_points :
        triangleGLCard z ϑ n * ∑ η : Matrix (D.GridIndex z 0 (n + 1)) (D.GridIndex z 0 n) R,
            Ψ η * ⟪x, D.triangleLift z ϑ (i + 1) n
              (D.triangleTransposedLift z ϑ i n Φ₀ (Pi.single η 1) y)⟫ =
          κ / c ϑ * triangleGLCard z ϑ (n + 2) *
            ∑ ξ : Matrix (D.GridIndex z 0 (n + 1 + 1)) (D.GridIndex z 0 (n + 1)) R, nextDatum Ψ ξ *
              ⟪x, D.triangleTransposedLift z ϑ i (n + 1) Φ₁ (Pi.single ξ 1)
                (D.triangleLift z ϑ i (n + 1) y)⟫ := by
      -- the index types of the nodes unfold to the sum types of `sum_eq_nextDatum`
      simpa [triangleLift_eq_triangleDatumLift] using! (h_law ϑ y (innerₛₗ ℂ x)).sum_eq_nextDatum Ψ
    rw [D.triangleTransposedLift_eq_sum z ϑ Φ₀, D.triangleTransposedLift_eq_sum z ϑ Φ₁]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right, map_inv₀, conj_conj, inv_div]
    exact h_points
  · rintro rfl
    have h_ratio : D.quotientRatio (i + 1) (i + 1 + n + 1) =
        fun ϑ ↦ D.lRatioProd ν.character ν.z (ϑ.pow dist) :=
          funext (quotientRatio_add_eq_lRatioProd dist (i + 1))
    rw [h_ratio]
    refine ν.hasAbsUpToNormPower_of_norm_sq_eq_lValueProd 1 dist (C := C / ‖κ‖ ^ 2) fun ϑ ↦ ?_
    have h_norm : ‖c ϑ‖ ^ 2 =
        C * lValueProd (D.twistModulus ϑ 1).places (ν.character * ϑ.toAutChar ^ dist.val)⁻¹ ν.z :=
          hc_norm ϑ
    rw [RCLike.norm_conj, norm_div, div_pow, h_norm, div_mul_eq_mul_div]

/-- The square law for point data in the square with reversed pairs of the triangle `z = false` (the
twisted one), for `i + n + 1 < D.m`. The reversed lifts `triangleReversedLift` go from `(i + 1, j)`
to `(i, j + 1)` and are formed with polynomials `Φ₀`, `Φ₁` that make edges along the reversed pairs
at `(i, n)`, `(i, n + 1)` (`IsReversedPair`). Let `ν` be the character of `quotientPair (n + 1)`, of
weight `-negWeight`, and let `(ν * ϑ ^ (n + 1))⁻¹` be tamely ramified exactly at the modulus, where
it is given by the character `χ ϑ` of the residue ring (`IsTameFor`). Apply a linear form `L` to the
two composites from `(i + 1, n)` to `(i, n + 2)`, each edge having as datum the indicator function
of a block of the matrix `ξ` or `η`. These functions `A ξ`, `B η` satisfy `SquareLaw` with constant
`κ / c`: both transform by `χ ϑ ∘ det`, and `∑ g B = κ / c * ∑ f A` for all functions `f`, `g`
matched by `χ ϑ` (`AreMatched`). Here `‖c‖ ^ 2` does not depend on `ϑ`. -/
lemma exists_squareLaw_triangleReversedLift {P : Parameters} (D : Data P) {i n : ℕ}
    (h_lt : i + (n + 1) < D.m) (hn : n + 1 ∈ D.LiftIndex)
    {Φ₀ : D.EdgePoly false (n + 1) n} {Φ₁ : D.EdgePoly false (n + 1 + 1) (n + 1)}
    (h_rev₀ : D.IsReversedPair false i n Φ₀) (h_rev₁ : D.IsReversedPair false i (n + 1) Φ₁)
    {χ : ∀ ϑ : D.MFoldTwist, MulChar (triangleModulus false ϑ).ResidueRing ℂ}
    (h_tame : ∀ ϑ : D.MFoldTwist, IsTameFor (triangleModulus false ϑ)
      ((D.quotientPair ⟨n + 1, hn⟩).character * ϑ.toAutChar ^ (n + 1))⁻¹
      (fun τ : NumberField.InfinitePlace D.E ↦ (D.quotientPair ⟨n + 1, hn⟩).negWeight τ) (χ ϑ)) :
    ∃ (C : ℝ) (κ : ℂ), ∀ ϑ : D.MFoldTwist, ∃ c ≠ (0 : ℂ), ‖c‖ ^ 2 = C ∧
      ∀ (y : D.TriangleForm false (i + 1) n) (L : D.TriangleForm false i (n + 1 + 1) →ₗ[ℂ] ℂ),
        SquareLaw (χ ϑ)
          (swapFirstTwo : D.GridIndex false 0 (n + 1) ⊕ D.GridIndex false 0 (n + 1) ≃
            D.GridIndex false 0 n ⊕ D.GridIndex false 0 (n + 1 + 1)) (κ / c)
          (fun ξ ↦ L (D.triangleReversedLift false ϑ i (n + 1) Φ₁ (Pi.single ξ.toCols₂ 1)
            (D.triangleDatumLift false ϑ (i + 1) n (Pi.single ξ.toCols₁ 1) y)))
          (fun η ↦ L (D.triangleDatumLift false ϑ i (n + 1) (Pi.single η.toRows₂ 1)
            (D.triangleReversedLift false ϑ i n Φ₀ (Pi.single η.toRows₁ 1) y))) := by
  have h_ranks : card (D.GridIndex false 0 n ⊕ D.GridIndex false 0 (n + 1 + 1)) =
      2 * card (D.GridIndex false 0 (n + 1)) := by
    rw [card_sum, card_gridIndex_add_card_gridIndex]
  have h_upper := D.isEdgeFamily_triangleKernel false h_lt
  -- the upper and the lower lift have the same character, of index `n + i + 1`
  simp only [triangleDatumLift, n.succ_add] at h_upper ⊢
  have h_square := one_square_identity_of_isEdgeFamily (gridSpace ..) (gridSpace ..) (gridSpace ..)
    (gridSpace ..) h_rev₁
    (D.isEdgeFamily_triangleKernel false (i := i + 1) (by lia)) h_upper h_rev₀ swapFirstTwo ?signs 0
      rfl
    ?range (fun τ ↦ ?weight) h_tame ?chars
  case signs => rw [negCount_sumElim, add_comm, ← negCount_gridSigns_add, add_comm]
  case range =>
    rw [h_ranks, negCount_sumElim, add_comm (negCount _), ← negCount_gridSigns_add]
    linarith [D.negCount_gridSigns_add_lt false (i := i) (n := n)]
  case weight => grind [D.card_gridIndex_le_quotientPair_negWeight false ⟨n + 1, hn⟩ τ]
  case chars =>
    intro ϑ p q _ _ h_card
    rw [inv_inv, ← add_assoc]
    exact D.gridChar_mul_leftPairChar false ϑ hn (by simpa using h_card) (by grind)
  -- the two middle spaces have equal rank, so the product of `L`-values is empty
  have h_empty (S : Set (FinPlace D.E)) (ν : AutChar D.E) : lValueProd S ν 0 = 1 := by
    simp [lValueProd]
  simpa only [h_empty, mul_one] using! h_square

/-- If `‖c ϑ‖ ^ 2` is the inverse of a fixed power of the number of elements of the residue ring of
`triangleModulus false ϑ`, then `c` has modulus `1` in the sense of `HasAbsUpToNormPower`. -/
lemma HasAbsUpToNormPower.of_norm_sq_mul_card_pow_eq_one {P : Parameters} {D : Data P}
    {c : D.MFoldTwist → ℂ} {k : ℕ}
    (hc : ∀ ϑ : D.MFoldTwist, ‖c ϑ‖ ^ 2 * card (triangleModulus false ϑ).ResidueRing ^ k = 1) :
    D.HasAbsUpToNormPower c 1 := by
  refine .of_norm_sq_eq_mul_card_zpow 1 1 (-k) fun ϑ ↦ ?_
  rw [one_mul, _root_.zpow_neg, _root_.zpow_natCast]
  exact eq_inv_of_mul_eq_one_left (hc ϑ)

/-- The commutation relation in the square with reversed pairs of the triangle `z = false` (the
twisted one), for `i + n + 1 < D.m`, the number of lifts of the data `D`. The reversed lifts
`triangleReversedLift` go from `(i + 1, j)` to `(i, j + 1)`. They are formed with polynomials `Φ₀`,
`Φ₁` that make edges along the reversed pairs at `(i, n)`, `(i, n + 1)` (`IsReversedPair`), and with
`fourierDatum`, the Fourier transform of the complex conjugate, of a datum `Ψ` and of its extension
`nextDatum Ψ` to the next column. The reversed lift followed by the lift is `γ ϑ` times the lift
followed by the reversed lift, where `‖γ ϑ‖²` is a constant times a fixed power of the norm of the
modulus Q of the twist `ϑ` (`HasAbsUpToNormPower γ 1`). -/
theorem exists_triangleLift_triangleReversedLift_comm {P : Parameters} (D : Data P) {i n : ℕ}
    (h_lt : i + (n + 1) < D.m) {Φ₀ : D.EdgePoly false (n + 1) n}
    {Φ₁ : D.EdgePoly false (n + 1 + 1) (n + 1)} (h_rev₀ : D.IsReversedPair false i n Φ₀)
    (h_rev₁ : D.IsReversedPair false i (n + 1) Φ₁) :
    ∃ γ : D.MFoldTwist → ℂ, D.HasAbsUpToNormPower γ 1 ∧
      ∀ (ϑ : D.MFoldTwist) (Ψ : D.EdgeDatum false ϑ n (n + 1)) (y : D.TriangleForm false (i + 1) n)
          (x : D.TriangleForm false i (n + 1 + 1)),
        ⟪x, D.triangleLift false ϑ i (n + 1)
          (D.triangleReversedLift false ϑ i n Φ₀ (D.fourierDatum false ϑ Ψ) y)⟫ =
          γ ϑ * ⟪x, D.triangleReversedLift false ϑ i (n + 1) Φ₁
            (D.fourierDatum false ϑ (nextDatum Ψ))
            (D.triangleLift false ϑ (i + 1) n y)⟫ := by
  -- The modulus is squarefree, so the tame character `χ ϑ` is primitive. Expand both Fourier
  -- transforms in point data and apply `SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum`.
  let dist : D.LiftIndex := ⟨n + 1, n.succ_pos, by omega⟩
  let ν : D.CriticalPair := D.quotientPair dist
  let χ (ϑ : D.MFoldTwist) : MulChar (triangleModulus false ϑ).ResidueRing ℂ :=
    ((triangleModulus false ϑ).charOfTamePart (ν.tamePart * ϑ.tamePart ^ (n + 1)))⁻¹
  have h_tame (ϑ : D.MFoldTwist) : IsTameFor (triangleModulus false ϑ)
      (ν.character * ϑ.toAutChar ^ (n + 1))⁻¹ (fun τ ↦ ν.negWeight τ) (χ ϑ) :=
    ν.isTameFor_inv_mul_pow (isRamified_quotientPair dist) 1 dist ϑ
  choose C κ c _hc_ne hc_norm h_law using
    D.exists_squareLaw_triangleReversedLift h_lt dist.prop h_rev₀ h_rev₁ h_tame
  choose γ hγ h_fourier using fun ϑ : D.MFoldTwist ↦
    SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum (D.Y n) (Fin D.t)
      (isPrimitive_primAddChar _)
      (isPrimitiveMulChar_of_isTameFor (h_tame ϑ))
  refine ⟨γ * fun ϑ ↦ κ / c ϑ, ?_, fun ϑ Ψ y x ↦ ?_⟩
  · have h_gauss : D.HasAbsUpToNormPower γ 1 := .of_norm_sq_mul_card_pow_eq_one hγ
    have h_exchange : D.HasAbsUpToNormPower (fun ϑ ↦ κ / c ϑ) 1 :=
      .of_norm_sq_eq_mul_card_zpow 1 (‖κ‖ ^ 2 / C) 0 (by simp [hc_norm, div_pow])
    simpa using h_gauss.mul h_exchange
  · let R : Type := (triangleModulus false ϑ).ResidueRing
    have h_points :
        ∑ η : Matrix (D.GridIndex false 0 n) (D.GridIndex false 0 (n + 1)) R,
            D.fourierDatum false ϑ Ψ η *
              ⟪x, D.triangleLift false ϑ i (n + 1)
                (D.triangleReversedLift false ϑ i n Φ₀ (Pi.single η 1) y)⟫ =
          γ ϑ * (κ / c ϑ) *
            ∑ ξ : Matrix (D.GridIndex false 0 (n + 1)) (D.GridIndex false 0 (n + 1 + 1)) R,
              D.fourierDatum false ϑ (n := n + 1) (n' := n + 1 + 1) (nextDatum Ψ) ξ *
                ⟪x, D.triangleReversedLift false ϑ i (n + 1) Φ₁ (Pi.single ξ 1)
                  (D.triangleLift false ϑ (i + 1) n y)⟫ := by
      -- the index types of the nodes unfold to the sum types of
      -- `exists_sum_matrixFourier_eq_sum_nextDatum`
      simpa [triangleLift_eq_triangleDatumLift] using! h_fourier ϑ Ψ (h_law ϑ y (innerₛₗ ℂ x))
    rw [D.triangleReversedLift_eq_sum false ϑ Φ₀, D.triangleReversedLift_eq_sum false ϑ Φ₁]
    simpa [inner_sum, inner_smul_right] using h_points

/-! ### Adjoints of descents and the triangle conditions -/

/-- The scalar matrix `Modulus.flipScalar` of the modulus of the triangle, a central element of the
finite adelic unitary group of a node in column `n`. Reversing a theta kernel translates by it. -/
abbrev reversalScalar {P : Parameters} (D : Data P) (z : Bool) (ϑ : D.MFoldTwist) (n : ℕ) :
    Gf D.E (D.GridIndex z 0 n) :=
  (triangleModulus z ϑ).flipScalar (D.GridIndex z 0 n)

/-- Reversal of the theta kernel of a left pair of the triangle `z = false` (the twisted one),
between the hermitian spaces `V`, `W` at the nodes `(i + 1, n)`, `(i, n + 1)`, with the characters
`χ ϑ n`, `χ ϑ (n + 1)` given by `leftPairChar`. The kernel `modKernel` depends on a datum `Ψ`, a
function on matrices modulo the modulus (`EdgeDatum`), and a polynomial `Φ` at infinity
(`EdgePoly`). Its conjugate is `τ ϑ ≠ 0` times the kernel from `W` to `V` with datum
`fourierDatum Ψ`, the Fourier transform of the conjugate of `Ψ`, and with the signed transpose
`flipPoly` of the conjugate of `Φ`, translated by the scalar matrix `reversalScalar`. Here `‖τ ϑ‖²`
is a constant times a fixed power of the norm of the modulus Q of `ϑ`. -/
lemma exists_conj_modKernel_leftPair_eq {P : Parameters} (D : Data P) (i n : ℕ) :
    let V : Space D.E (D.GridIndex false 0 n) (D.gridSigns false (i + 1) 0 n) :=
      D.gridSpace (i + 1) false 0 n
    let W : Space D.E (D.GridIndex false 0 (n + 1)) (D.gridSigns false i 0 (n + 1)) :=
      D.gridSpace i false 0 (n + 1)
    let χ (ϑ : D.MFoldTwist) (j : ℕ) : AutChar D.E :=
      D.leftPairChar false ϑ i (D.GridIndex false 0 j)
    ∃ τ : D.MFoldTwist → ℂ, D.HasAbsUpToNormPower τ 1 ∧ (∀ ϑ : D.MFoldTwist, τ ϑ ≠ 0) ∧
      ∀ (ϑ : D.MFoldTwist) (Ψ : D.EdgeDatum false ϑ n (n + 1)) (Φ : D.EdgePoly false n (n + 1))
          (g : New.G D.E (D.gridSigns false (i + 1) 0 n))
          (h : New.G D.E (D.gridSigns false i 0 (n + 1))),
        conj (modKernel V W (χ ϑ n) (χ ϑ (n + 1)) (triangleModulus false ϑ) Ψ Φ g h) =
          τ ϑ * modKernel W V (χ ϑ (n + 1)) (χ ϑ n) (triangleModulus false ϑ)
            (D.fourierDatum false ϑ Ψ) (flipPoly (D.gridSigns false (i + 1) 0 n)
              (D.gridSigns false i 0 (n + 1)) (Φ.map conj)) h
                (g * (1, D.reversalScalar false ϑ n)) := by
  intro V W χ
  choose τ h_norm h_swap using fun ϑ : D.MFoldTwist ↦
    exists_conj_modKernel_eq_swap (triangleModulus false ϑ) V W (χ ϑ n) (χ ϑ (n + 1))
  refine ⟨τ, .of_norm_sq_mul_card_pow_eq_one h_norm, fun ϑ ↦ ?_, h_swap⟩
  simpa using left_ne_zero_of_mul_eq_one (h_norm ϑ)

/-- In the triangle `z = false` (the twisted one), let `Φ` make an edge along the left pair from
`(i + 1, n)` to `(i, n + 1)` (`IsLeftPair`) and `Φ'` in the other direction (`IsReversedPair`). The
adjoint of `triangleTransposedLift` with `Φ` and datum `Ψ`, from forms at `(i, n + 1)` to forms at
`(i + 1, n)`, is `c ϑ` times the following map: right translation (`triangleRep`) by the inverse of
the scalar matrix `reversalScalar`, then `triangleReversedLift` with `Φ'` and `fourierDatum Ψ`, the
Fourier transform of the conjugate of `Ψ`. Here `‖c ϑ‖²` is a constant times a fixed power of the
norm of the modulus Q of the twist `ϑ`. -/
lemma exists_inner_triangleTransposedLift_eq {P : Parameters} (D : Data P) {i n : ℕ}
    {Φ : D.EdgePoly false n (n + 1)} {Φ' : D.EdgePoly false (n + 1) n}
    (hΦ : D.IsLeftPair false i n Φ) (hΦ' : D.IsReversedPair false i n Φ') :
    ∃ c : D.MFoldTwist → ℂ, D.HasAbsUpToNormPower c 1 ∧
      ∀ (ϑ : D.MFoldTwist) (Ψ : D.EdgeDatum false ϑ n (n + 1)) (x : D.TriangleForm false i (n + 1))
          (y : D.TriangleForm false (i + 1) n),
        ⟪D.triangleTransposedLift false ϑ i n Φ Ψ x, y⟫ =
          c ϑ * ⟪x, D.triangleReversedLift false ϑ i n Φ' (D.fourierDatum false ϑ Ψ)
            (D.triangleRep false (i + 1) n (D.reversalScalar false ϑ n)⁻¹ y)⟫ := by
  -- Reverse the kernel of the descent, and trade the transposed polynomial for `Φ'` and `κ`.
  obtain ⟨turn, h_turn_modulus, -, h_turn⟩ := D.exists_conj_modKernel_leftPair_eq i n
  let Q : D.EdgePoly false (n + 1) n :=
    flipPoly (D.gridSigns false (i + 1) 0 n) (D.gridSigns false i 0 (n + 1)) (Φ.map conj)
  obtain ⟨κ, hκ⟩ := hΦ'.petersson_lift_eq_mul_inner_modTransposedLift Q
  refine ⟨turn * fun _ ↦ conj κ, by simpa using h_turn_modulus.mul (.const (conj κ)),
    fun ϑ Ψ x y ↦ ?_⟩
  let u : Gf D.E (D.GridIndex false 0 n) := D.reversalScalar false ϑ n
  let y' : D.TriangleForm false (i + 1) n := D.triangleRep false (i + 1) n u⁻¹ y
  -- `L` is the lift of the conjugate of `x` along the reversed pair
  let L : New.G D.E (D.gridSigns false (i + 1) 0 n) → ℂ := Space.lift
    (pairThetaKer (D.gridSpace i false 0 (n + 1)) (D.gridSpace (i + 1) false 0 n)
      (D.leftPairChar false ϑ i (D.GridIndex false 0 (n + 1)))
      (D.leftPairChar false ϑ i (D.GridIndex false 0 n)))
    (modDatum _ _ (triangleModulus false ϑ) (D.fourierDatum false ϑ Ψ) (Fock.polyVector _ Q))
    (star x.val)
  have h_conj (g : New.G D.E (D.gridSigns false (i + 1) 0 n)) :
      conj ((D.triangleTransposedLift false ϑ i n Φ Ψ x).val g) = turn ϑ * L (g * (1, u)) := by
    refine (congrArg conj (hΦ.modTransposedLift_apply _ _ ϑ Ψ x g)).trans ?_
    simp [L, Q, u, lift_modDatum_apply, ← integral_conj, h_turn, mul_assoc, integral_const_mul]
  have h_trade : (D.gridSpace (i + 1) false 0 n).petersson y'.val (star L) =
      κ * ⟪D.triangleReversedLift false ϑ i n Φ' (D.fourierDatum false ϑ Ψ) y', x⟫ :=
    hκ ϑ _ _ (triangleModulus false ϑ) (D.fourierDatum false ϑ Ψ) x y'
  calc ⟪D.triangleTransposedLift false ϑ i n Φ Ψ x, y⟫
      = ⟪formRep _ _ u⁻¹ (D.triangleTransposedLift false ϑ i n Φ Ψ x), y'⟫ :=
        (inner_formRep u⁻¹ _ y).symm
    _ = turn ϑ * (D.gridSpace (i + 1) false 0 n).petersson (star L) y'.val := by
      simp [inner_eq_petersson, petersson, formRep_apply, h_conj, mul_assoc, integral_const_mul,
        Prod.mk_one_one]
    _ = turn ϑ * conj κ * ⟪x, D.triangleReversedLift false ϑ i n Φ' (D.fourierDatum false ϑ Ψ)
      y'⟫ := by
      rw [← conj_petersson, h_trade, map_mul, inner_conj_symm, mul_assoc]

/-- In the triangle `z = false` (the twisted one), let `Φ` make an edge along the left pair from
`(i + 1, n)` to `(i, n + 1)` (`IsLeftPair`) and `Φ'` in the other direction (`IsReversedPair`).
Right translation (`triangleRep`) by the inverse of the scalar matrix `reversalScalar`, followed by
`triangleReversedLift` with `Φ'` and `fourierDatum Ψ`, the Fourier transform of the conjugate of
`Ψ`, is `c ϑ` times the adjoint of `triangleTransposedLift` with `Φ` and `Ψ`. Here `‖c ϑ‖²` is a
constant times a fixed power of the norm of the modulus Q of the twist `ϑ`. -/
lemma exists_inner_triangleReversedLift_eq {P : Parameters} (D : Data P) {i n : ℕ}
    {Φ : D.EdgePoly false n (n + 1)} {Φ' : D.EdgePoly false (n + 1) n}
    (hΦ : D.IsLeftPair false i n Φ) (hΦ' : D.IsReversedPair false i n Φ') :
    ∃ c : D.MFoldTwist → ℂ, D.HasAbsUpToNormPower c 1 ∧
      ∀ (ϑ : D.MFoldTwist) (Ψ : D.EdgeDatum false ϑ n (n + 1)) (x : D.TriangleForm false i (n + 1))
          (y : D.TriangleForm false (i + 1) n),
        ⟪x, D.triangleReversedLift false ϑ i n Φ' (D.fourierDatum false ϑ Ψ)
            (D.triangleRep false (i + 1) n (D.reversalScalar false ϑ n)⁻¹ y)⟫ =
          c ϑ * ⟪D.triangleTransposedLift false ϑ i n Φ Ψ x, y⟫ := by
  -- Write `Φ'` as the transpose of the conjugate of some `Q`, reverse the kernel, and trade `Q` for
  -- `Φ`.
  obtain ⟨Q, hQ⟩ :=
    exists_flipPoly_map_conj_eq (D.gridSigns false (i + 1) 0 n) (D.gridSigns false i 0 (n + 1)) Φ'
  obtain ⟨turn, h_turn_modulus, h_turn_ne, h_turn⟩ := D.exists_conj_modKernel_leftPair_eq i n
  obtain ⟨κ, hκ⟩ := hΦ.petersson_lift_eq_mul_inner_modTransposedLift Q
  refine ⟨turn⁻¹ * fun _ ↦ κ, by simpa using h_turn_modulus.inv.mul (.const κ),
    fun ϑ Ψ x y ↦ ?_⟩
  let A : D.TriangleForm false i (n + 1) :=
    D.triangleReversedLift false ϑ i n Φ' (D.fourierDatum false ϑ Ψ)
    (D.triangleRep false (i + 1) n (D.reversalScalar false ϑ n)⁻¹ y)
  -- `L` is the lift of the conjugate of `y` along the left pair, with the polynomial `Q`
  let L : New.G D.E (D.gridSigns false i 0 (n + 1)) → ℂ := Space.lift
    (pairThetaKer (D.gridSpace (i + 1) false 0 n) (D.gridSpace i false 0 (n + 1))
      (D.leftPairChar false ϑ i (D.GridIndex false 0 n))
      (D.leftPairChar false ϑ i (D.GridIndex false 0 (n + 1))))
    (modDatum _ _ (triangleModulus false ϑ) Ψ (Fock.polyVector _ Q)) (star y.val)
  have h_conj (h : New.G D.E (D.gridSigns false i 0 (n + 1))) :
      conj (L h) = turn ϑ * A.val h := by
    -- write both sides as integrals, conjugate under the integral and reverse the kernel
    refine .trans ?_ (congrArg _ (hΦ'.modTransposedLift_formRep_inv_apply _ _ ϑ _ _ y h).symm)
    simp [L, lift_modDatum_apply, ← integral_conj, h_turn, hQ, mul_assoc, integral_const_mul]
  rw [Pi.mul_apply, Pi.inv_apply, mul_assoc, eq_inv_mul_iff_mul_eq₀ (h_turn_ne ϑ)]
  calc turn ϑ * ⟪x, A⟫ = (D.gridSpace i false 0 (n + 1)).petersson x.val (star L) := by
        simp [inner_eq_petersson, petersson, h_conj, mul_left_comm _ (turn ϑ), integral_const_mul]
    _ = κ * ⟪D.triangleTransposedLift false ϑ i n Φ Ψ x, y⟫ :=
      hκ ϑ _ _ (triangleModulus false ϑ) Ψ y x

/-- Let `i + n < D.m`, the number of lifts of the data `D`. The theta lift `triangleLift` for the
twist `ϑ`, from forms at the node `(i, n)` of the triangle `z` to forms at `(i, n + 1)`, commutes up
to a scalar of absolute value `1` with the right translations (`triangleRep`) by the inverses of the
scalar matrices `reversalScalar` in the finite adelic unitary groups of the two nodes. -/
lemma exists_triangleLift_reversalScalar_eq {P : Parameters} (D : Data P) (z : Bool)
    (ϑ : D.MFoldTwist) {i n : ℕ} (h_lt : i + n < D.m) :
    ∃ η : ℂ, ‖η‖ = 1 ∧ ∀ y : D.TriangleForm z i n,
      D.triangleLift z ϑ i n (D.triangleRep z i n (D.reversalScalar z ϑ n)⁻¹ y) =
        η • D.triangleRep z i (n + 1) (D.reversalScalar z ϑ (n + 1))⁻¹
          (D.triangleLift z ϑ i n y) := by
  -- The central pair acts on the datum of the lift through the character `pairChar`, so the lift
  -- intertwines the two translations up to a value of that character.
  have h_arrow := (D.isEdgeFamily_triangleKernel z h_lt).isArrow_lift (D.gridSpace i z 0 n)
    (D.gridSpace i z 0 (n + 1)) (pointDatum (triangleModulus z ϑ).ResidueRing) ϑ
  obtain ⟨η, hη, h_law⟩ : ∃ η : ℂ, ‖η‖ = 1 ∧ ∀ f : D.TriangleForm z i n,
      D.triangleRep z i (n + 1) (D.reversalScalar z ϑ (n + 1)) (D.triangleLift z ϑ i n f) =
        η • D.triangleLift z ϑ i n (D.triangleRep z i n (D.reversalScalar z ϑ n) f) :=
    ⟨pairChar _ _ _, Circle.norm_coe _, h_arrow.formRep_formLift_of_eq_smul
      (pairWeil_flipScalar (𝔪 := triangleModulus z ϑ) ..)⟩
  refine ⟨η, hη, fun y ↦ ?_⟩
  apply ((D.triangleRep z i (n + 1)).apply_bijective (D.reversalScalar z ϑ (n + 1))).injective
  rw [h_law, map_smul, Representation.self_inv_apply, Representation.self_inv_apply]

/-- For `i + n < D.m`, every form `x` at the node `(i, n + 1)` has an image `x'` at the node
`(i, n)` under the adjoint of the lift `triangleLift`. -/
lemma exists_inner_triangleLift_eq {P : Parameters} (D : Data P) (z : Bool) (ϑ : D.MFoldTwist)
    {i n : ℕ} (h_lt : i + n < D.m) (x : D.TriangleForm z i (n + 1)) :
    ∃ x' : D.TriangleForm z i n, ∀ y : D.TriangleForm z i n,
      ⟪D.triangleLift z ϑ i n y, x⟫ = ⟪y, x'⟫ := by
  have h_edge := D.isEdgeFamily_triangleKernel z h_lt
  obtain ⟨h_source, h_target, -⟩ := D.isEdgeFamily_triangleKernel z h_lt
  exact ⟨_, (h_edge.isArrow_lift _ _ _ ϑ).inner_formLift_adjoint (h_edge.isArrow_swap _ _ _ ϑ)
    (h_target _).2 (h_source true).2 x⟩

/-- The second commutation relation in adjoint form, in the triangle `z = false` (the twisted one),
for `i + n + 1 < D.m`, the number of lifts of the data `D`. The transposed lifts
`triangleTransposedLift` go from `(i, j + 1)` to `(i + 1, j)` and are formed with polynomials `Φ₀`,
`Φ₁` that make edges along the left pairs at `(i, n)`, `(i, n + 1)` (`IsLeftPair`). Let `x'` be the
image of `x` under the adjoint of `triangleLift` from `(i, n + 1)` to `(i, n + 2)`. Take the
transposed lift of `x` with `nextDatum Ψ`, the extension of the datum `Ψ` to the next column, and
apply the adjoint of `triangleLift` from `(i + 1, n)` to `(i + 1, n + 1)`. Up to a factor
`conj (κ ϑ)` this is the transposed lift of `x'` with `Ψ`, where `‖κ ϑ‖²` is a constant times a
fixed power of the norm of the modulus Q of the twist `ϑ` (`HasAbsUpToNormPower κ 1`). -/
theorem exists_triangleTransposedLift_adjoint_comm {P : Parameters} (D : Data P) {i n : ℕ}
    (h_lt : i + (n + 1) < D.m) {Φ₀ : D.EdgePoly false n (n + 1)}
    {Φ₁ : D.EdgePoly false (n + 1) (n + 1 + 1)} (h_pair₀ : D.IsLeftPair false i n Φ₀)
    (h_pair₁ : D.IsLeftPair false i (n + 1) Φ₁) :
    ∃ κ : D.MFoldTwist → ℂ, D.HasAbsUpToNormPower κ 1 ∧
      ∀ (ϑ : D.MFoldTwist) (Ψ : D.EdgeDatum false ϑ n (n + 1))
          (x : D.TriangleForm false i (n + 1 + 1)) (x' : D.TriangleForm false i (n + 1)),
        (∀ y : D.TriangleForm false i (n + 1), ⟪D.triangleLift false ϑ i (n + 1) y, x⟫ = ⟪y, x'⟫) →
        ∀ y : D.TriangleForm false (i + 1) n, ⟪D.triangleTransposedLift false ϑ i n Φ₀ Ψ x', y⟫ =
          κ ϑ * ⟪D.triangleTransposedLift false ϑ i (n + 1) Φ₁ (nextDatum Ψ) x,
            D.triangleLift false ϑ (i + 1) n y⟫ := by
  -- Turn the first descent into a reversed lift, commute it with the lift, and turn it back.
  obtain ⟨Φ₀', h_rev₀⟩ := D.exists_isReversedPair (i := i) (n := n) false h_lt.le
  obtain ⟨Φ₁', h_rev₁⟩ := D.exists_isReversedPair false h_lt
  obtain ⟨c₀, hc₀, h_descent⟩ := D.exists_inner_triangleTransposedLift_eq h_pair₀ h_rev₀
  obtain ⟨c₁, hc₁, h_ascent⟩ := D.exists_inner_triangleReversedLift_eq h_pair₁ h_rev₁
  obtain ⟨γ, hγ, h_comm⟩ := D.exists_triangleLift_triangleReversedLift_comm h_lt h_rev₀ h_rev₁
  choose η hη h_shift using fun ϑ : D.MFoldTwist ↦
    D.exists_triangleLift_reversalScalar_eq (i := i + 1) (n := n) false ϑ (by lia)
  have hη' : D.HasAbsUpToNormPower η 1 := ⟨1, 0, by simp [hη]⟩
  refine ⟨c₀ * γ * η * c₁, by simpa using ((hc₀.mul hγ).mul hη').mul hc₁,
    fun ϑ Ψ x x' h_adj y ↦ ?_⟩
  let A₀ : D.TriangleForm false (i + 1) n →ₗ[ℂ] D.TriangleForm false i (n + 1) :=
    D.triangleReversedLift false ϑ i n Φ₀' (D.fourierDatum false ϑ Ψ)
  let A₁ : D.TriangleForm false (i + 1) (n + 1) →ₗ[ℂ] D.TriangleForm false i (n + 1 + 1) :=
    D.triangleReversedLift false ϑ i (n + 1) Φ₁' (D.fourierDatum false ϑ (nextDatum Ψ))
  let y' : D.TriangleForm false (i + 1) n :=
    D.triangleRep false (i + 1) n (D.reversalScalar false ϑ n)⁻¹ y
  calc ⟪D.triangleTransposedLift false ϑ i n Φ₀ Ψ x', y⟫ = c₀ ϑ * ⟪x', A₀ y'⟫ := h_descent ϑ Ψ x' y
    _ = c₀ ϑ * ⟪x, D.triangleLift false ϑ i (n + 1) (A₀ y')⟫ := by
      rw [← inner_conj_symm x', ← h_adj, inner_conj_symm]
    _ = c₀ ϑ * (γ ϑ * ⟪x, A₁ (D.triangleLift false ϑ (i + 1) n y')⟫) := by rw [h_comm]
    _ = c₀ ϑ * (γ ϑ * (η ϑ * (c₁ ϑ * ⟪D.triangleTransposedLift false ϑ i (n + 1) Φ₁ (nextDatum Ψ) x,
          D.triangleLift false ϑ (i + 1) n y⟫))) := by
      rw [h_shift, map_smul, inner_smul_right, h_ascent]
    _ = _ := by simp only [Pi.mul_apply, mul_assoc]

/-- There are linear maps `d`, the descents, from `(i, n + 1)` to `(i + 1, n)` with the following
properties. With the theta lifts `triangleLift` from `(i, n)` to `(i, n + 1)`, the group orders
`triangleGLCard` as weights and the embeddings `triangleEmbedding` at `(i, 0)` of the forms at
`(0, 0)` fixed by the base level, they form a triangle `IsTriangle` of size `D.m`: each square
commutes up to a constant, on the copies of the base forms the first lift is adjoint to the first
descent, and their composite maps the copy in row `i` injectively to that in row `i + 1`. For
`z = false` the squares satisfy `HasSquareModuli`: their constants have the moduli `quotientRatio`
in the sense of `HasAbsUpToNormPower`, and the descent of the adjoint image of a form under the
upper lift is a multiple of the adjoint image of its descent under the lower lift, by a constant of
modulus `1` in the sense of `HasAbsUpToNormPower`. -/
theorem exists_isTriangle {P : Parameters} (D : Data P) (z : Bool) :
    ∃ d : D.MFoldTwist → ∀ i n : ℕ, D.TriangleForm z i (n + 1) →ₗ[ℂ] D.TriangleForm z (i + 1) n,
      IsTriangle D.m (D.triangleGLCard z) (D.triangleLift z) d (D.triangleEmbedding z) ∧
      (z = false →
        HasSquareModuli D.m (D.triangleGLCard z) D.HasAbsUpToNormPower D.quotientRatio
          (D.triangleLift z) d) := by
  -- The datum at `n = 0` makes the descent the adjoint of the lift; `nextDatum` gives the others.
  choose! Φ h_left_pair using fun (i n : ℕ) (h : i + n < D.m) ↦ D.exists_isLeftPair z h
  have h_adjoint_datum (i : ℕ) (h : i + 0 < D.m) (ϑ : D.MFoldTwist) :
      ∃ Ψ : D.EdgeDatum z ϑ 0 1, ∀ (y : D.TriangleForm z i 0) (x : D.TriangleForm z i 1),
        ⟪x, D.triangleLift z ϑ i 0 y⟫ = ⟪D.triangleTransposedLift z ϑ i 0 (Φ i 0) Ψ x,
          formNegEquiv _ _ y⟫ :=
    (D.isEdgeFamily_triangleKernel z h).exists_inner_modLift_eq_inner_modTransposedLift
      (D.gridSpace i z 0 0)
      (D.gridSpace i z 0 (0 + 1)) (h_left_pair i 0 h) ϑ
        (pointDatum (triangleModulus z ϑ).ResidueRing)
  choose! Ψ₀ h_adjoint using h_adjoint_datum
  -- the datum of the descent at `(i, n)` is defined by recursion on `n`
  let e (ϑ : D.MFoldTwist) (i : ℕ) : ∀ n : ℕ, D.EdgeDatum z ϑ n (n + 1) :=
    Nat.rec (Ψ₀ i ϑ) fun _ ↦ nextDatum
  let d (ϑ : D.MFoldTwist) (i n : ℕ) : D.TriangleForm z i (n + 1) →ₗ[ℂ] D.TriangleForm z (i + 1)
    n :=
    D.triangleTransposedLift z ϑ i n (Φ i n) (e ϑ i n)
  -- the first commutation relation
  have h_square (i n : ℕ) (h : i + (n + 1) < D.m) : ∃ β : D.MFoldTwist → ℂ,
      SquareCommutes (D.triangleGLCard z) (D.triangleLift z) d i n β ∧
      (z = false → D.HasAbsUpToNormPower β (D.quotientRatio (i + 1) (i + 1 + n + 1))) := by
    obtain ⟨β, h_comm, hβ⟩ :=
      D.exists_triangleLift_triangleTransposedLift_comm z h (h_left_pair i n h.le)
        (h_left_pair i (n + 1) h)
    refine ⟨β, fun ϑ y ↦ ext_inner_left ℂ fun x ↦ ?_, hβ⟩
    rw [inner_smul_right, inner_smul_right, div_eq_inv_mul, ← map_inv₀]
    -- the datum `e ϑ i (n + 1)` is by definition `nextDatum (e ϑ i n)`
    exact h_comm ϑ (e ϑ i n) y x
  -- With a = `triangleFirstLift`, let v be the form whose copy is d (a y). Then
  -- ⟪v, x⟫ = ⟪a y, a x⟫, which gives the level of v and the injectivity.
  have h_base (i : ℕ) (h : i < D.m) (ϑ : D.MFoldTwist) (y : D.triangleBase z)
    (v : D.TriangleForm z 0 0)
      (hv : D.triangleNegEquiv z (i + 1) v = d ϑ i 0
        (D.triangleLift z ϑ i 0 (D.triangleEmbedding z i y))) :
      v ∈ D.triangleBase z ∧ (v = 0 → y = 0) := by
    have h_pair (x : D.TriangleForm z 0 0) :
        ⟪v, x⟫ = ⟪D.triangleFirstLift z ϑ i y, D.triangleFirstLift z ϑ i x⟫ := by
      rw [← (D.triangleNegEquiv z (i + 1)).inner_map_map, hv]
      exact (h_adjoint i h ϑ (D.triangleNegEquiv z i x) _).symm
    obtain ⟨C, h_lift⟩ := D.exists_hasSum_inner_triangleFirstLift z i h
    obtain ⟨h_level, -⟩ := h_lift ϑ y
    exact h_level v h_pair
  -- the fields of `IsTriangle` in order: squares, adjointness, return to the base, injectivity
  refine ⟨d, ⟨fun i n h ↦ ?_, fun i h ϑ y ↦ ?_, fun i h ϑ y ↦ ?_, fun i h ϑ y hy ↦ ?_⟩, ?_⟩
  · obtain ⟨β, h_comm, -⟩ := h_square i n h
    exact ⟨β, h_comm⟩
  · -- the adjointness holds by the choice of the datum at `n = 0`
    exact h_adjoint i h ϑ (D.triangleEmbedding z i y)
  · obtain ⟨v, hv⟩ := (D.triangleNegEquiv z (i + 1)).surjective
      (d ϑ i 0 (D.triangleLift z ϑ i 0 (D.triangleEmbedding z i y)))
    obtain ⟨hv_mem, -⟩ := h_base i h ϑ y v hv
    exact ⟨⟨v, hv_mem⟩, hv⟩
  · obtain ⟨-, h_inj⟩ := h_base i h ϑ y 0 (by rw [hy, map_zero])
    exact h_inj rfl
  · rintro rfl
    refine ⟨.one, .mul, fun i n h ↦ ?_, fun i n h ↦ ?_⟩
    · obtain ⟨β, h_comm, hβ⟩ := h_square i n h
      exact ⟨β, hβ rfl, h_comm⟩
    · -- the second commutation relation
      obtain ⟨κ, hκ, h_adj⟩ :=
        D.exists_triangleTransposedLift_adjoint_comm h (h_left_pair i n h.le)
          (h_left_pair i (n + 1) h)
      refine ⟨κ, hκ, fun ϑ x ↦ ?_⟩
      obtain ⟨x', hx'⟩ := D.exists_inner_triangleLift_eq false ϑ h x
      exact ⟨x', hx', h_adj ϑ (e ϑ i n) x x' hx'⟩

end Data

end New

end TriangleArrows

namespace New.Data

open Finset Fintype Exchange Subgroup LevelPlaces

/-- The index set `D.Y 1` has two blocks: `blockNumber 1` is `0` on `RowIndex` and `1` on `Fin D.t`.
In `GL (D.Y 1)` over a commutative ring, the group of block upper triangular matrices (`parabolic`)
has the same index as the opposite parabolic `rangeParabolic` of the first block. -/
lemma index_rangeParabolic_inl_eq {P : Parameters} (D : Data P) (R : Type) [CommRing R] :
    (rangeParabolic (R := R) (.inl : D.RowIndex ↪ D.Y 1)).index =
      (parabolic (R := R) (blockNumber (R := D.RowIndex) (T := Fin D.t) 1)).index := by
  rw [index_rangeParabolic]
  congr 1
  -- both groups consist of the matrices with the same vanishing block
  exact ext fun _ ↦ forall₂_congr (by simp! [lt_iff_le_and_ne])

/-- The index of the level `New.Data.lastLevel` ϑ in K₀ is the product of the orders of the full
`GL (D.Y D.m)` over the residue fields at the chosen places and of the indices of the block upper
triangular groups over the residue fields at the places of ϑ. -/
lemma stdLevelIndex_lastLevel_eq_prod {P : Parameters} (D : Data P) (ϑ : D.MFoldTwist) :
    stdLevelIndex (D.lastLevel ϑ) =
      (∏ i : (D.levelPlaces ϑ).ChosenIndex,
          Nat.card (GL (D.Y D.m) (ResField ((D.levelPlaces ϑ).chosenPlace i)))) *
        ∏ w : (D.levelPlaces ϑ).TwistIndex,
          (parabolic (R := ResField ((D.levelPlaces ϑ).twistPlace w))
            (blockNumber (R := D.RowIndex) (T := Fin D.t) D.m)).index := by
  simp +instances [lastResidueLevel, relIndex_levelOf, Seesaw.index_pi_univ, placeAt,
    -Nat.card_eq_fintype_card]

/-- The weight `triangleGLCard false ϑ n` is the product of the orders of the general linear group
of the node `(0, n)` over the residue fields at the chosen places and at the places of ϑ. -/
lemma triangleGLCard_false_eq_prod {P : Parameters} (D : Data P) (ϑ : D.MFoldTwist) (n : ℕ) :
    D.triangleGLCard false ϑ n =
      (∏ i : (D.levelPlaces ϑ).ChosenIndex,
          Nat.card (GL (D.GridIndex false 0 n) (ResField ((D.levelPlaces ϑ).chosenPlace i)))) *
        ∏ w : (D.levelPlaces ϑ).TwistIndex,
          Nat.card (GL (D.GridIndex false 0 n) (ResField ((D.levelPlaces ϑ).twistPlace w))) := by
  simp +instances [triangleGLCard, triangleModulus, LevelPlaces.card_GL_levelModulus,
    relIndex_levelOf, Nat.card_pi, placeAt, -Nat.card_eq_fintype_card,
    -Bool.cond_eq_ite]

attribute [-simp] Bool.cond_eq_ite
attribute [local simp] Bool.cond_true Bool.cond_false

/-- Let m = `D.m` be the number of lifts of the data `D`. There are a constant C and an integer k
such that [K₀ : J] = C·N(Q)^k·δ(ϑ)^m·N_m / (N₀·N₁^m) for every twist ϑ whose tame part has
non-trivial powers up to m at all places of its set Q (`MFoldTwist`). Here N(Q) is the number of
elements of the residue ring of `twistModulus ϑ 0`, the product of the places in Q. The group
K₀ = `New.stdLevel` consists of the integral points, J = `lastLevel ϑ`, and
N_n = `triangleGLCard false ϑ n` is the order of a general linear group over a finite ring, so the
denominator is not zero. The number δ(ϑ) is the `gramFactor` of `descentPair ϑ 1`, a pair of spaces
W and V of ranks r and r + t: the index in K₀ of the level `DescentPair.levelGroup` on V, times
|GL_r| modulo Q and N(Q)^(tr), over |GL_r| modulo the prime divisors `chosenPlace` of `D.piM`. -/
lemma exists_stdLevelIndex_lastLevel_eq {P : Parameters} (D : Data P) :
    ∃ (C : ℂ) (k : ℤ), ∀ ϑ : D.MFoldTwist,
      (stdLevelIndex (D.lastLevel ϑ) : ℂ) =
        C * Fintype.card (D.twistModulus ϑ 0).ResidueRing ^ k * (D.descentPair ϑ 1).gramFactor ^ D.m
          *
            D.triangleGLCard false ϑ D.m /
          (D.triangleGLCard false ϑ 0 * D.triangleGLCard false ϑ 1 ^ D.m) := by
  -- Every quantity is a product over the chosen places times a product over `TwistIndex`. The
  -- former factors do not depend on `ϑ`; the constant (values at the trivial twist) absorbs
  -- them. At `w ∈ TwistIndex`, counting the flag groups leaves a fixed power of the number of
  -- elements of the residue field at `w`.
  choose k card_parab using exists_card_parabolic_blockNumber_eq D.RowIndex (Fin D.t)
  refine ⟨D.triangleGLCard false 1 0 *
      (D.triangleGLCard false 1 1 / (D.descentPair .one 1).gramFactor) ^ D.m,
    (k 1 - D.t * card D.RowIndex) * D.m - k D.m, fun ϑ ↦ ?_⟩
  let κ (w : (D.levelPlaces ϑ).TwistIndex) : Type := ResField ((D.levelPlaces ϑ).twistPlace w)
  -- Lagrange's theorem for the flag group in `GL (D.GridIndex false 0 n)` over the residue field at
  -- `w ∈ TwistIndex`.
  have card_GL_eq (n : ℕ) (w : (D.levelPlaces ϑ).TwistIndex) :
      (parabolic (R := κ w) (blockNumber (R := D.RowIndex) (T := Fin D.t) n)).index *
          (Nat.card (GL D.RowIndex (κ w)) * Nat.card (GL (Fin D.t) (κ w)) ^ n *
            Nat.card (κ w) ^ k n) =
        Nat.card (GL (D.GridIndex false 0 n) (κ w)) := by
    rw [← card_parab]
    exact index_mul_card _
  -- The trivial twist has empty `TwistIndex`.
  have no_places : (univ : Finset (D.levelPlaces .one).TwistIndex) = ∅ :=
    univ_eq_empty_iff.2 ⟨nofun⟩
  simp only [D.stdLevelIndex_lastLevel_eq_prod ϑ, D.triangleGLCard_false_eq_prod]
  -- Write both sides as products over the places, replace the orders of
  -- `GL (D.GridIndex false 0 1)` and `GL (D.GridIndex false 0 D.m)` at `w ∈ TwistIndex` by the flag
  -- count, and clear denominators. The index that enters `DescentPair.gramFactor` is that of the
  -- flag group of `D.GridIndex false 0 1`.
  let := Prop.linearOrder
  simp +instances [κ, index_rangeParabolic_inl_eq, no_places, ← card_GL_eq 1, ← card_GL_eq D.m,
    DescentPair.gramFactor, descentPair, DescentPair.rankDiff, descentResidueLevel,
    card_levelModulus_residueRing, card_ResField, relIndex_levelOf, Nat.card_pi,
      Seesaw.index_pi_univ,
    div_pow, prod_eq_zero_iff, zpow_sub₀, zpow_add₀, zpow_mul, prod_pow,
    -Nat.card_eq_fintype_card, prod_mul_distrib]
  field_simp [prod_eq_zero_iff, NeZero.ne, index_ne_zero_of_finite]
  -- The factors at the chosen places for `ϑ` and for the trivial twist agree by definition.
  ring!

/-- Let m = `D.m` be the number of lifts of the data `D`, let ϑ be an m-fold twist, and let x, y be
forms on Y₀ = `spaceY 0` fixed by J_M, the principal level at the prime divisors of `D.piM`
(`principalForms`). Their images ι_ϑ x and ι_ϑ y (`lowerChainAtLevel`) are algebraic forms on the
definite space Y_m, and their inner product, a sum over the classes of the level, is
[K₀ : J]·d·⟨u x, u y⟩. Here J = `lastLevel ϑ`, [K₀ : J] = `stdLevelIndex J`, d is the dimension of
the weight on Y_m with column counts `columnsY`, the cardinality of `WeylIndex`, and u is the chain
of m lifts Y₀ → Y_m of the triangle, each multiplied by its weight `triangleGLCard`. -/
lemma inner_lowerChainAtLevel {P : Parameters} (D : Data P) (ϑ : D.MFoldTwist)
    (x y : D.principalForms (D.spaceY 0)) :
    let u : D.TriangleForm false 0 0 →ₗ[ℂ] D.TriangleForm false 0 D.m :=
      weightedChain (D.triangleGLCard false) (D.triangleLift false) ϑ 0 D.m
    inner ℂ (D.lowerChainAtLevel ϑ x) (D.lowerChainAtLevel ϑ y) =
      stdLevelIndex (D.lastLevel ϑ) * Fintype.card (WeylIndex (D.Y D.m) D.columnsY) *
        inner ℂ (u x.val) (u y.val) := by
  intro u
  -- `erw`: the space `gridSpace 0 false 0 D.m` of the chain is `spaceY D.m` only by unfolding
  erw [LevelForm.inner_eq_petersson (D.spaceY _) D.isHCParam_paramY]
  -- The function of the algebraic form `D.lowerChainAtLevel ϑ v` is the chain of lifts of `v`: the
  -- weights of the lifts, indices of principal levels, are the orders `D.triangleGLCard false ϑ`.
  have h_chain (v : D.principalForms (D.spaceY 0)) :
      ofAlgForm (D.paramY D.m) (D.signsY D.m) (D.lowerChainAtLevel ϑ v).val = (u v.val).val := by
    simpa [u, weightedChain, triangleGLCard, triangleModulus, LevelPlaces.card_GL_levelModulus]
      using! Space.ofAlgForm_toAlgForm D.isHCParam_paramY _
  simp_rw [h_chain, Space.inner_eq_petersson]
  -- `stdLevelIndex` is by definition the relative index of the level in K₀
  rfl

/-- For every m-fold twist ϑ, the chain ι_ϑ (`New.Data.lowerChainAtLevel`) from forms of level J_M
on U(Y₀) to forms of level `New.Data.lastLevel` ϑ on U(Y_m) is injective. -/
@[simp]
lemma lowerChainAtLevel_injective {P : Parameters} (D : Data P) (ϑ : D.MFoldTwist) :
    Function.Injective (D.lowerChainAtLevel ϑ) := by
  -- If `D.lowerChainAtLevel ϑ y = 0`, the chain of lifts of `y` vanishes
  -- (`inner_lowerChainAtLevel`); chains are injective.
  obtain ⟨d, h_triangle, -⟩ := D.exists_isTriangle false
  refine (injective_iff_map_eq_zero (D.lowerChainAtLevel ϑ)).2 fun y hy ↦ ?_
  have h_chain : weightedChain (D.triangleGLCard false) (D.triangleLift false) ϑ 0 D.m y.val =
    0 := by
    simpa [hy, relIndex_ne_zero_of_isLevel, -Fintype.card_pi] using D.inner_lowerChainAtLevel ϑ y y
  exact h_triangle.eq_zero_of_weightedChain_eq_zero D.m 0 (by simp) y h_chain

end New.Data

end
