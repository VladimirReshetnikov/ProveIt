import New.Spanning.RemainingTerms.Box
import New.Spanning.RemainingTerms.SiegelLemma
import New.Spanning.Unfolding.BesselLevelStructure

/-!
# Near terms in the filling theorem: frames, cell ranks, nearness and integrality

The terms `γ` of the count in the filling theorem are rational elements of the unitary group.
The data are `S : New.Filling E 𝔰` for a shape `𝔰`, with the size hypotheses
`New.Filling.IsAdmissible`, which compare all constants with powers of the large parameter `b`.
For the frame `(e₁, …, e_ϱ, z)`, `New.frameImage γ` is the matrix of its image under `γ`, and
`S.frameProducts γ` is the Gram matrix of the frame against its image, with leading minors
`New.leadingMinor`. This file describes how the flags of the frame and of its image under `γ` meet,
defines the cell rank and nearness of `γ`, proves a norm identity for `S.termDisc γ`, bounds the
Gram entries of near terms by powers of `S.b`, and shows that the Gram entries of terms are
algebraic integers.

## Main definitions and results

* `New.Filling.CharsAgree`, `New.PairOccursAt`, `New.Filling.HasCellRank`: the terms that respect
  the unipotent character, the vectors common to the two flags of a term, and its cell rank.
* `New.Filling.IsNear`: `γ` is near if some boxed point `y` (`New.Filling.boxedPoints`) has `γ⁻¹ y`
  boxed.
* `New.Filling.norm_sq_middle_part_eq`, `New.Filling.map_termDisc_eq_norm`: a norm identity, which
  makes `S.termDisc γ` real and nonnegative at every infinite place. So `S.termDisc γ` is totally
  positive or zero (`New.Filling.termDisc_pos_or_eq_zero`).
* `New.Filling.IsNear.norm_frameProducts_le`, `New.Filling.IsNear.norm_map_leadingMinor_sq_le`: for
  a near term, the Gram entries and the leading minors are bounded by powers of the size parameter
  `S.b`.

Notions from other files:
* `New.Filling.G`: for a commutative ring R with involution, the unitary group over R of ϱ
  hyperbolic pairs and the middle Gram matrix diag(1, …, 1, −N) on X₀ ⊕ Ez, in the basis e₁, …, e_ϱ;
  x_i (i in κ), z; e*₁, …, e*_ϱ.
* `New.Filling.termDisc`: 𝗀(γ) = |D_{ϱ+1}|² − N²|D_ϱ|², with D_l the leading minors of
  `New.Filling.frameProducts γ`.
* `New.Shape.Form.besselU`, `New.Shape.Form.besselU0`: the Bessel unipotent group 𝖴 of isometries
  that are block upper unitriangular and trivial on the middle block, and its elements that fix each
  vector of the frame.
* `New.Filling.mainSecondMoment`, `New.Filling.identitySecondMoment`: the numbers
  sourceDim² / (besselDegree · mass), with the mass of the genus of the standard lattice, and
  sourceDim times the order of the reduced image of the Bessel subgroup `besselS`.
-/

noncomputable section

section FlagsAndCellRanks

open NumberField Matrix Fintype

namespace New

variable {R : Type*} {E : Type} [CommRing R] [Field E] [CMType E] {𝔰 : Shape} (S : Filling E 𝔰)
  [StarRing R] {T : 𝔰.Form R}

/-- For a square matrix T on the middle coordinates, the two-row block diagonal matrix with two
copies of the row of T indexed by z. -/
abbrev Filling.zRowBlockDiagonal (T : 𝔰.Form R) :
    Matrix (Unit ⊕ Unit) (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) R :=
  T.toRows₂.fromBlocks 0 0 T.toRows₂
/-- The module of the vectors x of X₀ for which there is a pair of middle vectors, both orthogonal
to z, that lies in the links (`New.link`) of both γ and γ' and whose first vector has
X₀-coordinates x. -/
def commonLink (γ γ' : T.G) : Submodule R (𝔰.κ → R) :=
  (link γ ⊓ link γ' ⊓ (Filling.zRowBlockDiagonal T).mulVecLin.ker).map
    (LinearMap.funLeft R R (Sum.inl ∘ .inl))

/-- The frame f = (e₁, …, e_ϱ, z) and its image γf satisfy fx = γfy for some coefficient vectors
x, y that vanish at indices above a and have x_a = c, y_a = c'. -/
def PairOccursAt (γ : T.G) (c c' : R) (a : Fin (𝔰.ϱ + 1)) : Prop :=
  ∃ x y : Fin (𝔰.ϱ + 1) → R,
    frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R) *ᵥ x = frameImage γ.val.val *ᵥ y ∧
    x a = c ∧ y a = c' ∧ ∀ b : Fin (𝔰.ϱ + 1), b > a → x b = 0 ∧ y b = 0

/-- For some c with c c̄ = 1 and every index a ≥ j (counted from 0), the flags of f and γf share a
vector with leading coefficients c and 1 at a. -/
def NormOnePairOccursFrom (j : ℕ) (γ : T.G) : Prop :=
  ∃ c : R, c * star c = 1 ∧ ∀ a : Fin (𝔰.ϱ + 1), j ≤ a.val → PairOccursAt γ c 1 a

namespace Filling

/-! ### Forms, coordinates, cell ranks and nearness -/

/-- The Gram matrix over E of the form on the space: two dual isotropic blocks of rank ϱ around the
middle Gram matrix `S.ratMiddle E` of X₀⊕Ez. -/
abbrev ratGram : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E := (S.ratMiddle E).splitGram

/-- The block diagonal matrix diag(M, −M) over E on two copies of X₀⊕Ez, M = `S.ratMiddle E`. -/
abbrev linkForm : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) E :=
  (S.ratMiddle E).fromBlocks 0 0 (-S.ratMiddle E)

/-- For a class c, the inverse of the matrix `New.Filling.classBasis` c; it takes rational
coordinates to coordinates in the basis of the lattice h_cΛ₀. -/
def classCoord (c : S.Classes) :
    Matrix (Fin 𝔰.ϱ ⊕ 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) (Fin 𝔰.ϱ ⊕ 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) (𝔸f E) :=
  (S.classBasis c)⁻¹.val

/-- The matrix whose columns are the standard basis vectors of X₀, written in the basis of the
middle part of the lattice h_cΛ₀ of the class c. It is `New.middleInclusionMatrix` times the inverse
of the chosen representative `c.out` of c in U(X₀)(𝔸_f), whose image in the unitary group of V is
h_c = `S.classRep c`. It depends on this choice of representative. -/
def classCoordX₀ (c : S.Classes) : Matrix (𝔰.κ ⊕ Unit) 𝔰.κ (𝔸f E) :=
  middleInclusionMatrix 𝔰 S.piN * ((c.out⁻¹ : Gf E 𝔰.κ) : Matrix 𝔰.κ 𝔰.κ (𝔸f E))

/-- The number `n_p = #R̄₀ n_X N ^ (-k f)` against which pairs of terms are counted: here `R̄₀` is
the reduced image of the Bessel subgroup `besselS`, `n_X` the number of classes and `f` the number
of infinite places. -/
abbrev pairCountScale : ℝ :=
  Nat.card (S.reducedImage besselS) * card S.Classes / S.N ^ (𝔰.k * numInfPlaces E)

/-- γ has cell rank j ≤ ϱ+1: `New.NormOnePairOccursFrom` j holds, the leading minor D_j of
`S.frameProducts γ` is nonzero, and `S.termDisc γ` is nonzero exactly when j = ϱ+1. -/
@[mk_iff]
structure HasCellRank (j : Fin (𝔰.ϱ + 1 + 1)) (γ : S.G E) : Prop where
  /-- For some c with c c̄ = 1 and every index a ≥ j, the flags of the frame f and of γf share a
  vector with leading coefficients c and 1 at a. -/
  normOnePairOccursFrom : NormOnePairOccursFrom j.val γ
  /-- The leading minor D_j of the products of the two frames is nonzero. -/
  leadingMinor_ne_zero : leadingMinor (S.frameProducts γ) j ≠ 0
  /-- The cell rank is the top one, ϱ+1, exactly when `S.termDisc γ` is nonzero. -/
  lt_iff_termDisc_ne_zero : 𝔰.ϱ < j.val ↔ S.termDisc γ ≠ 0

/-- The product over the infinite places v of E of the complex absolute values of the images under
the embeddings `Φ v` of `S.termDisc γ` = |D_{ϱ+1}|² − N²|D_ϱ|², where D_l is the leading minor of
order l of `S.frameProducts γ`. -/
def termDiscNorm (γ : S.G E) : ℝ := ∏ v : InfinitePlace E, ‖Φ v (S.termDisc γ)‖

/-- The rational element γ is near: there is an archimedean point y such that both y and γ⁻¹y
lie in the set `New.Filling.boxedPoints` of boxed points. -/
def IsNear (γ : S.G E) : Prop :=
  ∃ y ∈ S.boxedPoints, (S.ratToInf γ)⁻¹ * y ∈ S.boxedPoints

/-- The finite character `New.Filling.unipotentChar` takes the same value at u and at γ⁻¹uγ for
every rational u in 𝖴 ∩ γ𝖴γ⁻¹. -/
def CharsAgree (γ : S.G E) : Prop :=
  ∀ᵉ (u ∈ besselU) (u' ∈ besselU), u * γ = γ * u' →
    S.unipotentChar (S.ratToFin u) = S.unipotentChar (S.ratToFin u')

end Filling

end New

end FlagsAndCellRanks

namespace New.Filling

open Subgroup Real NumberField Matrix Finset ComplexOrder Complex Fin Floors FloorGroups Nat

variable {R : Type} [CommRing R] [StarRing R] {𝔰 : Shape} {T : 𝔰.Form R} {s s' : T.G}
  {E : Type} [Field E] [CMType E] {S : Filling E 𝔰} {γ u : S.G E} {c c' : S.Classes}
  {r : S.ResidueGL} {x y : Fin (𝔰.ϱ + 1) → E}

/-! ### Frames and the Bessel subgroup -/

/-- The frame columns of a product s s' are s times those of s'. -/
lemma frameImage_mul : frameImage (s * s').val.val = s.val.val * frameImage s'.val.val := rfl

/-- Multiplying γ on the right by an element u of `New.Shape.Form.besselU0`, which fixes the frame
(e₁, …, e_ϱ, z), does not change the image of the frame. -/
lemma frameImage_mul_of_mem_besselU0 (hu : u ∈ besselU0) :
    frameImage (γ * u).val.val = frameImage γ.val.val := by
  obtain ⟨hu_bessel, hu_frame⟩ := mem_besselU0_iff.1 hu
  simp [submatrix_mul_besselFrame hu_bessel, hu_frame]

/-- The isometry s⁻¹s' fixes the frame (e₁, …, e_ϱ, z) if and only if s and s' map the frame to
the same vectors. -/
lemma frameImage_inv_mul_eq_iff :
    frameImage (s⁻¹ * s').val.val = frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R) ↔
      frameImage s.val.val = frameImage s'.val.val := by
  -- cancel the invertible matrix `s⁻¹` on the left
  refine Iff.trans ?_ s⁻¹.val.val.mul_right_inj_of_invertible
  rw [← frameImage_mul, ← frameImage_mul, inv_mul_cancel, eq_comm]
  rfl

/-- A unitary γ preserves the form on combinations of frame vectors: γf · y has the same product
with itself as f · y. -/
lemma form_frameImage_mulVec (γ : S.G E) (y : Fin (𝔰.ϱ + 1) → E) :
    star (frameImage γ.val.val *ᵥ y) ⬝ᵥ (S.ratMiddle E).splitGram *ᵥ frameImage γ.val.val *ᵥ y =
      star (frameImage 1 *ᵥ y) ⬝ᵥ (S.ratMiddle E).splitGram *ᵥ frameImage 1 *ᵥ y := by
  rw [frameImage_mulVec γ.val.val, U.form_mulVec_mulVec γ]

/-! ### Vectors shared by two frames and the norm identity -/

/-- If `f · x = γ f · y`, then the `z`-coefficients of `x` and `y` have the same norm. -/
lemma star_mul_last_eq_of_frameImage_eq
    (hxy : frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ x =
      frameImage γ.val.val *ᵥ y) :
    star (x 𝔰.top) * x 𝔰.top = star (y 𝔰.top) * y 𝔰.top := by
  -- `γ` is unitary, so `frameImage 1 *ᵥ x` and `frameImage 1 *ᵥ y` have the same norm
  have h_norm := form_frameImage_mulVec γ y
  rw [← hxy] at h_norm
  -- on the span of the frame only the `z`-coordinate contributes, with the factor `-N`
  have h_scaled :
      (S.N : E) * (star (x 𝔰.top) * x 𝔰.top) = S.N * (star (y 𝔰.top) * y 𝔰.top) := by
    simpa [↓frameImage_one_mulVec, middleGram, dotProduct, mulVec, splitGram, mul_left_comm,
      mul_assoc] using h_norm
  exact mul_left_cancel₀ (by simp [Nat.Prime.ne_zero]) h_scaled

/-- If `γ f · y = f · x`, then its products with the frame vanish except the one with `z`, which
is `-N` times the `z`-coefficient of `x`. -/
lemma frameProducts_mulVec_of_frameImage_eq
    (hxy : frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ x =
      frameImage γ.val.val *ᵥ y) :
    S.frameProducts γ *ᵥ y = Pi.single 𝔰.top (-S.N * x 𝔰.top) := by
  -- the products of `γ f · y = f · x` with the frame are read off from the Gram matrix
  simp only [frameGram_eq_frameImage, ← mulVec_mulVec, ← hxy]
  simp [middleGram, splitGram, frameImage_one_mulVec, funext_iff, mulVec, dotProduct,
    Matrix.one_apply, forall_fin_succ', -mulVec_mulVec]

/-- The middle form is anisotropic on the vectors without `z`-coordinate. -/
lemma eq_zero_of_ratMiddle_form_eq_zero (w : 𝔰.MiddleIndex → E) (hw : w (Sum.inr ()) = 0)
    (h_norm : star w ⬝ᵥ S.ratMiddle E *ᵥ w = 0) :
    w = 0 := by
  let v₀ : InfinitePlace E := Classical.ofNonempty
  -- at an infinite place the form is the sum of the squared absolute values on `X₀`
  have h_sum : ∑ i : 𝔰.κ, ‖Φ v₀ (w (Sum.inl i))‖ ^ 2 = 0 := by
    simpa [middleGram, hw, conj_mul', dotProduct, mulVec, Matrix.one_apply, ← ofReal_inj]
      using congrArg (Φ v₀) h_norm
  simpa [hw, funext_iff, sum_eq_zero_iff_of_nonneg] using h_sum

/-- If `γ f · y` is orthogonal to `e₁, …, e_ϱ` and has product `D` with `z`, then it has no
`e*`-part. -/
lemma frameImage_mulVec_eStar_eq_zero {D : E}
    (h_prod : S.frameProducts γ *ᵥ y = Pi.single 𝔰.top D) (a : Fin 𝔰.ϱ) :
    (frameImage γ.val.val *ᵥ y) (eStar a) = 0 := by
  -- the product with the isotropic vector `e_a` reads off the dual coordinate
  have h_row : (S.frameProducts γ *ᵥ y) a.castSucc = 0 := by simp [h_prod, castSucc_ne_last]
  rw [frameProducts, frameGram_eq_frameImage, ← mulVec_mulVec, ← mulVec_mulVec] at h_row
  generalize frameImage γ.val.val *ᵥ y = t at h_row
  simpa [splitGram, mulVec, dotProduct, Matrix.one_apply, apply_ite star] using h_row

/-- If `γ f · y` is orthogonal to `e₁, …, e_ϱ` and has product `D` with `z`, then `-N` times
its `z`-coordinate is `D`. -/
lemma neg_mul_frameImage_mulVec_z_eq {D : E}
    (h_prod : S.frameProducts γ *ᵥ y = Pi.single 𝔰.top D) :
    -(S.N * (frameImage γ.val.val *ᵥ y) 𝔰.z) = D := by
  -- the product with `z` reads off the `z`-coordinate, with the factor `-N`
  have h_row : (S.frameProducts γ *ᵥ y) 𝔰.top = D := by simp [h_prod]
  rw [frameProducts, frameGram_eq_frameImage, ← mulVec_mulVec, ← mulVec_mulVec] at h_row
  generalize frameImage γ.val.val *ᵥ y = t at h_row
  simpa [middleGram, splitGram, mulVec, dotProduct, Matrix.one_apply] using h_row

/-- If `γ f · y` is orthogonal to `e₁, …, e_ϱ` and has product `D` with `z`, then at each
infinite place `N` times the squared length of its `X₀`-part is `|D|² - N² |y_z|²`. -/
lemma mul_sum_norm_sq_frameImage_mulVec_eq {D : E}
    (h_prod : S.frameProducts γ *ᵥ y = Pi.single 𝔰.top D) (v : InfinitePlace E) :
    S.N * ∑ i : 𝔰.κ, ‖Φ v ((frameImage γ.val.val *ᵥ y) (𝔰.indexX₀ i))‖ ^ 2 =
      ‖Φ v D‖ ^ 2 - (S.N * ‖Φ v (y 𝔰.top)‖) ^ 2 := by
  set t : 𝔰.BesselIndex → E := frameImage γ.val.val *ᵥ y
  have h_dual : ∀ a : Fin 𝔰.ϱ, t (eStar a) = 0 := frameImage_mulVec_eStar_eq_zero h_prod
  -- `γ` is unitary, so `t` has the same norm as `frameImage 1 *ᵥ y`. Write this out at the place
  -- `v`; the hyperbolic terms vanish by `h_dual`.
  have h_norm : ∑ i : 𝔰.κ, ‖Φ v (t (𝔰.indexX₀ i))‖ ^ 2 - S.N * ‖Φ v (t 𝔰.z)‖ ^ 2 =
      -(S.N * ‖Φ v (y 𝔰.top)‖ ^ 2) := by
    have h_unitary : star t ⬝ᵥ (S.ratMiddle E).splitGram *ᵥ t =
        star (frameImage 1 *ᵥ y) ⬝ᵥ (S.ratMiddle E).splitGram *ᵥ frameImage 1 *ᵥ y :=
      form_frameImage_mulVec γ y
    rw [frameImage_one_mulVec] at h_unitary
    simpa [middleGram, h_dual, ← ofReal_inj, conj_mul', mul_left_comm _ (S.N : ℂ), sub_eq_add_neg,
      dotProduct, mulVec, splitGram, Matrix.one_apply] using congrArg (Φ v) h_unitary
  have h_D : ‖Φ v D‖ = S.N * ‖Φ v (t 𝔰.z)‖ := by simp [← neg_mul_frameImage_mulVec_z_eq h_prod, t]
  rw [h_D]
  linear_combination (S.N : ℝ) * h_norm

/-- A vector `t` without `e*`-part lies in the span of the frame `f` if, at some infinite place,
`N` times the squared length of its `X₀`-part is at most zero. -/
lemma exists_frameImage_one_mulVec_eq_of_nonpos {t : 𝔰.BesselIndex → E}
    (h_dual : ∀ a : Fin 𝔰.ϱ, t (eStar a) = 0) {v : InfinitePlace E}
    (h_nonpos : S.N * ∑ i : 𝔰.κ, ‖Φ v (t (𝔰.indexX₀ i))‖ ^ 2 ≤ 0) :
    ∃ x : Fin (𝔰.ϱ + 1) → E, frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ x = t := by
  -- A sum of squares that is at most zero vanishes term by term, so `t` has only frame coordinates.
  have h_mid : ∀ i : 𝔰.κ, t (𝔰.indexX₀ i) = 0 := by
    simpa [Nat.Prime.ne_zero, sum_eq_zero_iff_of_nonneg] using h_nonpos.antisymm (by positivity)
  refine ⟨t ∘ 𝔰.besselFrame, ?_⟩
  rw [frameImage_one_mulVec]
  simp [init, h_dual, h_mid, funext_iff]

/-- Let `γ` be a rational element of the unitary group, `f = (e₁, …, e_ϱ, z)` the frame, and let
`t = γ f · y` be the combination of the image vectors with coefficients `y`. Suppose that `t` is
orthogonal to `e₁, …, e_ϱ` and has product `D` with `z`. Then `t` has no component along the dual
vectors `e*₁, …, e*_ϱ`, and `-N` times its `z`-coordinate is `D`. At each infinite place, `N` times
the squared length of the `X₀`-part of `t` is `|D|² - N² |y_z|²`, where `y_z = y 𝔰.top`; if it is at
most zero at some place, then `t` lies in the span of `f`. -/
lemma norm_sq_middle_part_eq {D : E} {t : 𝔰.BesselIndex → E}
    (h_prod : S.frameProducts γ *ᵥ y = Pi.single 𝔰.top D) (ht : frameImage γ.val.val *ᵥ y = t) :
    (∀ a : Fin 𝔰.ϱ, t (eStar a) = 0) ∧
    -(S.N * t 𝔰.z) = D ∧
    (∀ v : InfinitePlace E, S.N * ∑ i : 𝔰.κ, ‖Φ v (t (𝔰.indexX₀ i))‖ ^ 2 =
      ‖Φ v D‖ ^ 2 - (S.N * ‖Φ v (y 𝔰.top)‖) ^ 2) ∧
    ∀ v : InfinitePlace E, S.N * ∑ i : 𝔰.κ, ‖Φ v (t (𝔰.indexX₀ i))‖ ^ 2 ≤ 0 →
      ∃ x : Fin (𝔰.ϱ + 1) → E,
        frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ x = t := by
  subst ht
  exact ⟨frameImage_mulVec_eStar_eq_zero h_prod, neg_mul_frameImage_mulVec_z_eq h_prod,
    mul_sum_norm_sq_frameImage_mulVec_eq h_prod,
    fun v ↦ exists_frameImage_one_mulVec_eq_of_nonpos (frameImage_mulVec_eStar_eq_zero h_prod)⟩

/-- Let γ be any rational element of the unitary group, and let D_l be the leading minors of the
matrix `S.frameProducts γ` of products of the frame (e₁, …, e_ϱ, z) with its image under γ. At every
infinite place v the image of `S.termDisc γ` = |D_{ϱ+1}|² − N²|D_ϱ|², where |x|² means x x̄, equals
its absolute value: it is real and nonnegative. -/
lemma map_termDisc_eq_norm {γ : S.G E} (v : InfinitePlace E) :
    Φ v (S.termDisc γ) = ‖Φ v (S.termDisc γ)‖ := by
  -- Cramer's rule gives `y` with `S.frameProducts γ *ᵥ y = (0, …, 0, det (S.frameProducts γ))` and
  -- last coordinate the leading `ϱ × ϱ` minor; then the norm identity writes
  -- `Φ v (S.termDisc γ)` as `N` times a sum of squares.
  obtain ⟨y, hy, h_last⟩ : ∃ y : Fin (𝔰.ϱ + 1) → E,
      S.frameProducts γ *ᵥ y = Pi.single 𝔰.top (S.frameProducts γ).det ∧
      y 𝔰.top = leadingMinor (S.frameProducts γ) 𝔰.top.castSucc :=
    exists_mulVec_eq_single_det (S.frameProducts γ)
  set q : ℝ := ‖Φ v (S.frameProducts γ).det‖ ^ 2 - (S.N * ‖Φ v (y 𝔰.top)‖) ^ 2 with hq
  have h_eq : S.N * ∑ i : 𝔰.κ, ‖Φ v ((frameImage γ.val.val *ᵥ y) (𝔰.indexX₀ i))‖ ^ 2 = q :=
    mul_sum_norm_sq_frameImage_mulVec_eq hy v
  have h_nonneg : 0 ≤ q := h_eq.le.trans' (by positivity)
  have h_disc : Φ v (S.termDisc γ) = (q : ℂ) := by
    simp [hq, h_last, mul_pow, frameDisc, mul_conj']
  exact eq_coe_norm_of_nonneg (by rwa [h_disc, zero_le_real])

/-- If `S.termDisc γ` is nonzero, then `γ` has cell rank `ϱ + 1` (`S.HasCellRank` at
`last (𝔰.ϱ + 1)`). First, `NormOnePairOccursFrom (ϱ + 1)` holds vacuously, since no frame index lies
beyond it. Second, the determinant of `S.frameProducts γ` is nonzero. -/
lemma hasCellRank_last (h_disc_ne : S.termDisc γ ≠ 0) : S.HasCellRank (last (𝔰.ϱ + 1)) γ := by
  have h_form : NormOnePairOccursFrom (last (𝔰.ϱ + 1)).val γ :=
    ⟨1, by simp, fun a ha ↦ absurd ha (by simp [a.is_le])⟩
  refine ⟨h_form, fun (h_det : (S.frameProducts γ).det = 0) ↦ ?_, by simp [h_disc_ne]⟩
  -- If `det (S.frameProducts γ) = 0`, then `S.termDisc γ = -N² |D_ϱ|²`, while
  -- `map_termDisc_eq_norm` makes it nonnegative at an infinite place; so it vanishes.
  let v₀ : InfinitePlace E := Classical.ofNonempty
  have h_eval : ‖Φ v₀ (S.termDisc γ)‖ =
      -(S.N * ‖Φ v₀ (leadingMinor (S.frameProducts γ) 𝔰.top.castSucc)‖) ^ 2 := by
    rw [← ofReal_inj, ← map_termDisc_eq_norm]
    simp [frameDisc, h_det, mul_pow, mul_conj']
  have h_zero : ‖Φ v₀ (S.termDisc γ)‖ = 0 := by nlinarith [norm_nonneg (Φ v₀ (S.termDisc γ))]
  exact h_disc_ne (by simpa using h_zero)

/-- Either `S.termDisc γ` is totally positive, and then the matrix of products of the two frames
has a nonzero determinant, or `S.termDisc γ` vanishes. -/
theorem termDisc_pos_or_eq_zero (γ : S.G E) :
    ((∀ v : InfinitePlace E, 0 < Φ v (S.termDisc γ)) ∧ (S.frameProducts γ).det ≠ 0) ∨
      S.termDisc γ = 0 := by
  refine or_iff_not_imp_right.2 fun h_ne ↦
    ⟨fun v ↦ ?_, (hasCellRank_last h_ne).leadingMinor_ne_zero⟩
  rw [map_termDisc_eq_norm, zero_lt_real, norm_pos_iff]
  exact (map_ne_zero (Φ v)).2 h_ne

/-- Let `γ` be a rational element of the unitary group and `γ_v = S.ratToInf γ v` its rescaled image
at the infinite place `v`. Let `Z = realFrameGram γ_v` be the matrix of products of the frame
`(e₁, …, e_ϱ, z)` with its image under `γ_v`, and `D_ϱ` the leading principal minor of order `ϱ` of
`Z`. Then `gramDiscReal Z = |det Z|² - |D_ϱ|²` is `s²` times the complex absolute value of
`S.termDisc γ` under the embedding `Φ v`, where `s` is the product of the squared scales
`S.frameScaleSq v a` of the `n = ϱ + 1` frame vectors. -/
lemma gramDiscReal_realFrameGram_ratToInf {γ : S.G E} (v : InfinitePlace E) :
    RealPlace.gramDiscReal (realFrameGram (S.ratToInf γ v)) =
      (∏ a : Fin 𝔰.n, S.frameScaleSq v a) ^ 2 * ‖Φ v (S.termDisc γ)‖ := by
  -- The minors scale by products of the `S.frameScaleSq v a`; the last factor,
  -- `S.frameScaleSq v 𝔰.ϱ = 1 / N`, accounts for the `N ^ 2` in `S.termDisc γ`.
  have h_det : (realFrameGram (S.ratToInf γ v)).det =
      (∏ a : Fin 𝔰.n, S.frameScaleSq v a : ℝ) * Φ v (S.frameProducts γ).det := by
    simpa [frameScaleSq] using S.det_submatrix_realFrameGram_ratToInf γ v id
  have h_minor : leadingMinor (realFrameGram (S.ratToInf γ v)) 𝔰.top.castSucc =
      (∏ a : Fin 𝔰.ϱ, S.frameScaleSq v a : ℝ) *
        Φ v (leadingMinor (S.frameProducts γ) 𝔰.top.castSucc) := by
    simp [leadingMinor, det_submatrix_realFrameGram_ratToInf, frameScaleSq]
  have h_disc : frameDisc 1 (realFrameGram (S.ratToInf γ v)) =
      ((∏ a : Fin 𝔰.n, S.frameScaleSq v a) ^ 2 : ℝ) * Φ v (S.termDisc γ) := by
    simp [frameDisc, h_det, h_minor, frameScaleSq, prod_univ_castSucc]
    field_simp [Nat.Prime.ne_zero]
    ring
  rw [RealPlace.gramDiscReal, h_disc, re_ofReal_mul, ← ofReal_re ‖Φ v _‖, ← map_termDisc_eq_norm]

/-! ### Passing to the infinite and the finite places; the Bessel group; sizes of constants -/

/-- The image of an element of `New.Shape.Form.besselU0` at an infinite place lies in the
corresponding subgroup of the complex unitary group `𝔰.G₁`. -/
lemma ratToInf_mem_besselU0 (hu : u ∈ besselU0) (v : InfinitePlace E) :
    S.ratToInf u v ∈ besselU0 :=
  ⟨hu.left.ratToInf_mem_agreeWithOneOn v, hu.right.ratToInf_mem_agreeWithOneOn v⟩

/-- The image of γ at v is the conjugate of Φ_v γ by the diagonal `S.basisScale v`, so applied to
frame coordinates rescaled relative to a reference index a it gives the rescaled value of γf · y. -/
lemma frameImage_ratToInf_mulVec (γ : S.G E) (v : InfinitePlace E) (a i : 𝔰.BesselIndex)
    (y : Fin (𝔰.ϱ + 1) → E) :
    (frameImage (S.ratToInf γ v).val.val *ᵥ fun l : Fin (𝔰.ϱ + 1) ↦
        S.basisScale v a / S.basisScale v (𝔰.besselFrame l) * Φ v (y l)) i =
      S.basisScale v a / S.basisScale v i * Φ v ((frameImage γ.val.val *ᵥ y) i) := by
  simp only [mulVec, dotProduct, map_sum, map_mul, mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  suffices Φ v (γ.val.val i (𝔰.besselFrame l)) *
      (S.basisScale v (𝔰.besselFrame l) / S.basisScale v i) *
        (S.basisScale v a / S.basisScale v (𝔰.besselFrame l) * Φ v (y l)) =
      S.basisScale v a / S.basisScale v i * (Φ v (γ.val.val i (𝔰.besselFrame l)) * Φ v (y l)) by
    simpa
  field [basisScale_ne_zero]

/-- The property that a norm-one pair occurs from `j` passes from a rational element γ to its
rescaled image `S.ratToInf γ v` at any infinite place `v`. -/
lemma _root_.New.NormOnePairOccursFrom.ratToInf {γ : S.G E} (v : InfinitePlace E) {j : ℕ}
    (h_pair : NormOnePairOccursFrom j γ) :
    NormOnePairOccursFrom j (S.ratToInf γ v) := by
  obtain ⟨c, hc, h_flag⟩ := h_pair
  refine ⟨Φ v c, by simpa using congrArg (Φ v) hc, fun a ha ↦ ?_⟩
  obtain ⟨x, y, hxy, hxa, hya, h_above⟩ := h_flag a ha
  -- `S.ratToInf γ v` is `Φ v γ` conjugated by the diagonal `S.basisScale v`, so rescale the
  -- coordinates of the common vector by `d`, which is `1` at the leading index.
  let d : 𝔰.BesselIndex → ℂ := fun i ↦ S.basisScale v (𝔰.besselFrame a) / S.basisScale v i
  have hd : d (𝔰.besselFrame a) = 1 := by simp [d, basisScale_ne_zero]
  refine ⟨d ∘ 𝔰.besselFrame * Φ v ∘ x, d ∘ 𝔰.besselFrame * Φ v ∘ y, ?_, ?_⟩
  · ext i
    calc (frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) *ᵥ
          (d ∘ 𝔰.besselFrame * Φ v ∘ x)) i
        = d i * Φ v ((frameImage (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ x) i) := by
          simpa [d, Function.comp_def, Pi.mul_def] using
            frameImage_ratToInf_mulVec (S := S) 1 v (𝔰.besselFrame a) i x
      _ = d i * Φ v ((frameImage γ.val.val *ᵥ y) i) := by rw [hxy]
      _ = (frameImage (S.ratToInf γ v).val.val *ᵥ (d ∘ 𝔰.besselFrame * Φ v ∘ y)) i :=
          (frameImage_ratToInf_mulVec γ v (𝔰.besselFrame a) i y).symm
  · simp +contextual [hd, hxa, hya, h_above]

/-- If γ is a term over (c, r, c'), then the matrix of h_c⁻¹ γ h_c' in the lattice basis is
integral over Ô E. -/
lemma termsOver.isIntMatrix_translateByClassReps :
    γ ∈ S.termsOver c r c' → IsIntMatrix (Ô E) (S.translateByClassReps c c' γ).val.val := by
  rintro ⟨g, -, hg⟩
  rw [← hg]
  exact g.2.isIntMatrix

/-- For a class c, the matrix classCoord c, which takes rational coordinates to coordinates in the
basis of the lattice h_cΛ₀, carries the form in rational coordinates to the form in lattice
coordinates. -/
lemma classCoord_conj_splitGram (c : S.Classes) :
    (S.classCoord c)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram * S.classCoord c =
      (S.ratMiddle (𝔸f E)).splitGram := by
  have h_basis : (classBasis c).valᴴ * (S.ratMiddle (𝔸f E)).splitGram * (classBasis c).val =
      (S.latticeMiddle (𝔸f E)).splitGram :=
    gram_mul_of_gram_eq (toBesselH 𝔰 (S.N : 𝔸f E) c.out).prop
      (gram_besselLatticeBasis _ _ S.piN_mul_star)
  exact gram_inv_of_gram_eq h_basis

/-- The frame image of h_c⁻¹ γ h_c' in the lattice basis is the frame image of γ, read in the
adeles and written in the coordinates classCoord c of the lattice h_cΛ₀. -/
lemma frameImage_translateByClassReps :
    frameImage (S.translateByClassReps c c' γ).val.val =
      S.classCoord c * finAdeleMatrix (frameImage γ.val.val) := by
  -- the right factor `classBasis c'` of `S.translateByClassReps c c' γ` fixes the frame
  rw [coe_translateByClassReps]
  exact frameImage_mul_of_mem_agreeWithOneOn (by simp [classBasis, toBesselH, besselLatticeBasis,
    Matrix.mul_apply, Matrix.one_apply]) _

/-- The Gram matrix of the adelic element `h_c⁻¹ γ h_c'` in the lattice basis is that of `γ`. -/
lemma frameGram_translateByClassReps :
    (S.latticeMiddle (𝔸f E)).frameGram (S.translateByClassReps c c' γ) = finAdeleMatrix
      (S.frameProducts γ) := by
  -- `S.classCoord c` carries one form to the other (`classCoord_conj_splitGram`), and it fixes the
  -- frame
  have h_frame :
      ((1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E).submatrix 𝔰.besselFrame id).map
          (algebraMap E (𝔸f E)) * (S.classCoord c)ᴴ =
        (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)).submatrix 𝔰.besselFrame id := by
    simp [classCoord, ← ext_iff, classBasis, toBesselH, besselLatticeBasis,
      fromBlocks_conjTranspose, Matrix.one_apply, Matrix.mul_apply, forall_fin_succ']
  simp [frameGram_eq_frameImage, frameImage_translateByClassReps, ← classCoord_conj_splitGram c,
    ← Matrix.mul_assoc, map_splitGram_ratMiddle, h_frame]

/-- If γ is near, that is, γ joins two boxed archimedean points, then so is u γ u' for rational u
and u' in the group besselU0 of Bessel unipotent elements that fix the frame. -/
lemma IsNear.mul_of_mem_besselU0 {u' : (S.ratMiddle E).G} (h_near : S.IsNear γ)
    (hu : u ∈ besselU0) (hu' : u' ∈ besselU0) :
    S.IsNear (u * γ * u') := by
  -- if y witnesses that γ is near, then the image of u times y does so for u γ u'
  obtain ⟨y, hy, hy'⟩ := h_near
  refine ⟨S.ratToInf u * y,
    (mul_mem_boxedPoints_iff fun v ↦ ratToInf_mem_besselU0 hu v).2 hy, ?_⟩
  show (S.ratToInf (u * γ * u'))⁻¹ * (S.ratToInf u * y) ∈ S.boxedPoints
  simpa [mul_assoc, mul_mem_boxedPoints_iff, ratToInf_mem_besselU0, hu'] using hy'

/-- An isometry that fixes every vector of the frame (e₁, …, e_ϱ, z) lies in `besselS`. -/
lemma mem_besselS_of_frameImage_eq_one (h_fix : frameImage s.val.val = frameImage 1) :
    s ∈ besselS :=
  mem_besselS_iff_frameImage.2 fun i a _ ↦ congrFun₂ h_fix i a

/-- For admissible data with size parameter `b`, the powers `b ^ e` with `e ≤ 10 ^ 5 n ^ 9 f` are at
most `τ = S.tailScale = b ^ (k f / 4)`. Here `n = ϱ + 1` is the number of frame vectors, `k` is the
rank of `X₀` and `f` is the number of infinite places. -/
lemma pow_le_tailScale [S.IsAdmissible] {e : ℕ} (he : e ≤ 10 ^ 5 * 𝔰.n ^ 9 * numInfPlaces E) :
    S.b ^ e ≤ S.tailScale := by
  -- compare the exponents
  have h_exponent : (e : ℝ) ≤ 𝔰.k * numInfPlaces E / 4 := by
    have hk : 1000 * (2 * 𝔰.ϱ + 2) ^ 9 ≤ 𝔰.k := S.pow_le_k
    rify at he hk
    grw [he, ← hk]
    grind
  simpa [tailScale] using rpow_le_rpow_of_exponent_le S.one_le_b h_exponent

/-- For admissible data, the fourth power of `tailScale` `τ = b ^ (k f / 4)` is `b ^ (k f)`, where
`k = 𝔰.k` and `f = numInfPlaces E` is the number of infinite places of `E`. -/
lemma tailScale_pow_four [S.IsAdmissible] :
    S.tailScale ^ 4 = S.b ^ (𝔰.k * numInfPlaces E) := by
  rw [tailScale, ← rpow_mul_natCast (by linarith [S.thousand_le_b]), ← rpow_natCast]
  push_cast
  ring_nf

/-- The ratio of `mainSecondMoment` to `identitySecondMoment` is at least `τ ^ 44 = b ^ (11 k f)`,
where `τ = tailScale`. -/
lemma tailScale_pow_mul_identitySecondMoment_le [S.IsAdmissible] :
    S.tailScale ^ 44 * S.identitySecondMoment ≤ S.mainSecondMoment := by
  rw [pow_mul _ 4 11, tailScale_pow_four, ← pow_mul']
  exact IsAdmissible.mul_identitySecondMoment_le

lemma two_le_M : 2 ≤ S.M := by simp [two_le_iff, Nat.Prime.ne_one, Nat.Prime.ne_zero]

lemma two_le_b : 2 ≤ S.b := by linarith [S.thousand_le_b]

lemma b_pos : 0 < S.b := by linarith [S.thousand_le_b]

lemma two_le_tailScale [S.IsAdmissible] : 2 ≤ S.tailScale :=
  two_le_b.trans (by simpa using pow_le_tailScale (S := S) (e := 1) NeZero.one_le)

lemma one_le_tailScale [S.IsAdmissible] : 1 ≤ S.tailScale := one_le_two.trans two_le_tailScale

lemma identitySecondMoment_nonneg : 0 ≤ S.identitySecondMoment := by simp [identitySecondMoment]

lemma mainSecondMoment_nonneg : 0 ≤ S.mainSecondMoment :=
  div_nonneg (sq_nonneg _) (mul_pos S.besselDegree_pos (mass_pos ..)).le

/-- The number `pairCountScale`, which is the size of the reduced image of the Bessel subgroup times
the number of classes, divided by `N ^ (k f)`, is positive. -/
lemma pairCountScale_pos : 0 < S.pairCountScale := by
  have hN : 0 < S.N := S.N_prime.pos
  positivity [Nat.card_pos (α := S.reducedImage besselS)]

/-- For a natural number `C ≤ 10 ^ 5`, `C * 𝔰.n ^ 2 ≤ 𝔰.n ^ 3`. This holds because the filling data
`S` forces `𝔰.n ≥ 10 ^ 5`. -/
lemma mul_sq_le_cube (S : Filling E 𝔰) {C : ℕ} (hC : C ≤ 10 ^ 5) : C * 𝔰.n ^ 2 ≤ 𝔰.n ^ 3 := by
  rw [pow_succ' _ 2]
  exact Nat.mul_le_mul_right _ (hC.trans (S.ten_pow_five_le_varrho.trans 𝔰.ϱ.le_succ))

/-- Let the data be admissible, with size parameter `b = S.b`, and let `γ` be near: some archimedean
point `y` has both `y` and `γ⁻¹ y` in `boxedPoints`. Then the products of the frame vectors with
their images under `γ`, the entries of `S.frameProducts γ`, have absolute value at most
`b ^ (134 n)`, `n = ϱ + 1`, at every infinite place `w`. -/
lemma IsNear.norm_frameProducts_le [S.IsAdmissible] (w : InfinitePlace E)
    (i j : Fin (𝔰.ϱ + 1)) (h_near : S.IsNear γ) :
    ‖Φ w (S.frameProducts γ i j)‖ ≤ S.b ^ (134 * 𝔰.n) := by
  obtain ⟨y, hy, hy'⟩ := h_near
  have h_box : ‖frameVector (y w) i‖ ≤ S.frameBoxRadius := mem_frameBox_of_mem_boxedPoints hy w i
  have h_box' : ‖frameVector (((S.ratToInf γ)⁻¹ * y) w) j‖ ≤ S.frameBoxRadius :=
    mem_frameBox_of_mem_boxedPoints hy' w j
  have hb : 0 < S.b := b_pos
  have hN : 0 < S.N := S.N_prime.pos
  -- The entry `(i, j)` of `realFrameGram (S.ratToInf γ w)` is that of `S.frameProducts γ` times
  -- `|S.realM w| ^ ((ϱ - i) + (ϱ - j)) / N`, and it is bounded by the product of the norms of the
  -- frame vectors `i` of `y` and `j` of `γ⁻¹ y`.
  have h_entry : |S.realM w| ^ (𝔰.ϱ - i + (𝔰.ϱ - j)) * ‖Φ w (S.frameProducts γ i j)‖ ≤
      S.N * ‖frameVector (y w) i‖ * ‖frameVector (((S.ratToInf γ)⁻¹ * y) w) j‖ := by
    simpa [field, ← pow_add] using norm_realFrameGram_le_mul (S.ratToInf γ w) (y w) i j
  -- Both norms are at most `frameBoxRadius = b ^ (37 n)`, and `N ≤ b ^ (60 n)`.
  grw [← one_le_abs_realM, one_pow, one_mul, h_box, frameBoxRadius, h_box', frameBoxRadius, N_le,
    ← pow_add, ← pow_add] at h_entry
  exact h_entry.trans_eq (by ring)

/-- For admissible data with size parameter `b = S.b` and a near term `γ` (see `IsNear`), the
leading minors of the matrix `S.frameProducts γ` of products of the frame with its image under `γ`
have squared absolute value at most `b ^ (270 n²)`, `n = ϱ + 1`, at every infinite place `w`. -/
lemma IsNear.norm_map_leadingMinor_sq_le [S.IsAdmissible] (l : Fin (𝔰.ϱ + 1 + 1))
    (w : InfinitePlace E) (h_near : S.IsNear γ) :
    ‖Φ w (leadingMinor (S.frameProducts γ) l)‖ ^ 2 ≤ S.b ^ (270 * 𝔰.n ^ 2) := by
  have hb : 0 < S.b := b_pos
  -- the minor is a sum of at most `l ^ l` products of `l` entries, each bounded by
  -- `norm_frameProducts_le`
  have h_det : ‖Φ w (leadingMinor (S.frameProducts γ) l)‖ ≤
      (l : ℝ) ^ l.val * S.b ^ (134 * 𝔰.n * l.val) := by
    grw [← place_apply, leadingMinor, det_le (by bound [h_near.norm_frameProducts_le w]),
      Nat.factorial_le_pow]
    simp [← pow_mul]
  -- by `l ≤ ϱ + 1 ≤ b` the left side is at most a power of `b`; compare the exponents
  have hl : (l : ℝ) ≤ S.b := by grw [l.is_le, S.succ_le_b]
  have h_exponent : (l.val + 134 * 𝔰.n * l.val) * 2 ≤ 270 * 𝔰.n ^ 2 := by
    nlinarith [S.ten_pow_five_le_varrho, l.is_le]
  grw [h_det, hl, ← pow_add, ← pow_mul]
  exact pow_le_pow_right₀ S.one_le_b h_exponent

/-- Under `S.IsAdmissible`, if `γ` is a term over `(c, r, c')` and `u` is a term over `(c, r', d)`
with the same frame image `frameImage γ = frameImage u`, then `r⁻¹ * r'` lies in
`S.reducedImage besselS`, the reduced image of the Bessel subgroup. So `r` and `r'` lie in one left
coset of it. -/
lemma termsOver.inv_mul_mem_reducedImage [S.IsAdmissible] (hγ : γ ∈ S.termsOver c r c')
    {r' : S.ResidueGL} {d : S.Classes} (hu : u ∈ S.termsOver c r' d)
    (h_same_frame : frameImage γ.val.val = frameImage u.val.val) :
    r⁻¹ * r' ∈ S.reducedImage besselS := by
  obtain ⟨m, rfl, hm⟩ := hγ
  obtain ⟨m', rfl, hm'⟩ := hu
  have h_eq : frameImage m.val.val.val = frameImage m'.val.val.val := by
    rw [hm, hm', frameImage_translateByClassReps, frameImage_translateByClassReps, h_same_frame]
  exact ⟨m⁻¹ * m', mem_besselS_of_frameImage_eq_one (frameImage_inv_mul_eq_iff.2 h_eq), by simp⟩

/-- Under `S.IsAdmissible`, let `γ ∈ S.termsOver c r c'` and `u ∈ S.termsOver c r d`. Suppose they
have the same `frameImage`, the image of the frame `(e₁, …, e_ϱ, z)`. Then `c' = d` and `γ⁻¹ * u`
lies in `S.classUnipotent₀ c'`, the integral unipotent elements fixing every frame vector. -/
lemma termsOver.eq_and_mem_classUnipotent₀ [S.IsAdmissible] (hγ : γ ∈ S.termsOver c r c')
    {d : S.Classes} (hu : u ∈ S.termsOver c r d)
    (h_same_frame : frameImage γ.val.val = frameImage u.val.val) :
    c' = d ∧ γ⁻¹ * u ∈ S.classUnipotent₀ c' := by
  -- `γ⁻¹ * u` fixes the frame, so it lies in `besselS`, and it is a term over `(c', 1, d)`
  have h_fix : frameImage (γ⁻¹ * u).val.val = frameImage 1 :=
    frameImage_inv_mul_eq_iff.2 h_same_frame
  have h_over : γ⁻¹ * u ∈ S.termsOver c' 1 d := by simpa using mul (inv hγ) hu
  obtain ⟨h_class, h_mem⟩ :=
    eq_and_mem_classUnipotent_of_besselS (mem_besselS_of_frameImage_eq_one h_fix) h_over
  -- fixing every frame vector is the extra condition of `classUnipotent₀`
  have h_frame : frameMatrix (γ⁻¹ * u) = 1 := by
    show (frameImage (γ⁻¹ * u).val.val).submatrix 𝔰.besselFrame id = 1
    rw [h_fix]
    simp [submatrix_submatrix, submatrix_one, besselFrame_injective]
  exact ⟨h_class, h_mem, mem_besselU0_iff.2 ⟨h_mem.1, h_frame⟩⟩

/-- If `γ` is a term over `(c, r, c')`, so that `h_c⁻¹ γ h_c'` is integral, then the products of
the frame with its image under `γ` are algebraic integers. -/
lemma isIntegral_frameProducts [S.IsAdmissible] (hγ : γ ∈ S.termsOver c r c')
    (i j : Fin (𝔰.ϱ + 1)) : IsIntegral ℤ (S.frameProducts γ i j) := by
  -- the adelic entry is that of a product of two integral matrices
  have h_int : (S.latticeMiddle (𝔸f E)).frameGram (S.translateByClassReps c c' γ) i j ∈ Ô E :=
    S.isUnimodular_latticeMiddle.splitGram.isIntMatrix.mul
      (termsOver.isIntMatrix_translateByClassReps hγ) _ _
  simpa [frameGram_translateByClassReps] using h_int

end New.Filling

end
