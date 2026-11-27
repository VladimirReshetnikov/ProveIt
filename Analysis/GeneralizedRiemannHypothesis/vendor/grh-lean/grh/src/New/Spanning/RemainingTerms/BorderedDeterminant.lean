import New.Spanning.Unfolding.Link

/-!
# Links, lifts and gauges of a term

The data are `S : New.Filling`, and terms are rational elements `γ` of the unitary group
`New.Filling.G`. The frame is `f = (e₁, …, e_ϱ, z)`, `A` is the span of the `e_a` and `X₀` that of
the `x_i`. `S.frameProducts γ` is the matrix of products of `f` with `γ f`, and `S.HasCellRank j γ`
says that `γ` has cell rank `j`. `New.Filling.minorNorm j γ` is the absolute norm of the leading
`j × j` minor of `S.frameProducts γ`, scaled by a power of `N` when `j = ϱ + 1`.

## Main definitions and results

* `New.Filling.gram_linkForm_eq_zero_of_le_link`: the link is isotropic for `S.linkForm`.
* `New.Filling.linkMetric` is a totally positive form (`New.Filling.linkMetric_posDef`), and
  `New.Filling.linkDiscSq` is the squared discriminant of a lattice for it.
* `New.Filling.HasIntegralLifts`: the predicate that the columns of an adelic matrix are images
  under `New.linkMatrix γ` of vectors of `h_c Λ₀` that are adelic combinations of rational vectors
  orthogonal to `A` and `γ A`.
* `New.Filling.paddedLeading`: the first `j` rows of a matrix, completed by rows of `1`; its
  determinant is the leading minor of order `j` (`New.Filling.det_paddedLeading`). For the matrix
  `S.frameProducts γ` its inverse gives the vectors that `f` and `γ f` share
  (`New.Filling.HasCellRank.exists_shared_frame_vector`).
* `New.Filling.latticeDisc`, `New.Filling.isotropicRowsIndex`, `New.Filling.torsionIndex`: a
  discriminant and two lattice indices. `New.submoduleIndex M M'` is the index of `M ⊓ M'` in `M'`,
  `New.colLattice` a column span.
* `New.Filling.subframeMinor`: the minor `δ_*(γ)`, nonzero for a term with a cell rank
  (`New.Filling.HasCellRank.subframeMinor_ne_zero`).
* `New.Filling.minorGauge`, `New.Filling.maxGauge`: the gauges of a term.
  `New.Filling.IsNearRepresentative` marks the kept terms, and `New.Filling.IsNearTermAt` selects
  the terms that are counted.

Notions from other files:
* `New.link`: the pairs of middle coordinates of `t` and `γ⁻¹ t`, for `t` orthogonal to `A` and
  `γ A`; `New.linkMatrix γ` is the matrix of the map that sends `t` to this pair.
* `New.framePair γ`: the matrix `(f | γ f)` of the two frames; `New.isotropicFramePair γ` is its
  part `(A | γ A)`.
* `New.Filling.Classes`: the classes `c` of a finite double coset space of `U(X₀)`; `h_c` is the
  representative of `c`, and `S.translateByClassReps c c' γ` is `h_c⁻¹ γ h_c'`.
* `New.Filling.classCoord`: `S.classCoord c` takes rational coordinates to coordinates in the
  basis of `h_c Λ₀`, in which the middle Gram matrix is `S.latticeMiddle`; in rational coordinates
  it is `S.ratMiddle = diag(1, -N)`, and `S.linkForm` is the form `diag(T, -T)` for this matrix `T`.
* `New.genIndex`: the generalised index `[a]` of an adele `a`; it is `0` for a non-unit.
-/

noncomputable section

/-!
## Forms on pairs of middle coordinates, lifts, and isotropy of the link

The space has the basis `e_a`; `x_i`, `z`; `e*_a` (`New.Shape.BesselIndex`) and Gram matrix
`New.Filling.ratGram`: `ϱ` hyperbolic pairs around the middle block
`T = S.ratMiddle E = diag(1, -N)`.

* `New.Filling.dotProduct_linkMetric_mulVec`: `linkMetric` is the mean of the products of the two
  images in `X₀ ⊥ E z⁺`, where `z⁺` has norm `N`. On the link it is the form of `X₀ ⊥ E z⁺` on the
  first image, that under `linkSource` (`New.Filling.linkMetric_form_of_mem_link`).
* `New.linkMatrix` is the map to pairs; `New.Filling.gram_linkMatrix_mul` expresses forms on pairs
  through `New.Filling.ratGram`.
-/

section LinkLifts

open Matrix Module ComplexOrder Fintype RingHom Finset Algebra

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {σ τ : Type}

/-- Liouville inequality for Gram determinants, over a CM field `E` that contains a primitive root
of unity of order `5040`. Let `Q` be positive definite at each infinite place `w`, after mapping its
entries by the complex embedding `Φ w` chosen for `w`. Let `det (aᴴ Q b) ≠ 0`, and let `v`, `v'` be
invertible finite adelic matrices. Write `Nm` for the norm to `ℚ` and `[δ]` for the generalised
index `genIndex δ` of a finite adele `δ`. This is the inverse of the factor by which multiplication
by `δ` scales Haar measure if `δ` is a unit, and `0` otherwise. If `0 ≤ x ≤ [det(vᴴ aᴴ Q b v')]`,
then `x² ≤ [det v]² · |Nm det(aᴴ Q a)| · |Nm det(bᴴ Q b)| · [det v']²`. -/
lemma liouville_gram [Fintype σ] [Fintype τ]
    [DecidableEq σ] [HasPrimitiveRoot5040 E] {Q : Matrix τ τ E}
    (hQ : ∀ w : NumberField.InfinitePlace E, (Q.map (Φ w)).PosDef) (a b : Matrix τ σ E)
    (v v' : GL σ (𝔸f E)) (h_det : (aᴴ * Q * b).det ≠ 0) {x : ℝ} (hx : 0 ≤ x)
    (h_index :
      let δ : 𝔸f E := (v.valᴴ * (finAdeleMatrix (aᴴ * Q * b) * v'.val)).det
      IsUnit δ → x ≤ genIndex δ) :
    x ^ 2 ≤ genIndex v.val.det ^ 2 *
        (|↑(Algebra.norm ℚ (aᴴ * Q * a).det)| * |↑(Algebra.norm ℚ (bᴴ * Q * b).det)| *
          genIndex v'.val.det ^ 2) := by
  -- Cauchy–Schwarz for the Gram matrix of `(a | b)` at each infinite place `w`; the norm |N z| is
  -- the product of the ‖Φ w z‖².
  have h_place (w : NumberField.InfinitePlace E) :
      ‖Φ w (aᴴ * Q * b).det‖ ^ 2 ≤ ‖Φ w (aᴴ * Q * a).det‖ * ‖Φ w (bᴴ * Q * b).det‖ := by
    have h_gram := (hQ w).posSemidef.conjTranspose_mul_mul_same ((a.fromCols b).map (Φ w))
    rw [← fromBlocks_toBlocks (_ * _)] at h_gram
    simpa [map_conjTranspose, map_det] using! norm_det_sq_le_of_posSemidef h_gram
  have h_norm : |↑(norm ℚ (aᴴ * Q * b).det)| ^ 2 ≤
      |(norm ℚ (aᴴ * Q * a).det : ℝ)| * |↑(norm ℚ (bᴴ * Q * b).det)| := by
    simp only [abs_norm_eq_prod_norm_sq, ← prod_pow, ← prod_mul_distrib, ← mul_pow]
    grw [h_place]
  -- The generalised index of the pairing determinant is `[det v] * |Nm det (aᴴ Q b)| * [det v']`.
  have h_le :
      x ≤ genIndex v.val.det * (|↑(norm ℚ (aᴴ * Q * b).det)| * genIndex v'.val.det) := by
    simpa [h_det, ← mapMatrix_apply, ← map_det] using h_index
  grw [h_le, mul_pow, mul_pow, h_norm]

/-- Write `h` for the form `S.ratGram` and `T` for its middle block `S.ratMiddle E`. Let the columns
of `t` be orthogonal to `A` and `γ A`, and those of `t'` to `A` and `γ' A`. Then the pairs
`linkMatrix γ * t` and `linkMatrix γ' * t'` have, for the form `diag(a T, -b T)`, the product
`a h(t, t') - b h(t, γ γ'⁻¹ t')`. -/
lemma gram_linkMatrix_mul {S : Filling E 𝔰} {γ γ' : S.G E} {t : Matrix 𝔰.BesselIndex σ E}
    {t' : Matrix 𝔰.BesselIndex τ E} (ht : (isotropicFramePair γ)ᴴ * S.ratGram * t = 0)
    (ht' : (isotropicFramePair γ')ᴴ * S.ratGram * t' = 0) (a b : E) :
    (linkMatrix γ * t)ᴴ * (a • S.ratMiddle E).fromBlocks 0 0 (-b • S.ratMiddle E) *
        (linkMatrix γ' * t') =
      a • (tᴴ * S.ratGram * t') - b • (tᴴ * S.ratGram * ((γ * γ'⁻¹).val.val * t')) := by
  -- Entry by entry. The columns `x` of `t` and `y` of `t'` have vanishing `eStar` coordinates, as
  -- do `γ⁻¹ x` and `γ'⁻¹ y`; on such vectors the form `S.ratGram` is `S.ratMiddle E` on the middle
  -- coordinates.
  ext i j
  let x : 𝔰.BesselIndex → E := t.col i
  let y : 𝔰.BesselIndex → E := t'.col j
  obtain ⟨hx, hγx⟩ :
      (∀ l : Fin 𝔰.ϱ, x (eStar l) = 0) ∧ ∀ l : Fin 𝔰.ϱ, (γ⁻¹.val.val *ᵥ x) (eStar l) = 0 :=
    orthogonal_isotropicFramePair_iff.1 (congrFun (congrArg transpose ht) i)
  obtain ⟨hy, hγy⟩ :
      (∀ l : Fin 𝔰.ϱ, y (eStar l) = 0) ∧ ∀ l : Fin 𝔰.ϱ, (γ'⁻¹.val.val *ᵥ y) (eStar l) = 0 :=
    orthogonal_isotropicFramePair_iff.1 (congrFun (congrArg transpose ht') j)
  change star (linkMatrix γ *ᵥ x) ᵥ* (a • S.ratMiddle E).fromBlocks 0 0 (-b • S.ratMiddle E) ⬝ᵥ
      linkMatrix γ' *ᵥ y =
    a * star x ᵥ* S.ratGram ⬝ᵥ y - b * star x ᵥ* S.ratGram ⬝ᵥ (γ * γ'⁻¹).val.val *ᵥ y
  -- in the last term apply the isometry `γ⁻¹` to both vectors first
  have h_move : γ⁻¹.val.val *ᵥ ((γ * γ'⁻¹).val.val *ᵥ y) = γ'⁻¹.val.val *ᵥ y := by
    simp [mulVec_mulVec, ← Matrix.mul_assoc]
  rw [← dotProduct_mulVec, ← dotProduct_mulVec, ← dotProduct_mulVec,
    ← U.form_mulVec_mulVec γ⁻¹ x ((γ * γ'⁻¹).val.val *ᵥ y), h_move,
    ratGram_form_of_eStar_eq_zero hx hy, ratGram_form_of_eStar_eq_zero hγx hγy]
  simp [linkMatrix_mulVec, fromBlocks_mulVec, smul_mulVec, neg_mulVec, dotProduct, mul_sum,
    sub_eq_add_neg, mul_add, mul_left_comm]

/-- Let `A` be the isotropic span of the basis vectors `e₁, …, e_ϱ`. The link of `γ` is the space of
the pairs of middle coordinates (those in `X₀ ⊕ E z`) of `t` and `γ⁻¹ t`, for `t` orthogonal to `A`
and `γ A`. Two matrices `v`, `u` with columns in the link are orthogonal for the form
`S.linkForm = diag(T, -T)`, where `T = S.ratMiddle E` is the Gram matrix of `X₀ ⊕ E z`. -/
lemma gram_linkForm_eq_zero_of_le_link [Fintype τ] [DecidableEq τ] {S : Filling E 𝔰} {γ : S.G E}
    {v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E} [Fintype σ]
    {u : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) σ E}
    (hv : colSpan v ≤ link γ) (hu : colSpan u ≤ link γ) : vᴴ * S.linkForm * u = 0 := by
  classical
  -- each entry pairs a column of `v` with a column of `u`, and both lie in the link
  rw [Matrix.mul_assoc]
  ext i j
  have huj : u.col j ∈ link γ := hu ⟨Pi.single j 1, u.mulVec_single_one j⟩
  have hvi : v.col i ∈ link γ := hv ⟨Pi.single i 1, v.mulVec_single_one i⟩
  change star (v.col i) ⬝ᵥ S.linkForm *ᵥ u.col j = 0
  exact mem_link_iff_orthogonal.1 huj _ hvi

variable [Fintype τ] [DecidableEq τ] (S : Filling E 𝔰) (c : S.Classes) {c' : S.Classes} {γ : S.G E}
  (t : Matrix 𝔰.BesselIndex σ E) (t' : Matrix 𝔰.BesselIndex τ E)
  (v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E)

/-- The matrix `½·diag(T, T) + N⁻¹·L* L` on two copies of `X₀ ⊕ E z`, where `T = S.ratMiddle E`,
the two rows `L = zRowBlockDiagonal T` are the `z`-row of `T` in either copy, and `*` is the
conjugate transpose. -/
def linkMetric : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) E :=
  (2⁻¹ : E) • (S.ratMiddle E).fromBlocks 0 0 (S.ratMiddle E) +
    (S.N : E)⁻¹ • ((zRowBlockDiagonal (S.ratMiddle E))ᴴ * zRowBlockDiagonal (S.ratMiddle E))

/-- The number `|Nm det(vᴴ Q v)| · [det e]²`, with `Nm` the norm to `ℚ`, `[·]` the generalised
index and `Q = S.linkMetric`: the squared discriminant of the lattice with adelic basis `v e`. -/
def linkDiscSq (e : GL τ (𝔸f E)) : ℝ :=
  |↑(Algebra.norm ℚ (vᴴ * S.linkMetric * v).det)| * genIndex e.val.det ^ 2

variable {S} (γ) {R : Type*} [CommRing R] [StarRing R] {T : 𝔰.Form R} (k : T.G)

/-- Let `T` be a Gram matrix on the middle coordinates and `k` an isometry of `T.splitGram`, the
form made of `ϱ` hyperbolic pairs around `T`. For every vector `t`, its products with `z` and with
`k z` are obtained from its image under `linkMatrix k` by `zRowBlockDiagonal T`, the block diagonal
matrix with two copies of the `z`-row of `T`. -/
lemma framePair_last_eq_zRowBlockDiagonal_mul :
    ((framePair k).submatrix id
        (Sum.map (fun _ : Unit ↦ 𝔰.top) fun _ : Unit ↦ 𝔰.top))ᴴ * T.splitGram =
      zRowBlockDiagonal T * linkMatrix k := by
  -- The `z`-row of `T.splitGram * g` only sees the middle rows of `g`. The first row of the claim
  -- is the case `g = 1`, the second the case `g = k⁻¹`, by unitarity.
  have h_row (g : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R) (l : 𝔰.BesselIndex) :
      (T.splitGram * g) (𝔰.besselFrame 𝔰.top) l = (T.toRows₂ * g.toRows₂.toRows₁) () l := by
    simp [splitGram, Matrix.mul_apply]
  ext (i | i) l
  · simpa [Matrix.mul_apply, Matrix.one_apply, linkMatrix] using h_row 1 l
  · have h_inv := h_row k⁻¹.val.val l
    rw [U.form_mul_inv_eq k] at h_inv
    simpa [Matrix.mul_apply, linkMatrix] using h_inv

/-- The change to lattice coordinates `S.classCoord c` fixes the isotropic coordinates, and on the
middle ones its columns are those of `S.classCoordX₀ c` and the vector `z`. -/
lemma classCoord_eq_fromBlocks :
    S.classCoord c =
      fromBlocks 1 0 0 (((S.classCoordX₀ c).fromCols (fromRows 0 1)).fromBlocks 0 0 1) := by
  simp [classCoordX₀, classCoord, classBasis, toBesselH, besselLatticeBasis, fromBlocks_multiply,
    fromCols_mul_fromBlocks]

/-- The columns of `m` are the images under `linkMatrix γ` of vectors of the lattice `h_c Λ₀`
(the vectors with integral `S.classCoord c`-coordinates) that are adelic combinations of rational
vectors orthogonal to `A` and `γ A`. -/
def HasIntegralLifts (m : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ (𝔸f E)) : Prop :=
  ∃ ρ : Type, ∃ (_ : Fintype ρ) (t : Matrix 𝔰.BesselIndex ρ E) (w : Matrix ρ τ (𝔸f E)),
    (isotropicFramePair γ)ᴴ * S.ratGram * t = 0 ∧
    IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix t * w) ∧
    finAdeleMatrix (linkMatrix γ * t) * w = m

/-! ### Products in the coordinates of the lattice -/

/-- The basis `x_i` of `X₀`, written in the lattice coordinates of `c` (the columns of
`S.classCoordX₀ c`), is orthonormal for the middle Gram matrix `S.latticeMiddle` of the lattice. -/
lemma gram_classCoordX₀ : (S.classCoordX₀ c)ᴴ * S.latticeMiddle (𝔸f E) * S.classCoordX₀ c = 1 := by
  -- the block of `classCoord_conj_splitGram` with rows and columns `𝔰.indexX₀`
  simpa [classCoord_eq_fromBlocks, splitGram, fromBlocks_conjTranspose, fromBlocks_multiply] using!
    congrArg (submatrix · 𝔰.indexX₀ 𝔰.indexX₀) (classCoord_conj_splitGram c)

omit [Fintype τ] [DecidableEq τ] in
/-- The products of rational vectors `t`, `t'` for the form `S.ratGram` can be computed in the
lattice coordinates `S.classCoord c` of a class `c`, with the Gram matrix of `S.latticeMiddle`. -/
lemma classCoord_gram :
    (S.classCoord c * finAdeleMatrix t)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram *
        (S.classCoord c * finAdeleMatrix t') =
      finAdeleMatrix (tᴴ * S.ratGram * t') := by
  simp [map_splitGram_ratMiddle, ← classCoord_conj_splitGram c, Matrix.mul_assoc,
    finAdeleMatrix_conjTranspose]

variable [Fintype σ] {c γ v t t' k}

/-- The form `S.linkMetric` is half the orthogonal sum of two copies of `S.positiveGram`, the
Gram matrix `diag(1, N)` of the space `X₀ ⊥ E z⁺`, in which `z⁺` has norm `N`. -/
lemma linkMetric_eq_smul_fromBlocks :
    S.linkMetric = (2⁻¹ : E) • fromBlocks S.positiveGram 0 0 S.positiveGram := by
  have hN : (S.N : E) ≠ 0 := Nat.cast_ne_zero.2 S.N_prime.ne_zero
  -- the sixteen blocks of entries are computed in the same way
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;>
    simp [linkMetric, positiveGram, Shape.middleGram, Matrix.mul_apply, diagonal_apply,
      Matrix.one_apply, hN] <;>
    ring

/-- `S.linkMetric` is positive definite at every complex embedding `Φ w` of the CM type. -/
lemma linkMetric_posDef (w : NumberField.InfinitePlace E) : (S.linkMetric.map (Φ w)).PosDef := by
  -- it is diagonal with the entries `1/2` on `X₀` and `N/2` at `z`
  rw [linkMetric_eq_smul_fromBlocks, positiveGram, fromBlocks_diagonal, ← diagonal_smul,
    diagonal_map (map_zero _), posDef_diagonal_iff]
  rintro ((i | i) | (i | i)) <;> simp [map_ofNat, S.N_prime.pos]

open Sum in
/-- Let `X₀ ⊥ E z⁺` be the space of middle coordinates with the Gram matrix
`S.positiveGram = diag(1, N)`. Its last basis vector `z⁺` has norm `N = S.N`, the prime of the
filling `S`. Let `p`, `q` be pairs of middle coordinate vectors, indexed by
`𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex`. The form `linkMetric` on `p`, `q` is the mean of the products in
this space of their two images under `linkSource` and under `linkTarget`. `linkSource` takes the
`X₀`-part of the first member and the `z`-coordinate of the second; `linkTarget` does the same with
the members exchanged. -/
lemma dotProduct_linkMetric_mulVec (p q : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E) :
    star p ⬝ᵥ S.linkMetric *ᵥ q =
      2⁻¹ * (star (linkSource E 𝔰 p) ⬝ᵥ S.positiveGram *ᵥ linkSource E 𝔰 q +
        star (linkTarget E 𝔰 p) ⬝ᵥ S.positiveGram *ᵥ linkTarget E 𝔰 q) := by
  have h_split : star p ⬝ᵥ fromBlocks S.positiveGram 0 0 S.positiveGram *ᵥ q =
      star (p ∘ inl) ⬝ᵥ S.positiveGram *ᵥ (q ∘ inl) +
        star (p ∘ inr) ⬝ᵥ S.positiveGram *ᵥ (q ∘ inr) := by
    simp [fromBlocks_mulVec, dotProduct]
  rw [linkMetric_eq_smul_fromBlocks, smul_mulVec, dotProduct_smul, h_split]
  simp [dotProduct_positiveGram_mulVec_eq_sum_add, linkSource, linkTarget]
  ring

/-- For pairs `p`, `q` in the link of `γ`, the form `linkMetric` is the product of their images
under `linkSource` for the Gram matrix `S.positiveGram = diag(1, N)` on the middle coordinates. -/
theorem linkMetric_form_of_mem_link {p q : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E}
    (hp : p ∈ link γ) (hq : q ∈ link γ) :
    star p ⬝ᵥ S.linkMetric *ᵥ q =
      star (linkSource E 𝔰 p) ⬝ᵥ S.positiveGram *ᵥ linkSource E 𝔰 q := by
  rw [dotProduct_linkMetric_mulVec, ← form_linkSource_eq_form_linkTarget hp hq]
  ring

/-- If the columns of `v` are independent (`v` has a left inverse), then their Gram matrix for
`S.linkMetric` has nonzero determinant. -/
lemma det_gram_linkMetric_ne_zero (h : HasLeftInv v) : (vᴴ * S.linkMetric * v).det ≠ 0 := by
  -- At a complex embedding `Φ w` the form `S.linkMetric` is positive definite and `v` stays
  -- injective.
  obtain ⟨l, hl⟩ := h
  let w : NumberField.InfinitePlace E := Classical.ofNonempty
  have h_inj : (v.map (Φ w)).mulVec.Injective :=
    HasLeftInv.injective_mulVec ⟨l.map (Φ w), by simp [← Matrix.map_mul, hl]⟩
  apply_fun Φ w
  simpa [map_det, map_conjTranspose] using
    ((linkMetric_posDef w).conjTranspose_mul_mul_same h_inj).det_pos.ne'

omit [CMType E] in
/-- If `v` has a left inverse, the number of its columns is the dimension of their span. -/
lemma card_eq_finrank_colSpan {v : Matrix σ τ E} (h : HasLeftInv v) :
    Fintype.card τ = Module.finrank E (colSpan v) := by
  classical
  simp [v.mulVecLin.finrank_range_of_inj h.injective_mulVec]

/-- In the lattice coordinates `S.classCoord c`, the frame pair `framePair γ` (entries embedded in
the finite adeles) is `framePair` of `S.translateByClassReps c c' γ`, namely h_c⁻¹ γ h_c'. -/
lemma classCoord_mul_framePair :
    S.classCoord c * finAdeleMatrix (framePair γ) = framePair (S.translateByClassReps c c' γ) := by
  rw [framePair, framePair, frameImage_translateByClassReps]
  simp [← ext_iff, classCoord_eq_fromBlocks, Fin.forall_fin_succ', Matrix.mul_apply,
    Matrix.one_apply]

/-- In the lattice coordinates `S.classCoord c`, the pair `isotropicFramePair γ` = (A | γ A) of
isotropic frames (entries embedded in the finite adeles) is `isotropicFramePair` of
`S.translateByClassReps c c' γ`, namely h_c⁻¹ γ h_c'. -/
lemma classCoord_mul_isotropicFramePair :
    S.classCoord c * finAdeleMatrix (isotropicFramePair γ) =
      isotropicFramePair (S.translateByClassReps c c' γ) :=
  -- both sides are the columns of index `castSucc a` of `classCoord_mul_framePair`
  congrArg (submatrix · id (Sum.map Fin.castSucc Fin.castSucc)) classCoord_mul_framePair

/-- Let `k = S.translateByClassReps c c' γ = h_c⁻¹ γ h_c'` be the matrix of the rational element `γ`
in the bases of the lattices of the classes `c` and `c'`, and let `C = S.classCoord c` take rational
coordinates to those of the lattice of `c`. In these the form has the Gram matrix
`J = (S.latticeMiddle (𝔸f E)).splitGram`, made of `ϱ` hyperbolic pairs around the middle block
`S.latticeMiddle`; in rational coordinates it has the Gram matrix `J₀ = S.ratGram`. Write `F_g(k)`
for the columns with the indices `g` of `framePair k = (f | k f)`. Then
`F_g(k)ᴴ J (C t) = F_g(γ)ᴴ J₀ t` as finite adelic matrices, for every rational matrix `t` with rows
indexed by the basis `e₁, …, e_ϱ, x_i, z, e*₁, …, e*_ϱ`. -/
lemma framePair_translateByClassReps_mul_classCoord {S : Filling E 𝔰} {ι ρ : Type} [Fintype ι]
    [Fintype ρ] (c c' : S.Classes) (γ : S.G E) (g : ι → Fin (𝔰.ϱ + 1) ⊕ Fin (𝔰.ϱ + 1))
    (t : Matrix 𝔰.BesselIndex ρ E) :
    ((framePair (S.translateByClassReps c c' γ)).submatrix id g)ᴴ *
      (S.latticeMiddle (𝔸f E)).splitGram *
        (S.classCoord c * finAdeleMatrix t) =
      finAdeleMatrix (((framePair γ).submatrix id g)ᴴ * S.ratGram * t) := by
  classical
  -- selecting columns commutes with the change of coordinates
  have h_select : (framePair (S.translateByClassReps c c' γ)).submatrix id g =
      S.classCoord c * finAdeleMatrix ((framePair γ).submatrix id g) :=
    congrArg (submatrix · id g) classCoord_mul_framePair.symm
  rw [h_select, classCoord_gram]

/-- If the matrix of `k` has entries in a subring `O`, so has the pair `(f | k f)` of frames. -/
lemma isIntMatrix_framePair {O : Subring R} (hk : IsIntMatrix O k.val.val) :
    IsIntMatrix O (framePair k) := by
  simp [IsIntMatrix, ite_mem, hk _, Matrix.one_apply]

end New.Filling

end LinkLifts

/-!
## Lattice indices, gauges and the selection of counted terms

A term `γ` is taken with two classes `c`, `c'`; its adelic form is
`S.translateByClassReps c c' γ = h_c⁻¹ γ h_c'`.
-/

section GaugeDefs

open NumberField Matrix Fin Pointwise

namespace New.Filling

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape}

section

variable (S : Filling E 𝔰) {R : Type*} (j : Fin (𝔰.ϱ + 2)) (c : S.Classes)
  (Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) R) (k : S.GFin)

/-! ### Rows of the matrix of products -/

/-- The indices `a < j` of the isotropic vectors `e_a` of the frame. -/
abbrev IndexBelow : Type := {a : Fin 𝔰.ϱ // a.val < j}

/-- The rows of `Z` that belong to the isotropic vectors of the frame. -/
abbrev isotropicRows : Matrix (Fin 𝔰.ϱ) (Fin (𝔰.ϱ + 1)) R := Z.submatrix (castSucc (n := 𝔰.ϱ)) id

/-- The first `j` rows of `Z`, completed by rows of the identity matrix. -/
def paddedLeading [CommRing R] : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) R :=
  of fun a b ↦ if a.1 < ↑j then Z a b else if a = b then 1 else 0

/-- The matrix `paddedLeading j Z` keeps the first `j` rows of `Z` and completes them by the
remaining rows of the identity matrix. Its determinant is the leading minor `D_j` of `Z`. -/
@[simp]
lemma det_paddedLeading [CommRing R] {j : Fin (𝔰.ϱ + 2)}
    {Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) R} :
    (paddedLeading j Z).det = leadingMinor Z j := by
  -- Expanding along the rows of `1` leaves the minor on the indices `a < j`, reindexed by `Fin j`.
  have h_reindex : leadingMinor Z j =
      (Z.submatrix (fun a : {a : Fin (𝔰.ϱ + 1) // a.val < j} ↦ a.val) Subtype.val).det :=
    det_submatrix_equiv_self (castLEquiv j.is_le) (Z.submatrix Subtype.val Subtype.val)
  rw [h_reindex, paddedLeading]
  -- What is left is to match the piecewise rows and the decidability instances.
  convert! Z.det_piecewise_one_eq_submatrix_det {a : Fin (𝔰.ϱ + 1) | a.val < j} <;> aesop

/-! ### Discriminants and indices -/

/-- The middle coordinates of the image of the frame under `γ`: those in `X₀` and along `z`. -/
abbrev frameMiddle (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R) :
    Matrix 𝔰.MiddleIndex (Fin (𝔰.ϱ + 1)) R :=
  (frameImage (R := R) (𝔰 := 𝔰) γ).toRows₂.toRows₁

/-- The discriminant (`New.Filling.sublatticeDiscriminant`) of `Λ ∩ V`, for the lattice `Λ` of the
class `c` and a subspace `V` of `X₀`. -/
def latticeDisc : Submodule E (𝔰.κ → E) → ℝ := sublatticeDiscriminant (S.gram_classCoordX₀ c)

/-- Among the products of `Λ ∩ A` with the frame of `k`, the index of those that
come from the vectors `e_a` with `a < j`. -/
def isotropicRowsIndex : ℕ :=
  submoduleIndex
    (colLattice (Ô E)
      (submatrix ((S.latticeMiddle (𝔸f E)).frameGram k) (fun a : IndexBelow j ↦ a.1.castSucc) id)ᴴ)
    (colLattice (Ô E) (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram k))ᴴ)

/-- The index of `Λ ∩ A + k (Λ ∩ A)` in `Λ ∩ (A + k A)`, for the standard lattice `Λ` and the
isotropic space `A`. -/
def torsionIndex : ℕ :=
  submoduleIndex (colLattice (Ô E) (isotropicFramePair k))
    (intVectors (Ô E) 𝔰.BesselIndex ⊓ (colSpan (isotropicFramePair k)).restrictScalars (Ô E))

/-- The absolute norm of the leading minor of order `j` of the matrix of products of the frame with
its image under `γ`, divided by `N ^ (2 r)` at the top rank `j = ϱ + 1`, with `r` the number of
infinite places. -/
def minorNorm (j : Fin (𝔰.ϱ + 2)) (γ : S.G E) : ℝ :=
  |(Algebra.norm ℚ (leadingMinor (S.frameProducts γ) j) : ℝ)| /
    S.N ^ (2 * (j - 𝔰.ϱ) * numInfPlaces E)

/-- The indices of the subframe made of the first `j` vectors of the frame `(e₁, …, e_ϱ, z)` and its
last vector `z`. For `j = ϱ` and `j = ϱ + 1` the subframe is the whole frame. -/
abbrev subframeIndices (j : Fin (𝔰.ϱ + 2)) : Finset (Fin (𝔰.ϱ + 1)) :=
  {a : Fin (𝔰.ϱ + 1) | a.val < j.val ∨ a = 𝔰.top}

/-- The minor `δ_*(γ)` of `S.frameProducts γ` on the rows and columns `subframeIndices j`: the
determinant of the products of the subframe made of the first `j` vectors of the frame
`(e₁, …, e_ϱ, z)` and its last vector `z` with the image of this subframe under `γ`. -/
def subframeMinor (j : Fin (𝔰.ϱ + 2)) (γ : S.G E) : E :=
  ((S.frameProducts γ).submatrix ((↑) : subframeIndices j → Fin (𝔰.ϱ + 1))
    ((↑) : subframeIndices j → Fin (𝔰.ϱ + 1))).det

/-- The gauge `𝗀♯ = Nm δ_*(γ) / (i_γ i'_γ N ^ r)` of the term `γ` from `c'` to `c`. Here `Nm` is the
absolute norm, `δ_*(γ) = S.subframeMinor j γ`, `i_γ` and `i'_γ` are the indices `isotropicRowsIndex`
at `h_c⁻¹ γ h_c'` and at its inverse, and `r` is the number of infinite places. -/
def minorGauge (j : Fin (𝔰.ϱ + 2)) (c c' : S.Classes) (γ : S.G E) : ℝ :=
  |(Algebra.norm ℚ (S.subframeMinor j γ) : ℝ)| /
    (S.isotropicRowsIndex j (S.translateByClassReps c c' γ) * S.isotropicRowsIndex j
      (S.translateByClassReps c c' γ)⁻¹ *
      S.N ^ numInfPlaces E)

/-- The larger of `𝗀♯ = minorGauge` and `termDiscNorm`, the product of the absolute values of
`𝗀(γ) = S.termDisc γ` at the infinite places. The gauge `𝗀*` is this number times a power of the
congruence level `S.M`. -/
def maxGauge (j : Fin (𝔰.ϱ + 2)) (c c' : S.Classes) (γ : S.G E) : ℝ :=
  max (S.minorGauge j c c' γ) (S.termDiscNorm γ)

/-- The term `γ` is near, and it is the chosen element of its double coset `U⁰_c γ U⁰_c'`. Near
means that some archimedean point `y` and `γ⁻¹ y` both lie in `S.boxedPoints`, the reduced points
of bounded size at every infinite place. The group `U⁰_c = S.classUnipotent₀ c` consists of the
rational `u` in the unipotent group `besselU` that fix every vector of the frame and have
`h_c⁻¹ u h_c` in the principal congruence subgroup `S.principalLevel`. -/
def IsNearRepresentative (c c' : S.Classes) (γ : S.G E) : Prop :=
  S.IsNear γ ∧ (DoubleCoset.mk (S.classUnipotent₀ c) (S.classUnipotent₀ c') γ).out = γ

/-- Let `p = (c', γ)`, and let `B = S.reducedImage besselS` be the image in the finite group
`S.ResidueGL` of the integral points of the Bessel subgroup `besselS`. The term `γ` from `c'` to `c`
is near and chosen (`IsNearRepresentative`) and has a cell rank (`HasCellRank`). Moreover
`h_c⁻¹ γ h_c'` is integral with reduction `s` (`termsOver`), and `s = r t` for the chosen
representative `r` of the coset `s B`. -/
def IsNearTermAt (c : S.Classes) (t : S.reducedImage besselS) (p : S.Classes × S.G E) : Prop :=
  (S.IsNearRepresentative c p.1 p.2 ∧ ∃ j : Fin (𝔰.ϱ + 2), S.HasCellRank j p.2) ∧
    ∃ s : S.ResidueGL, p.2 ∈ S.termsOver c s p.1 ∧ (Subgroup.groupEquivQuotientProdSubgroup s).2 = t

omit [HasPrimitiveRoot5040 E] in
/-- At the top rank `j = ϱ + 1` all isotropic vectors of the frame are counted, so the index
`isotropicRowsIndex` is `1`. -/
lemma isotropicRowsIndex_top : S.isotropicRowsIndex ⊤ k = 1 :=
  AddSubgroup.relIndex_eq_one.2
    (colLattice_le fun a : Fin 𝔰.ϱ ↦ col_mem_colLattice (⟨a, by simp⟩ : IndexBelow ⊤))

end

/-! ### Terms of cell rank `j` -/

section

omit [HasPrimitiveRoot5040 E]

/-- If `γ` has cell rank `j` (`S.HasCellRank j γ`), then `S.minorNorm j γ`, the absolute norm of the
leading minor of order `j` of `S.frameProducts γ` (divided by a power of `N` when `j = ϱ + 1`), is
positive. -/
lemma HasCellRank.minorNorm_pos {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    (h : S.HasCellRank j γ) : 0 < S.minorNorm j γ := by
  simp [minorNorm, h.leadingMinor_ne_zero, zero_lt_iff, Nat.Prime.ne_zero]

/-- If `γ` has cell rank `j` for `S`, then so does `γ⁻¹`. That is, `New.NormOnePairOccursFrom j`
holds, the leading minor `D_j` of `S.frameProducts` is nonzero, and `S.termDisc` is nonzero exactly
when `j = ϱ+1`, for `γ⁻¹` as for `γ`. -/
lemma HasCellRank.inv {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    (h : S.HasCellRank j γ) : S.HasCellRank j γ⁻¹ := by
  -- `S.frameProducts γ⁻¹` is the conjugate transpose of `S.frameProducts γ`, so its leading minors
  -- are the conjugates, and `frameDisc`, made of the products of minors with their conjugates, does
  -- not change.
  refine ⟨h.normOnePairOccursFrom.inv, ?_, ?_⟩
  · simpa [leadingMinor, ← conjTranspose_submatrix] using h.leadingMinor_ne_zero
  · simpa [leadingMinor, frameDisc, ← conjTranspose_submatrix, mul_comm] using
      h.lt_iff_termDisc_ne_zero

/-- If `γ` has cell rank `j` (`S.HasCellRank j γ`), then `paddedLeading j (S.frameProducts γ)`, the
first `j` rows of `S.frameProducts γ` completed by identity rows, is invertible: its product with
its inverse is `1`. -/
lemma HasCellRank.paddedLeading_mul_inv {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    (h : S.HasCellRank j γ) :
    paddedLeading j (S.frameProducts γ) * (paddedLeading j (S.frameProducts γ))⁻¹ = 1 := by
  simp [h.leadingMinor_ne_zero]

/-- Let `γ` have cell rank `j`: the flags of the frame `f` and of `γ f` share a vector at each index
from `j` on, and the leading minor `D_j` of the matrix `Z = S.frameProducts γ` of products of `f`
with `γ f` is nonzero. The matrix `paddedLeading j Z` keeps the rows `a < j` of `Z` and has rows of
the identity elsewhere; its determinant is `D_j`, so it is invertible. For `b ≥ j`, the combination
of the columns `frameImage γ` of `γ f` whose coefficients form column `b` of its inverse is
`frameImage 1 *ᵥ w` for some `w`, so it lies in the span of `f`. -/
lemma HasCellRank.exists_shared_frame_vector {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    (h : S.HasCellRank j γ) {b : Fin (𝔰.ϱ + 1)} (hjb : j.val ≤ b.val) :
    ∃ w : Fin (𝔰.ϱ + 1) → E, frameImage 1 *ᵥ w =
      frameImage γ.val.val *ᵥ col (paddedLeading j (S.frameProducts γ))⁻¹ b := by
  -- The norm-one pairs occurring from `j` on give `x` equal to the `b`-th basis vector from index
  -- `j` on, such that the combination `x` of `γ f` lies in the span of `f`; this `x` is the `b`-th
  -- column of the inverse.
  obtain ⟨w, x, hx, hwx⟩ : ∃ w x : Fin (𝔰.ϱ + 1) → E,
      (∀ a : Fin (𝔰.ϱ + 1), j.val ≤ a.val → x a = col 1 b a) ∧
      frameImage 1 *ᵥ w = frameImage γ.val.val *ᵥ x :=
    exists_frameImage_eq_of_normOnePairOccursFrom h.normOnePairOccursFrom (col 1 b)
  have hZ : S.frameProducts γ *ᵥ x = Pi.single 𝔰.top (-↑S.N * w 𝔰.top) :=
    frameProducts_mulVec_of_frameImage_eq hwx
  have h_col : paddedLeading j (S.frameProducts γ) *ᵥ x = Pi.single b 1 := by
    ext a
    by_cases ha : a.val < j.val
    · -- A row of index `< j ≤ b` is a row of the products, and it is not the last one.
      have ha_top : a ≠ 𝔰.top := Fin.ne_of_val_ne (by simp; lia)
      have hab : a ≠ b := Fin.ne_of_val_ne (by lia)
      calc (paddedLeading j (S.frameProducts γ) *ᵥ x) a = (S.frameProducts γ *ᵥ x) a := by
            simp [paddedLeading, mulVec, dotProduct, ha]
        _ = (Pi.single b 1 : Fin (𝔰.ϱ + 1) → E) a := by simp [hZ, ha_top, hab]
    · -- The rows from `j` on are rows of `1`.
      simp [paddedLeading, mulVec, dotProduct, ha, hx a (not_lt.1 ha), Matrix.one_apply,
        Pi.single_apply]
  -- The padded matrix is invertible, its determinant being a nonzero leading minor.
  have hx_col : col (paddedLeading j (S.frameProducts γ))⁻¹ b = x := by
    simp [← mulVec_single_one, ← h_col, h.leadingMinor_ne_zero]
  exact ⟨w, by rw [hx_col, hwx]⟩

/-- A term has at most one cell rank: if `γ` has the cell ranks `j` and `j'`, then `j = j'`. With
`D_l` the leading minors of `S.frameProducts γ`, cell rank `j` means that norm-one pairs occur from
the index `j` on (`New.NormOnePairOccursFrom`), `D_j ≠ 0`, and that `𝗀(γ) = |D_{ϱ+1}|² - N² |D_ϱ|²`
is nonzero exactly when `j = ϱ + 1`. -/
lemma HasCellRank.unique {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    (h : S.HasCellRank j γ) {j' : Fin (𝔰.ϱ + 2)} (h' : S.HasCellRank j' γ) : j = j' := by
  -- Let `j < j'`. Then `j' ≤ ϱ`, as the top rank is decided by `𝗀 ≠ 0`. The shared vector at the
  -- index `j' - 1` gives a relation between the columns of the leading block of order `j'`, whose
  -- determinant is not zero.
  wlog h_lt : j < j' generalizing j j' with h_symm
  · obtain h_eq | h_gt := (not_lt.1 h_lt).eq_or_lt
    exacts [h_eq.symm, (h_symm h' h h_gt).symm]
  obtain ⟨ζ, -, h_flag⟩ : ∃ ζ : E, ζ * star ζ = 1 ∧
      ∀ a : Fin (𝔰.ϱ + 1), j.val ≤ a.val → PairOccursAt γ ζ 1 a := h.normOnePairOccursFrom
  have h_low : j'.val ≤ 𝔰.ϱ := by
    by_contra! h_top
    have hj_high : 𝔰.ϱ < j.val := h.lt_iff_termDisc_ne_zero.2 (h'.lt_iff_termDisc_ne_zero.1 h_top)
    lia
  obtain ⟨i, hi⟩ : ∃ i : Fin (𝔰.ϱ + 1), i.val + 1 = j'.val := ⟨⟨j'.val - 1, by lia⟩, by lia⟩
  have hji : j.val ≤ i.val := by lia
  obtain ⟨x, y, hxy, -, hy_lead, h_above⟩ : PairOccursAt γ ζ 1 i := h_flag i hji
  have hZ : S.frameProducts γ *ᵥ y = Pi.single 𝔰.top (-↑S.N * x 𝔰.top) :=
    frameProducts_mulVec_of_frameImage_eq hxy
  let y' : Fin j'.val → E := y ∘ castLE j'.is_le
  have hy'_ne : y' ≠ 0 := by
    intro h_zero
    have hy_zero : y i = 0 := congrFun h_zero ⟨i.val, by lia⟩
    simp [hy_lead] at hy_zero
  have h_kernel :
      (S.frameProducts γ).submatrix (castLE j'.is_le) (castLE j'.is_le) *ᵥ y' = 0 := by
    ext a
    have ha_top : castLE j'.is_le a ≠ 𝔰.top := Fin.ne_of_val_ne (by simp; lia)
    -- `y` vanishes outside the first `j'` indices, so the sum extends over all indices.
    have hy_vanish (b : Fin (𝔰.ϱ + 1)) (hb : b ∉ Set.range (castLE j'.is_le)) : y b = 0 := by
      have h_ge : j'.val ≤ b.val := by simpa using hb
      have hib : i < b := by lia
      exact (h_above b hib).2
    calc ((S.frameProducts γ).submatrix (castLE j'.is_le) (castLE j'.is_le) *ᵥ y') a
      _ = (S.frameProducts γ *ᵥ y) (castLE j'.is_le a) :=
        Fintype.sum_of_injective _ (castLE_injective j'.is_le) _ _
          (fun b hb ↦ by rw [hy_vanish b hb, mul_zero]) fun _ ↦ rfl
      _ = 0 := by simp [hZ, ha_top]
  have h_minor : leadingMinor (S.frameProducts γ) j' = 0 :=
    exists_mulVec_eq_zero_iff.1 ⟨y', hy'_ne, h_kernel⟩
  exact absurd h_minor h'.leadingMinor_ne_zero

end

end New.Filling

end GaugeDefs

/-!
## The hermitian form against a moved frame

Let `k` be an isometry and `n` a vector orthogonal to `f` and `k f`.
`New.Filling.isotropicRows_conjTranspose_mul_eq` expresses the conjugate transpose of the first `ϱ`
rows of the frame Gram matrix of `k`, applied to the `e`-coordinates of `n`, through the form `T` on
the middle parts.
-/

section FrameForm

open Matrix

/-- Let `T` be a Gram matrix on the middle coordinates and `k` an isometry of `T.splitGram`, the
form made of `ϱ` hyperbolic pairs `e_a`, `e*_a` around `T`. Let the columns of `n` be orthogonal to
both frames `f` and `k f`: to `A` and `k A`, and to `z` and `k z`. Then the adjoint of the first `ϱ`
rows of the matrix `T.frameGram k` of products of `f` with `k f`, times minus the `e_a`-coordinates
`n.toRows₁` of `n`, is the matrix of `T`-products of the middle coordinates `frameMiddle k` of `k f`
with the middle coordinates `n.toRows₂.toRows₁` of `n`. -/
lemma New.Filling.isotropicRows_conjTranspose_mul_eq {R σ : Type*} [CommRing R] [StarRing R]
    {𝔰 : Shape} {T : 𝔰.Form R} {k : T.G} {n : Matrix 𝔰.BesselIndex σ R}
    (h_isotropic : (isotropicFramePair k)ᴴ * T.splitGram * n = 0)
    (h_z : zRowBlockDiagonal T * linkMatrix k * n = 0) :
    (isotropicRows (T.frameGram k))ᴴ * -n.toRows₁ =
      (frameMiddle k.val.val)ᴴ * T * n.toRows₂.toRows₁ := by
  rw [← framePair_last_eq_zRowBlockDiagonal_mul] at h_z
  ext l i
  -- The products with the `e_a` are the `e*`-coordinates of the column `i`, which therefore vanish.
  have h_eStar (a : Fin 𝔰.ϱ) : n (Sum.inr (Sum.inr a)) i = 0 := by
    simpa [mul_apply, splitGram, Matrix.one_apply, apply_ite star] using
      congrFun (congrFun h_isotropic (Sum.inl a)) i
  -- The entry is the product of the column `i` with the vector of index `l` of `k f`.
  have h_frame : ((framePair k)ᴴ * T.splitGram * n) (Sum.inr l) i = 0 := by
    induction l using Fin.lastCases with
    | last => exact congrFun (congrFun h_z (Sum.inr ())) i
    | cast a => exact congrFun (congrFun h_isotropic (Sum.inr a)) i
  simpa [mul_apply, splitGram, frameGram, h_eStar, neg_eq_iff_add_eq_zero,
    conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.one_apply,
    fromBlocks_conjTranspose] using h_frame

end FrameForm

/-!
## The padded matrix with the last row of the products

For `γ` of cell rank `j`, keep the first `j` rows and the last row of the matrix of products, and
complete them by rows of the identity matrix. The determinant is the minor `S.subframeMinor j γ`,
and its norm is `minorNorm j γ` times a power of `N`. This expresses the gauges through `minorNorm`.
-/

section LastRow

open Matrix Fin

/-- If `B y` is the `i`-th basis vector, then putting `r` for the `i`-th row of `B` multiplies the
determinant by `r ⬝ᵥ y`. -/
lemma New.det_updateRow_of_mulVec_eq_single {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    {B : Matrix n n R} {i : n} {y : n → R} (hy : B *ᵥ y = Pi.single i 1) (r : n → R) :
    (B.updateRow i r).det = r ⬝ᵥ y * B.det := by
  have h_col : B.adjugate *ᵥ Pi.single i 1 = B.det • y := by
    rw [← hy, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  calc (B.updateRow i r).det = (r ᵥ* B.adjugate) ⬝ᵥ Pi.single i 1 := by
        rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose,
          mulVec_transpose, dotProduct_single, mul_one]
    _ = r ⬝ᵥ y * B.det := by
        rw [← dotProduct_mulVec, h_col, dotProduct_smul, smul_eq_mul, mul_comm]

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape}

/-- The leading minors for `γ⁻¹` are the conjugates of those for `γ`, so their norms agree. -/
lemma minorNorm_inv {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E} :
    S.minorNorm j γ⁻¹ = S.minorNorm j γ := by
  simp [minorNorm, leadingMinor, ← conjTranspose_submatrix, abs_norm_eq_prod_norm_sq]

/-- Let the CM field `E` have `r = numInfPlaces E` infinite places and contain a primitive `5040`-th
root of unity. Let `N = S.N` be the prime of the data `S`. Let `γ` have cell rank `j`
(`S.HasCellRank j γ`); in particular the leading minor of order `j` of `Z` is nonzero. Here
`Z = S.frameProducts γ` is the matrix of hermitian products of the frame `f = (e₁,…,e_ϱ,z)` with
`γ f`. Keep the rows `a < j` and the last row (index `𝔰.top`) of `Z`, and put rows of the identity
matrix for the others. The absolute value of the norm to `ℚ` of the determinant is
`N ^ (2 r) * S.minorNorm j γ`. -/
lemma HasCellRank.abs_norm_det_updateRow_paddedLeading {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)}
    {γ : S.G E} [HasPrimitiveRoot5040 E] (h : S.HasCellRank j γ) :
    |(Algebra.norm ℚ ((paddedLeading j (S.frameProducts γ)).updateRow 𝔰.top
        (S.frameProducts γ 𝔰.top)).det : ℝ)| =
      S.N ^ (2 * numInfPlaces E) * S.minorNorm j γ := by
  by_cases hj : 𝔰.ϱ < j.val
  · have h_row : S.frameProducts γ 𝔰.top = paddedLeading j (S.frameProducts γ) 𝔰.top := by
      ext b
      simp [paddedLeading, hj]
    rw [h_row, updateRow_eq_self, det_paddedLeading, minorNorm, show j.val - 𝔰.ϱ = 1 by omega,
      mul_one, mul_div_cancel₀ _ (by simp [S.N_prime.ne_zero])]
  -- Below the top rank, the last column `y` of the inverse of the padded matrix gives a shared
  -- vector `γ z + … = ζ z + …` with `ζ ζ̄ = 1`, and the last row of `Z` sends `y` to `-N ζ`.
  let y : Fin (𝔰.ϱ + 1) → E := col (paddedLeading j (S.frameProducts γ))⁻¹ 𝔰.top
  obtain ⟨x, hxy⟩ : ∃ x : Fin (𝔰.ϱ + 1) → E, frameImage 1 *ᵥ x = frameImage γ.val.val *ᵥ y :=
    h.exists_shared_frame_vector (not_lt.1 hj)
  have h_padded : paddedLeading j (S.frameProducts γ) *ᵥ y = Pi.single 𝔰.top 1 := by
    simp only [y, ← mulVec_single_one, mulVec_mulVec, h.paddedLeading_mul_inv, one_mulVec]
  have hy_top : y 𝔰.top = 1 := by
    simpa [paddedLeading, mulVec, dotProduct, hj] using congrFun h_padded 𝔰.top
  have h_last : S.frameProducts γ 𝔰.top ⬝ᵥ y = -S.N * x 𝔰.top := by
    simpa [mulVec] using congrFun (frameProducts_mulVec_of_frameImage_eq hxy) 𝔰.top
  have h_unit (v : NumberField.InfinitePlace E) : ‖Φ v (x 𝔰.top)‖ ^ 2 = 1 := by
    simpa [hy_top, sq] using
      congrArg (fun t : E ↦ ‖Φ v t‖) (star_mul_last_eq_of_frameImage_eq hxy)
  rw [det_updateRow_of_mulVec_eq_single h_padded, det_paddedLeading, h_last, minorNorm,
    show j.val - 𝔰.ϱ = 0 by omega, abs_norm_eq_prod_norm_sq, abs_norm_eq_prod_norm_sq]
  simp [mul_pow, h_unit, Finset.prod_mul_distrib, ← pow_mul]

/-- Let the CM field `E` have `r` infinite places and contain a primitive `5040`-th root of unity.
Let `Z = S.frameProducts γ` be the matrix of products of the frame `f = (e₁, …, e_ϱ, z)` with `γ f`,
and let `γ` have the cell rank `j`: at every index `l ≥ j` (counted from `0`) the flags of `f` and
`γ f` share a vector with leading coefficients `ζ` and `1` (one `ζ` with `ζ ζ̄ = 1`), the leading
minor `D_j` of order `j` of `Z` is nonzero, and `j = ϱ + 1` exactly when `S.termDisc γ ≠ 0`. Then
the absolute norm of `S.subframeMinor j γ`, the minor of `Z` on the first `j` rows and columns and
the last one, is `N ^ (2 r) * S.minorNorm j γ`. Here `N = S.N` is the prime of the data `S`, and
`S.minorNorm j γ` is the absolute norm of `D_j`, divided by `N ^ (2 r)` when `j = ϱ + 1`. -/
lemma HasCellRank.abs_norm_subframeMinor {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    [HasPrimitiveRoot5040 E] (hγ : S.HasCellRank j γ) :
    |(Algebra.norm ℚ (S.subframeMinor j γ) : ℝ)| = S.N ^ (2 * numInfPlaces E) * S.minorNorm j
      γ := by
  -- Completing the rows of the subframe by rows of the identity matrix keeps the determinant.
  have h_rows : of ((subframeIndices j).piecewise (S.frameProducts γ).row
      (1 : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E).row) =
      (paddedLeading j (S.frameProducts γ)).updateRow 𝔰.top (S.frameProducts γ 𝔰.top) := by
    ext a b
    by_cases ha : a = 𝔰.top <;>
      simp [Finset.piecewise, row, paddedLeading, ha, ite_apply, Matrix.one_apply]
  rw [subframeMinor, ← det_piecewise_one_eq_submatrix_det, h_rows,
    hγ.abs_norm_det_updateRow_paddedLeading]

/-- If `γ` has the cell rank `j`, then the minor `δ_*(γ) = S.subframeMinor j γ` of the products of
the first `j` vectors of the frame `(e₁, …, e_ϱ, z)` and its last vector `z` with their images under
`γ` is not zero. -/
theorem HasCellRank.subframeMinor_ne_zero {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    [HasPrimitiveRoot5040 E] (hγ : S.HasCellRank j γ) : S.subframeMinor j γ ≠ 0 := by
  intro h_zero
  simpa [h_zero, S.N_prime.ne_zero, hγ.minorNorm_pos.ne'] using hγ.abs_norm_subframeMinor

/-- Let the CM field `E` have `r` infinite places and contain a primitive `5040`-th root of unity,
let `N = S.N` be the prime of the data `S`, and let `γ` have the cell rank `j`. Put
`k = S.translateByClassReps c c' γ = h_c⁻¹ γ h_c'`. Take the rows `a = 1, …, ϱ` of the matrix of
products of the frame `f = (e₁, …, e_ϱ, z)` with `k f`; `S.isotropicRowsIndex j k` is the index, in
the lattice that they span, of the lattice spanned by the first `j` of them. Then the gauge
`𝗀♯ = S.minorGauge j c c' γ` is `N ^ r * S.minorNorm j γ` divided by the product of these indices at
`k` and at `k⁻¹`. -/
lemma HasCellRank.minorGauge_eq {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    [HasPrimitiveRoot5040 E] (hγ : S.HasCellRank j γ) (c c' : S.Classes) :
    S.minorGauge j c c' γ = S.N ^ numInfPlaces E * S.minorNorm j γ /
      (S.isotropicRowsIndex j (S.translateByClassReps c c' γ) *
        S.isotropicRowsIndex j (S.translateByClassReps c c' γ)⁻¹) := by
  have hN : (S.N : ℝ) ^ numInfPlaces E ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 S.N_prime.ne_zero)
  -- The norm of the minor has the factor `N ^ (2 r)`, and one `N ^ r` cancels.
  have h_norm : |(Algebra.norm ℚ (S.subframeMinor j γ) : ℝ)| =
      S.N ^ numInfPlaces E * S.minorNorm j γ * S.N ^ numInfPlaces E := by
    rw [hγ.abs_norm_subframeMinor]
    ring
  rw [minorGauge, h_norm, mul_div_mul_right _ _ hN]

/-- Let the CM field `E` have `r` infinite places and contain a primitive `5040`-th root of unity,
let `N = S.N` be the prime of the data `S`, and let `γ` have the cell rank `j`. Let `m` be the
larger of `N ^ r * S.minorNorm j γ` and `S.termDiscNorm γ`, the product of the absolute values of
`𝗀(γ) = S.termDisc γ` at the infinite places. Put
`k = S.translateByClassReps c c' γ = h_c⁻¹ γ h_c'`. Take the rows `a = 1, …, ϱ` of the matrix of
products of the frame `f = (e₁, …, e_ϱ, z)` with `k f`; `S.isotropicRowsIndex j k` is the index, in
the lattice that they span, of the lattice spanned by the first `j` of them. Then
`S.maxGauge j c c' γ` is `m` divided by the product of these indices at `k` and at `k⁻¹`. -/
lemma HasCellRank.maxGauge_eq {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    [HasPrimitiveRoot5040 E] (hγ : S.HasCellRank j γ) (c c' : S.Classes) :
    S.maxGauge j c c' γ = (S.termDiscNorm γ ⊔ S.N ^ numInfPlaces E * S.minorNorm j γ) /
      (S.isotropicRowsIndex j (S.translateByClassReps c c' γ) *
        S.isotropicRowsIndex j (S.translateByClassReps c c' γ)⁻¹) := by
  rw [maxGauge, hγ.minorGauge_eq, ← max_div_div_right (by positivity), max_comm]
  by_cases h_disc : S.termDisc γ = 0
  · simp [termDiscNorm, h_disc]
  · -- At the top rank both indices are `1`.
    obtain rfl : j = ⊤ := hγ.unique (hasCellRank_last h_disc)
    simp [isotropicRowsIndex_top]

end New.Filling

end LastRow

end
