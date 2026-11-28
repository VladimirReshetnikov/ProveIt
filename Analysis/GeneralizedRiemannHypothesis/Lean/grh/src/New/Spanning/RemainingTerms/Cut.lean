import New.Spanning.RemainingTerms.LinkLattice
import New.Spanning.RemainingTerms.LinkVectors

/-!
# The cut: from the lattice of a link to the vectors common to two links

Let `A` be the span of `e₁, …, e_ϱ`, `Λ` the lattice of a class and `M` the level. The vectors of
`Λ` orthogonal to `A` and `γ A` whose part in `A` is divisible by `M` give a lattice `L⁺_γ` in the
link of a term `γ`. We descend from it to its intersection with the link of a second term `γ'`,
and from there to the part orthogonal to `z⁺` and `Υ_γ⁻¹ z⁺`, which lies in
`L_γ = S.termLattice c c' γ`. The last step costs at most a principal minor of their Gram matrix.
So the discriminant of this part, times the torsion index `S.torsionIndex`, the discriminant of
the projection to the complement of the intersection and a gain `x` from the places where the
residue meets, is at most the gauge `S.levelGauge` of the term (`nonempty_linkSplitting` below).

* `New.Filling.HasCellRank.abs_norm_minor_gram_linkVectors_mul_le`,
  `New.Filling.minorNorm_sq_le_linkDiscSq_mul`: the cost of the cut, in the three cases of rank
  `0`, `1` and `2`. The first bounds the principal minors of the Gram matrix of the two vectors;
  the second is the resulting lower bound for the discriminant of a lattice in the link on whose
  span the `z`-forms are injective.
* `New.Filling.LinkSplitting`, `New.Filling.nonempty_linkSplitting`: the splitting of a link along
  its intersection with a second link.
* `New.Filling.HasIntegralLifts.isIntMatrix_linkForm`: for two terms over one block, the form
  `S.linkForm / M` is integral on pairs of lifts.

Notions from other files:

* `New.link γ`: the space of pairs (class of `y`, class of `γ⁻¹ y`) in `(A^⊥ / A)²`, with `y`
  orthogonal to `A` and `γ A`. Here `A^⊥ / A = X₀ ⊥ E z` with `z` of norm `-N`, and the link is
  the graph of an isometry `Υ_γ` of `X₀ ⊥ E z⁺`, with `z⁺` of norm `N`.
* `New.Filling.linkDiscSq`: for a rational basis `v` and an adelic change of basis `e`,
  `S.linkDiscSq v e` is the squared discriminant of the lattice `v e` for `S.linkMetric`, which on
  the link is the form of `X₀ ⊥ E z⁺`.
* `New.Filling.HasIntegralLifts`, `New.Filling.HasLevelLifts`: the columns of a matrix are the
  images in the link of vectors of `Λ` orthogonal to `A` and `γ A`, respectively lie in `L⁺_γ`.
* `New.Filling.termsOver`: `S.termsOver c s c'` is the block of rational `γ` whose matrix in the
  bases of the lattices of `c` and `c'` is integral with reduction `s`.
-/

open Matrix Submodule Module Finset Fin Fintype Pointwise

namespace New.Filling

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {𝔰 : Shape} {τ : Type}
  {S : Filling E 𝔰}

section

omit [HasPrimitiveRoot5040 E]

/-- Let `n = S.classCoord c * finAdeleMatrix t * w` be the coordinates of the adelic combinations
`t w` of rational vectors in the basis of the lattice of the class `c`. Let
`k = S.translateByClassReps c c' γ` be the matrix of `γ` in the bases of the lattices of `c` and
`c'`. The products with `z` on both halves (`zRowBlockDiagonal`) for `S.latticeMiddle` take the same
values on `linkMatrix k * n` as those for `S.ratMiddle` take on `linkMatrix γ * t * w`. -/
lemma zRowBlockDiagonal_mul_linkMatrix_mul_classCoord {ρ : Type} [Fintype ρ] (c c' : S.Classes)
    (γ : S.G E) (t : Matrix 𝔰.BesselIndex ρ E) (w : Matrix ρ τ (𝔸f E)) :
    zRowBlockDiagonal (S.latticeMiddle (𝔸f E)) * linkMatrix (S.translateByClassReps c c' γ) *
        (S.classCoord c * finAdeleMatrix t * w) =
      finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) *
        (finAdeleMatrix (linkMatrix γ * t) * w) := by
  -- Both sides are the products with the last column of each of the two frames.
  rw [← framePair_last_eq_zRowBlockDiagonal_mul, ← Matrix.mul_assoc,
    framePair_translateByClassReps_mul_classCoord,
    framePair_last_eq_zRowBlockDiagonal_mul]
  simp [Matrix.mul_assoc]

/-- Let the columns of the rational matrix `t` be orthogonal to `A` and `γ A`
(`isotropicFramePair γ`). Then the coordinates of the adelic combinations `t w` in the basis of the
lattice of the class `c` are orthogonal to `A` and `k A`, where `k` is the matrix of `γ` in the
bases of the lattices of `c` and `c'`. -/
lemma isotropicFramePair_mul_classCoord_eq_zero {γ : S.G E} {ρ : Type} [Fintype ρ]
    (c c' : S.Classes) {t : Matrix 𝔰.BesselIndex ρ E}
    (h_orth : (isotropicFramePair γ)ᴴ * S.ratGram * t = 0) (w : Matrix ρ τ (𝔸f E)) :
    (isotropicFramePair (S.translateByClassReps c c' γ))ᴴ * (S.latticeMiddle (𝔸f E)).splitGram *
      (S.classCoord c * finAdeleMatrix t * w) = 0 := by
  rw [← Matrix.mul_assoc, framePair_translateByClassReps_mul_classCoord, h_orth]
  simp

/-- If the first half of the images `linkMatrix γ * t * w` of adelic combinations `t w` of rational
vectors is a matrix `p` in `X₀`, the middle part of the coordinates of `t w` in the basis of the
lattice of the class `c` is `S.classCoordX₀ c * p`. -/
lemma toRows_classCoord_mul {γ : S.G E} {ρ : Type} [Fintype ρ] (c : S.Classes)
    {t : Matrix 𝔰.BesselIndex ρ E} {w : Matrix ρ τ (𝔸f E)} {p : Matrix 𝔰.κ τ (𝔸f E)}
    (hp : (finAdeleMatrix (linkMatrix γ * t) * w).toRows₁ = fromRows p 0) :
    (S.classCoord c * finAdeleMatrix t * w).toRows₂.toRows₁ = S.classCoordX₀ c * p := by
  -- The first half of the images is the middle part of `t w`, and `S.classCoord c` is block
  -- diagonal.
  classical
  have h_middle : (finAdeleMatrix t * w).toRows₂.toRows₁ = fromRows p 0 := by
    rw [← hp]
    simp [← ext_iff, linkMatrix, mul_apply, Matrix.one_apply]
  have h_block (q : Matrix 𝔰.BesselIndex τ (𝔸f E)) :
      q.toRows₂.toRows₁ = fromRows p 0 →
        (S.classCoord c * q).toRows₂.toRows₁ = S.classCoordX₀ c * p := by
    simp +contextual [← ext_iff, classCoord_eq_fromBlocks, mul_apply]
  rw [Matrix.mul_assoc, h_block _ h_middle]

end

section

variable {c c' : S.Classes} {γ : S.G E} {j : Fin (𝔰.ϱ + 2)}

/-- Let the columns of `m` be orthogonal to those of `y` for `S.linkMetric`, and let the columns of
`(m | y) f` lie in the lattice `L⁺_γ` of the link of `γ` for the class `c` (`HasLevelLifts c γ`).
Then there are adelic changes of basis `a`, `v` and a shear `z` such that the columns of `m a` and
of `m z + y v` lie in `L⁺_γ`, and the squared discriminant `S.linkDiscSq` of `(m | y) f` is the
product of those of `m a` and `y v`. -/
lemma HasLevelLifts.exists_orthogonal_split [Fintype τ] [DecidableEq τ] {r : ℕ}
    {m : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E}
    {y : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin r) E} {f : GL (τ ⊕ Fin r) (𝔸f E)}
    (h_lift : HasLevelLifts c γ (finAdeleMatrix (fromCols m y) * f.val))
    (h_orth : mᴴ * S.linkMetric * y = 0) :
    ∃ (a : GL τ (𝔸f E)) (v : GL (Fin r) (𝔸f E)) (z : Matrix τ (Fin r) (𝔸f E)),
      HasLevelLifts c γ (finAdeleMatrix m * a.val) ∧
      HasLevelLifts c γ (finAdeleMatrix m * z + finAdeleMatrix y * v.val) ∧
      S.linkDiscSq m a * S.linkDiscSq y v = S.linkDiscSq (fromCols m y) f := by
  -- An integral change of basis `V` makes `f * V` block triangular; both block columns of
  -- `finAdeleMatrix (fromCols m y) * f * V` lift.
  obtain ⟨a, v, z, h_prim⟩ :
      ∃ (a : GL τ (𝔸f E)) (v : GL (Fin r) (𝔸f E)) (z : Matrix τ (Fin r) (𝔸f E)),
        IsPrimitiveMatrix (Ô E) (f⁻¹.val * fromBlocks a.val z 0 v.val) :=
    exists_isPrimitiveMatrix_mul_fromBlocks f⁻¹.val ⟨f.val, f.mul_inv⟩
  obtain ⟨V, hV, hV_eq⟩ :
      ∃ V ∈ intGL (τ ⊕ Fin r) (Ô E), V.val = f⁻¹.val * fromBlocks a.val z 0 v.val :=
    isPrimitiveMatrix_iff.1 h_prim
  have hV_int : IsIntMatrix (Ô E) V.val := by
    rw [hV_eq]
    exact h_prim.left
  have h_triangular : f.val * V.val = fromBlocks a.val z 0 v.val := by
    rw [hV_eq, Units.mul_inv_cancel_left]
  have h_blocks : finAdeleMatrix (fromCols m y) * f.val * V.val =
      fromCols (finAdeleMatrix m * a.val) (finAdeleMatrix m * z + finAdeleMatrix y * v.val) := by
    simp [Matrix.mul_assoc, h_triangular, fromCols_map, fromCols_mul_fromBlocks]
  have h_lift' : HasLevelLifts c γ (fromCols (finAdeleMatrix m * a.val)
      (finAdeleMatrix m * z + finAdeleMatrix y * v.val)) := by
    rw [← h_blocks]
    exact h_lift.mul hV_int
  refine ⟨a, v, z, h_lift'.submatrix Sum.inl, h_lift'.submatrix Sum.inr, ?_⟩
  obtain ⟨h_open, h_compact⟩ : IsOpen (Ô E : Set (𝔸f E)) ∧ IsCompact (Ô E : Set (𝔸f E)) :=
    IsAdelic.isOpen_isCompact
  have h_index : genIndex f.val.det = genIndex a.val.det * genIndex v.val.det := by
    rw [← map_mul, ← det_fromBlocks_zero₂₁ a.val z, ← h_triangular, det_mul, map_mul,
      genIndex_det_eq_one h_open h_compact hV, mul_one]
  have h_gram : ((fromCols m y)ᴴ * S.linkMetric * fromCols m y).det =
      (mᴴ * S.linkMetric * m).det * (yᴴ * S.linkMetric * y).det := by
    simp [h_orth, conjTranspose_fromCols_eq_fromRows_conjTranspose]
  simp only [linkDiscSq, h_gram, h_index, map_mul, Rat.cast_mul, abs_mul]
  ring

variable [Fintype τ] {s : S.ResidueGL} {x : ℕ}

/-- Let `γ` be a term over the classes `c`, `c'` with reduction `s`, where `s` is compatible with
the unipotent character (`S.Agrees s`), and let the columns of `w` have integral lifts. Let `ρ`
choose rows among the two `z`-forms `zRowBlockDiagonal`, such that the minor of their values on `w`
is a unit of the finite adeles. Then the generalised index `genIndex` of the minor is at least `x`,
if `x` is at most the norm `S.meetNorm s` of the product of the places with `S.MeetsAt s`, and if
both forms are chosen unless `x = 1`. -/
lemma HasIntegralLifts.le_genIndex_det_zRowBlockDiagonal (hs : S.Agrees s)
    (h_term : γ ∈ S.termsOver c s c') {r : ℕ}
    {w : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin r) (𝔸f E)}
    (h_lift : HasIntegralLifts c γ w) {ρ : Fin r → Unit ⊕ Unit} (hx : x ≤ S.meetNorm s)
    (hρ : x ≠ 1 → ρ.Bijective)
    (h_unit : IsUnit ((finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) * w).submatrix ρ
      id).det) :
    x ≤ genIndex ((finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) * w).submatrix ρ id).det := by
  -- The values of the `z`-forms are products of the lifts `n` with `z` and `γ z`. So the minor is
  -- integral, and divisible by the places at which `s` meets if both forms occur.
  obtain ⟨⟨k, hk_mem⟩, rfl, rfl : k = S.translateByClassReps c c' γ⟩ := h_term
  obtain ⟨ι, _, t, u, h_orth, hn_int, h_eq⟩ := h_lift
  set n : Matrix 𝔰.BesselIndex (Fin r) (𝔸f E) := S.classCoord c * finAdeleMatrix t * u
  have hn_z : zRowBlockDiagonal (S.latticeMiddle (𝔸f E)) *
        linkMatrix (S.translateByClassReps c c' γ) * n =
      finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) * w := by
    rw [← h_eq]
    exact zRowBlockDiagonal_mul_linkMatrix_mul_classCoord c c' γ t u
  have hn_orth :
      (isotropicFramePair (S.translateByClassReps c c' γ))ᴴ * (S.latticeMiddle (𝔸f E)).splitGram * n
        = 0 :=
    isotropicFramePair_mul_classCoord_eq_zero c c' h_orth u
  have hJn : IsIntMatrix (Ô E) ((S.latticeMiddle (𝔸f E)).splitGram * n) :=
    S.isUnimodular_latticeMiddle.splitGram.isIntMatrix.mul hn_int
  let P : Matrix (Fin (𝔰.ϱ + 1) ⊕ Fin (𝔰.ϱ + 1)) (Fin r) (𝔸f E) :=
    (framePair (S.translateByClassReps c c' γ))ᴴ * ((S.latticeMiddle (𝔸f E)).splitGram * n)
  have h_products : (finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) * w).submatrix ρ id =
      P.submatrix (Sum.map (fun _ : Unit ↦ 𝔰.top) (fun _ : Unit ↦ 𝔰.top) ∘ ρ) id := by
    rw [← hn_z, ← framePair_last_eq_zRowBlockDiagonal_mul, Matrix.mul_assoc]
    rfl
  rw [h_products] at h_unit ⊢
  obtain rfl | h_ne := eq_or_ne x 1
  · have hP_int : IsIntMatrix (Ô E) P :=
      (isIntMatrix_framePair hk_mem.isIntMatrix).conjTranspose.mul hJn
    exact_mod_cast one_le_genIndex (IsIntMatrix.det_mem fun a b ↦ hP_int _ b) h_unit
  · have hP_zero : P.submatrix (Sum.map castSucc castSucc) id = 0 := by
      rwa [Matrix.mul_assoc] at hn_orth
    exact le_genIndex_det_of_le_meetNorm hs hJn hP_zero (.ofBijective ρ (hρ h_ne)) h_unit hx

omit [HasPrimitiveRoot5040 E] in
/-- Let `γ` have cell rank `j ≤ ϱ + 1` (`S.HasCellRank`): in particular the leading minor of order
`j` of the matrix of products of the standard frame with its image under `γ` is nonzero. Take a
principal minor of order `r`, on the indices chosen by `ρ`, of the Gram matrix of `z⁺` and
`Υ_γ⁻¹ z⁺` (`linkVectors γ`), where `r = 2` is allowed only at the top cell rank `j = ϱ + 1`. Its
absolute norm is at most `(G / μ) ^ 2`. Here `μ = S.minorNorm j γ` is the normalised norm of that
leading minor, and `G` is the maximum of `N ^ f * μ` and of `S.termDiscNorm γ`, the product of the
moduli of the discriminant `S.termDisc γ` of the frames. The prime `N = S.N` of the filling is the
norm of `z⁺`, and `f` is the number of infinite places. -/
lemma HasCellRank.abs_norm_minor_gram_linkVectors_mul_le (h_cell : S.HasCellRank j γ) {r : ℕ}
    (hr : r ≤ 1 + (j - 𝔰.ϱ)) {ρ : Fin r → Fin 2} (hρ : ρ.Injective) :
    |(Algebra.norm ℚ
        (((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).submatrix ρ ρ).det : ℝ)| *
        S.minorNorm j γ ^ 2 ≤
      (S.termDiscNorm γ ⊔ S.N ^ numInfPlaces E * S.minorNorm j γ) ^ 2 := by
  -- The minor is `1`, `N` or the Gram determinant, of modulus `N² |S.termDisc γ| / |δ|²` at each
  -- place, where `δ` is the leading minor of order `j` of the products of the frames.
  have h_minor : 0 < S.minorNorm j γ := h_cell.minorNorm_pos
  obtain _ | _ | r := r
  · grw [← le_max_right, ← S.N_prime.one_le]
    simp
  · have h_entry : ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ) (ρ 0) (ρ 0) = S.N := by
      rw [gram_linkVectors]
      generalize ρ 0 = i
      fin_cases i <;> rfl
    have h_norm : |(Algebra.norm ℚ (S.N : E) : ℝ)| = (S.N ^ numInfPlaces E) ^ 2 := by
      simp [abs_norm_eq_prod_norm_sq, ← pow_mul, mul_comm]
    rw [det_fin_one, submatrix_apply, h_entry, h_norm, ← mul_pow]
    grw [← le_max_right]
  · have hρ_bij : ρ.Bijective := hρ.bijective_of_nat_card_le (by simp)
    have h_det : (((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).submatrix ρ ρ).det =
        ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det :=
      det_submatrix_equiv_self (.ofBijective ρ hρ_bij) _
    have h_top : j - 𝔰.ϱ = 1 := by lia
    have h_ne (v : NumberField.InfinitePlace E) :
        ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ ≠ 0 := by
      simpa using h_cell.leadingMinor_ne_zero
    have h_norm : |(Algebra.norm ℚ ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det : ℝ)| *
        S.minorNorm j γ ^ 2 = S.termDiscNorm γ ^ 2 := by
      simp only [termDiscNorm, minorNorm, h_top, abs_norm_eq_prod_norm_sq,
        h_cell.norm_det_gram_linkVectors]
      have h_prod := prod_ne_zero_iff.2 fun v (_ : v ∈ univ) ↦ h_ne v
      have hN : (S.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 S.N_prime.ne_zero
      simp [field, prod_pow, pow_mul, prod_mul_distrib, prod_div_distrib]
    grw [h_det, h_norm, termDiscNorm, ← le_max_left]

/-- **The part seen by the `z`-forms.** Let `γ` have cell rank `j` and be a term over the classes
`c`, `c'` with reduction `s`, where `s` is compatible with the unipotent character (`S.Agrees s`).
Let the `r` columns of `y` lie in the link, where `r ≤ 2`, and `r ≤ 1` unless `j = ϱ + 1`. Let the
two `z`-forms `zRowBlockDiagonal` be injective on their span, and let them take the same values on
the basis `y v` as on a matrix `w` that has integral lifts. Then the squared discriminant of the
lattice with basis `y v` is at least `(x * μ / G) ^ 2`. Here `μ = S.minorNorm j γ` is the normalised
norm of the leading minor of order `j` of the products of the frames, and `G` is the maximum of
`S.termDiscNorm γ` and `N ^ f * μ`, where the prime `N = S.N` of the filling is the norm of `z⁺` and
`f` is the number of infinite places. The number `x` is at most the norm `S.meetNorm s` of the
product of the places with `S.MeetsAt s`, and `x = 1` unless `r = 2`. -/
lemma minorNorm_sq_le_linkDiscSq_mul (hs : S.Agrees s) (h_term : γ ∈ S.termsOver c s c')
    (h_cell : S.HasCellRank j γ) (hx : x ≤ S.meetNorm s) {r : ℕ} (hr_le : r ≤ 1 + (j - 𝔰.ϱ))
    (hr_eq : x ≠ 1 → r = 2) {y : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin r) E}
    (hy_le : colSpan y ≤ link γ) (hy_inv : HasLeftInv (zRowBlockDiagonal (S.ratMiddle E) * y))
    (v : GL (Fin r) (𝔸f E)) {w : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin r) (𝔸f E)}
    (h_lift : HasIntegralLifts c γ w)
    (h_forms : finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) * w =
      finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E) * y) * v.val) :
    x ^ 2 * S.minorNorm j γ ^ 2 ≤
      S.linkDiscSq y v * (S.termDiscNorm γ ⊔ S.N ^ numInfPlaces E * S.minorNorm j γ) ^ 2 := by
  -- The `z`-forms are the products with the pairs `ε` over `-z⁺` and `-Υ_γ⁻¹ z⁺`. Choose `r` of
  -- them, by `ρ`, that pair nondegenerately with `y`. The determinant of the pairing has index at
  -- least `x`, so the squared discriminant of the lattice is at least `x ^ 2 / D`, where `D` is
  -- the absolute norm of their Gram determinant.
  let ε : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Unit ⊕ Unit) E := linkVectorPairs γ
  have hε_repr : εᴴ * S.linkMetric * y = zRowBlockDiagonal (S.ratMiddle E) * y :=
    linkVectorPairs_mul_linkMetric_mul hy_le
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Fin r → Unit ⊕ Unit,
      ((zRowBlockDiagonal (S.ratMiddle E) * y).submatrix ρ id).det ≠ 0 :=
    not_forall.1 (det_eval_eq_zero_iff_not_linearIndependent.not_left.2
      (mulVec_injective_iff.1 hy_inv.injective_mulVec))
  have hρ_inj : ρ.Injective := by
    intro a b h_eq
    by_contra h_ne
    exact hρ (det_zero_of_row_eq h_ne (by simp [funext_iff, h_eq]))
  let e : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin r) E := ε.submatrix id ρ
  have he_repr : eᴴ * S.linkMetric * y = (zRowBlockDiagonal (S.ratMiddle E) * y).submatrix ρ id :=
    congrArg (fun A ↦ A.submatrix ρ id) hε_repr
  have h_pairing : (1 : GL (Fin r) (𝔸f E)).valᴴ * (finAdeleMatrix (eᴴ * S.linkMetric * y) * v.val) =
      (finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) * w).submatrix ρ id := by
    rw [h_forms, he_repr, Units.val_one, conjTranspose_one, Matrix.one_mul]
    rfl
  have h_gram : eᴴ * S.linkMetric * e =
      ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).submatrix
        (zFormIndex ∘ ρ) (zFormIndex ∘ ρ) :=
    congrArg (fun A ↦ A.submatrix ρ ρ) (gram_linkVectorPairs γ)
  have h_index :
      IsUnit ((finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) * w).submatrix ρ id).det →
      x ≤ genIndex ((finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) * w).submatrix ρ id).det :=
    h_lift.le_genIndex_det_zRowBlockDiagonal hs h_term hx
      fun h_ne ↦ hρ_inj.bijective_of_nat_card_le (by simp [hr_eq h_ne])
  rw [← h_pairing] at h_index
  set D : ℝ := |(Algebra.norm ℚ (eᴴ * S.linkMetric * e).det : ℝ)| with hD
  have h_liouville : x ^ 2 ≤ S.linkDiscSq y v * D := by
    have h_det : (eᴴ * S.linkMetric * y).det ≠ 0 := by rwa [he_repr]
    refine (liouville_gram linkMetric_posDef e y 1 v h_det x.cast_nonneg h_index).trans_eq ?_
    rw [Units.val_one, det_one, map_one, linkDiscSq]
    ring
  have h_minor : D * S.minorNorm j γ ^ 2 ≤
      (S.termDiscNorm γ ⊔ S.N ^ numInfPlaces E * S.minorNorm j γ) ^ 2 := by
    rw [hD, h_gram]
    exact h_cell.abs_norm_minor_gram_linkVectors_mul_le hr_le (zFormIndex_injective.comp hρ_inj)
  have h_nonneg : 0 ≤ S.linkDiscSq y v := by
    unfold linkDiscSq
    positivity
  grw [h_liouville, mul_assoc, h_minor]

/-- Let `V` be a subspace of `X₀` and let `Λ` be the lattice of the class `c`. Let the frame be
`e₁, …, e_ϱ, z`, with isotropic part `A` spanned by `e₁, …, e_ϱ`, and let
`k = S.translateByClassReps c c' γ`. The index of `Λ ∩ V ∩ L_γ` in the saturated lattice `Λ ∩ V`
(`saturatedLattice`) is read on the products with the image of the frame under `k`. It is the index,
in the module of the products of vectors of `Λ ∩ V` with this image, of those products that are `M`
times the products of a vector of `Λ ∩ A`. -/
lemma submoduleIndex_termLattice (V : Submodule E (𝔰.κ → E)) :
    submoduleIndex (S.termLattice c c' γ) (saturatedLattice (S.gram_classCoordX₀ c) V) =
      sublatticeIndex (S.gram_classCoordX₀ c) V
        ((frameMiddle (S.translateByClassReps c c' γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)))ᴴ
          *
          S.latticeMiddle (𝔸f E))
        (S.ideleM • colLattice (Ô E)
          (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram
            (S.translateByClassReps c c' γ)))ᴴ) := by
  rw [termLattice, classLatticeX₀, submoduleIndex_inf_comap _ (saturatedLattice_le _ V),
    sublatticeIndex, saturatedLattice, colLattice, colLattice, colLattice, ← Submodule.map_comp,
    ← Matrix.mul_assoc _ (S.classCoordX₀ c), mulVecLin_mul _ (sublatticeBasis _ V).val]
  rfl

omit [HasPrimitiveRoot5040 E] in
/-- Let the columns of `m` be pairs of vectors of `X₀ ⊕ E z` on which both `z`-forms, the products
with `z` on the two halves, vanish. Then the first half of any adelic combination `m a` of them
lies in `X₀`: its `z`-coordinate is zero. -/
lemma toRows₁_mul_eq_fromRows_zero {m : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E}
    (hm_forms : zRowBlockDiagonal (S.ratMiddle E) * m = 0) (a : Matrix τ τ (𝔸f E)) :
    (finAdeleMatrix m * a).toRows₁ = fromRows (finAdeleMatrix m.toRows₁.toRows₁ * a) 0 := by
  simp_all [← ext_iff, mul_apply, middleGram, Nat.Prime.ne_zero]

omit [HasPrimitiveRoot5040 E] in
/-- Let the columns of `m` lie in the link of `γ`, and let both `z`-forms vanish on them. Their Gram
matrix for `S.linkMetric` is the standard Gram matrix of their parts in `X₀`. -/
lemma gram_linkMetric_eq_gram_toRows₁ {m : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E}
    (hm_link : colSpan m ≤ link γ) (hm_forms : zRowBlockDiagonal (S.ratMiddle E) * m = 0) :
    mᴴ * S.linkMetric * m = m.toRows₁.toRows₁ᴴ * m.toRows₁.toRows₁ := by
  -- The two halves of `m` have equal Gram matrices and no `z`-coordinates, and `S.linkMetric` is
  -- the mean of the forms on the two halves where the `z`-forms vanish.
  classical
  have h_isotropic : mᴴ * S.linkForm * m = 0 := gram_linkForm_eq_zero_of_le_link hm_link hm_link
  simp_all [← ext_iff, linkMetric, mul_apply, middleGram, add_neg_eq_zero, ← two_mul,
    Nat.Prime.ne_zero, Matrix.one_apply, Matrix.mul_add, Matrix.add_mul]

end

/-- **The part in `X₀`.** Let `m` have a left inverse. Let its columns span a subspace of `link γ`
on which both `z`-forms vanish: `zRowBlockDiagonal (S.ratMiddle E) * m = 0`, the rows indexed by `z`
in each copy. Let `p = m.toRows₁.toRows₁` be the parts in `X₀`. Let the lattice with basis `m a` lie
in `L⁺_γ` (`HasLevelLifts`): it has integral lifts whose part in `A` is divisible by the level `M`.
Let `V` be the span of the columns of `p`. Let `L` be the intersection of `saturatedLattice` of `V`
with `L_γ = S.termLattice c c' γ`. Then `r = finrank E V`, and `L` is a lattice of rank `r`. Its
squared discriminant is at most `S.linkDiscSq m a`, the squared discriminant of `m a`, as `L`
contains the columns of `p a`. -/
lemma HasLevelLifts.discriminant_sq_le {c : S.Classes} {γ : S.G E} {r : ℕ}
    {m : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin r) E} (hm : HasLeftInv m)
    (hm_link : colSpan m ≤ link γ) (hm_forms : zRowBlockDiagonal (S.ratMiddle E) * m = 0)
    {a : GL (Fin r) (𝔸f E)} (h_lift : HasLevelLifts c γ (finAdeleMatrix m * a.val))
    (c' : S.Classes) :
    let V : Submodule E (𝔰.κ → E) := colSpan m.toRows₁.toRows₁
    let L : Submodule (Ô E) (𝔰.κ → 𝔸f E) :=
      saturatedLattice (S.gram_classCoordX₀ c) V ⊓ S.termLattice c c' γ
    r = finrank E V ∧
      IsLatticeOfRank (finrank E V) L ∧
      discriminant (finrank E V) L ^ 2 ≤ S.linkDiscSq m a := by
  -- The integral lifts `n` of `m a` show that the columns of `p a` lie in `L`. So `L` has finite
  -- index in the saturated lattice of `V`, and its discriminant is at most that of `p a`.
  intro V L
  let p : Matrix 𝔰.κ (Fin r) E := m.toRows₁.toRows₁
  have h_gram : mᴴ * S.linkMetric * m = pᴴ * p := gram_linkMetric_eq_gram_toRows₁ hm_link hm_forms
  have h_det : (pᴴ * p).det ≠ 0 := by
    rw [← h_gram]
    exact det_gram_linkMetric_ne_zero hm
  have hp_inv : HasLeftInv p := ⟨(pᴴ * p)⁻¹ * pᴴ, by simp [h_det, Matrix.mul_assoc]⟩
  have h_rank : r = finrank E V := by simpa using card_eq_finrank_colSpan hp_inv
  have h_disc : S.linkDiscSq m a =
      genIndex (finAdeleMatrix (pᴴ * p)).det * genIndex a.val.det ^ 2 := by
    simp [← genIndex_algebraMap, RingHom.map_det, linkDiscSq, h_gram]
  obtain ⟨ρ, _, t, w, h_orth, hn_int, hn_level, h_eq⟩ := h_lift
  set n : Matrix 𝔰.BesselIndex (Fin r) (𝔸f E) := S.classCoord c * finAdeleMatrix t * w
  let k : S.GFin := S.translateByClassReps c c' γ
  let T : 𝔰.Form (𝔸f E) := S.latticeMiddle (𝔸f E)
  have hn_z : zRowBlockDiagonal T * linkMatrix k * n =
      finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) * (finAdeleMatrix m * a.val) := by
    rw [← h_eq]
    exact zRowBlockDiagonal_mul_linkMatrix_mul_classCoord c c' γ t w
  have hn_orth : (isotropicFramePair k)ᴴ * T.splitGram * n = 0 :=
    isotropicFramePair_mul_classCoord_eq_zero c c' h_orth w
  let Y : Matrix (Fin (𝔰.ϱ + 1)) 𝔰.MiddleIndex (𝔸f E) :=
    (frameMiddle (k : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E)))ᴴ * T
  have h_middle : n.toRows₂.toRows₁ = S.classCoordX₀ c * (finAdeleMatrix p * a.val) := by
    apply toRows_classCoord_mul (γ := γ)
    rw [h_eq]
    exact toRows₁_mul_eq_fromRows_zero hm_forms a.val
  have h_int : IsIntMatrix (Ô E) (S.classCoordX₀ c * (finAdeleMatrix p * a.val)) := by
    rw [← h_middle]
    exact fun i ↦ hn_int (.inr (.inl i))
  -- `n` is orthogonal to both frames, so the products of its middle part with the frame of `γ` are
  -- those of its part in `A`, up to sign, and this part is divisible by `M`.
  have hn_forms : zRowBlockDiagonal T * linkMatrix k * n = 0 := by
    rw [hn_z]
    simp [← Matrix.mul_assoc, ← Matrix.map_mul, hm_forms]
  have h_products : (isotropicRows (T.frameGram k))ᴴ * -n.toRows₁ = Y * n.toRows₂.toRows₁ :=
    isotropicRows_conjTranspose_mul_eq hn_orth hn_forms
  have h_mem (i : Fin r) : (Y * (S.classCoordX₀ c * (finAdeleMatrix p * a.val))).col i ∈
      S.ideleM • colLattice (Ô E) (isotropicRows (T.frameGram k))ᴴ := by
    let u : Fin 𝔰.ϱ → 𝔸f E := -(S.ideleM⁻¹ • n.toRows₁.col i)
    have hu_mem : (isotropicRows (T.frameGram k))ᴴ *ᵥ u ∈ colLattice (Ô E)
      (isotropicRows (T.frameGram k))ᴴ :=
      ⟨u, fun b ↦ hn_level.neg b i, rfl⟩
    have h_col : S.ideleM • ((isotropicRows (T.frameGram k))ᴴ *ᵥ u) =
        ((isotropicRows (T.frameGram k))ᴴ * -n.toRows₁).col i := by
      rw [← mulVec_smul, smul_neg, smul_inv_smul]
      rfl
    rw [← h_middle, ← h_products, ← h_col]
    exact smul_mem_pointwise_smul _ _ _ hu_mem
  -- `L` has finite index in the saturated lattice `Λ` of `V`.
  let Λ : Submodule (Ô E) (𝔰.κ → 𝔸f E) := saturatedLattice (S.gram_classCoordX₀ c) V
  have h_index : submoduleIndex L Λ = sublatticeIndex (S.gram_classCoordX₀ c) V Y
      (S.ideleM • colLattice (Ô E) (isotropicRows (T.frameGram k))ᴴ) := by
    rw [submoduleIndex_inf_of_le le_rfl, submoduleIndex_termLattice]
  obtain ⟨h_le, -, h_finite⟩ :
      (sublatticeDiscriminant (S.gram_classCoordX₀ c) V * submoduleIndex L Λ) ^ 2 ≤ S.linkDiscSq m a
        ∧
        0 < sublatticeDiscriminant (S.gram_classCoordX₀ c) V ∧ 1 ≤ submoduleIndex L Λ := by
    rw [h_index, h_disc]
    exact sublatticeDiscriminant_mul_index_sq_le (S.gram_classCoordX₀ c) V h_rank.symm le_rfl h_det
      a
      h_int Y h_mem
  obtain ⟨h_lattice, h_disc_eq⟩ : IsLatticeOfRank (finrank E V) L ∧
      discriminant (finrank E V) L = discriminant (finrank E V) Λ * submoduleIndex L Λ :=
    (isLatticeOfRank_saturatedLattice _ V).of_le_and_discriminant_eq_mul_index inf_le_left
      (Nat.one_le_iff_ne_zero.1 h_finite)
  rw [h_disc_eq, discriminant_saturatedLattice]
  exact ⟨h_rank, h_lattice, h_le⟩

variable (S) in
/-- A splitting of the link of `γ` along its intersection with the link of `γ'`, with a complement
of rank `i` and a lattice in it whose vectors have integral lifts modulo the intersection. The
discriminant of this lattice, times `x`, the torsion index of `γ` and the discriminant of
`S.commonPart`, the part of `L_γ` common to the two links, is at most the gauge
`𝗀* = S.levelGauge j c c' γ`. -/
structure LinkSplitting (c c' : S.Classes) (j : Fin (𝔰.ϱ + 2)) (x : ℕ) (γ γ' : S.G E) (i : ℕ) where
  /-- The index set of a family that spans the intersection of the links. -/
  CommonIndex : Type
  [fintypeCommonIndex : Fintype CommonIndex]
  /-- A family that spans the intersection of the links. -/
  commonCols : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) CommonIndex E
  /-- A basis of a complement of the intersection in the link of `γ`. -/
  complCols : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin i) E
  /-- The lattice in the complement has the basis `complCols * complLattice`. -/
  complLattice : GL (Fin i) (𝔸f E)
  /-- The coefficients of the vectors of the intersection that are added to the basis vectors. -/
  complShear : Matrix CommonIndex (Fin i) (𝔸f E)
  /-- The columns of `commonCols` span the intersection of the links. -/
  colSpan_common : colSpan commonCols = link γ ⊓ link γ'
  /-- The complement lies in the link of `γ`. -/
  colSpan_compl_le : colSpan complCols ≤ link γ
  /-- The columns of `complCols` are independent modulo the intersection. -/
  eq_zero_of_mulVec_mem : ∀ t : Fin i → E, complCols *ᵥ t ∈ link γ ⊓ link γ' → t = 0
  /-- The intersection and the complement span the link of `γ`. -/
  colSpan_fromCols : colSpan (fromCols commonCols complCols) = link γ
  /-- The basis vectors, moved along the intersection by `complShear`, have integral lifts. -/
  hasIntegralLifts :
    HasIntegralLifts c γ
      (finAdeleMatrix commonCols * complShear + finAdeleMatrix complCols * complLattice.val)
  /-- The part of `L_γ` common to the two links is a full lattice in `commonLink γ γ'`. -/
  isLatticeOfRank_commonPart :
    IsLatticeOfRank (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ')
  /-- The bound by the gauge, squared. -/
  discriminant_sq_mul_le :
    (S.torsionIndex (S.translateByClassReps c c' γ) *
        discriminant (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ') * x) ^ 2 *
      S.linkDiscSq complCols complLattice ≤ S.levelGauge j c c' γ ^ 2

section

omit [HasPrimitiveRoot5040 E]

/-- Let `γ` have cell rank `j ≤ ϱ + 1` (`S.HasCellRank`). The dimension of the intersection of the
links of `γ` and `γ'` exceeds that of `commonLink γ γ'`, the vectors of `X₀` that both links send
to one vector of `X₀`, by at most `2`, and by at most `1` unless `j = ϱ + 1`. -/
lemma HasCellRank.finrank_link_inf_le {γ : S.G E} {j : Fin (𝔰.ϱ + 2)}
    (h_cell : S.HasCellRank j γ) (γ' : S.G E) :
    finrank E ↥(link γ ⊓ link γ') ≤ finrank E (commonLink γ γ') + (1 + (j - 𝔰.ϱ)) := by
  have h_linked : finrank E (linkedX₀ γ) + (j - 𝔰.ϱ) = 𝔰.k := h_cell.finrank_linkedX₀_add_sub
  have h_corank : finrank E (linkedX₀ γ) + finrank E ↥(link γ ⊓ link γ') ≤
      finrank E (commonLink γ γ') + (𝔰.k + 1) := finrank_linkedX₀_add_finrank_inf_le γ γ'
  omega

/-- Let `γ` have the top cell rank `j = ϱ + 1`, and let the links of `γ` and `γ'` be equal, that is,
of corank `S.linkCorank γ γ' = 0`. Then the dimension of their intersection exceeds by `2` that of
`commonLink γ γ'`, the vectors of `X₀` that both links send to one vector of `X₀`. -/
lemma HasCellRank.finrank_link_inf_eq_add_two {γ γ' : S.G E} {j : Fin (𝔰.ϱ + 2)}
    (h_cell : S.HasCellRank j γ) (h_top : 𝔰.ϱ < j) (h_corank : S.linkCorank γ γ' = 0) :
    finrank E ↥(link γ ⊓ link γ') = finrank E (commonLink γ γ') + 2 := by
  have hj : j - 𝔰.ϱ = 1 := by omega
  have h_linked : finrank E (linkedX₀ γ) + (j - 𝔰.ϱ) = 𝔰.k := h_cell.finrank_linkedX₀_add_sub
  have h_common : finrank E (commonLink γ γ') ≤ finrank E (linkedX₀ γ) :=
    finrank_mono ((commonLink_le_linkedX₀_inf γ γ').trans inf_le_left)
  have h_le : finrank E ↥(link γ ⊓ link γ') ≤ finrank E (commonLink γ γ') + (1 + (j - 𝔰.ϱ)) :=
    h_cell.finrank_link_inf_le γ'
  rw [linkCorank] at h_corank
  omega

omit [CMType E] in
/-- Let `y` extend `x` to a basis of `L` by `r` columns in the kernel of `A` (`IsKernelExtension`).
Then the numbers of columns of `x` and `y` add up to the dimension of `L`. -/
lemma IsKernelExtension.card_add_eq_finrank [Fintype τ] {P : Type} [Fintype P] [DecidableEq τ]
    {A : Matrix τ P E} {x : Matrix P τ E} {L : Submodule E (P → E)} {r : ℕ} {y : Matrix P (Fin r) E}
    (h_ext : IsKernelExtension A x L y) : Fintype.card τ + r = finrank E L := by
  rw [← h_ext.colSpan_fromCols, ← card_eq_finrank_colSpan h_ext.hasLeftInv, card_sum,
    Fintype.card_fin]

end

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- **The splitting.** Let `γ` be a term of cell rank `j` over the classes `c`, `c'` with reduction
`s`, where `s` is compatible with the unipotent character (`S.Agrees s`). Let `x` be a natural
number that is at most the norm `S.meetNorm s` of the product of the places with `S.MeetsAt s`, and
that is `1` unless `j = ϱ + 1` and the links of `γ` and `γ'` are equal. Then there is a
`LinkSplitting`, which consists of the following. Its `complCols` are a basis of a complement of the
intersection of the two links in the link of `γ`, of rank `S.linkCorank γ γ'`, the codimension of
the intersection. Its `complLattice` is a lattice in the complement whose basis vectors have
integral lifts modulo the intersection. The part `S.commonPart c c' γ γ'` of the lattice `L_γ` of
the term that is common to the two links is a full lattice in `commonLink γ γ'`. Finally
`(t * d * x) ^ 2 * D ≤ 𝗀* ^ 2`. Here `t` is the torsion index `S.torsionIndex` of the matrix of
`γ` in the bases of the lattices of `c` and `c'`, `d` is the discriminant of the common part, `D` is
the squared discriminant of the lattice in the complement, and the gauge
`𝗀* = S.levelGauge j c c' γ` is a power of the congruence level `M` times `S.minorGauge j c c'
γ / (S.N ^ f * S.minorNorm j γ)` times the larger of `S.termDiscNorm γ` and
`S.N ^ f * S.minorNorm j γ`, with `f` the number of infinite places. -/
theorem nonempty_linkSplitting {c c' : S.Classes} {γ : S.G E} {j : Fin (𝔰.ϱ + 2)} {s : S.ResidueGL}
    {x : ℕ} (hs : S.Agrees s) (h_term : γ ∈ S.termsOver c s c')
    (h_cell : S.HasCellRank j γ) (γ' : S.G E) (hx : x ≤ S.meetNorm s)
    (h_top : x ≠ 1 → 𝔰.ϱ < j) (h_corank : x ≠ 1 → S.linkCorank γ γ' = 0) :
    Nonempty (S.LinkSplitting c c' j x γ γ' (S.linkCorank γ γ')) := by
  -- Take a basis of `link γ` in three orthogonal parts: `m` spans the kernel of the two `z`-forms
  -- in the intersection of the links, `m` and `u` span the intersection, and `y` completes them.
  -- The discriminant of the lattice of the link is the product of those of three graded pieces.
  obtain ⟨t, m, hm, hm_span⟩ : ∃ (t : ℕ) (m : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin t) E),
      HasLeftInv m ∧ colSpan m = link γ ⊓ link γ' ⊓
        (zRowBlockDiagonal (S.ratMiddle E)).mulVecLin.ker :=
    ⟨_, exists_hasLeftInv_colSpan_eq _⟩
  have hm_link : colSpan m ≤ link γ := hm_span.trans_le (inf_le_left.trans inf_le_left)
  have hm_forms : zRowBlockDiagonal (S.ratMiddle E) * m = 0 :=
    mul_eq_zero_of_colSpan_le_ker (hm_span.trans_le inf_le_right)
  obtain ⟨r, u, hu⟩ : ∃ (r : ℕ) (u : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin r) E),
      IsKernelExtension (mᴴ * S.linkMetric) m (link γ ⊓ link γ') u :=
    exists_isKernelExtension (det_gram_linkMetric_ne_zero hm) (hm_span.trans_le inf_le_left)
  have hmu_span : colSpan (fromCols m u) = link γ ⊓ link γ' := hu.colSpan_fromCols
  obtain ⟨i, y, hy⟩ : ∃ (i : ℕ) (y : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Fin i) E),
      IsKernelExtension ((fromCols m u)ᴴ * S.linkMetric) (fromCols m u) (link γ) y :=
    exists_isKernelExtension (det_gram_linkMetric_ne_zero hu.hasLeftInv)
      (hmu_span.trans_le inf_le_left)
  set k : S.GFin := S.translateByClassReps c c' γ
  obtain ⟨f, hf, hf_disc : S.torsionIndex k ^ 2 * S.linkDiscSq (fromCols (fromCols m u) y) f ≤
      (S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) * S.minorGauge j c c' γ /
        S.N ^ numInfPlaces E) ^ 2⟩ :=
    exists_hasLevelLifts_linkDiscSq_le h_term h_cell hy.hasLeftInv hy.colSpan_fromCols
  obtain ⟨a₁, v, z, ha₁, hv, h_split₂ : S.linkDiscSq (fromCols m u) a₁ * S.linkDiscSq y v =
      S.linkDiscSq (fromCols (fromCols m u) y) f⟩ := hf.exists_orthogonal_split hy.mul_eq_zero
  obtain ⟨a, v₀, z₀, ha, hv₀, h_split₁ : S.linkDiscSq m a * S.linkDiscSq u v₀ =
      S.linkDiscSq (fromCols m u) a₁⟩ := ha₁.exists_orthogonal_split hu.mul_eq_zero
  -- The part `m` is compared with `S.commonPart`.
  have h_common : colSpan m.toRows₁.toRows₁ = commonLink γ γ' := by
    rw [commonLink, ← hm_span, ← LinearMap.range_comp]
    rfl
  obtain ⟨h_rank₀, h_lattice, hm_disc⟩ : t = finrank E (commonLink γ γ') ∧
      IsLatticeOfRank (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ') ∧
      discriminant (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ') ^ 2 ≤
        S.linkDiscSq m a := by
    rw [commonPart, ← h_common]
    exact ha.discriminant_sq_le hm hm_link hm_forms c'
  have h_rank₁ : finrank E (commonLink γ γ') + r = finrank E ↥(link γ ⊓ link γ') := by
    simpa [← h_rank₀] using hu.card_add_eq_finrank
  have h_rank₂ : t + r + i = 𝔰.k + 1 := by simpa [finrank_link] using hy.card_add_eq_finrank
  obtain rfl : i = S.linkCorank γ γ' := by
    rw [linkCorank]
    omega
  -- The part `u` has rank `r ≤ 2`, and the two `z`-forms are injective on its span.
  have hr_le : r ≤ 1 + (j - 𝔰.ϱ) :=
    Nat.le_of_add_le_add_left (h_rank₁.trans_le (h_cell.finrank_link_inf_le γ'))
  have hr_eq (hx_ne : x ≠ 1) : r = 2 := Nat.add_left_cancel
    (h_rank₁.trans (h_cell.finrank_link_inf_eq_add_two (h_top hx_ne) (h_corank hx_ne)))
  have hu_inv : HasLeftInv (zRowBlockDiagonal (S.ratMiddle E) * u) := .of_ker_le_bot fun w hw ↦
    hu.eq_zero_of_mulVec_mem w (hm_span.ge ⟨hu.colSpan_le ⟨w, rfl⟩, by simpa using hw⟩)
  set G : ℝ := S.termDiscNorm γ ⊔ S.N ^ numInfPlaces E * S.minorNorm j γ
  have hu_forms : finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E)) *
      (finAdeleMatrix m * z₀ + finAdeleMatrix u * v₀.val) =
        finAdeleMatrix (zRowBlockDiagonal (S.ratMiddle E) * u) * v₀.val := by
    simp [← Matrix.mul_assoc, ← Matrix.map_mul, hm_forms, Matrix.mul_add]
  have hu_disc : x ^ 2 * S.minorNorm j γ ^ 2 ≤ S.linkDiscSq u v₀ * G ^ 2 :=
    minorNorm_sq_le_linkDiscSq_mul hs h_term h_cell hx hr_le hr_eq
      (hu.colSpan_le.trans inf_le_left) hu_inv v₀ hv₀.hasIntegralLifts hu_forms
  refine ⟨{
    CommonIndex := Fin t ⊕ Fin r
    commonCols := fromCols m u
    complCols := y
    complLattice := v
    complShear := z
    colSpan_common := hmu_span
    colSpan_compl_le := hy.colSpan_le
    eq_zero_of_mulVec_mem := fun w hw ↦ hy.eq_zero_of_mulVec_mem w (hmu_span.ge hw)
    colSpan_fromCols := hy.colSpan_fromCols
    hasIntegralLifts := hv.hasIntegralLifts
    isLatticeOfRank_commonPart := h_lattice
    discriminant_sq_mul_le := le_of_mul_le_mul_right ?_ (pow_pos h_cell.minorNorm_pos 2) }⟩
  have hN : (S.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 S.N_prime.ne_zero
  calc (S.torsionIndex k *
          discriminant (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ') * x) ^ 2 *
        S.linkDiscSq y v * S.minorNorm j γ ^ 2
    _ = discriminant (finrank E (commonLink γ γ')) (S.commonPart c c' γ γ') ^ 2 *
        S.torsionIndex k ^ 2 * S.linkDiscSq y v * (x ^ 2 * S.minorNorm j γ ^ 2) := by ring
    _ ≤ S.linkDiscSq m a * S.torsionIndex k ^ 2 * S.linkDiscSq y v *
        (S.linkDiscSq u v₀ * G ^ 2) := by
      have hm_nonneg : 0 ≤ S.linkDiscSq m a := (sq_nonneg _).trans hm_disc
      have hy_nonneg : 0 ≤ S.linkDiscSq y v := mul_nonneg (abs_nonneg _) (sq_nonneg _)
      gcongr
    _ = S.torsionIndex k ^ 2 * S.linkDiscSq ((m.fromCols u).fromCols y) f * G ^ 2 := by
      rw [← h_split₂, ← h_split₁]
      ring
    _ ≤ (S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) * S.minorGauge j c c' γ /
        S.N ^ numInfPlaces E) ^ 2 * G ^ 2 := by gcongr
    _ = S.levelGauge j c c' γ ^ 2 * S.minorNorm j γ ^ 2 := by
      simp only [levelGauge, h_cell.maxGauge_eq, h_cell.minorGauge_eq, G]
      field_simp

omit [HasPrimitiveRoot5040 E] in
/-- Let `γ` and `γ'` be terms over the classes `c`, `c'` with the same reduction `s` modulo the
level `M = S.M`. Let `w` and `w'` have integral lifts (`HasIntegralLifts`): their columns are the
images, in the links of `γ` and `γ'`, of vectors of the lattice of `c`. Then the products of the
columns of `w` with those of `w'` for the form `S.linkForm / M` are integral adeles. Here
`S.linkForm = diag(T, -T)` on two copies of `X₀ ⊕ E z`, of Gram matrix `T`. -/
lemma HasIntegralLifts.isIntMatrix_linkForm {c c' : S.Classes} {s : S.ResidueGL} {γ γ' : S.G E}
    {σ : Type} [Fintype σ] {w : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ (𝔸f E)}
    {w' : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) σ (𝔸f E)} (h_lift : HasIntegralLifts c γ w)
    (hγ : γ ∈ S.termsOver c s c') (hγ' : γ' ∈ S.termsOver c s c')
    (h_lift' : HasIntegralLifts c γ' w') :
    IsIntMatrix (Ô E) (wᴴ * finAdeleMatrix ((S.M⁻¹ : E) • S.linkForm) * w') := by
  -- The matrix `k` of `δ = γ γ'⁻¹` in the basis of the lattice is congruent to `1` modulo `M`. The
  -- pairing is `-nᴴ J (k - 1) n' / M` for the integral lifts `n`, `n'` of `w`, `w'` and the Gram
  -- matrix `J` of the lattice.
  classical
  obtain ⟨ρ, _, t, u, ht_orth, hn_int, rfl⟩ := h_lift
  obtain ⟨ρ', _, t', u', ht'_orth, hn'_int, rfl⟩ := h_lift'
  set n : Matrix 𝔰.BesselIndex τ (𝔸f E) := S.classCoord c * finAdeleMatrix t * u with hn
  set n' : Matrix 𝔰.BesselIndex σ (𝔸f E) := S.classCoord c * finAdeleMatrix t' * u' with hn'
  let δ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E := (γ * γ'⁻¹ : S.G E)
  let k : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := S.translateByClassReps c c (γ * γ'⁻¹)
  let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex (𝔸f E) := (S.latticeMiddle (𝔸f E)).splitGram
  have hJ_int : IsIntMatrix (Ô E) J := S.isUnimodular_latticeMiddle.splitGram.isIntMatrix
  have hk_congr : IsIntMatrix (Ô E) (S.ideleM⁻¹ • (k - 1)) := by
    have h_one : γ * γ'⁻¹ ∈ S.termsOver c 1 c := by simpa using termsOver.mul hγ (.inv hγ')
    have h_level : S.translateByClassReps c c (γ * γ'⁻¹) ∈ unitaryLevel (Ô E) S.ideleM J :=
      S.principalLevel_eq_unitaryLevel.le h_one
    exact h_level.right
  -- The pairing of the rational vectors, over `E`.
  have h_rat : (linkMatrix γ * t)ᴴ * ((S.M⁻¹ : E) • S.linkForm) * (linkMatrix γ' * t') =
      (S.M⁻¹ : E) • (tᴴ * S.ratGram * t') - (S.M⁻¹ : E) • (tᴴ * S.ratGram * (δ * t')) := by
    simpa [δ, fromBlocks_smul] using gram_linkMatrix_mul ht_orth ht'_orth (S.M⁻¹ : E) (S.M⁻¹ : E)
  -- `S.classCoord c` carries `S.ratGram` to `J` and conjugates `δ` to `k`.
  have h_gram (y : Matrix 𝔰.BesselIndex ρ' E) :
      uᴴ * finAdeleMatrix (tᴴ * S.ratGram * y) * u' =
        nᴴ * J * (S.classCoord c * finAdeleMatrix y * u') := by
    rw [← classCoord_gram c, hn]
    simp only [J, conjTranspose_mul, Matrix.mul_assoc]
  have h_conj : S.classCoord c * finAdeleMatrix δ = k * S.classCoord c := by
    have hk_eq : k = S.classCoord c * finAdeleMatrix δ * (classBasis c).val :=
      congrArg Units.val (coe_translateByClassReps c c (γ * γ'⁻¹))
    rw [hk_eq, classCoord, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have h_move : S.classCoord c * finAdeleMatrix (δ * t') * u' = k * n' := by
    rw [finAdeleMatrix, Matrix.map_mul, ← Matrix.mul_assoc, h_conj, hn']
    simp only [Matrix.mul_assoc]
  have hM_inv : ((S.M⁻¹ : E) : 𝔸f E) = S.ideleM⁻¹.val := by simp [ideleM]
  have h_pairing :
      (finAdeleMatrix (linkMatrix γ * t) * u)ᴴ * finAdeleMatrix ((S.M⁻¹ : E) • S.linkForm) *
          (finAdeleMatrix (linkMatrix γ' * t') * u') =
        -(nᴴ * J * (S.ideleM⁻¹ • (k - 1) * n')) :=
    calc (finAdeleMatrix (linkMatrix γ * t) * u)ᴴ * finAdeleMatrix ((S.M⁻¹ : E) • S.linkForm) *
          (finAdeleMatrix (linkMatrix γ' * t') * u')
      _ = uᴴ * finAdeleMatrix
          ((linkMatrix γ * t)ᴴ * ((S.M⁻¹ : E) • S.linkForm) * (linkMatrix γ' * t')) * u' := by
        simp only [conjTranspose_mul, Matrix.map_mul, finAdeleMatrix_conjTranspose,
          Matrix.mul_assoc]
      _ = S.ideleM⁻¹.val • (uᴴ * finAdeleMatrix (tᴴ * S.ratGram * t') * u') -
          S.ideleM⁻¹.val • (uᴴ * finAdeleMatrix (tᴴ * S.ratGram * (δ * t')) * u') := by
        rw [h_rat, ← hM_inv]
        simp [Matrix.map_sub, Matrix.mul_sub, Matrix.sub_mul]
      _ = S.ideleM⁻¹.val • (nᴴ * J * n') - S.ideleM⁻¹.val • (nᴴ * J * (k * n')) := by
        rw [h_gram t', h_gram (δ * t'), h_move]
      _ = -(nᴴ * J * (S.ideleM⁻¹ • (k - 1) * n')) := by
        simp [Units.smul_def, smul_sub, Matrix.mul_sub, Matrix.sub_mul]
  rw [h_pairing]
  exact ((hn_int.conjTranspose.mul hJ_int).mul (hk_congr.mul hn'_int)).neg

end New.Filling
