import Lib.Adelic.Reduction.MinkowskiTheorems
import Lib.Shimura.Uniformisation.AdelicFrames

/-!
# Lattice indices, primitive matrices, Jacobi's identity and covolumes of fundamental domains

The first part is lattice algebra over an adelic pair `R ⊆ A` (`New.IsAdelic`; among its conditions,
`R` is open and compact in `A`), modelled on `New.Ô` inside the finite adeles. The file proves
results on indices and determinants under integral base change. For a CM field `E`, it then gives
tools for computing, coordinate by coordinate, the covolume of an arithmetic subgroup of a unipotent
group.

## Main definitions and results

* `New.genIndex_det_conj_of_isIntMatrix`: the size of a determinant does not change under an
  integral base change with integral inverse.
* `New.exists_isPrimitiveMatrix_mul_fromBlocks`, `New.exists_preimageLattice_eq_colLattice`: a left
  invertible matrix becomes primitive after multiplication by an invertible (block triangular)
  matrix.
* `New.exists_mulVec_eq_of_orthogonal`: for `J` hermitian and invertible, if the left invertible `F`
  and `n` have orthogonal columns, as many in all as `J` has rows, the orthogonal complement of `n`
  lies in the span of `F`.
* `New.genIndex_det_orthogonal_mul_submoduleIndex_sq`: Jacobi's identity between a lattice and its
  orthogonal complement; `New.Filling.jacobi_perp_discriminant` joins it with the previous result.
* `New.exists_fundamental_domain_classLattice`: the covolume of a lattice in `(E ⊗ ℝ)ⁿ` cut out by a
  finite adelic matrix and rescaled at the infinite places.
* `New.Filling.existsUnique_mul_mem_box`: suppose a group `Γ` shifts the coordinates of `G` in a
  triangular way by additive submonoids. Then the box over strict fundamental domains of these
  submonoids meets each coset `xΓ` exactly once.
* `New.Filling.exists_fundamental_domain_im_skew`: the covolume of the group
  `New.Filling.imSkewLattice` of rescaled purely imaginary integers of `E`, if `E` contains a
  primitive 5040th root of unity.

Notions from other files:
* `New.genIndex`: on units the inverse of the factor by which multiplication scales Haar measure,
  and `0` elsewhere; `New.submoduleIndex M M'`: the index of `M ∩ M'` in `M'`, as additive groups
  (`0` if infinite).
* `New.IsPrimitiveMatrix`: a matrix with entries in `R` and a left inverse with entries in `R`.
* `New.colLattice`: the `R`-module spanned by the columns of `M`; `New.preimageLattice`: the
  `R`-module of vectors `v` over `A` such that `M v` has entries in `R`.
* `New.Variety.classLattice g S Q`: the image, under the CM embedding followed by the linear map
  `Q`, of the group of `y` in `Eⁿ` such that the class of `g⁻¹ y` in `(𝔸_f/Ô)ⁿ` lies in `S`.

## Relation to the literature

Known; see `Lib.Adelic.Adeles.Basic` and `New.Spanning.RemainingTerms.SiegelLemma` for sources.
-/

namespace New

/-! ## Indices, primitive matrices and Jacobi's identity -/

section LatticeComplement

open Matrix Fintype AddSubgroup Submodule

variable {A : Type*} [CommRing A] {R : Subring A}
  {π σ τ ρ : Type} [Fintype π] [DecidableEq π] [Fintype σ] [DecidableEq σ]
  [DecidableEq τ] [Fintype ρ] {M D : Submodule R (τ → A)} {K K' : Submodule R (σ → A)}
  {H J : Matrix π π A} {m F : Matrix π σ A} {n : Matrix π τ A} (P : (τ → A) →ₗ[R] σ → A)

/-! ### Indices under a linear map and divisibility -/

omit [Fintype σ] [DecidableEq σ] [DecidableEq τ] in
/-- If `P` maps `D` into `K` and `K'` lies in `P M + K`, then the index of `K` in `K'` divides the
index of `D` in `M` (indices in the sense of `New.submoduleIndex`). -/
lemma Filling.submoduleIndex_dvd_of_le (hD : D ≤ K.comap P) (hK' : K' ≤ M.map P ⊔ K) :
    submoduleIndex K K' ∣ submoduleIndex D M := by
  -- The index of `K` in `K'` divides the index of `K` in `M.map P ⊔ K`, which is the index of
  -- `K.comap P` in `M`; that divides the index of `D ≤ K.comap P` in `M`.
  calc submoduleIndex K K'
    _ ∣ submoduleIndex K (M.map P ⊔ K) := by
      rw [submoduleIndex, ← relIndex_addSubgroupOf (toAddSubgroup_mono hK')]
      exact relIndex_dvd_index_of_normal _ _
    _ ∣ (AddSubgroup.comap (P : (τ → A) →+ σ → A) K.toAddSubgroup).relIndex M.toAddSubgroup := by
      simp [submoduleIndex, sup_toAddSubgroup, map_toAddSubgroup, ← relIndex_comap]
    _ ∣ submoduleIndex D M := relIndex_dvd_of_le_left _ (toAddSubgroup_mono hD)

lemma ne_zero_and_le_of_dvd {a b : ℕ} (hb : b ≠ 0) (hab : a ∣ b) : a ≠ 0 ∧ a ≤ b :=
  ⟨ne_zero_of_dvd_ne_zero hb hab, Nat.le_of_dvd hb.pos hab⟩

/-! ### Orthogonal complements over a commutative ring -/

omit [DecidableEq π] in
/-- If `P * Q = 1`, `P * n = 0` and `l * n = 1`, then the matrix with row blocks `P` and
`l - l * Q * P` is a left inverse of the matrix with column blocks `Q` and `n`. -/
lemma fromRows_mul_fromCols_eq_one {P : Matrix σ π A} {Q : Matrix π σ A} {n : Matrix π τ A}
    {l : Matrix τ π A} (hPQ : P * Q = 1) (hPn : P * n = 0) (hln : l * n = 1) :
    fromRows P (l - l * Q * P) * fromCols Q n = 1 := by
  simp [← fromBlocks_one, hPQ, hPn, hln, Matrix.mul_assoc, sub_eq_add_neg, Matrix.add_mul]

/-- Let `J` be hermitian and invertible, and let `F` and `n` be left invertible, with the columns of
`F` orthogonal to those of `n` for `J` and as many columns in all as `J` has rows. Then a vector
orthogonal to the columns of `n` is a combination of the columns of `F`. -/
lemma exists_mulVec_eq_of_orthogonal [Fintype τ] [StarRing A] {J : GL π A} {F : Matrix π σ A}
    {n : Matrix π τ A} (h_herm : J.valᴴ = J.val) (hF : HasLeftInv F) (hn : HasLeftInv n)
    (hFn : Fᴴ * J.val * n = 0) (hπ : card π = card σ + card τ) {v : π → A}
    (hv : nᴴ *ᵥ J.val *ᵥ v = 0) :
    ∃ w : σ → A, F *ᵥ w = v := by
  -- With `r * F = 1`, `P = Fᴴ * J` and `Q = J⁻¹ * rᴴ`, the square matrix `B = (Q | n)` has a left,
  -- hence two-sided, inverse `B'` with upper block `P`.
  obtain ⟨r, hrF⟩ := hF
  obtain ⟨l, hln⟩ := hn
  let P : Matrix σ π A := Fᴴ * J.val
  let Q : Matrix π σ A := J⁻¹.val * rᴴ
  have hPQ : P * Q = 1 := by simpa [P, Q, Matrix.mul_assoc] using congrArg conjTranspose hrF
  let B : Matrix π (σ ⊕ τ) A := fromCols Q n
  let B' : Matrix (σ ⊕ τ) π A := fromRows P (l - l * Q * P)
  have h_right : B * B' = 1 := (mul_eq_one_comm_of_card_eq π (σ ⊕ τ) A (by rw [card_sum, hπ])).2
    (fromRows_mul_fromCols_eq_one hPQ hFn hln)
  -- Apply the adjoint of `h_right` for `J` to `v`: the terms through `nᴴ * J` vanish.
  have h_apply : (J⁻¹.val * (B * B')ᴴ * J.val) *ᵥ v = v := by simp [h_right]
  refine ⟨Qᴴ *ᵥ J.val *ᵥ v, ?_⟩
  simpa [← mulVec_mulVec, B, B', P, Q, h_herm, hv, Matrix.mul_assoc, fromCols_mul_fromRows,
    Matrix.mul_add, add_mulVec, neg_mulVec, sub_eq_add_neg] using h_apply

variable [Fintype τ]

variable [StarRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
  [ad : IsAdelic R] {l : Matrix τ π A}

include ad

/-! ### Determinants, saturation and orthogonal complements -/

/-- Replacing the form `H` by `Jᴴ * H * J` multiplies the generalised index of its determinant by
the square of that of `det J` (`genIndex` is the inverse Haar modulus on units, `0` elsewhere). -/
lemma genIndex_det_conj [PolishSpace A] :
    genIndex (Jᴴ * H * J).det = genIndex H.det * genIndex J.det ^ 2 := by
  simp [field]

/-- If `n` and `l` are integral and inverse to each other, the Gram matrix `nᴴ * H * n` of `H` in
the basis `n` has a determinant of the same generalised index as `det H`. -/
lemma genIndex_det_conj_of_isIntMatrix [PolishSpace A] (hn : IsIntMatrix R n) (hl : IsIntMatrix R l)
    (hln : l * n = 1) (hnl : n * l = 1) :
    genIndex H.det = genIndex (nᴴ * H * n).det := by
  -- `n * nᴴ` is integral with the integral inverse `lᴴ * l`, so its determinant has `genIndex = 1`.
  have h_inv : lᴴ * l * (n * nᴴ) = 1 := by
    simp [Matrix.mul_assoc, ← Matrix.mul_assoc l n, hln, ← conjTranspose_mul, hnl]
  obtain ⟨u, hu, hu_eq⟩ : ∃ u ∈ intGL π R, u.val = n * nᴴ := isPrimitiveMatrix_iff.1
    ⟨hn.mul hn.conjTranspose, lᴴ * l, hl.conjTranspose.mul hl, h_inv⟩
  have h_det : (nᴴ * H * n).det = u.1.det * H.det := by
    rw [← det_comm' hnl hln, ← Matrix.mul_assoc, ← hu_eq, det_mul]
  simp [h_det, genIndex_det_eq_one ad.isOpen_isCompact.1 ad.isOpen_isCompact.2 hu]

omit [IsTopologicalRing A] [LocallyCompactSpace A] in
/-- A left invertible matrix whose columns fall into two blocks becomes primitive after
multiplication by a block upper triangular matrix with invertible diagonal blocks. -/
lemma exists_isPrimitiveMatrix_mul_fromBlocks (m : Matrix π (σ ⊕ τ) A) (hm : HasLeftInv m) :
    ∃ᵉ (a : GL σ A) (e : GL τ A) (z : Matrix σ τ A),
      IsPrimitiveMatrix R (m * fromBlocks a.val z 0 e.val) := by
  -- Some `b`, block triangular for the weight 0 on `σ` and 1 on `τ`, makes `m * b` primitive.
  obtain ⟨b, hb_tri, hb_prim⟩ := ad.isValuationPair.exists_isPrimitiveMatrix_mul hm (0 ⊕ᵥ 1)
  have h_lower : b.1.toBlocks₂₁ = 0 := Matrix.ext fun i j ↦ hb_tri zero_lt_one
  have h_blocks : fromBlocks b.1.toBlocks₁₁ b.1.toBlocks₁₂ 0 b.1.toBlocks₂₂ = b.1 := by
    rw [← h_lower, fromBlocks_toBlocks]
  -- The diagonal blocks of an invertible block triangular matrix are invertible.
  obtain ⟨h₁, h₂⟩ : IsUnit b.1.toBlocks₁₁ ∧ IsUnit b.1.toBlocks₂₂ := by
    rw [← isUnit_fromBlocks_zero₂₁ (B := b.1.toBlocks₁₂), h_blocks]
    exact b.isUnit
  exact ⟨h₁.unit, h₂.unit, b.1.toBlocks₁₂, by simpa [h_blocks]⟩

omit [IsTopologicalRing A] [LocallyCompactSpace A] in
/-- For an adelic pair `R ⊆ A` and a left invertible matrix `m` over `A`, there is an invertible
`a` whose columns span `{y | m y integral}` over `R`, with `m * a` primitive over `R`. -/
lemma exists_preimageLattice_eq_colLattice (hm : HasLeftInv m) :
    ∃ a : GL σ A, preimageLattice R m = colLattice R a.val ∧ IsPrimitiveMatrix R (m * a.val) := by
  -- Some invertible `a` makes `m * a` integral with an integral left inverse `l`.
  obtain ⟨a, -, h_int, l, hl_int, hl⟩ := ad.isValuationPair.exists_isPrimitiveMatrix_mul hm
  refine ⟨a, le_antisymm ?_ (colLattice_le h_int.transpose), h_int, l, hl_int, hl⟩
  -- Conversely, if `m v` is integral then `v = a (l m v)`, as `l * m` is inverse to `a`.
  intro v (hv : m *ᵥ v ∈ intVectors R π)
  have h_inv : a.val * (l * m) = 1 := mul_eq_one_comm.1 (by rw [Matrix.mul_assoc, hl])
  exact ⟨l *ᵥ m *ᵥ v, hl_int.mulVec hv, by simp [h_inv]⟩

omit [DecidableEq π] ad in
/-- If the Gram matrix of the columns `(F | p)` for the form `J`, with `c` added on the diagonal of
the `p` block, has a determinant of nonzero generalised index (that is, a unit determinant), then
`F` has a left inverse over `A`. -/
lemma hasLeftInv_of_genIndex_det_ne_zero [DecidableEq ρ] {N : Matrix (σ ⊕ ρ) (σ ⊕ ρ) A}
    {p : Matrix π ρ A} {c : Aˣ}
    (hN : N = (fromCols F p)ᴴ * J * fromCols F p + fromBlocks 0 0 0 (c • 1))
    (h_det : genIndex N.det ≠ 0) : HasLeftInv F := by
  refine ⟨toRows₁ (N⁻¹ * (fromCols F p)ᴴ * J), ?_⟩
  let e : Matrix (σ ⊕ ρ) σ A := fromRows (1 : Matrix σ σ A) (0 : Matrix ρ σ A)
  -- The first block column of `N` is `(F | p)ᴴ * J * F`.
  have h_col : N * e = (fromCols F p)ᴴ * J * F := by
    simp [e, hN, Matrix.add_mul, Matrix.mul_assoc, fromCols_mul_fromRows, fromBlocks_mul_fromRows]
  have h_cancel : N⁻¹ * ((fromCols F p)ᴴ * J * F) = e := by
    rw [← h_col, N.nonsing_inv_mul_cancel_left e (genIndex.apply_ne_zero_iff.1 h_det)]
  -- the definition of `toRows₁` has to unfold, hence `using!`
  simpa [e, ← Matrix.mul_assoc, -fromRows_mul] using! congrArg toRows₁ h_cancel

omit [Fintype π] [DecidableEq π] in
/-- If `F` is integral and the columns of the invertible `a` span `{y | F y integral}`, the index of
`R^σ` in this lattice is the inverse of the generalised index of `det a`. -/
lemma submoduleIndex_intVectors_mul_genIndex_det [PolishSpace A] {a : GL σ A} (hF : IsIntMatrix R F)
    (h_sat : preimageLattice R F = colLattice R a.val) :
    submoduleIndex (intVectors R σ) (preimageLattice R F) * genIndex a.val.det = 1 := by
  have h_le : intVectors R σ ≤ colLattice R a.1 :=
    le_of_le_of_eq (fun v hv ↦ hF.mulVec hv) h_sat
  have h_one : submoduleIndex (colLattice R a.1) (intVectors R σ) = 1 :=
    relIndex_eq_one.2 (toAddSubgroup_mono h_le)
  have h_quot :
      1 / (submoduleIndex (intVectors R σ) (preimageLattice R F) : ℝ) = genIndex a.1.det := by
    simpa [h_one, h_sat] using submoduleIndex_colLattice_div (R := R) (M := a)
  -- the index is nonzero because `genIndex (det a)` is
  have h_pos : 0 < genIndex a.1.det := by simpa using genIndex_pos a.det
  grind

omit [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A] ad in
/-- Let `P = (F * a)ᴴ * u` with `u` hermitian and `P * Q = 1`, and let `N` be the Gram matrix of the
columns `(F | p)` for `u` with `c` added on the diagonal of the `p` block. Then the displayed
matrix, one plus a product of a block column and a block row, is `N` between two block triangular
matrices. -/
lemma one_add_fromRows_mul_fromCols_eq [DecidableEq ρ] {u : GL π A} {a : GL σ A}
    {Q : Matrix π σ A} {p : Matrix π ρ A} {c : Aˣ} {N : Matrix (σ ⊕ ρ) (σ ⊕ ρ) A}
    (h_herm : u.1ᴴ = u.1) (hPQ : (F * a.1)ᴴ * u.1 * Q = 1)
    (hN : N = (fromCols F p)ᴴ * u.1 * fromCols F p + fromBlocks 0 0 0 (c • 1)) :
    1 + fromRows ((F * a.1)ᴴ * u.1) (pᴴ * u.1 * (1 - Q * ((F * a.1)ᴴ * u.1))) *
        fromCols (u⁻¹.1 * ((F * a.1)ᴴ * u.1)ᴴ - Q) (c⁻¹ • p) =
      fromBlocks aᴴ 0 (-pᴴ * u.1 * Q * a.1ᴴ) 1 * N * fromBlocks a 0 0 (c⁻¹ • 1) := by
  -- Write both sides as block matrices and compare the four blocks.
  set P : Matrix σ π A := (F * a.1)ᴴ * u.1
  set C : Matrix ρ σ A := -pᴴ * u.1 * Q * a.1ᴴ
  have hN_blocks : N = fromBlocks (Fᴴ * u.1 * F) (Fᴴ * u.1 * p) (pᴴ * u.1 * F)
      (pᴴ * u.1 * p + c • 1) := by
    simp [hN, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromBlocks_add]
  have hPu : u⁻¹.1 * Pᴴ = F * a.1 := by simp [P, h_herm, ← Matrix.mul_assoc]
  have h₁₁ : 1 + P * (u⁻¹.1 * Pᴴ - Q) = a.1ᴴ * (Fᴴ * u.1 * F) * a.1 := by
    rw [hPu, Matrix.mul_sub, hPQ]
    simp [P, Matrix.mul_assoc]
  have h₂₁ : pᴴ * u.1 * (1 - Q * P) * (u⁻¹.1 * Pᴴ - Q) =
      (C * (Fᴴ * u.1 * F) + pᴴ * u.1 * F) * a.1 := by
    have hQ : (1 - Q * P) * Q = 0 := by simp [Matrix.sub_mul, Matrix.mul_assoc, hPQ]
    rw [Matrix.mul_sub, Matrix.mul_assoc _ (1 - Q * P) Q, hQ, hPu]
    simp [P, C, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, sub_eq_neg_add]
  have h₂₂ : 1 + pᴴ * u.1 * (1 - Q * P) * (c⁻¹ • p) =
      (C * (Fᴴ * u.1 * p) + (pᴴ * u.1 * p + c • 1)) * (c⁻¹ • (1 : Matrix ρ ρ A)) := by
    simp [P, C, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm]
  rw [hN_blocks, fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_add, fromBlocks_multiply,
    fromBlocks_multiply, h₁₁, h₂₂, h₂₁]
  simp [P, Matrix.mul_assoc]

variable [PolishSpace A]

/-- Jacobi's identity between the discriminants of a lattice and of its orthogonal complement. Let
`J` be unimodular hermitian, `F` integral and left invertible over `A`, and `n` primitive, with the
columns of `F` orthogonal to those of `n` and as many columns in all as `J` has rows. Take the Gram
matrix of the columns `(F | p)` and add the unit `c` on the diagonal of the `p` block. The
generalised index of its determinant is the product of the generalised index of the determinant on
`n` of the form `J + c⁻¹ J p pᴴ J`, of the square of the index of `R^σ` in `{y | F y integral}`,
and of `genIndex c ^ card ρ`. -/
lemma genIndex_det_orthogonal_mul_submoduleIndex_sq [DecidableEq ρ] {J : Matrix π π A}
    {F : Matrix π σ A} {n : Matrix π τ A} (hJ : IsUnimodular R J) (hF : IsIntMatrix R F)
    (hF_inv : HasLeftInv F) (hn : IsPrimitiveMatrix R n) (hFn : Fᴴ * J * n = 0)
    (hπ : card π = card σ + card τ) (p : Matrix π ρ A) (c : Aˣ) :
    genIndex (nᴴ * (J + c⁻¹ • (J * p * pᴴ * J)) * n).det *
        submoduleIndex (intVectors R σ) (preimageLattice R F) ^ 2 * genIndex c.val ^ card ρ =
      genIndex ((fromCols F p)ᴴ * J * fromCols F p + fromBlocks 0 0 0 (c • 1)).det := by
  -- Saturate `F` to a primitive `F * a` with left inverse `r`. With `P = (F * a)ᴴ * J` and
  -- `Q = J⁻¹ * rᴴ`, the integral matrix `B = (Q | n)` has an integral inverse `B'`. Compute the
  -- determinant of one matrix `H` twice: in the basis `B`, and by
  -- `det (1 + X * Y) = det (1 + Y * X)`.
  obtain ⟨a, h_sat, hFa, r, hr, hrFa⟩ := exists_preimageLattice_eq_colLattice (R := R) hF_inv
  obtain ⟨hn_int, l, hl, hln⟩ := hn
  obtain ⟨h_herm, u, hu, rfl⟩ := hJ
  let N : Matrix (σ ⊕ ρ) (σ ⊕ ρ) A :=
    (fromCols F p)ᴴ * u.1 * fromCols F p + fromBlocks 0 0 0 (c • 1)
  let P : Matrix σ π A := (F * a.1)ᴴ * u.1
  let Q : Matrix π σ A := u⁻¹.1 * rᴴ
  have hP : IsIntMatrix R P := hFa.conjTranspose.mul hu.isIntMatrix
  have hQ : IsIntMatrix R Q := hu.isIntMatrix_inv.mul hr.conjTranspose
  have hPQ : P * Q = 1 := by simpa [P, Q, Matrix.mul_assoc] using congrArg conjTranspose hrFa
  have hPn : P * n = 0 := by simpa [P, Matrix.mul_assoc] using congrArg (a.1ᴴ * ·) hFn
  let B : Matrix π (σ ⊕ τ) A := fromCols Q n
  let B' : Matrix (σ ⊕ τ) π A := fromRows P (l - l * Q * P)
  have h_left : B' * B = 1 := fromRows_mul_fromCols_eq_one hPQ hPn hln
  have h_right : B * B' = 1 :=
    (mul_eq_one_comm_of_card_eq π (σ ⊕ τ) A (by rw [card_sum, hπ])).2 h_left
  have hB : IsIntMatrix R B := fun i ↦ Sum.rec (hQ i) (hn_int i)
  have hB' : IsIntMatrix R B' := Sum.rec hP (hl.sub ((hl.mul hQ).mul hP))
  let X : Matrix π (σ ⊕ ρ) A := fromCols (u⁻¹.1 * Pᴴ - Q) (c⁻¹ • p)
  let Y : Matrix (σ ⊕ ρ) π A := fromRows P (pᴴ * u.1 * (1 - Q * P))
  let H : Matrix π π A := u.1 * (1 + X * Y)
  -- In the basis `B`, `H` is block triangular with diagonal blocks `1` and the form on `n`.
  have h_tri : (Bᴴ * H * B).det = (nᴴ * (u.1 + c⁻¹ • (u.1 * p * pᴴ * u.1)) * n).det := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul]
    simp [B, H, X, Y, hPQ, hPn, ← conjTranspose_mul, Units.smul_def, Matrix.mul_add, sub_eq_add_neg,
      Matrix.mul_assoc, fromCols_mul_fromRows, Matrix.add_mul]
  -- `1 + Y * X` is `N` up to two block triangular factors, of determinants `det aᴴ` and
  -- `det a * c⁻¹ ^ card ρ`.
  have h_swap :
      1 + Y * X = fromBlocks aᴴ 0 (-pᴴ * u.1 * Q * a.1ᴴ) 1 * N * fromBlocks a 0 0 (c⁻¹ • 1) :=
    one_add_fromRows_mul_fromCols_eq h_herm hPQ rfl
  have h_factor : genIndex H.det =
      genIndex N.det * genIndex a.1.det ^ 2 * genIndex c⁻¹.1 ^ card ρ := by
    rw [det_mul, det_one_add_mul_comm, h_swap]
    simp [Units.smul_def, genIndex_det_eq_one ad.isOpen_isCompact.1 ad.isOpen_isCompact.2 hu]
    ring
  -- Equate the two computations of `genIndex H.det` and cancel the factors of `a` and of `c`.
  calc _ = genIndex N.det *
        (submoduleIndex (intVectors R σ) (preimageLattice R F) * genIndex a.1.det) ^ 2 *
          (genIndex c.1 * genIndex c⁻¹.1) ^ card ρ := by
        rw [← h_tri, ← genIndex_det_conj_of_isIntMatrix hB hB' h_left h_right, h_factor]
        ring
    _ = genIndex N.det := by
        rw [submoduleIndex_intVectors_mul_genIndex_det hF h_sat, ← map_mul]
        simp

/-- Jacobi's identity, over `R ⊂ A` modelled on `Ô ⊂ 𝔸_f` (`IsAdelic R`). Let `J` be unimodular
hermitian, `F` integral and `n` primitive, with `Fᴴ J n = 0` and `card π = card σ + card τ`; let `N`
be `(F | p)ᴴ J (F | p)` plus the unit `c` on the diagonal of the `p` block, and let `F` be left
invertible or `genIndex N.det ≠ 0`, where `genIndex a` is the inverse of the Haar-measure scaling
factor of multiplication by `a` (`0` for a non-unit). Then (a) every `u` with `nᴴ J u = 0` equals
`F v` for some `v` over `A`, and (b) `genIndex N.det` is the product of
`genIndex det (nᴴ (J + c⁻¹ J p pᴴ J) n)`, the square of the index of `R^σ` in `{y | F y integral}`,
and `genIndex c ^ card ρ`. -/
lemma Filling.jacobi_perp_discriminant [DecidableEq ρ] {J : Matrix π π A} {F : Matrix π σ A}
    {n : Matrix π τ A} {N : Matrix (σ ⊕ ρ) (σ ⊕ ρ) A} (hJ : IsUnimodular R J)
    (hF : IsIntMatrix R F) (hn : IsPrimitiveMatrix R n) (hFn : Fᴴ * J * n = 0)
    (hπ : card π = card σ + card τ) (p : Matrix π ρ A) (c : Aˣ)
    (hN : N = (fromCols F p)ᴴ * J * fromCols F p + fromBlocks 0 0 0 (c • 1))
    (hFN : HasLeftInv F ∨ genIndex N.det ≠ 0) :
    -- (a)
    (∀ u : π → A, nᴴ *ᵥ J *ᵥ u = 0 → ∃ v : σ → A, F *ᵥ v = u) ∧
    -- (b)
    genIndex (nᴴ * (J + c⁻¹ • (J * p * pᴴ * J)) * n).det *
        submoduleIndex (intVectors R σ) (preimageLattice R F) ^ 2 * genIndex c.val ^ card ρ =
      genIndex N.det := by
  have hF_inv : HasLeftInv F := hFN.elim id (hasLeftInv_of_genIndex_det_ne_zero hN)
  refine ⟨fun u hu ↦ ?_, ?_⟩
  · obtain ⟨h_herm, J, -, rfl⟩ := hJ
    obtain ⟨-, l, -, hln⟩ := hn
    exact exists_mulVec_eq_of_orthogonal h_herm hF_inv ⟨l, hln⟩ hFn hπ hu
  · simpa only [hN] using genIndex_det_orthogonal_mul_submoduleIndex_sq hJ hF hF_inv hn hFn hπ p c

end LatticeComplement

/-! ## The quotient of a unimodular lattice by an isotropic sublattice -/

section Quotient

open Matrix Fintype Sum

variable {A : Type*} {π σ μ : Type} [CommRing A] [StarRing A] {R : Subring A} [Fintype π]
  [Fintype σ] [Fintype μ] [DecidableEq π] [DecidableEq σ] [DecidableEq μ]

omit [DecidableEq π] in
/-- Orthogonality for a hermitian form `J` is symmetric. -/
lemma orthogonal_symm {J : Matrix π π A} (hJ : Jᴴ = J) {ρ ρ' : Type} {x : Matrix π ρ A}
    {y : Matrix π ρ' A} (h : xᴴ * J * y = 0) : yᴴ * J * x = 0 := by
  rw [← conjTranspose_eq_zero, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    hJ, ← Matrix.mul_assoc, h]

variable (R) in
/-- Let `Λ = R ^ π` carry the form `J`, and let the columns of `ι` be a basis of `Λ ∩ I` for an
isotropic space `I`. The columns of `B` represent a basis of the lattice `(Λ ∩ I^⊥)/(Λ ∩ I)`, and
`q` gives the coordinates of the class of a vector of `I^⊥` in this basis. -/
structure IsQuotientBasis (J : Matrix π π A) (ι : Matrix π σ A) (B : Matrix π μ A)
    (q : Matrix μ π A) : Prop where
  /-- The representatives lie in `Λ`. -/
  isIntMatrix_basis : IsIntMatrix R B
  /-- A vector of `Λ` has integral coordinates. -/
  isIntMatrix_coord : IsIntMatrix R q
  /-- The vectors of `I` have the class zero. -/
  coord_mul_isotropic : q * ι = 0
  /-- The coordinates of the columns of `B` are the unit vectors. -/
  coord_mul_basis : q * B = 1
  /-- The representatives lie in `I^⊥`. -/
  basis_orthogonal : ιᴴ * J * B = 0
  /-- A vector of `I^⊥` differs from the representative of its class by a vector of `I`, with
  coefficients that depend integrally on the vector. -/
  exists_eq_add : ∃ l : Matrix σ π A, IsIntMatrix R l ∧
    ∀ {ρ : Type} {x : Matrix π ρ A}, ιᴴ * J * x = 0 → x = ι * (l * x) + B * (q * x)

namespace IsQuotientBasis

variable {J : Matrix π π A} {ι : Matrix π σ A} {B : Matrix π μ A} {q : Matrix μ π A}
  {ρ ρ' : Type} {x : Matrix π ρ A} {y : Matrix π ρ' A}

omit [DecidableEq π] [DecidableEq σ] in
/-- The product of two vectors of `I^⊥` depends only on the class of the second. -/
lemma mul_basis_mul_coord (h : IsQuotientBasis R J ι B q) (hx : xᴴ * J * ι = 0)
    (hy : ιᴴ * J * y = 0) : xᴴ * J * B * (q * y) = xᴴ * J * y := by
  obtain ⟨l, -, hl⟩ := h.exists_eq_add
  conv_rhs => rw [hl hy]
  rw [Matrix.mul_add, ← Matrix.mul_assoc _ ι, hx, Matrix.zero_mul, zero_add, Matrix.mul_assoc _ B]

omit [DecidableEq π] [DecidableEq σ] in
/-- The form `Bᴴ J B` on the quotient is induced by `J`: on the coordinates of the classes of two
vectors of `I^⊥` it takes the value of `J` on the vectors themselves, for hermitian `J`. -/
lemma gram_coord (h : IsQuotientBasis R J ι B q) (hJ : Jᴴ = J) (hx : ιᴴ * J * x = 0)
    (hy : ιᴴ * J * y = 0) : (q * x)ᴴ * (Bᴴ * J * B) * (q * y) = xᴴ * J * y := by
  have h_swap {τ τ' : Type} (s : Matrix π τ A) (t : Matrix π τ' A) :
      (sᴴ * J * t)ᴴ = tᴴ * J * s := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  have hy' : yᴴ * J * ι = 0 := orthogonal_symm hJ hy
  have hB : Bᴴ * J * ι = 0 := orthogonal_symm hJ h.basis_orthogonal
  -- Replace the class of `y` by `y`, transpose, and then replace the class of `x` by `x`.
  calc (q * x)ᴴ * (Bᴴ * J * B) * (q * y)
    _ = (q * x)ᴴ * (Bᴴ * J * y) := by rw [Matrix.mul_assoc, h.mul_basis_mul_coord hB hy]
    _ = (yᴴ * J * B * (q * x))ᴴ := by
      rw [conjTranspose_mul (yᴴ * J * B), h_swap y B]
    _ = (yᴴ * J * x)ᴴ := by rw [h.mul_basis_mul_coord hy' hx]
    _ = xᴴ * J * y := h_swap y x

omit [DecidableEq σ] in
/-- Let `Λ = R^π` carry the form `J`, let the columns of `ι` be a basis of `Λ ∩ I` for an isotropic
space `I`, and let `B` represent a basis of `(Λ ∩ I^⊥)/(Λ ∩ I)` (`IsQuotientBasis`). If `R` is
stable under `star` and `J` is unimodular over `R` (hermitian and in GL(R)), then so is the Gram
matrix `Bᴴ J B`. -/
lemma isUnimodular [IsStarStable R] (h : IsQuotientBasis R J ι B q) (hJ : IsUnimodular R J) :
    IsUnimodular R (Bᴴ * J * B) := by
  -- The columns of `D = J⁻¹ qᴴ` are integral, orthogonal to `I` and dual to those of `B`.
  have hJ_int : IsIntMatrix R J := hJ.isIntMatrix
  obtain ⟨h_herm, U, hU, rfl⟩ := hJ
  let D := U⁻¹.val * qᴴ
  have h_products {τ : Type} (s : Matrix π τ A) : sᴴ * U.val * D = (q * s)ᴴ := by
    simp [D, Matrix.mul_assoc]
  have h_dual : ιᴴ * U.val * D = 0 := by rw [h_products, h.coord_mul_isotropic, conjTranspose_zero]
  have h_inv : Bᴴ * U.val * B * (q * D) = 1 := by
    rw [h.mul_basis_mul_coord (orthogonal_symm h_herm h.basis_orthogonal) h_dual, h_products,
      h.coord_mul_basis, conjTranspose_one]
  refine ⟨by simp [h_herm, Matrix.mul_assoc], isPrimitiveMatrix_iff.1 ⟨?_, q * D, ?_, ?_⟩⟩
  · exact (h.isIntMatrix_basis.conjTranspose.mul hJ_int).mul h.isIntMatrix_basis
  · exact h.isIntMatrix_coord.mul
      (IsIntMatrix.mul (mem_intGL.1 hU).2 h.isIntMatrix_coord.conjTranspose)
  · exact mul_eq_one_comm.1 h_inv

end IsQuotientBasis

/-- Let `R` be an adelic ring and `Λ = R ^ π` unimodular for `J`. Let the columns of `ι₀` span an
isotropic space `I`, and let those of `(ι₀ | y)` be a basis of `I^⊥`: they have a left inverse, are
orthogonal to `I` and are as many as the rank of `I^⊥`. Then for some invertible `a` the columns of
`ι₀ a` lie in `Λ`, and the quotient `(Λ ∩ I^⊥)/(Λ ∩ I)` has a basis `B` with coordinates `q`. -/
lemma exists_isQuotientBasis [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
    [PolishSpace A] [IsAdelic R] {J : Matrix π π A} (hJ : IsUnimodular R J) {ι₀ : Matrix π σ A}
    {y : Matrix π μ A} (h_inv : HasLeftInv (fromCols ι₀ y)) (h_orth : ι₀ᴴ * J * fromCols ι₀ y = 0)
    (h_card : card π = card (σ ⊕ μ) + card σ) :
    ∃ (a : GL σ A) (B : Matrix π μ A) (q : Matrix μ π A),
      IsIntMatrix R (ι₀ * a.val) ∧ IsQuotientBasis R J (ι₀ * a.val) B q := by
  -- A block triangular change of basis makes `(ι₀ | y)` a basis `(ι | B)` of `Λ ∩ I^⊥`.
  obtain ⟨a, e, z, h_int, l, hl_int, hl⟩ :=
    exists_isPrimitiveMatrix_mul_fromBlocks (R := R) _ h_inv
  have h_orth' : (ι₀ * a.val)ᴴ * J * (fromCols ι₀ y * fromBlocks a.val z 0 e.val) = 0 := by
    rw [conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc a.valᴴ, Matrix.mul_assoc a.valᴴ,
      h_orth, Matrix.mul_zero, Matrix.zero_mul]
  rw [fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero] at h_int hl h_orth'
  have hι_int : IsIntMatrix R (ι₀ * a.val) := fun i k ↦ h_int i (inl k)
  have hB_int : IsIntMatrix R (ι₀ * z + y * e.val) := fun i k ↦ h_int i (inr k)
  refine ⟨a, ι₀ * z + y * e.val, l.toRows₂, hι_int, ?_⟩
  generalize ι₀ * a.val = ι, ι₀ * z + y * e.val = B at hB_int hl h_orth' ⊢
  -- The row blocks of the left inverse `l` give the coordinates with respect to `ι` and `B`.
  have h_blocks : fromBlocks (l.toRows₁ * ι) (l.toRows₁ * B) (l.toRows₂ * ι) (l.toRows₂ * B) =
      fromBlocks 1 0 0 1 := by
    rw [← fromRows_mul_fromCols, fromRows_toRows, hl, fromBlocks_one]
  obtain ⟨h_left, -, h_zero, h_one⟩ := fromBlocks_inj.1 h_blocks
  rw [mul_fromCols, ← fromCols_zero, fromCols_ext_iff] at h_orth'
  obtain ⟨h_isotropic, hB_orth⟩ : ιᴴ * J * ι = 0 ∧ ιᴴ * J * B = 0 := h_orth'
  -- The columns of `(ι | B)` span all of `I^⊥`, as they are orthogonal to `ι` and left invertible.
  have h_decomp {ρ : Type} {x : Matrix π ρ A} (hx : ιᴴ * J * x = 0) :
      x = ι * (l.toRows₁ * x) + B * (l.toRows₂ * x) := by
    obtain ⟨h_herm, U, -, rfl⟩ := hJ
    have h_cols : (fromCols ι B)ᴴ * U.val * ι = 0 :=
      orthogonal_symm h_herm (by rw [mul_fromCols, h_isotropic, hB_orth, fromCols_zero])
    have h_col (k : ρ) : ιᴴ *ᵥ U.val *ᵥ x.col k = 0 := by
      rw [mulVec_mulVec]
      exact funext fun i : σ ↦ congrFun₂ hx i k
    have h_span (k : ρ) : ∃ w : σ ⊕ μ → A, fromCols ι B *ᵥ w = x.col k :=
      exists_mulVec_eq_of_orthogonal h_herm ⟨l, hl⟩ ⟨l.toRows₁, h_left⟩ h_cols h_card (h_col k)
    choose w hw using h_span
    have h_eq : fromCols ι B * (of w)ᵀ = x := ext_col hw
    -- As `l` is a left inverse of `(ι | B)`, the coefficients `w` of `x` are given by `l * x`.
    have h_coeff : (of w)ᵀ = l * x := by rw [← h_eq, ← Matrix.mul_assoc, hl, Matrix.one_mul]
    calc x = fromCols ι B * (l * x) := by rw [← h_coeff, h_eq]
      _ = ι * (l.toRows₁ * x) + B * (l.toRows₂ * x) := by
        rw [← fromCols_mul_fromRows, ← fromRows_mul, fromRows_toRows]
  exact {
    isIntMatrix_basis := hB_int
    isIntMatrix_coord := fun i k ↦ hl_int (inr i) k
    coord_mul_isotropic := h_zero
    coord_mul_basis := h_one
    basis_orthogonal := hB_orth
    exists_eq_add := ⟨l.toRows₁, fun i k ↦ hl_int (inl i) k, h_decomp⟩ }

end Quotient

/-!
## Covolumes of scaled lattices and boxes of fundamental domains

Fundamental domains are strict: every point has exactly one translate in `F`.
-/

section FundamentalDomains

open NumberField MeasureTheory Matrix Finset Variety ZSpan MeasurableEquiv mixedEmbedding

variable {E n : Type _} [Field E] [CMType E] [Fintype n]

/-- Let `t` be a unit of `(E ⊗ ℝ)ⁿ` and `F` a strict fundamental domain of the lattice of the
`t * y`, `y ∈ Eⁿ` whose class `frameTorsionClass m⁻¹ y`, the class of `m y` in `(𝔸_f/Ô)ⁿ`
(`AdelicTorsion E n`), is trivial. Then for all `z` and every class `w` exactly one `y ∈ Eⁿ` of
class `w` has `t * y + z ∈ F`. -/
lemma existsUnique_mul_toRealVectors_add_mem [DecidableEq n] {t : RealVectors E n} (ht : IsUnit t)
    {m : GL n (𝔸f E)} {F : Set (RealVectors E n)}
    (h_fund : ∀ x : RealVectors E n,
      ∃! l : classLattice m⁻¹ ⊥ (ContinuousLinearEquiv.smulLeft ht.unit), l.val + x ∈ F)
    (z : RealVectors E n) (w : AdelicTorsion E n) :
    ∃! y : n → E, t * toRealVectors y + z ∈ F ∧ frameTorsionClass m⁻¹ y = w := by
  have h_mem {v : RealVectors E n} :
      v ∈ classLattice m⁻¹ ⊥ (ContinuousLinearEquiv.smulLeft ht.unit) ↔
        ∃ y : n → E, frameTorsionClass m⁻¹ y = 0 ∧ t * toRealVectors y = v := by
    simp [mem_classLattice]
  -- Write `w` as the class of `y₀`; then `y ↦ t * (y - y₀)` maps the solutions to the lattice.
  obtain ⟨y₀, rfl⟩ := frameTorsionClass_surjective (g := m⁻¹) w
  obtain ⟨⟨l, hl⟩, hlF, hl_eq⟩ := h_fund (t * toRealVectors y₀ + z)
  obtain ⟨y, hy, rfl⟩ := h_mem.1 hl
  refine ⟨y + y₀, ⟨by simpa [mul_add, add_assoc] using hlF, by simp [hy]⟩, ?_⟩
  rintro y' ⟨hy'F, hy'⟩
  have hy'_shift : t * toRealVectors (y' - y₀) + (t * toRealVectors y₀ + z) ∈ F := by
    simpa [mul_sub, ← add_assoc] using hy'F
  have h_eq : t * toRealVectors (y' - y₀) = t * toRealVectors y :=
    congrArg Subtype.val (hl_eq ⟨_, h_mem.2 ⟨y' - y₀, by simp [hy'], rfl⟩⟩ hy'_shift)
  exact sub_eq_iff_eq_add.1 (toRealVectors_injective (ht.mul_left_cancel h_eq))

/-- Let `t ∈ (E ⊗ ℝ)ⁿ` (here `RealVectors E n`) and the finite adelic matrix `m` be invertible. The
vectors `(t j v * Φ v (x j))`, for `x ∈ Eⁿ` with `m x` integral (`Φ` is the CM type), form the group
`classLattice m⁻¹ ⊥ _` (`⊥`: the class of `m x` in `(𝔸_f/Ô)ⁿ` is to be zero; the last argument is
multiplication by `t`). It has a measurable strict fundamental domain `F` of volume
`(∏ w, ‖∏ j, t j w‖ ^ 2) / genIndex (det m) / volÔ E ^ n`, where `genIndex` is the inverse Haar
modulus and `volÔ E = 2 ^ r₂ / √|disc E|`. -/
lemma exists_fundamental_domain_classLattice [DecidableEq n] (t : RealVectors E n) (ht : IsUnit t)
    (m : GL n (𝔸f E)) :
    ∃ F : Set (RealVectors E n),
      MeasurableSet F ∧
      -- (a) the volume of `F`
      volume.real F =
        (∏ w : InfinitePlace E, ‖∏ j : n, t j w‖ ^ 2) / genIndex m.val.det /
          volÔ E ^ Fintype.card n ∧
      -- (b) `F` is a fundamental domain of the lattice
      ∀ x : RealVectors E n, ∃! l : classLattice m⁻¹ ⊥ (ContinuousLinearEquiv.smulLeft ht.unit),
        l.val + x ∈ F := by
  -- Let `F` be the box of a `ℤ`-basis of the lattice and `a` the adelic matrix `(diag t, m)`. For
  -- each adelic `x` exactly one `ξ ∈ Eⁿ` has `a (ξ + x) ∈ F × Ôⁿ`, so unfolding over `𝔸ⁿ / Eⁿ`
  -- gives `vol (F × Ôⁿ) = |det a|`.
  let L : Submodule ℤ (RealVectors E n) := classLattice m⁻¹ ⊥ (.smulLeft ht.unit)
  obtain ⟨F, h_meas, h_fund⟩ : ∃ F, MeasurableSet F ∧ ∀ x, ∃! l : L, l.1 + x ∈ F := by
    let b : Module.Basis _ ℝ (RealVectors E n) := (Module.finBasis ℤ L).ofZLatticeBasis ℝ
    have h_span := exist_unique_vadd_mem_fundamentalDomain b
    rw [Module.Basis.ofZLatticeBasis_span] at h_span
    exact ⟨fundamentalDomain b, fundamentalDomain_measurableSet b, h_span⟩
  refine ⟨F, h_meas, ?_, h_fund⟩
  let a : GL n (𝔸 E) :=
    mkAdelicGL (fun w ↦ (diagGL fun j ↦ (ht.apply j).unit).map (Pi.evalRingHom _ w), m)
  -- `S = F × Ôⁿ`, as a set of adelic vectors
  let S : Set (n → 𝔸 E) :=
    arrowProdEquivProdArrow _ _ n ⁻¹' F ×ˢ Set.univ.pi fun _ ↦ (Ô E : Set (𝔸f E))
  have hS : MeasurableSet S :=
    (arrowProdEquivProdArrow ..).measurable (h_meas.prod (.univ_pi fun _ ↦ isOpen_Ô.measurableSet))
  have h_count (x : n → 𝔸 E) : {ξ : n → E | a.val *ᵥ (toAdele ∘ ξ + x) ∈ S}.encard = 1 := by
    -- Translate by the infinite part of `a x`; the class to meet is minus that of its finite part.
    let z : RealVectors E n := fun i ↦ t i * (x i).1
    let w : AdelicTorsion E n := torsionClass (-fun i : n ↦ ∑ j : n, m i j * (x j).2)
    let q : (n → E) → (n → 𝔸 E) := fun ξ ↦ a.val *ᵥ (toAdele ∘ ξ + x)
    -- the infinite part of `a (ξ + x)`
    have h_inf (ξ : n → E) : (fun i : n ↦ (q ξ i).1) = t * toRealVectors ξ + z := by
      ext
      simp [q, a, z, diagonal, mulVec_eq_sum, mul_add, sum_add_distrib, ← prod_mk_sum]
    -- the finite part of `a (ξ + x)` is integral iff `ξ` has the class `w`
    have h_fin (ξ : n → E) : (∀ i : n, (q ξ i).2 ∈ Ô E) ↔ frameTorsionClass m⁻¹ ξ = w := by
      rw [show frameTorsionClass m⁻¹ ξ = torsionClass (m.val *ᵥ (algebraMap E (𝔸f E) ∘ ξ)) from rfl,
        torsionClass_eq_iff]
      simp [q, a, mulVec_eq_sum, mul_add, mul_comm, Algebra.smul_def, sum_add_distrib,
        ← prod_mk_sum]
    have h_mem (ξ : n → E) :
        q ξ ∈ S ↔ t * toRealVectors ξ + z ∈ F ∧ frameTorsionClass m⁻¹ ξ = w := by
      simp [← h_inf, ← h_fin, S, arrowProdEquivProdArrow]
    rw [Set.encard_eq_one, Set.singleton_iff_unique_mem]
    simpa [q, h_mem] using existsUnique_mul_toRealVectors_add_mem ht h_fund z w
  -- `lintegral_encard_rat_points`: `|det a⁻¹| * vol S` is the mean of this count over `𝔸ⁿ / Eⁿ`
  have h_vol : ENNReal.ofReal (ideleAbs a⁻¹.det) * volume S = 1 := by
    rw [lintegral_encard_rat_points a⁻¹ hS]
    simp [h_count]
  -- `vol S = vol F * volÔ ^ n`
  have h_real : volume.real F * volÔ E ^ Fintype.card n = ideleAbs a.det := by
    have h_volS : (volume S).toReal = volume.real F * volÔ E ^ Fintype.card n := by
      rw [(volume_measurePreserving_arrowProdEquivProdArrow ..).measure_preimage_equiv]
      simp [volume_pi_pi, Measure.volume_eq_prod, Measure.real]
    have h_inv : (ideleAbs a.det)⁻¹ * (volume S).toReal = 1 := by
      simpa using congrArg ENNReal.toReal h_vol
    simpa [h_volS] using (inv_eq_of_mul_eq_one_right h_inv).symm
  rw [← GeneralLinearGroup.val_det_apply, genIndex_eq_inv_finIdeleAbs m.det]
  simpa [a, field, Core.ideleAbs_det_mkAdelicGL] using h_real

/-- Let `c` be injective coordinates on a group `G`, with values in additive groups `V i` and
graded by `deg`, and let `F i` be strict fundamental domains of submonoids `L i` of `V i`. Let `Γ`
be a subgroup that acts on the coordinates from the right in a triangular way: every point of `L i`
is coordinate `i` of some `γ ∈ Γ` whose other coordinates of degree `≤ deg i` are those of `1`
(`h_onto`); if the coordinates of `γ ∈ Γ` of degree `< deg i` are those of `1`, then `c γ i ∈ L i`
(`h_mem`) and right multiplication by `γ` adds `c γ i` on the left to coordinate `i` (`h_transl`).
Then for every `x` exactly one `γ ∈ Γ` has `c (x γ)` in the box over the `F i`. -/
lemma Filling.existsUnique_mul_mem_box {G ι : Type*} [Group G] [Fintype ι] {V : ι → Type*}
    [∀ i : ι, AddGroup (V i)] (deg : ι → ℕ) (c : G → ∀ i : ι, V i) (h_inj : c.Injective)
    (Γ : Subgroup G) (L : ∀ i : ι, AddSubmonoid (V i)) (F : ∀ i : ι, Set (V i))
    (hF : ∀ (i : ι) (v : V i), ∃! l : L i, l.val + v ∈ F i)
    (h_onto : ∀ i : ι, ∀ l ∈ L i, ∃ γ : Γ, c γ i = l ∧ ∀ j ≠ i, deg j ≤ deg i → c γ j = c 1 j)
    (h_mem : ∀ (γ : Γ) (i : ι), (∀ j : ι, deg j < deg i → c γ j = c 1 j) → c γ i ∈ L i)
    (h_transl : ∀ (γ : Γ) (i : ι),
      (∀ j : ι, deg j < deg i → c γ j = c 1 j) → ∀ x : G, c (x * γ) i = c γ i + c x i)
    (x : G) :
    ∃! γ : Γ, c (x * γ) ∈ Set.univ.pi F := by
  classical
  have h_one (i : ι) : c 1 i = 0 := by simpa using h_transl 1 i (fun _ _ ↦ rfl) 1
  -- Existence: move the coordinates into their domains in the order of increasing degree.
  obtain ⟨γ, hγ⟩ : ∃ γ : Γ, ∀ i ∈ univ, c (x * γ) i ∈ F i := by
    refine univ.induction_on_max_value deg (by simp) fun a s ha h_max ⟨γ, hγ⟩ ↦ ?_
    obtain ⟨l, hl⟩ := (hF a (c (x * γ) a)).exists
    obtain ⟨δ, hδ, hδ_zero⟩ := h_onto a l l.property
    refine ⟨γ * δ, fun i hi ↦ ?_⟩
    -- `δ` shifts coordinate `a` by `l` and leaves the coordinates treated before unchanged
    have h_deg : deg i ≤ deg a := by grind
    have h_low (j : ι) (hj : deg j < deg i) : c δ j = c 1 j :=
      hδ_zero j (ne_of_apply_ne deg (hj.trans_le h_deg).ne) (hj.trans_le h_deg).le
    have h_shift : c (x * γ * δ) i = c δ i + c (x * γ) i := h_transl δ i h_low (x * γ)
    rw [Subgroup.coe_mul, ← mul_assoc, h_shift]
    obtain rfl | hi_s := mem_insert.1 hi
    · rwa [hδ]
    · rw [hδ_zero i (ne_of_mem_of_not_mem hi_s ha) (h_max i hi_s), h_one, zero_add]
      exact hγ i hi_s
  refine ⟨γ, by simpa using hγ, fun γ' hγ' ↦ ?_⟩
  -- Uniqueness: if `x * γ` and `x * γ * δ` are both in the box, the coordinates of `δ` vanish, by
  -- induction on the degree.
  obtain ⟨δ, rfl⟩ := mul_left_surjective γ γ'
  have h_coord (i : ι) : c δ i = c 1 i := by
    induction i using (measure deg).wf.induction with | _ i ih => ?_
    have h_box : c δ i + c (x * γ) i ∈ F i := by
      simpa [← h_transl δ i ih (x * γ), mul_assoc] using hγ' i
    have h_zero : (⟨c δ i, h_mem δ i ih⟩ : L i) = 0 :=
      (hF i (c (x * γ) i)).unique h_box (by simpa using hγ i)
    simpa [h_one] using h_zero
  simpa using h_inj (funext h_coord)

/-- The group of the vectors `(t v * Im Φ_v(s))_v`, for integers `s` of the CM field `E` with
`star s = -s`; here `Φ` is the CM type. -/
noncomputable def Filling.imSkewLattice (t : InfinitePlace E → ℝ) :
    AddSubgroup (InfinitePlace E → ℝ) :=
  (skewAdjoint (𝓞 E)).map
    (AddMonoidHom.mk' (fun (s : 𝓞 E) (v : InfinitePlace E) ↦ t v * (Φ v s.val).im)
      (by simp [funext_iff, mul_add]))

/-- A vector lies in `imSkewLattice t` iff it is `(t v * Im Φ_v(s))_v` for an integer `s` of `E`
with `star s = -s`. -/
lemma Filling.mem_imSkewLattice {t l : InfinitePlace E → ℝ} :
    l ∈ imSkewLattice t ↔
      ∃ s : 𝓞 E, star s = -s ∧ (fun v : InfinitePlace E ↦ t v * (Φ v s.val).im) = l :=
  Iff.rfl

/-- If `ι² = -1`, `star ι = -ι` and all `Φ_v(ι)` are imaginary, the group `imSkewLattice t`
consists of the vectors `(t v * Im Φ_v(ι) * Re Φ_v(a))_v`, `a` an integer of the maximal real
subfield. -/
lemma Filling.mem_imSkewLattice_iff_exists_real {t : InfinitePlace E → ℝ} {ι : 𝓞 E}
    (hι_sq : ι * ι = -1) (hι_star : star ι = -ι) (h_re : ∀ v : InfinitePlace E, (Φ v ι.val).re = 0)
    (l : InfinitePlace E → ℝ) :
    l ∈ imSkewLattice t ↔ ∃ a : 𝓞 (maximalRealSubfield E),
      (fun v : InfinitePlace E ↦ t v * ((Φ v ι.val).im * (Φ v a.val.val).re)) = l := by
  have hι_unit : IsUnit ι := isUnit_of_mul_isUnit_left (y := ι) (by simp [hι_sq])
  -- substitute `s = ι * a`; then `star s = -s` says that `a` is fixed by complex conjugation
  have h_skew (a : 𝓞 E) : star (ι * a) = -(ι * a) ↔ star a = a := by
    simp [hι_star, hι_unit.ne_zero]
  have h_val (a : 𝓞 E) : (fun v : InfinitePlace E ↦ t v * (Φ v (ι * a).val).im) =
      fun v ↦ t v * ((Φ v ι.val).im * (Φ v a.val).re) := by simp [h_re]
  -- the integers `a` of `E` with `star a = a` are the integers of the real subfield
  have h_real (a : 𝓞 E) :
      star a = a ↔ ∃ a₀ : 𝓞 (maximalRealSubfield E), algebraMap _ (𝓞 E) a₀ = a :=
    IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := E) a
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨a, rfl⟩ : ι ∣ s := hι_unit.dvd
    obtain ⟨a₀, rfl⟩ := (h_real a).1 ((h_skew a).1 hs)
    exact ⟨a₀, (h_val (algebraMap _ (𝓞 E) a₀)).symm⟩
  · rintro ⟨a₀, rfl⟩
    exact ⟨_, (h_skew _).2 ((h_real _).2 ⟨a₀, rfl⟩), h_val (algebraMap _ (𝓞 E) a₀)⟩

/-- Let the CM field `E` contain a primitive 5040th root of unity (`New.HasPrimitiveRoot5040`) and
let all `t v` be nonzero. Then the group `imSkewLattice t` of rescaled imaginary parts of the
integers `s` of `E` with `star s = -s` has a measurable strict fundamental domain, whose volume is
`∏ |t v| * √√|disc E|`. -/
lemma Filling.exists_fundamental_domain_im_skew [HasPrimitiveRoot5040 E] (t : InfinitePlace E → ℝ)
    (ht : ∀ v : InfinitePlace E, t v ≠ 0) :
    ∃ F : Set (InfinitePlace E → ℝ),
      MeasurableSet F ∧
      -- (a) the volume of `F`
      volume.real F = (∏ v : InfinitePlace E, |t v|) * √√|NumberField.discr E| ∧
      -- (b) `F` is a fundamental domain of the lattice
      ∀ x : InfinitePlace E → ℝ, ∃! l : imSkewLattice t, l.val + x ∈ F := by
  classical
  -- With `ι² = -1`, `star ι = -ι`, the integers `s` with `star s = -s` are the `ι * a` with `a`
  -- an integer of the real subfield, and `Im Φ_v(ι a) = ± Φ_v(a)`. So the lattice is the
  -- Minkowski lattice of that field, rescaled by the diagonal entries `t v * Im Φ_v(ι) = ± t v`.
  obtain ⟨ι, hι_sq, hι_star⟩ := HasPrimitiveRoot5040.exists_mul_self_eq_neg_one (E := E)
  -- `f` identifies the Minkowski space of `E⁺` with `InfinitePlace E → ℝ`, preserving the measure,
  -- and sends `a ∈ E⁺` to `v ↦ Re Φ_v(a)`
  obtain ⟨f, hf_meas, hf⟩ := exists_mixedEquiv_maximalRealSubfield (E := E)
  have hΦ {v : InfinitePlace E} : (Φ v ι.val).re = 0 ∧ |(Φ v ι).im| = 1 := by
    have h_sq : Φ v ι * Φ v ι = .I * .I := by simp [← map_mul, hι_sq]
    rcases mul_self_eq_mul_self_iff.1 h_sq with h | h <;> simp [h]
  have h_det : (diagonal fun v ↦ t v * (Φ v ι).im).toLin'.det ≠ 0 := by
    simp [prod_eq_zero_iff, ht, ← abs_pos, hΦ]
  let scale := (diagonal fun v ↦ t v * (Φ v ι).im).toLin'.equivOfDetNeZero h_det
  let b : Module.Basis _ ℝ (InfinitePlace E → ℝ) :=
    ((latticeBasis (maximalRealSubfield E)).map f).map scale
  refine ⟨fundamentalDomain b, fundamentalDomain_measurableSet b, ?_, fun x ↦ ?_⟩
  · -- the volume scales by `|det|`, `f` preserves it, the real subfield has no complex place,
    -- and `|disc E| = (disc E⁺)²`
    let F₀ := fundamentalDomain (latticeBasis (maximalRealSubfield E))
    have h_image : fundamentalDomain b = (scale : (InfinitePlace E → ℝ) →ₗ[ℝ] _) '' (f '' F₀) := by
      rw [LinearEquiv.coe_coe, map_fundamentalDomain, map_fundamentalDomain]
    have h_abs_det : |LinearMap.det (scale : (InfinitePlace E → ℝ) →ₗ[ℝ] _)| =
        ∏ v : InfinitePlace E, |t v| := by
      simp [scale, abs_prod, hΦ]
    have h_pres : volume (f '' F₀) = volume F₀ := by
      rw [map_fundamentalDomain,
        ← hf_meas.measure_preimage (fundamentalDomain_measurableSet _).nullMeasurableSet,
        ← map_fundamentalDomain, f.injective.preimage_image]
    have h_vol : volume.real (fundamentalDomain b) =
        (∏ v : InfinitePlace E, |t v|) * volume.real F₀ := by
      rw [h_image, Measure.real, volume.addHaar_image_linearMap, h_pres, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (abs_nonneg _), h_abs_det, Measure.real]
    rw [h_vol, Measure.real, volume_fundamentalDomain_latticeBasis]
    simp [norm, ← Int.cast_abs, abs_discr_eq_discr_maximalRealSubfield_sq, Real.sqrt_sq_eq_abs]
  · have h_lattice (l : InfinitePlace E → ℝ) :
        l ∈ Submodule.span ℤ (Set.range b) ↔ l ∈ imSkewLattice t := by
      simp [mem_imSkewLattice_iff_exists_real hι_sq hι_star (fun v ↦ hΦ.1), b, scale, ← ZSpan.map,
        mem_span_latticeBasis, mul_assoc, hf, mulVec_diagonal, funext_iff (g := l),
        exists_exists_eq_and]
    exact (Equiv.subtypeEquivRight h_lattice).existsUnique_congr_right.1
      (exist_unique_vadd_mem_fundamentalDomain b x)

end FundamentalDomains

/-! ## Lattices with an integral Gram matrix -/

section IntegralLattice

open MeasureTheory Matrix Module Fintype ZSpan

/-- The fundamental domain of the product basis `Pi.basis b` is the product of the fundamental
domains; if these have volume `1`, so has the product. -/
lemma volume_fundamentalDomain_pi_basis {ι : Type*} [Fintype ι] {σ V : ι → Type*}
    [∀ i : ι, NormedAddCommGroup (V i)] [∀ i : ι, NormedSpace ℝ (V i)]
    [∀ i : ι, MeasureSpace (V i)] [∀ i : ι, SigmaFinite (volume : Measure (V i))]
    (b : ∀ i : ι, Basis (σ i) ℝ (V i)) (hb : ∀ i : ι, volume (fundamentalDomain (b i)) = 1) :
    volume (fundamentalDomain (Pi.basis b)) = 1 := by
  have h_pi : fundamentalDomain (Pi.basis b) = Set.univ.pi fun i ↦ fundamentalDomain (b i) :=
    Set.ext fun x ↦ by simp [mem_fundamentalDomain, Sigma.forall]
  simp [h_pi, volume_pi_pi, hb]

/-- The unit square in `ℂ` has area `1`. -/
lemma volume_fundamentalDomain_basisOneI : volume (fundamentalDomain Complex.basisOneI) = 1 := by
  rw [measure_congr (fundamentalDomain_ae_parallelepiped Complex.basisOneI volume),
    ← Complex.toBasis_orthonormalBasisOneI, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.volume_parallelepiped]

/-- Let `L` be a lattice in a real vector space with a basis `e` whose fundamental domain has
measure `1`. If the euclidean product in the coordinates of `e` is integral on `L`, then `L` has a
fundamental domain of finite measure at least `1`. -/
lemma exists_isAddFundamentalDomain_of_integral {V σ : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] [Fintype σ] (e : Basis σ ℝ V) (he : μ (fundamentalDomain e) = 1)
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (h_int : ∀ x ∈ L, ∀ y ∈ L, ∃ n : ℤ, ∑ s : σ, e.repr x s * e.repr y s = n) :
    ∃ D : Set V, MeasurableSet D ∧ IsAddFundamentalDomain L D μ ∧ 1 ≤ μ D ∧ μ D ≠ ⊤ := by
  -- The measure is `|det M|` for the matrix `M` of a basis `b` of `L`, and `Mᵀ M` is an integer
  -- matrix with nonzero determinant.
  classical
  have := ZLattice.module_finite ℝ L
  have := ZLattice.module_free ℝ L
  let b : Basis σ ℤ L := (Free.chooseBasis ℤ L).reindex <| equivOfCardEq <| by
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L, finrank_eq_card_basis e]
  let M : Matrix σ σ ℝ := e.toMatrix (b.ofZLatticeBasis ℝ L)
  have h_det : M.det ≠ 0 := (e.isUnit_det (b.ofZLatticeBasis ℝ L)).ne_zero
  have h_entry (s t : σ) : ∃ n : ℤ, (Mᵀ * M) s t = n := by
    simpa [M, mul_apply, Basis.toMatrix_apply] using h_int _ (b s).2 _ (b t).2
  choose N hN using h_entry
  have h_map : (Int.castRingHom ℝ).mapMatrix (of N) = Mᵀ * M := ext fun s t ↦ (hN s t).symm
  have h_cast : ((of N).det : ℝ) = M.det ^ 2 := by
    rw [← eq_intCast (Int.castRingHom ℝ), RingHom.map_det, h_map, det_mul, det_transpose, sq]
  have h_one_le : (1 : ℝ) ≤ M.det ^ 2 := by
    have h_pos : (0 : ℝ) < (of N).det := by simpa [h_cast, sq_pos_iff] using h_det
    rw [← h_cast]
    exact_mod_cast h_pos
  refine ⟨fundamentalDomain (b.ofZLatticeBasis ℝ L), fundamentalDomain_measurableSet _,
    ZLattice.isAddFundamentalDomain b μ, ?_, (fundamentalDomain_isBounded _).measure_lt_top.ne⟩
  rw [measure_fundamentalDomain _ μ e, he, mul_one, Basis.det_apply]
  exact ENNReal.one_le_ofReal.2 ((one_le_sq_iff_one_le_abs _).1 h_one_le)

end IntegralLattice

end New
