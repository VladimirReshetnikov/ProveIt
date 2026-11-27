import Lib.Adelic.Adeles.LocalFactors
import Lib.General.NumberTheory.LatticeCovolumes
import New.Spanning.Unfolding.Setup

/-!
# Discriminants of sublattices, Siegel's lemma and a height zeta function of subspaces

Let `E` be a CM field containing a primitive 5040th root of unity, `𝔸f E` its finite adeles and
`Ô E` their integers. A lattice is given by an adelic basis: a matrix over `E`, embedded by
`New.Filling.finAdeleMatrix`, times a matrix over the finite adeles. Subspaces `T` of `E^κ` have
heights relative to the lattice `E^κ ∩ u Ô^κ` of a finite adelic unitary matrix `u : New.Gf E κ`.
Here `d T = New.Filling.sublatticeDiscriminant u.val.val_inv T` is the discriminant of `T ∩ u Ô^κ`;
the first argument proves `u u⁻¹ = 1`.

## Main definitions and results

* `New.Filling.sublatticeBasis`, `New.Filling.sublatticeDiscriminant`: a basis and the discriminant
  of the points of a subspace `V` that `H` makes integral.
* `New.Filling.siegel_lemma`: a subspace of codimension `s` is cut out by `s` short vectors.
* `New.Filling.tsum_sublatticeDiscriminant_inv_le`: an explicit bound for `∑ (d T)⁻¹ ^ (#κ + 1)`
  over the subspaces `T` of `E^κ` of codimension `s`. It follows from `New.Filling.siegel_lemma`:
  each `T` is charged to its tuple of vectors, and a packing bound sums over the lattice.

Notions from other files:
* `New.CMType E`: `E` is a CM number field (it extends `NumberField E` and `IsCMField E`) with a
  chosen complex embedding `Φ v` inducing each infinite place `v`.
* `New.IsPrimitiveMatrix O X`: `X` has entries in `O` and a left inverse with entries in `O`.
* `New.genIndex a`: the inverse of the factor by which a unit `a` scales Haar measure, `0` for a
  non-unit.

## Relation to the literature

Known result: Siegel's lemma over number fields (Bombieri–Vaaler). It is stated for lattices in the
genus of the standard hermitian lattice over a stably unramified CM field
(`New.HasPrimitiveRoot5040`: `E` contains a primitive `5040`-th root of unity). A subspace is cut
out by lattice vectors; a power of the product of their norms is bounded by an explicit constant,
depending on the degree, the codimension and the root discriminant, times its discriminant. Source:
E. Bombieri, J. Vaaler, On Siegel's lemma, Invent. Math. 73 (1983).
-/

noncomputable section

namespace New.Filling

/-! ## Adelic matrices, bases along a kernel, and discriminants of subspaces -/

section GramLiouville

open NumberField Matrix Module

variable {E P σ τ m n k : Type} [Field E] [NumberField E] [IsCMField E] [Fintype P] [Fintype σ]
  [DecidableEq σ] [Field k]

/-- For a matrix over `E`, the matrix over the finite adeles of `E` obtained by embedding each
entry. -/
abbrev finAdeleMatrix (M : Matrix m n E) : Matrix m n (𝔸f E) := M.map ((↑) : E → 𝔸f E)

lemma finAdeleMatrix_conjTranspose (M : Matrix m n E) :
    finAdeleMatrix Mᴴ = (finAdeleMatrix M)ᴴ := by aesop

/-- A complex embedding of a CM field commutes with conjugation, hence with the conjugate
transpose of matrices. -/
lemma map_conjTranspose (M : Matrix m n E) (φ : E →+* ℂ) : Mᴴ.map φ = (M.map φ)ᴴ := by aesop

omit [IsCMField E] in
@[simp]
lemma finAdeleMatrix_smul (M : Matrix m n E) (a : E) :
    finAdeleMatrix (a • M) = (a : 𝔸f E) • finAdeleMatrix M := by aesop

/-! ### Splitting along a kernel -/

omit [Fintype σ] [DecidableEq σ] in
/-- If the column span of `y` lies in the kernel of `A`, then `A * y = 0`. -/
lemma mul_eq_zero_of_colSpan_le_ker [Fintype τ] {y : Matrix P τ k} {A : Matrix σ P k}
    (h_le : colSpan y ≤ A.mulVecLin.ker) : A * y = 0 := by
  simpa [IsConcreteLE.le_iff, ext_iff_mulVec] using h_le

/-- The columns of `y` lie in `L` and in the kernel of `A`, and together with the columns of `x`
they form a basis of `L`. `colSpan` is the span of the columns, and `HasLeftInv` says that there is
a left inverse. -/
structure IsKernelExtension (A : Matrix σ P k) (x : Matrix P σ k) (L : Submodule k (P → k)) {s : ℕ}
    (y : Matrix P (Fin s) k) : Prop where
  /-- The number of columns of `y` is the dimension of `L ⊓ ker A`. -/
  finrank_eq : finrank k ↥(L ⊓ A.mulVecLin.ker) = s
  /-- The columns of `x` and `y` together are independent. -/
  hasLeftInv : HasLeftInv (fromCols x y)
  /-- The columns of `x` and `y` together span `L`. -/
  colSpan_fromCols : colSpan (fromCols x y) = L
  /-- The columns of `y` lie in `L`. -/
  colSpan_le : colSpan y ≤ L
  /-- The columns of `y` lie in the kernel of `A`. -/
  mul_eq_zero : A * y = 0
  /-- Only the trivial combination of the columns of `y` lies in the span of those of `x`. -/
  eq_zero_of_mulVec_mem : ∀ t : Fin s → k, y *ᵥ t ∈ colSpan x → t = 0

/-- If `A * x` is invertible and a subspace `L` contains the columns of `x`, then these columns
extend to a basis of `L` by the columns of a matrix `y`, a basis of `L ⊓ ker A`. -/
lemma exists_isKernelExtension {A : Matrix σ P k} {x : Matrix P σ k} (h_det : (A * x).det ≠ 0)
    {L : Submodule k (P → k)} (hL : colSpan x ≤ L) :
    ∃ᵉ (s : ℕ) (y : Matrix P (Fin s) k), IsKernelExtension A x L y := by
  classical
  -- Take for `y` a basis of `L ⊓ ker A`, with left inverse `l`. As `A * y = 0`, the matrix
  -- `C = (A * x)⁻¹ * A` reads off the `x`-coordinates of a combination of the columns of `x` and
  -- `y`, and `l - l * x * C` its `y`-coordinates.
  obtain ⟨y, ⟨l, hl⟩, hy⟩ := exists_hasLeftInv_colSpan_eq (L ⊓ A.mulVecLin.ker)
  have hyL : colSpan y ≤ L := hy.le.trans inf_le_left
  have hAy : A * y = 0 := mul_eq_zero_of_colSpan_le_ker (hy.le.trans inf_le_right)
  let C : Matrix σ P k := (A * x)⁻¹ * A
  have hCx : C * x = 1 := by simp [C, Matrix.mul_assoc, h_det]
  have hCy : C * y = 0 := by simp [C, Matrix.mul_assoc, hAy]
  have hDx : (l - l * x * C) * x = 0 := by simp [Matrix.sub_mul, Matrix.mul_assoc, hCx]
  have hDy : (l - l * x * C) * y = 1 := by simp [Matrix.sub_mul, Matrix.mul_assoc, hCy, hl]
  have h_left : fromRows C (l - l * x * C) * fromCols x y = 1 := by
    simp [*]
  refine ⟨_, y, {
    finrank_eq := rfl
    hasLeftInv := ⟨_, h_left⟩
    colSpan_fromCols := le_antisymm ?_ fun v hv ↦ ?_
    colSpan_le := hyL
    mul_eq_zero := hAy
    eq_zero_of_mulVec_mem := ?_ }⟩
  · rintro _ ⟨c, rfl⟩
    rw [mulVecLin_apply, fromCols_mulVec]
    exact add_mem (hL ⟨c ∘ Sum.inl, rfl⟩) (hyL ⟨c ∘ Sum.inr, rfl⟩)
  · have h_ker : A *ᵥ (v - x *ᵥ C *ᵥ v) = 0 := by simp [C, mulVec_sub, ← A.mul_assoc, h_det]
    obtain ⟨d, hd⟩ : v - x *ᵥ C *ᵥ v ∈ colSpan y :=
      hy.ge ⟨sub_mem hv (hL ⟨C *ᵥ v, rfl⟩), h_ker⟩
    have h_sum : x *ᵥ C *ᵥ v + y *ᵥ d = v := add_eq_of_eq_sub' hd
    exact ⟨C *ᵥ v ⊕ᵥ d, by rw [mulVecLin_apply, fromCols_mulVec_sumElim, h_sum]⟩
  · rintro t ⟨r, hr : x *ᵥ r = y *ᵥ t⟩
    calc t = (l - l * x * C) *ᵥ y *ᵥ t := by rw [mulVec_mulVec, hDy, one_mulVec]
      _ = 0 := by rw [← hr, mulVec_mulVec, hDx, zero_mulVec]

/-! ### The discriminant of the integral points of a subspace -/

variable [HasPrimitiveRoot5040 E] {L : Matrix σ P (𝔸f E)} {H : Matrix P σ (𝔸f E)}

/-- Let `E` be a CM field containing a primitive `5040`-th root of unity, and let the finite adelic
matrix `H` have a left inverse `L`. A subspace `V` of `E^σ` of dimension `s` has a basis `y` (the
columns of a left invertible matrix over `E`) and an `a ∈ GL_s(𝔸_f)` such that `H y a` is
primitive: it has entries in `Ô` and a left inverse with entries in `Ô`. -/
lemma exists_isPrimitiveMatrix_mul_finAdeleMatrix (hLH : L * H = 1) (V : Submodule E (σ → E))
    {s : ℕ} (hs : finrank E V = s) :
    ∃ᵉ (y : Matrix σ (Fin s) E) (a : GL (Fin s) (𝔸f E)),
      HasLeftInv y ∧ colSpan y = V ∧ IsPrimitiveMatrix (Ô E) (H * (finAdeleMatrix y * a.val)) := by
  classical
  subst hs
  obtain ⟨y, ⟨l, hl⟩, hy⟩ := exists_hasLeftInv_colSpan_eq V
  have h_left : finAdeleMatrix l * L * (H * finAdeleMatrix y) = 1 := by
    simp [← L.mul_assoc, hLH, hl, ← Matrix.map_mul, Matrix.mul_assoc]
  obtain ⟨a, -, ha⟩ := exists_preimageLattice_eq_colLattice ⟨finAdeleMatrix l * L, h_left⟩
  exact ⟨y, a, ⟨l, hl⟩, hy, by rwa [← H.mul_assoc]⟩

open scoped Classical in
/-- Let `H` have a left inverse `L`. This is a chosen matrix `m = y a`, with the columns of `y` a
basis of `V` over `E`, `a` invertible over `𝔸_f` and `H m` primitive over `Ô` (integral, with an
integral left inverse); it exists by `exists_isPrimitiveMatrix_mul_finAdeleMatrix`. -/
@[irreducible]
def sublatticeBasis (hLH : L * H = 1) (V : Submodule E (σ → E)) :
    {m : Matrix σ (Fin (finrank E V)) (𝔸f E) //
      IsPrimitiveMatrix (Ô E) (H * m) ∧
      ∃ᵉ (y : Matrix σ (Fin (finrank E V)) E) (a : GL (Fin (finrank E V)) (𝔸f E)),
        HasLeftInv y ∧ colSpan y = V ∧ m = finAdeleMatrix y * a.val} :=
  Nonempty.some <| by
    obtain ⟨y, a, hy_inv, hy_span, h_prim⟩ := exists_isPrimitiveMatrix_mul_finAdeleMatrix hLH V rfl
    exact ⟨finAdeleMatrix y * a.val, h_prim, y, a, hy_inv, hy_span, rfl⟩

lemma isPrimitiveMatrix_mul_sublatticeBasis (hLH : L * H = 1) (V : Submodule E (σ → E)) :
    IsPrimitiveMatrix (Ô E) (H * (sublatticeBasis hLH V).val) :=
  (sublatticeBasis hLH V).property.left

/-- The chosen basis is `y a`, with the columns of `y` a basis of `V` over `E` and `a` invertible
over `𝔸_f`. -/
lemma exists_sublatticeBasis_eq_finAdeleMatrix_mul (hLH : L * H = 1) (V : Submodule E (σ → E)) :
    ∃ᵉ (y : Matrix σ (Fin (finrank E V)) E) (a : GL (Fin (finrank E V)) (𝔸f E)),
      HasLeftInv y ∧ colSpan y = V ∧ (sublatticeBasis hLH V).val = finAdeleMatrix y * a.val :=
  (sublatticeBasis hLH V).property.right

/-- The discriminant `√[det mᴴ m]` of the lattice of adelic points of `V` that `H` makes integral,
for its basis `m = New.Filling.sublatticeBasis hLH V`. Here `[·]` is the generalised index
`New.genIndex`, which is `|N(z)|` at a nonzero `z ∈ E` for the norm `N` from `E` to `ℚ`. So for a
lattice with a basis `x` over `E` the discriminant is `√|N(det xᴴ x)|`. -/
def sublatticeDiscriminant (hLH : L * H = 1) (V : Submodule E (σ → E)) : ℝ :=
  √(genIndex ((sublatticeBasis hLH V).valᴴ * (sublatticeBasis hLH V).val).det)

/-- The index of `K ∩ M` in `M` (`0` if infinite), where `M` is the `Ô`-span of the columns of
`Y H m` and `m = New.Filling.sublatticeBasis hLH V` is the basis of the points of `V` that `H`
makes integral. -/
abbrev sublatticeIndex (hLH : L * H = 1) (V : Submodule E (σ → E)) (Y : Matrix τ P (𝔸f E))
    (K : Submodule (Ô E) (τ → 𝔸f E)) : ℕ :=
  submoduleIndex K (colLattice (Ô E) (Y * (H * (sublatticeBasis hLH V).val)))

/-- Let `E` be a CM field containing a primitive `5040`-th root of unity, and let the finite adelic
matrix `H` have a left inverse `L`. The columns of `m = sublatticeBasis hLH V` are an `Ô`-basis of
the adelic points of the subspace `V` that `H` makes integral. Let the matrix `x` over `E` have
`dim V` columns, all in `V`, with `det xᴴ x ≠ 0`. Then for every invertible finite adelic `w` there
is an invertible finite adelic `A` with `x w = m A`. -/
lemma exists_finAdeleMatrix_mul_eq_sublatticeBasis_mul (hLH : L * H = 1) {V : Submodule E (σ → E)}
    {x : Matrix σ (Fin (finrank E V)) E} (hx : colSpan x ≤ V) (hx_det : (xᴴ * x).det ≠ 0)
    (w : GL (Fin (finrank E V)) (𝔸f E)) :
    ∃ A : GL (Fin (finrank E V)) (𝔸f E),
      finAdeleMatrix x * w.val = (sublatticeBasis hLH V).val * A.val := by
  classical
  obtain ⟨y, a, -, hy, hm⟩ : ∃ᵉ (y : Matrix σ (Fin (finrank E V)) E)
      (a : GL (Fin (finrank E V)) (𝔸f E)),
      HasLeftInv y ∧ colSpan y = V ∧ (sublatticeBasis hLH V).val = finAdeleMatrix y * a.val :=
    exists_sublatticeBasis_eq_finAdeleMatrix_mul hLH V
  -- The columns of `x` lie in `V`, the span of those of `y`.
  obtain ⟨B, rfl⟩ : ∃ B : Matrix (Fin (finrank E V)) (Fin (finrank E V)) E, y * B = x :=
    exists_mul_eq_of_col_mem_range fun i ↦ hy.ge (hx ⟨Pi.single i 1, x.mulVec_single_one i⟩)
  have h_gram : (y * B)ᴴ * (y * B) = Bᴴ * (yᴴ * y) * B := by simp [Matrix.mul_assoc]
  have hB_det : B.det ≠ 0 := fun h_zero ↦ hx_det (by rw [h_gram, det_mul, h_zero, mul_zero])
  obtain ⟨b, hb⟩ : IsUnit (finAdeleMatrix B) :=
    ((isUnit_iff_isUnit_det B).2 hB_det.isUnit).map (algebraMap E (𝔸f E)).mapMatrix
  exact ⟨a⁻¹ * b * w, by simp [hm, hb, Matrix.mul_assoc]⟩

/-- Let `E` be a CM field containing a primitive `5040`-th root of unity, and let the finite adelic
matrix `H` have a left inverse `L`. Let `m = sublatticeBasis hLH V` be the chosen `Ô`-basis of the
adelic points of the subspace `V` that `H` makes integral. Let `δ = √[det mᴴ m]` be its discriminant
`sublatticeDiscriminant`. Here `[a]` is the generalised index `genIndex a`: for a unit `a`, the
inverse of the factor by which multiplication by `a` scales Haar measure, and `0` otherwise. If
`x w = m A` for a matrix `x` over `E` and square finite adelic matrices `w` and `A`, then
`δ² [det A]² = [det xᴴ x] [det w]²`. -/
lemma sublatticeDiscriminant_sq_mul_genIndex_sq (hLH : L * H = 1) {V : Submodule E (σ → E)}
    {x : Matrix σ (Fin (finrank E V)) E}
    {w A : Matrix (Fin (finrank E V)) (Fin (finrank E V)) (𝔸f E)}
    (hA : finAdeleMatrix x * w = (sublatticeBasis hLH V).val * A) :
    sublatticeDiscriminant hLH V ^ 2 * genIndex A.det ^ 2 =
      genIndex (finAdeleMatrix (xᴴ * x)).det * genIndex w.det ^ 2 := by
  set m : Matrix σ (Fin (finrank E V)) (𝔸f E) := (sublatticeBasis hLH V).val
  have h_gram : Aᴴ * (mᴴ * m) * A = wᴴ * finAdeleMatrix (xᴴ * x) * w := by
    have h_sq : (m * A)ᴴ * (m * A) = (finAdeleMatrix x * w)ᴴ * (finAdeleMatrix x * w) := by rw [hA]
    simpa [finAdeleMatrix_conjTranspose, Matrix.mul_assoc] using h_sq
  have h_nonneg : 0 ≤ genIndex (mᴴ * m).det := by
    by_cases h_unit : IsUnit (mᴴ * m).det
    · exact (genIndex_pos h_unit.unit).le
    · exact (genIndex.map_nonunit h_unit).ge
  rw [sublatticeDiscriminant, Real.sq_sqrt h_nonneg, ← genIndex_det_conj, ← genIndex_det_conj,
    h_gram]

/-- Let `E` be a CM field containing a primitive `5040`-th root of unity, and let the finite adelic
matrix `H` have a left inverse `L`. Suppose the subspace `V` contains the columns of a matrix `x`
over `E` with `dim V` columns and `det xᴴ x ≠ 0`. Then `sublatticeDiscriminant hLH V`, the
discriminant of the lattice of adelic points of `V` that `H` makes integral, is positive. -/
lemma sublatticeDiscriminant_pos (hLH : L * H = 1) {V : Submodule E (σ → E)}
    {x : Matrix σ (Fin (finrank E V)) E} (hx : colSpan x ≤ V) (hx_det : (xᴴ * x).det ≠ 0) :
    0 < sublatticeDiscriminant hLH V := by
  obtain ⟨A, hA⟩ := exists_finAdeleMatrix_mul_eq_sublatticeBasis_mul hLH hx hx_det 1
  have h_sq : sublatticeDiscriminant hLH V ^ 2 * genIndex A.val.det ^ 2 =
      |↑(Algebra.norm ℚ (xᴴ * x).det)| := by
    simp [sublatticeDiscriminant_sq_mul_genIndex_sq hLH hA, ← genIndex_algebraMap, RingHom.map_det]
  refine (Real.sqrt_nonneg _).lt_of_ne' fun h_zero : sublatticeDiscriminant hLH V = 0 ↦ hx_det ?_
  simpa [h_zero] using h_sq.symm

/-- Let `E` be a CM field containing a primitive `5040`-th root of unity, and let the finite adelic
matrix `H` have a left inverse `L`. Let `δ` be the discriminant `sublatticeDiscriminant` of the
lattice `Λ` of adelic points of `V` that `H` makes integral. Let `Y` be a finite adelic matrix and
`K` an `Ô`-module in the target of `Y`. The index `i = sublatticeIndex hLH V Y K` is that of
`K ∩ Y H Λ` in `Y H Λ`, the image of `Λ` under `Y H`. Let `x` have `s = dim V` columns, all in `V`,
with `det xᴴ x ≠ 0`, and let `w ∈ GL_s(𝔸_f)`. Suppose `H x w` is integral and the columns of
`Y H x w` lie in `K`. Then `(δ i)² ≤ [det xᴴ x] [det w]²`, with `[·]` the generalised index
`genIndex`; also `δ > 0`, and the index is finite. -/
lemma sublatticeDiscriminant_mul_index_sq_le (hLH : L * H = 1) (V : Submodule E (σ → E)) {s : ℕ}
    (hs : finrank E V = s) {x : Matrix σ (Fin s) E} (hx : colSpan x ≤ V)
    (hx_det : (xᴴ * x).det ≠ 0) (w : GL (Fin s) (𝔸f E))
    (h_int : IsIntMatrix (Ô E) (H * (finAdeleMatrix x * w.val))) (Y : Matrix τ P (𝔸f E))
    {K : Submodule (Ô E) (τ → 𝔸f E)}
    (h_mem : ∀ j : Fin s, (Y * (H * (finAdeleMatrix x * w.val))).col j ∈ K) :
    (sublatticeDiscriminant hLH V * sublatticeIndex hLH V Y K) ^ 2 ≤
        genIndex (finAdeleMatrix (xᴴ * x)).det * genIndex w.val.det ^ 2 ∧
      0 < sublatticeDiscriminant hLH V ∧
      1 ≤ sublatticeIndex hLH V Y K := by
  classical
  -- Write `x w = m A` with `m` the chosen basis. The right side is `δ² [det A]²`, and `[det A]` is
  -- the index of the column lattice of `A` in `Ô ^ s`. It bounds `i`, since `Y H m` maps that
  -- lattice into `K` and `Ô ^ s` onto the span of the columns of `Y H m`.
  subst hs
  obtain ⟨A, hA⟩ := exists_finAdeleMatrix_mul_eq_sublatticeBasis_mul hLH hx hx_det w
  rw [← sublatticeDiscriminant_sq_mul_genIndex_sq hLH hA]
  rw [hA] at h_int h_mem
  set m : Matrix σ (Fin (finrank E V)) (𝔸f E) := (sublatticeBasis hLH V).val
  obtain ⟨-, l, hl_int, hl⟩ := isPrimitiveMatrix_mul_sublatticeBasis hLH V
  -- `A = l H m A` is integral, so `[det A]` is an index of lattices.
  have hA_int : IsIntMatrix (Ô E) A.val := by
    have h_prod : IsIntMatrix (Ô E) (l * (H * (m * A.val))) := hl_int.mul h_int
    rwa [← H.mul_assoc, ← l.mul_assoc, hl, Matrix.one_mul] at h_prod
  let n : ℕ := submoduleIndex (colLattice (Ô E) A.val) (intVectors (Ô E) (Fin (finrank E V)))
  have hn : (n : ℝ) = genIndex A.val.det := submoduleIndex_colLattice_intVectors hA_int
  have hn_ne : n ≠ 0 := Nat.cast_ne_zero.1 (hn.trans_ne (genIndex_pos A.det).ne')
  have h_maps :
      colLattice (Ô E) A.val ≤ K.comap ((Y * (H * m)).mulVecLin.restrictScalars (Ô E)) :=
    colLattice_le fun j ↦ show (Y * (H * m) * A.val).col j ∈ K by
      simpa only [Matrix.mul_assoc] using h_mem j
  have h_dvd : sublatticeIndex hLH V Y K ∣ n := submoduleIndex_dvd_of_le _ h_maps le_sup_left
  obtain ⟨hi_ne, hi_le⟩ := ne_zero_and_le_of_dvd hn_ne h_dvd
  refine ⟨?_, sublatticeDiscriminant_pos hLH hx hx_det, hi_ne.pos⟩
  grw [mul_pow, hi_le, hn]

end GramLiouville

/-!
## Siegel's lemma and convergence of the height zeta function

`(stdSpace E κ).move (1, u)` is `E^κ` with the form `∑ x_i x̄_i` and the point `u`.
`.baseLattice` is its lattice `E^κ ∩ u Ô^κ`, `.archCoords` the vector of complex coordinates at all
infinite places, and `numInfPlaces E` the number of infinite places.
-/

section SiegelLemma

open NumberField Matrix Module Finset Fintype ENNReal Space AddSubgroup RingHom New.Core
  Prod

section Steps

variable {E κ : Type} [Field E] [CMType E] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- Let `E` be a CM field with a chosen CM type (`CMType E`), and let `ᴴ` be the conjugate
transpose for its complex conjugation. If `x` is a left invertible `κ × t` matrix over `E` and
`t + s = #κ`, the hermitian orthogonal `ker xᴴ` of its columns has dimension `s`. -/
lemma finrank_ker_conjTranspose {t s : ℕ} (hts : t + s = Fintype.card κ) {x : Matrix κ (Fin t) E}
    (hx : HasLeftInv x) : Module.finrank E xᴴ.mulVecLin.ker = s := by
  obtain ⟨k, hk⟩ := hx
  have h_range : xᴴ.mulVecLin.range = ⊤ :=
    LinearMap.range_eq_top.2 fun v ↦ ⟨kᴴ *ᵥ v, by simp [← conjTranspose_mul, hk]⟩
  have h_rank := xᴴ.mulVecLin.finrank_range_add_finrank_ker
  rw [h_range, finrank_top, Module.finrank_pi, Module.finrank_pi, Fintype.card_fin] at h_rank
  omega

/-- Let `E` be a CM field with a chosen CM type (`CMType E`), and let `x`, `y`, `B` be matrices over
`E`. If the columns of `y` span the hermitian orthogonal `ker xᴴ` of the columns of `x` and `B` is
invertible, then the hermitian orthogonal of the columns of `y Bᵀ` is the column span of `x`. -/
lemma ker_conjTranspose_mul_transpose {t s : ℕ} {x : Matrix κ (Fin t) E} {y : Matrix κ (Fin s) E}
    (hy : colSpan y = xᴴ.mulVecLin.ker) {B : Matrix (Fin s) (Fin s) E} (hB : B.det ≠ 0) :
    (y * Bᵀ)ᴴ.mulVecLin.ker = colSpan x := by
  have hxy : xᴴ * y = 0 := mul_eq_zero_of_colSpan_le_ker hy.le
  have hyx : yᴴ * x = 0 := by simpa using congrArg conjTranspose hxy
  obtain ⟨f, g, h_split⟩ := exists_mul_add_mul_eq_one hy.ge
  have h_split' : fᴴ * yᴴ + x * gᴴ = 1 := by simpa using congrArg conjTranspose h_split
  refine le_antisymm ?_ ?_
  · intro v (hv : (y * Bᵀ)ᴴ *ᵥ v = 0)
    refine ⟨gᴴ *ᵥ v, ?_⟩
    have hyv : yᴴ *ᵥ v = 0 := by simpa [hB] using congrArg (Bᵀᴴ⁻¹ *ᵥ ·) hv
    calc x *ᵥ gᴴ *ᵥ v = (fᴴ * yᴴ + x * gᴴ) *ᵥ v := by
          rw [add_mulVec, ← mulVec_mulVec, hyv, mulVec_zero, zero_add, mulVec_mulVec]
      _ = v := by rw [h_split', one_mulVec]
  · simp [IsConcreteLE.le_iff, hyx, Matrix.mul_assoc]

/-- Orthogonal lattices have the same discriminant. Let `E` be a CM field with a chosen CM type
(`CMType E`), containing a primitive `5040`-th root of unity, and let `u` be a finite adelic unitary
matrix. Let `x` and `y` be matrices over `E` with `#κ` columns in all and `xᴴ y = 0`. Let `b` and
`a` be invertible over `𝔸_f`, with `u⁻¹ x b` and `u⁻¹ y a` primitive. Then
`[det a]² |N(det yᴴ y)| = [det (x b)ᴴ (x b)]`. Here `[·]` is the generalised index `genIndex`: at a
unit the inverse of the factor by which it scales Haar measure on the finite adeles, so `|N(z)|` at
a nonzero `z ∈ E`, and `0` at a non-unit. `N` is the norm from `E` to `ℚ`. -/
lemma genIndex_sq_mul_abs_norm_eq [HasPrimitiveRoot5040 E] (u : Gf E κ) {t s : ℕ}
    (hts : t + s = Fintype.card κ)
    {x : Matrix κ (Fin t) E} {y : Matrix κ (Fin s) E} (hxy : xᴴ * y = 0)
    {b : GL (Fin t) (𝔸f E)} {a : GL (Fin s) (𝔸f E)}
    (hx_prim : IsPrimitiveMatrix (Ô E) (u.val.inv * (finAdeleMatrix x * b.val)))
    (hy_prim : IsPrimitiveMatrix (Ô E) (u.val.inv * (finAdeleMatrix y * a.val))) :
    genIndex a.val.det ^ 2 * |(Algebra.norm ℚ (yᴴ * y).det : ℝ)| =
      genIndex ((finAdeleMatrix x * b.val)ᴴ * (finAdeleMatrix x * b.val)).det := by
  -- Jacobi's identity for `u⁻¹ m` and `u⁻¹ w`, where `m = x b` and `w = y a`: the lattice index in
  -- it is `1` as `u⁻¹ m` is primitive, and the unitary `u⁻¹` drops out of the Gram matrices.
  set m : Matrix κ (Fin t) (𝔸f E) := finAdeleMatrix x * b.val with hm
  obtain ⟨hm_int, p, hp_int, hp⟩ := hx_prim
  have h_gram {i j : ℕ} (A : Matrix κ (Fin i) (𝔸f E)) (B : Matrix κ (Fin j) (𝔸f E)) :
      (u.val.inv * A)ᴴ * (u.val.inv * B) = Aᴴ * B := by
    simpa using U.gram_invariant u⁻¹ A B
  let w : Matrix κ (Fin s) (𝔸f E) := finAdeleMatrix y * a.val
  -- As `xᴴ y = 0`, also `(u⁻¹ m)ᴴ (u⁻¹ w) = mᴴ w = bᴴ (xᴴ y) a = 0`.
  have h_perp : (u.val.inv * m)ᴴ * (u.val.inv * w) = 0 := by
    have h_mw : mᴴ * w = b.valᴴ * finAdeleMatrix (xᴴ * y) * a.val := by
      simp [hm, w, finAdeleMatrix_conjTranspose, Matrix.mul_assoc]
    rw [h_gram, h_mw]
    simp [hxy]
  have h_index :
      submoduleIndex (intVectors (Ô E) (Fin t)) (preimageLattice (Ô E) (u.val.inv * m)) = 1 :=
    relIndex_eq_one.2 fun v hv ↦ by
      have hv_int : p *ᵥ (u.val.inv * m) *ᵥ v ∈ intVectors (Ô E) (Fin t) := hp_int.mulVec hv
      rwa [mulVec_mulVec, hp, one_mulVec] at hv_int
  have h_disc : genIndex ((u.val.inv * w)ᴴ * (u.val.inv * w)).det =
      genIndex ((u.val.inv * m)ᴴ * (u.val.inv * m)).det := by
    set F : Matrix κ (Fin t) (𝔸f E) := u.val.inv * m
    -- Take the extra columns to be zero, with `c = 1`; the Gram matrix is then block diagonal.
    obtain ⟨-, h_jacobi⟩ := jacobi_perp_discriminant (p := (0 : Matrix κ κ (𝔸f E))) (c := 1)
      (show IsUnimodular (Ô E) (1 : Matrix κ κ (𝔸f E)) by simp [IsUnimodular]) hm_int hy_prim
      (by rwa [Matrix.mul_one]) (by simp [hts]) rfl (.inl ⟨p, hp⟩)
    have h_block : (fromCols F 0)ᴴ * (1 : Matrix κ κ (𝔸f E)) * fromCols F (0 : Matrix κ κ (𝔸f E)) +
        fromBlocks 0 0 0 ((1 : (𝔸f E)ˣ) • 1) =
          fromBlocks (Fᴴ * F) 0 0 (1 : Matrix κ κ (𝔸f E)) := by
      rw [Matrix.mul_one, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]
      simp [fromBlocks_add]
    rw [h_index, h_block] at h_jacobi
    simpa [w, Matrix.mul_assoc] using h_jacobi
  have h_conj : wᴴ * w = a.valᴴ * finAdeleMatrix (yᴴ * y) * a.val := by
    simp [w, finAdeleMatrix_conjTranspose, Matrix.mul_assoc]
  rw [h_gram, h_gram, h_conj, det_mul, det_mul, det_conjTranspose] at h_disc
  -- The generalised index of an element of `E` is the absolute value of its norm.
  simpa [field, ← mapMatrix_apply, ← map_det] using h_disc

omit [DecidableEq κ] in
/-- Let `r v` make the columns of `y` orthonormal at each infinite place `v`, with embedding `Φ v`,
and let `a` be invertible over `𝔸_f`. Then `ideleAbs` of the determinant of `mkAdelicGL (r, a)`,
times `√([det a]² |N(det yᴴ y)|)`, is at least `1`. Here `[·]` is the generalised index `genIndex`:
at a unit it is the inverse of the factor by which the unit scales Haar measure on the finite
adeles, and at a non-unit it is `0`. `N` is the norm from `E` to `ℚ`. -/
lemma one_le_ideleAbs_det_mul_sqrt {s : ℕ} {y : Matrix κ (Fin s) E}
    {r : InfinitePlace E → GL (Fin s) ℂ}
    (hr : ∀ v : InfinitePlace E, (y.map (Φ v) * (r v).val)ᴴ * (y.map (Φ v) * (r v).val) = 1)
    (a : GL (Fin s) (𝔸f E)) :
    1 ≤ ideleAbs (mkAdelicGL (r, a)).det *
      √(genIndex a.val.det ^ 2 * |(Algebra.norm ℚ (yᴴ * y).det : ℝ)|) := by
  -- The infinite part cancels the norm of `det yᴴ y`, the finite part the index of `det a`.
  have hr_det (v : InfinitePlace E) : ‖(r v).val.det‖ ^ 2 * ‖Φ v (yᴴ * y).det‖ = 1 := by
    have h_one : (r v).valᴴ * (yᴴ * y).map (Φ v) * (r v).val = 1 := by
      simpa [← map_conjTranspose, Matrix.map_mul, Matrix.mul_assoc] using hr v
    have h_det : star (r v).val.det * Φ v (yᴴ * y).det * (r v).val.det = 1 := by
      simpa [← mapMatrix_apply, ← map_det] using congrArg Matrix.det h_one
    simpa [sq, mul_right_comm] using congrArg (‖·‖) h_det
  have ha : genIndex a.val.det = (finIdeleAbs a.det)⁻¹ := genIndex_eq_inv_finIdeleAbs a.det
  have ha_pos : 0 < finIdeleAbs a.det := by simp [finIdeleAbs]
  have h_pos : 0 < ∏ v, ‖(r v).val.det‖ ^ 2 := prod_pos fun v _ ↦ by
    simp [GeneralLinearGroup.det_ne_zero]
  have h_norm : |(Algebra.norm ℚ (yᴴ * y).det : ℝ)| = (∏ v, ‖(r v).val.det‖ ^ 2)⁻¹ ^ 2 := by
    rw [abs_norm_eq_prod_norm_sq, prod_pow]
    congr 1
    exact eq_inv_of_mul_eq_one_right (by simp [← prod_mul_distrib, hr_det])
  rw [ideleAbs_det_mkAdelicGL, ha, h_norm, ← mul_pow, Real.sqrt_sq (by positivity)]
  exact le_of_eq (by field_simp)

/-- Let `r v` make the columns of `y` orthonormal at each infinite place `v`, with embedding `Φ v`.
Then the Euclidean length of `y c` over all infinite places is that of the vectors `(r v)⁻¹ (Φ v c)`
taken together. -/
lemma norm_archCoords_mulVec (u : Gf E κ) {s : ℕ} {y : Matrix κ (Fin s) E}
    {r : InfinitePlace E → GL (Fin s) ℂ}
    (hr : ∀ v : InfinitePlace E, (y.map (Φ v) * (r v).val)ᴴ * (y.map (Φ v) * (r v).val) = 1)
    (c : Fin s → E) :
    ‖((stdSpace E κ).move (1, u)).archCoords (y *ᵥ c)‖ =
      √(∑ v : InfinitePlace E, ∑ i : Fin s, ‖((r v)⁻¹.val *ᵥ Φ v ∘ c) i‖ ^ 2) := by
  -- At the place `v` the vector `y c` is the image of `(r v)⁻¹ c` under the isometry `y (r v)`.
  have h_coord (v : InfinitePlace E) (i : κ) :
      (((stdSpace E κ).move (1, u)).vecAtPoint (y *ᵥ c) i).1 v = (y.map (Φ v) *ᵥ Φ v ∘ c) i := by
    rw [vecAtPoint_move]
    simp [Space.vecAtPoint, mulVec_eq_sum, fst_sum, Matrix.one_apply]
  have h_iso (v : InfinitePlace E) : ∑ i : κ, ‖(y.map (Φ v) *ᵥ Φ v ∘ c) i‖ ^ 2 =
      ∑ i : Fin s, ‖((r v)⁻¹.val *ᵥ Φ v ∘ c) i‖ ^ 2 := by
    rw [← sum_norm_sq_mulVec_of_isometry (hr v), mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one]
  simp only [PiLp.norm_eq_of_L2, sum_prod_type, archCoords, AddMonoidHom.mk'_apply, h_coord, h_iso]

/-- The length `frameLength` of a rational vector `c` at the adelic matrix `mkAdelicGL (r, a)`, with
infinite part `r` and finite part `a`, is the Euclidean length of the vectors `(r v)⁻¹ (Φ v c)` over
all infinite places `v`, with embedding `Φ v`. -/
lemma frameLength_mkAdelicGL {s : ℕ} (r : InfinitePlace E → GL (Fin s) ℂ) (a : GL (Fin s) (𝔸f E))
    (c : Fin s → E) :
    frameLength (mkAdelicGL (r, a)) c =
      √(∑ v : InfinitePlace E, ∑ i : Fin s, ‖((r v)⁻¹.val *ᵥ Φ v ∘ c) i‖ ^ 2) := by
  have h_coord (z : InfinitePlace E → GL (Fin s) ℂ) (v : InfinitePlace E) (i : Fin s) :
      (((mkAdelicGL (z, a⁻¹)).val *ᵥ toAdele ∘ c) i).1 v = ((z v).val *ᵥ Φ v ∘ c) i := by
    simp [mulVec_eq_sum, fst_sum]
  simp only [frameLength, PiLp.norm_eq_of_L2, sum_prod_type, ← map_inv, Prod.inv_mk, h_coord,
    Pi.inv_apply]

/-- Let `u` be a finite adelic unitary matrix. If `u⁻¹ y Bᵀ` is integral, its `i`-th column shows
that the rational vector `y (B i)` lies in the lattice `((stdSpace E κ).move (1, u)).baseLattice`,
which is `E^κ ∩ u Ô^κ`. -/
lemma mulVec_mem_baseLattice (u : Gf E κ) {s : ℕ} {y : Matrix κ (Fin s) E}
    {B : Matrix (Fin s) (Fin s) E}
    (h_int : IsIntMatrix (Ô E) (u.val.inv * (finAdeleMatrix y * finAdeleMatrix Bᵀ))) (i : Fin s) :
    y *ᵥ B i ∈ ((stdSpace E κ).move (1, u)).baseLattice := by
  -- The finite part of the `j`-th coordinate of `u⁻¹ y (B i)` is the entry `(j, i)` of `u⁻¹ y Bᵀ`;
  -- `vecAtPoint_move` must fire before `vecAtPoint` is unfolded.
  intro j
  change (((stdSpace E κ).move (1, u)).vecAtPoint (y *ᵥ B i) j).2 ∈ Ô E
  simpa [↓vecAtPoint_move, mulVec, mul_apply, Space.vecAtPoint, dotProduct, snd_sum] using
    h_int j i

/-- Let `u` be a finite adelic unitary matrix. A nonzero vector of the lattice
`((stdSpace E κ).move (1, u)).baseLattice`, which is `E^κ ∩ u Ô^κ`, has Euclidean length at least
`1` over all infinite places. -/
lemma one_le_norm_archCoords (u : Gf E κ) {x : κ → E}
    (hx_mem : x ∈ ((stdSpace E κ).move (1, u)).baseLattice) (hx_ne : x ≠ 0) :
    1 ≤ ‖((stdSpace E κ).move (1, u)).archCoords x‖ :=
  (one_le_firstMinimum fun _ _ ↦ rfl).trans (firstMinimum_le hx_mem hx_ne)

/-- Minkowski's second theorem for the adelic matrix `(r, a)`, with infinite part `r` and finite
part `a`: there is an invertible `B` over `E` such that `a⁻¹ Bᵀ` is integral and the rows `B i`
satisfy `|det (r, a)| * ∏ (len (B i)) ^ (2 f) ≤ (2 f s rd) ^ (f s)`. Here `len c` is the length
`frameLength (mkAdelicGL (r, a)) c`: the Euclidean norm of the vectors `(r v)⁻¹ (Φ v c)` at all
infinite places `v` taken together, with `Φ v` the embedding at `v`. Further, `|·|` is the idele
absolute value, `f` the number of infinite places and `rd` the root discriminant. -/
lemma exists_det_ne_zero_prod_frameLength_le {s : ℕ} (r : InfinitePlace E → GL (Fin s) ℂ)
    (a : GL (Fin s) (𝔸f E)) :
    ∃ B : Matrix (Fin s) (Fin s) E, B.det ≠ 0 ∧
      IsIntMatrix (Ô E) (a.inv * finAdeleMatrix Bᵀ) ∧
      ideleAbs (mkAdelicGL (r, a)).det *
          ∏ i : Fin s, frameLength (mkAdelicGL (r, a)) (B i) ^ (2 * numInfPlaces E) ≤
        (2 * (numInfPlaces E * s) * rootDiscr E) ^ (numInfPlaces E * s) := by
  have h_basis := minkowski_second_theorem (mkAdelicGL (r, a))
  rw [Fintype.card_fin] at h_basis
  obtain ⟨B, hB_indep, hB_int, -, h_mink⟩ := h_basis
  have hB_unit : IsUnit (of B) := linearIndependent_row_iff_isUnit.1 hB_indep
  refine ⟨of B, ((isUnit_iff_isUnit_det _).1 hB_unit).ne_zero, fun j i ↦ ?_, h_mink⟩
  rw [← show (((mkAdelicGL (r, a))⁻¹.val *ᵥ toAdele ∘ B i) j).2 =
    (a.inv * finAdeleMatrix (of B)ᵀ) j i from snd_sum]
  exact hB_int i j

end Steps

variable {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {κ : Type} [Fintype κ]
  [DecidableEq κ]

/-- A form of Siegel's lemma (compare Bombieri–Vaaler). A subspace `T` of `E^κ` of codimension `s`
is (a) the hermitian orthogonal of `s` vectors `X i` that are (b) nonzero and in `E^κ ∩ u Ô^κ`, with
(c) `(∏ ‖X i‖) ^ (2 f) ≤ (8 f s rd) ^ (f s) * d`. The length is Euclidean over all `f` infinite
places together and `rd` is the root discriminant. -/
lemma siegel_lemma (u : Gf E κ) {T : Submodule E (κ → E)} {s : ℕ}
    (hs : Module.finrank E T + s = Fintype.card κ) :
    ∃ X : Matrix (Fin s) κ E,
      -- (a) `T` is the hermitian orthogonal of the rows of `X`
      Xᵀᴴ.mulVecLin.ker = T ∧
      -- (b) the rows are nonzero lattice vectors
      (∀ i : Fin s, X i ∈ ((stdSpace E κ).move (1, u)).baseLattice ∧ X i ≠ 0) ∧
      -- (c) the bound for the product of their lengths
      (∏ i : Fin s, ‖((stdSpace E κ).move (1, u)).archCoords (X i)‖) ^ (2 * numInfPlaces E) ≤
        (8 * (numInfPlaces E * s) * rootDiscr E) ^ (numInfPlaces E * s) *
          sublatticeDiscriminant u.val.val_inv T := by
  -- Take lattice bases `x b` of `T` and `y a` of its orthogonal complement; by Jacobi's identity
  -- their discriminants agree. Minkowski's second theorem gives short lattice vectors `y B i`.
  unfold sublatticeDiscriminant
  set m : Matrix κ (Fin (Module.finrank E T)) (𝔸f E) := (sublatticeBasis u.val.val_inv T).val
  have hm_prim : IsPrimitiveMatrix (Ô E) (u.val.inv * m) :=
    isPrimitiveMatrix_mul_sublatticeBasis u.val.val_inv T
  obtain ⟨x, b, hx_inv, hx, hm⟩ :
      ∃ᵉ (x : Matrix κ (Fin (Module.finrank E T)) E) (b : GL (Fin (Module.finrank E T)) (𝔸f E)),
        HasLeftInv x ∧ colSpan x = T ∧ m = finAdeleMatrix x * b.val :=
    exists_sublatticeBasis_eq_finAdeleMatrix_mul u.val.val_inv T
  obtain ⟨y, a, ⟨l, hl⟩, hy, hy_prim⟩ : ∃ᵉ (y : Matrix κ (Fin s) E) (a : GL (Fin s) (𝔸f E)),
      HasLeftInv y ∧ colSpan y = xᴴ.mulVecLin.ker ∧
        IsPrimitiveMatrix (Ô E) (u.val.inv * (finAdeleMatrix y * a.val)) :=
    exists_isPrimitiveMatrix_mul_finAdeleMatrix u.val.val_inv _
      (finrank_ker_conjTranspose hs hx_inv)
  have h_jacobi :
      genIndex a.val.det ^ 2 * |(Algebra.norm ℚ (yᴴ * y).det : ℝ)| = genIndex (mᴴ * m).det := by
    rw [hm] at hm_prim ⊢
    exact genIndex_sq_mul_abs_norm_eq u hs (mul_eq_zero_of_colSpan_le_ker hy.le) hm_prim hy_prim
  -- At each infinite place make the columns of `y` orthonormal by `r v`.
  have h_orth (v : InfinitePlace E) :
      ∃ r : GL (Fin s) ℂ, (y.map (Φ v) * r.val)ᴴ * (y.map (Φ v) * r.val) = 1 :=
    have h_inv : l.map (Φ v) * y.map (Φ v) = 1 := by simp [← Matrix.map_mul, hl]
    (exists_orthonormal_mul id ⟨l.map (Φ v), h_inv⟩).imp fun _ ↦ And.right
  choose r hr using h_orth
  have h_vol : 1 ≤ ideleAbs (mkAdelicGL (r, a)).det * √(genIndex (mᴴ * m).det) := by
    rw [← h_jacobi]
    exact one_le_ideleAbs_det_mul_sqrt hr a
  -- Minkowski's second theorem for `(r, a)`: a rational basis `B i` with `a⁻¹ B i` integral and a
  -- bounded product of the lengths of the `r⁻¹ B i`, which are those of the `y B i`.
  obtain ⟨B, hB_det, haB, h_mink⟩ := exists_det_ne_zero_prod_frameLength_le r a
  simp only [frameLength_mkAdelicGL, ← norm_archCoords_mulVec u hr] at h_mink
  refine ⟨fun i ↦ y *ᵥ B i, ?_, fun i ↦ ⟨?_, fun h_zero : y *ᵥ B i = 0 ↦ ?_⟩, ?_⟩
  · exact (ker_conjTranspose_mul_transpose hy hB_det).trans hx
  · -- `u⁻¹ y Bᵀ = (u⁻¹ y a) (a⁻¹ Bᵀ)` is a product of integral matrices.
    obtain ⟨hy_int, -⟩ := hy_prim
    exact mulVec_mem_baseLattice u (by simpa [Matrix.mul_assoc] using hy_int.mul haB) i
  · have hBi : B i = 0 := by simpa [hl] using congrArg (l *ᵥ ·) h_zero
    exact hB_det (det_eq_zero_of_row_eq_zero i (congrFun hBi))
  · -- Trade the determinant of `(r, a)` for the discriminant by `h_vol`.
    have h_rootDiscr_pos : 0 < rootDiscr E := rootDiscr_pos E
    calc
      _ ≤ (ideleAbs (mkAdelicGL (r, a)).det *
            ∏ i : Fin s, ‖((stdSpace E κ).move (1, u)).archCoords (y *ᵥ B i)‖ ^
              (2 * numInfPlaces E)) * √(genIndex (mᴴ * m).det) := by
        grw [mul_right_comm, ← h_vol, one_mul, prod_pow]
      _ ≤ (8 * (numInfPlaces E * s) * rootDiscr E) ^ (numInfPlaces E * s) *
          √(genIndex (mᴴ * m).det) := by
        grw [h_mink]
        gcongr
        norm_num

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- Siegel's lemma, raised to the power `k + 1` with `k = #κ`, as a bound for one term of the height
zeta function. A subspace `T` of `E^κ` of codimension `s` is the hermitian orthogonal of `s` nonzero
vectors `X i` of `E^κ ∩ u Ô^κ` with `(d T)⁻¹ ^ (k + 1) ≤ ∏ (‖X i‖⁻¹ ^ (2 n) C)`, where
`n = f (k + 1)`, `C = (8 f k rd) ^ n`, `f` is the number of infinite places and `rd` the root
discriminant. -/
lemma exists_inv_sublatticeDiscriminant_pow_le_prod (u : Gf E κ) {T : Submodule E (κ → E)} {s : ℕ}
    (hs : Module.finrank E T + s = Fintype.card κ) :
    ∃ X : Matrix (Fin s) κ E,
      Xᵀᴴ.mulVecLin.ker = T ∧
      (∀ i : Fin s, X i ∈ ((stdSpace E κ).move (1, u)).baseLattice ∧ X i ≠ 0) ∧
      (sublatticeDiscriminant u.val.val_inv T ^ (Fintype.card κ + 1))⁻¹ ≤
        ∏ i : Fin s, ‖((stdSpace E κ).move (1, u)).archCoords (X i)‖⁻¹ ^
            (2 * (numInfPlaces E * (Fintype.card κ + 1))) *
          (8 * (numInfPlaces E * Fintype.card κ) * rootDiscr E) ^
            (numInfPlaces E * (Fintype.card κ + 1)) := by
  obtain ⟨X, h_ker, hX, h_siegel⟩ := siegel_lemma u hs
  refine ⟨X, h_ker, hX, ?_⟩
  set d : ℝ := sublatticeDiscriminant u.val.val_inv T
  set P : ℝ := ∏ i, ‖((stdSpace E κ).move (1, u)).archCoords (X i)‖
  set n : ℕ := numInfPlaces E * (card κ + 1) with hn
  set C : ℝ := (8 * (numInfPlaces E * card κ) * rootDiscr E) ^ n with hC
  have h_rootDiscr_nonneg : 0 ≤ rootDiscr E := Real.rpow_nonneg (by positivity) _
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hP : 1 ≤ P := one_le_prod₀ fun i _ ↦ one_le_norm_archCoords u (hX i).left (hX i).right
  have h_pow : P ^ (2 * n) ≤ C ^ s * d ^ (card κ + 1) :=
    calc
      _ = (P ^ (2 * numInfPlaces E)) ^ (card κ + 1) := by rw [hn, ← pow_mul, mul_assoc]
      _ ≤ ((8 * (numInfPlaces E * card κ) * rootDiscr E) ^ (numInfPlaces E * s) * d) ^
          (card κ + 1) := by
        grw [h_siegel]
        gcongr
        omega
      _ = C ^ s * d ^ (card κ + 1) := by
        rw [hC, hn, mul_pow, ← pow_mul, ← pow_mul, mul_right_comm _ s]
  calc
    _ ≤ C ^ s / P ^ (2 * n) := by
      rw [inv_eq_one_div]
      exact div_le_of_le_mul₀ (by positivity) (by positivity)
        (by rwa [div_mul_eq_mul_div, one_le_div (by positivity)])
    _ = _ := by simp [P, field, prod_pow, prod_mul_distrib]

/-- The height zeta function of the subspaces of codimension `s` converges at `k + 1`, `k = #κ`.
Then `∑ (d T)⁻¹ ^ (k + 1) ≤ (200 f k rd) ^ (f (k + 1) s)`, the sum over all subspaces `T` of `E^κ`
of codimension `s`. Here `rd` is the root discriminant of `E` and `f = numInfPlaces E` the number of
infinite places. -/
lemma tsum_sublatticeDiscriminant_inv_le (u : Gf E κ) (s : ℕ) :
    ∑' T : {T : Submodule E (κ → E) // Module.finrank E T + s = Fintype.card κ},
        ENNReal.ofReal (sublatticeDiscriminant u.val.val_inv T.val ^ (Fintype.card κ + 1))⁻¹ ≤
      ENNReal.ofReal
        ((200 * (numInfPlaces E * Fintype.card κ) * rootDiscr E) ^
          (numInfPlaces E * (Fintype.card κ + 1) * s)) := by
  -- By `siegel_lemma`, in the form `exists_inv_sublatticeDiscriminant_pow_le_prod`, each `T` is the
  -- orthogonal of a tuple `X` of nonzero lattice vectors whose weight bounds the term of `T`; the
  -- sum over tuples is a power of a sum over the lattice.
  let V : Space E κ 1 := (stdSpace E κ).move (1, u)
  let L : Set (κ → E) := {x ∈ V.baseLattice | x ≠ 0}
  let n : ℕ := numInfPlaces E * (card κ + 1)
  let C : ℝ := (8 * (numInfPlaces E * card κ) * rootDiscr E) ^ n
  let wt (x : L) : ℝ := ‖V.archCoords x.val‖⁻¹ ^ (2 * n) * C
  have h_rootDiscr_nonneg : 0 ≤ rootDiscr E := Real.rpow_nonneg (by positivity) _
  have h_wt (x : L) : 0 ≤ wt x := by positivity
  -- Nonzero lattice vectors have length at least `1`, so they are `1`-separated and the packing
  -- bound `∑ ‖x‖⁻¹ ^ (2 n) ≤ 5 ^ (2 n)` holds, as `2 n` exceeds the real dimension
  -- `2 * numInfPlaces E * card κ` by at least `2`.
  have h_long (x : L) : 1 ≤ ‖V.archCoords x.val‖ :=
    one_le_norm_archCoords u x.property.left x.property.right
  have h_sep (x y : L) (hxy : x ≠ y) : 1 ≤ ‖V.archCoords x.val - V.archCoords y.val‖ := by
    simpa using h_long ⟨x - y,
      sub_mem x.property.left y.property.left, sub_ne_zero.2 (Subtype.coe_injective.ne hxy)⟩
  obtain ⟨h_summable, h_packing⟩ := tsum_inv_pow_le_of_separated one_pos h_sep h_long
    (n := 2 * n) (by simp [n, finrank_real_of_complex, mul_add, NeZero.one_le])
  -- Multiply by `C`, using `200 = 5 ^ 2 * 8`.
  have h_sum : ∑' x, ENNReal.ofReal (wt x) ≤
      .ofReal ((200 * (numInfPlaces E * card κ) * rootDiscr E) ^ n) := by
    rw [← ofReal_tsum_of_nonneg h_wt (h_summable.mul_right C), tsum_mul_right]
    grw [h_packing, pow_mul, ← mul_pow]
    exact le_of_eq (by ring_nf)
  have h_term (T : {T : Submodule E (κ → E) // finrank E T + s = card κ}) :
      ∃ X : Fin s → L, (of fun i ↦ (X i).val)ᵀᴴ.mulVecLin.ker = T.val ∧
        (sublatticeDiscriminant u.val.val_inv T.val ^ (card κ + 1))⁻¹ ≤ ∏ i, wt (X i) := by
    obtain ⟨X, h_ker, hX, h_le⟩ := exists_inv_sublatticeDiscriminant_pow_le_prod u T.property
    exact ⟨fun i ↦ ⟨X i, hX i⟩, h_ker, h_le⟩
  choose tuple h_ker h_le using h_term
  -- A subspace is recovered from its tuple as the orthogonal.
  have h_inj : Function.Injective tuple := fun T T' h_eq ↦
    Subtype.ext (by rw [← h_ker T, ← h_ker T', h_eq])
  calc
    _ ≤ ∑' T, ∏ i, ENNReal.ofReal (wt (tuple T i)) := by
      gcongr with T
      grw [← ofReal_prod_of_nonneg fun i _ ↦ h_wt _, h_le]
    _ ≤ ∑' X : Fin s → L, ∏ i, ENNReal.ofReal (wt (X i)) :=
      tsum_comp_le_tsum_of_injective h_inj fun X : Fin s → L ↦ ∏ i, ENNReal.ofReal (wt (X i))
    _ ≤ ∏ _ : Fin s, ∑' x, ENNReal.ofReal (wt x) :=
      tsum_prod_le_prod_tsum fun x : L ↦ ENNReal.ofReal (wt x)
    _ ≤ _ := by grw [h_sum, Fin.prod_const, ← ofReal_pow (by positivity), ← pow_mul]

end SiegelLemma

end New.Filling

end
