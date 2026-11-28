import Lib.Weil.Periods.Grading

/-!
# The lattice of a finite point of a graded space

A finite point `x` of the unitary group of a hermitian space `V` gives a self-dual lattice
`New.Space.lattice` over `Ô`, spanned by the orthonormal frame `V.xFin * x`. A grading
(`New.Grading`) writes `V = X ⊕ X^⊥`, where `X^⊥` is spanned by the string. The lattice has an
intersection `Λ'⁻` with `X^⊥` (`New.Grading.latticeMinus`) and a projection `Λ'⁺` to `X^⊥`
(`New.Grading.latticePlus`); `Λ⁻` is the intersection for the point `1`.

* `New.Space.mem_lattice_iff_formFin`: the lattice of a point is self-dual.
* `New.Space.lattice_eq_iff`: two points have the same lattice if and only if they differ by an
  integral unitary matrix.
* `New.Grading.mem_latticeMinus_iff_formFin`, `New.Grading.mem_latticePlus_iff_formFin`: the
  intersection and the projection are dual to each other.
* `New.Grading.exists_lattice_inclXFin_mul_eq`: lattices of points with the same intersection with
  `X^⊥` are conjugate under the unitary group of `X`, assuming `[HasPrimitiveRoot5040 E]`.

Notions from other files:
* `𝔸f E`, `Ô E`: the finite adeles of the CM field `E` and their subring of integral adeles.
* `Gf E ι`, `stdLevel E ι`: the matrices `g` over `𝔸f E` with `gᴴ g = 1`, and those with integral
  entries.
* `Space E ι ε`: a Gram matrix `V.J` over `E` with a frame `V.xFin` over `𝔸f E` in which the form is
  standard; `V.ratCoordMatrixFin g` is the matrix `V.xFin * g * V.xFin⁻¹`.
* `Grading V N X s`: an identification `Y.indexEquiv` of the basis indices with `X ⊕ Fin s`, for
  which the form is standard on `X` and the string of `s` vectors is orthogonal to `X`.

## Relation to the literature

The results are known: duality of lattices, and Witt's theorem for unimodular hermitian lattices.
Sources: O'Meara, Introduction to Quadratic Forms; Jacobowitz, Hermitian forms over local fields
(1962).
-/

open Matrix Pointwise

noncomputable section

namespace New

section

variable {E ι : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- An inclusion `c • A ≤ B` of lattices of finite adelic vectors can be checked on the vectors of
`A`. -/
lemma smul_le_iff_forall {c : 𝔸f E} {A B : Submodule (Ô E) (ι → 𝔸f E)} :
    c • A ≤ B ↔ ∀ y ∈ A, c • y ∈ B :=
  Submodule.map_le_iff_le_comap

/-- A matrix `P` over the finite adeles with a left inverse (`HasLeftInv P`) is primitive (integral
with an integral left inverse) if, for every vector `c`, the vector `P c` is integral if and only
if `c` is. -/
lemma isPrimitiveMatrix_of_mulVec_mem_iff {κ : Type} [Fintype κ] [DecidableEq κ]
    {P : Matrix ι κ (𝔸f E)} (h_inv : HasLeftInv P)
    (h_int : ∀ c : κ → 𝔸f E, (∀ i : ι, (P *ᵥ c) i ∈ Ô E) ↔ ∀ j : κ, c j ∈ Ô E) :
    IsPrimitiveMatrix (Ô E) P := by
  -- Some invertible `b` makes `P * b` primitive, with left inverse `L`. Then `b` is integral.
  obtain ⟨b, -, hPb_int : IsIntMatrix (Ô E) (P * b.val), L, hL_int : IsIntMatrix (Ô E) L,
    hLb : L * (P * b.val) = 1⟩ := isValuationPair_Ô.exists_isPrimitiveMatrix_mul h_inv
  have hP : IsIntMatrix (Ô E) P :=
    fun i j ↦ by simpa using (h_int (Pi.single j 1)).2 (single_mem_intVectors j) i
  have hb : IsIntMatrix (Ô E) b.val := fun i j ↦ by
    have h_col : ∀ k : ι, (P *ᵥ b.val.col j) k ∈ Ô E := fun k ↦ by
      simpa [mulVec, dotProduct, Matrix.mul_apply] using hPb_int k j
    exact (h_int (b.val.col j)).1 h_col i
  refine ⟨hP, b.val * L, hb.mul hL_int, ?_⟩
  calc b.val * L * P = b.val * (L * (P * b.val)) * b⁻¹.val := by simp [Matrix.mul_assoc]
    _ = 1 := by rw [hLb, Matrix.mul_one, Units.mul_inv]

namespace Space

variable {ε : ι → ℤˣ} (V : Space E ι ε)

/-- The lattice of a finite point `x`, in rational coordinates: the vectors whose coordinates in
the frame `V.xFin * x` are integral. -/
def lattice (x : Gf E ι) : Submodule (Ô E) (ι → 𝔸f E) :=
  preimageLattice (Ô E) (V.xFin * x.val)⁻¹.val

/-- The hermitian form of `V` on finite adelic vectors, conjugate linear in the first variable. -/
def formFin (y z : ι → 𝔸f E) : 𝔸f E := star y ⬝ᵥ V.J.map (algebraMap E (𝔸f E)) *ᵥ z

variable {V} {x x' g : Gf E ι} {y z : ι → 𝔸f E}

lemma mem_lattice : y ∈ V.lattice x ↔ ∀ i : ι, ((V.xFin * x.val)⁻¹.val *ᵥ y) i ∈ Ô E := Iff.rfl

/-- The lattice of `x` consists of the images of the integral vectors in the frame
`V.xFin * x`. -/
lemma mulVec_mem_lattice : (V.xFin * x.val).val *ᵥ y ∈ V.lattice x ↔ ∀ i : ι, y i ∈ Ô E := by
  rw [mem_lattice, mulVec_mulVec, Units.inv_mul, one_mulVec]

/-- For a finite point `x`, the frame `V.xFin * x` is orthonormal for the form of `V`. -/
lemma gram_xFin_mul_eq_one (x : Gf E ι) :
    (V.xFin * x.val).valᴴ * V.J.map (algebraMap E (𝔸f E)) * (V.xFin * x.val).val = 1 :=
  gram_mul_of_gram_eq V.gram_xFin x.2

/-- The Gram matrix of `V` is `g⁻¹ᴴ g⁻¹` for the orthonormal frame `g = V.xFin * x`. -/
lemma gram_frame_inv (x : Gf E ι) :
    (V.xFin * x.val)⁻¹.valᴴ * (V.xFin * x.val)⁻¹.val = V.J.map (algebraMap E (𝔸f E)) := by
  simpa only [mul_one] using gram_inv_of_gram_eq (gram_xFin_mul_eq_one x)

/-- For a finite point `x`, the form of `V` is the standard form in the coordinates of the frame
`V.xFin * x`. -/
lemma formFin_eq_dotProduct (x : Gf E ι) (y z : ι → 𝔸f E) :
    V.formFin y z = star ((V.xFin * x.val)⁻¹.val *ᵥ y) ⬝ᵥ (V.xFin * x.val)⁻¹.val *ᵥ z := by
  rw [formFin, ← gram_frame_inv x, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

/-- The form of `V` on finite adelic vectors is hermitian. -/
lemma star_formFin (y z : ι → 𝔸f E) : star (V.formFin y z) = V.formFin z y := by
  rw [formFin_eq_dotProduct 1, formFin_eq_dotProduct 1, ← star_dotProduct]

/-- A scalar moves from the second argument of the form of `V` to the first with a conjugation. -/
lemma formFin_star_smul (c : 𝔸f E) (y z : ι → 𝔸f E) :
    V.formFin y (star c • z) = V.formFin (c • y) z := by
  simp only [formFin, mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]

/-- The lattice of a point is its own dual: `z` lies in it if and only if its products with all
vectors of the lattice are integral. -/
lemma mem_lattice_iff_formFin : z ∈ V.lattice x ↔ ∀ y ∈ V.lattice x, V.formFin y z ∈ Ô E := by
  simp only [formFin_eq_dotProduct x]
  refine ⟨fun hz y hy ↦ ?_, fun h ↦ mem_lattice.2 fun i ↦ ?_⟩
  · exact sum_mem fun i _ ↦ mul_mem (star_mem_Ô (mem_lattice.1 hy i)) (mem_lattice.1 hz i)
  · -- The coordinate `i` of `z` is its pairing with the column `i` of the frame.
    simpa only [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.star_single, star_one,
      single_one_dotProduct] using h _ (mulVec_mem_lattice.2 (single_mem_intVectors i))

/-- The point `g`, acting in rational coordinates, carries the lattice of `x` onto that of
`g x`. -/
lemma mulVec_mem_lattice_mul :
    V.ratCoordMatrixFin g *ᵥ y ∈ V.lattice (g * x) ↔ y ∈ V.lattice x := by
  have h_coord : (V.xFin * (g * x).val)⁻¹ * (V.xFin * g.val * V.xFin⁻¹) = (V.xFin * x.val)⁻¹ := by
    simp [Gf.coe_mul, mul_assoc]
  simp only [mem_lattice, mulVec_mulVec, ratCoordMatrixFin, ← Units.val_mul, h_coord]

/-- The lattice of `x'` is contained in that of `x` if and only if the change of frame `x⁻¹ * x'`
is integral, that is, lies in `stdLevel E ι`. -/
lemma lattice_le_iff : V.lattice x' ≤ V.lattice x ↔ x⁻¹ * x' ∈ stdLevel E ι := by
  have h_frame : (V.xFin * x.val)⁻¹ = (x⁻¹ * x').val * (V.xFin * x'.val)⁻¹ := by
    simp [Gf.coe_mul, Gf.coe_inv, mul_assoc]
  refine ⟨fun h ↦ mem_stdLevel.2 fun i j ↦ ?_, fun h y hy ↦ ?_⟩
  · -- The column `j` of the frame of `x'` lies in the lattice of `x`.
    have h_column : (V.xFin * x'.val).val *ᵥ Pi.single j 1 ∈ V.lattice x :=
      h (mulVec_mem_lattice.2 (single_mem_intVectors j))
    rw [mem_lattice, mulVec_mulVec, ← Units.val_mul, h_frame, inv_mul_cancel_right,
      mulVec_single_one] at h_column
    exact h_column i
  · rw [mem_lattice, h_frame, Units.val_mul, ← mulVec_mulVec]
    exact IsIntMatrix.mulVec (mem_stdLevel.1 h) hy

/-- Two points have the same lattice if and only if they differ by an integral unitary matrix. -/
lemma lattice_eq_iff : V.lattice x = V.lattice x' ↔ x⁻¹ * x' ∈ stdLevel E ι := by
  refine ⟨fun h ↦ lattice_le_iff.1 h.ge, fun h ↦ le_antisymm ?_ (lattice_le_iff.2 h)⟩
  simpa [lattice_le_iff] using inv_mem h

/-- The conjugate `x⁻¹ g x` lies in the group `stdLevel E ι` of integral unitary matrices if and
only if `g`, acting through its matrix `V.ratCoordMatrixFin g` in rational coordinates, maps the
lattice of `x` into itself. -/
lemma conj_mem_stdLevel_iff :
    x⁻¹ * (g * x) ∈ stdLevel E ι ↔ ∀ y ∈ V.lattice x, V.ratCoordMatrixFin g *ᵥ y ∈ V.lattice x := by
  rw [← lattice_le_iff (V := V)]
  refine ⟨fun h y hy ↦ h (mulVec_mem_lattice_mul.2 hy), fun h z hz ↦ ?_⟩
  obtain ⟨y, rfl⟩ : ∃ y, V.ratCoordMatrixFin g *ᵥ y = z :=
    ⟨V.ratCoordMatrixFin g⁻¹ *ᵥ z, by simp [ratCoordMatrixFin, Gf.coe_inv, mul_assoc]⟩
  exact h y (mulVec_mem_lattice_mul.1 hz)

/-- The matrix of a finite point `g` in rational coordinates preserves the Gram matrix of `V`. -/
lemma ratCoordMatrixFin_isometry (g : Gf E ι) :
    (V.ratCoordMatrixFin g)ᴴ * V.J.map (algebraMap E (𝔸f E)) * V.ratCoordMatrixFin g =
      V.J.map (algebraMap E (𝔸f E)) :=
  -- By definition this matrix is `(V.xFin * g) * V.xFin⁻¹`.
  gram_mul_of_gram_eq (x := V.xFin * g.val) (gram_xFin_mul_eq_one g)
    (gram_inv_of_gram_eq V.gram_xFin)

end Space

end

namespace Grading

variable {E X ι : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι]
  [DecidableEq X] {ε : ι → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} (Y : Grading V N X s)

/-- The projection to the span of the basis vectors `i` of grade `d`, that is, with
`Y.gradeOf i = d`, where `Y.gradeOf` is the integer grade that the grading attaches to each
index. -/
def gradeProj (d : ℤ) : (ι → 𝔸f E) →ₗ[𝔸f E] ι → 𝔸f E :=
  (diagonal fun i : ι ↦ if Y.gradeOf i = d then 1 else 0).mulVecLin

/-- The orthogonal projection to `X^⊥`, the span of the string. -/
def stringProj : (ι → 𝔸f E) →ₗ[𝔸f E] ι → 𝔸f E :=
  (diagonal fun i : ι ↦ if (Y.indexEquiv.symm i).isRight then 1 else 0).mulVecLin

/-- A lattice is graded if it contains, for each integer `d`, the part `Y.gradeProj d y` of grade
`d` of each of its vectors `y`. -/
def IsGraded (L : Submodule (Ô E) (ι → 𝔸f E)) : Prop := ∀ d : ℤ, ∀ y ∈ L, Y.gradeProj d y ∈ L

/-- The intersection `Λ'⁻` of the lattice of `x` with `X^⊥`. -/
def latticeMinus (x : Gf E ι) : Submodule (Ô E) (ι → 𝔸f E) :=
  V.lattice x ⊓ Y.stringProj.range.restrictScalars (Ô E)

/-- The projection `Λ'⁺` of the lattice of `x` to `X^⊥`. -/
def latticePlus (x : Gf E ι) : Submodule (Ô E) (ι → 𝔸f E) :=
  (V.lattice x).map (Y.stringProj.restrictScalars (Ô E))

/-- The bounds `q̄ ^ k Λ⁻ ⊆ Λ'⁻` and `q ^ k Λ'⁻ ⊆ Λ⁻`, where `Λ'⁻` and `Λ⁻` are the intersections
with `X^⊥` of the lattices of `x` and of `1`. -/
structure HasLatticeBounds (q : 𝔸f E) (k : ℕ) (x : Gf E ι) : Prop where
  /-- `q̄ ^ k Λ⁻ ⊆ Λ'⁻`. -/
  lower : star q ^ k • Y.latticeMinus 1 ≤ Y.latticeMinus x
  /-- `q ^ k Λ'⁻ ⊆ Λ⁻`. -/
  upper : q ^ k • Y.latticeMinus x ≤ Y.latticeMinus 1

/-- The orbit of `x` under the finite Bessel subgroup has a point whose lattice is graded and
satisfies the bounds `New.Grading.HasLatticeBounds`. -/
def HasBoundedOrbit (q : 𝔸f E) (k : ℕ) (x : Gf E ι) : Prop :=
  ∃ r ∈ Y.besselFin, Y.IsGraded (V.lattice (r * x)) ∧ Y.HasLatticeBounds q k (r * x)

/-- The finite part of the matrix `Y.stringMap Y'` (the second component of each of its entries),
acting on vectors: the map between two graded spaces that kills `X` and sends each string vector to
a multiple of the string vector with the same number. -/
def stringMapFin {X' ι' : Type} [Fintype ι'] [DecidableEq ι'] [DecidableEq X'] {ε' : ι' → ℤˣ}
    {s' : ℕ} {V' : Space E ι' ε'} (Y' : Grading V' N X' s') : (ι → 𝔸f E) →ₗ[𝔸f E] ι' → 𝔸f E :=
  ((Y.stringMap Y').map Prod.snd).mulVecLin

variable {Y} {x x' : Gf E ι} {y z : ι → 𝔸f E} {c : 𝔸f E}

lemma stringProj_apply_inl (y : ι → 𝔸f E) (a : X) :
    Y.stringProj y (Y.indexEquiv (.inl a)) = 0 := by
  simp [stringProj, mulVec_diagonal]

lemma stringProj_apply_inr (y : ι → 𝔸f E) (b : Fin s) :
    Y.stringProj y (Y.indexEquiv (.inr b)) = y (Y.indexEquiv (.inr b)) := by
  simp [stringProj, mulVec_diagonal]

/-- A vector is fixed by the projection to `X^⊥` if and only if its coordinates on `X` vanish. -/
lemma stringProj_eq_self_iff : Y.stringProj y = y ↔ ∀ a : X, y (Y.indexEquiv (.inl a)) = 0 := by
  simp [funext_iff, Y.indexEquiv.forall_congr_right.symm, stringProj_apply_inl,
    stringProj_apply_inr, eq_comm]

lemma stringProj_stringProj (y : ι → 𝔸f E) : Y.stringProj (Y.stringProj y) = Y.stringProj y :=
  stringProj_eq_self_iff.2 (stringProj_apply_inl y)

lemma mem_latticeMinus : y ∈ Y.latticeMinus x ↔ y ∈ V.lattice x ∧ Y.stringProj y = y := by
  simp only [latticeMinus, Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_range]
  refine and_congr_right fun _ ↦ ⟨?_, fun h ↦ ⟨y, h⟩⟩
  rintro ⟨z, rfl⟩
  exact stringProj_stringProj z

lemma mem_latticePlus : y ∈ Y.latticePlus x ↔ ∃ z ∈ V.lattice x, Y.stringProj z = y := Iff.rfl

lemma stringProj_eq_of_mem_latticePlus (hy : y ∈ Y.latticePlus x) : Y.stringProj y = y := by
  obtain ⟨z, -, rfl⟩ := mem_latticePlus.1 hy
  exact stringProj_stringProj z

/-- Multiples of vectors of the projection `Λ'⁺` lie in `X^⊥`. -/
lemma stringProj_smul_of_mem_latticePlus (hy : y ∈ Y.latticePlus x) :
    Y.stringProj (c • y) = c • y := by
  rw [map_smul, stringProj_eq_of_mem_latticePlus hy]

lemma latticeMinus_le_lattice : Y.latticeMinus x ≤ V.lattice x := inf_le_left

lemma latticeMinus_le_latticePlus : Y.latticeMinus x ≤ Y.latticePlus x :=
  fun y hy ↦ mem_latticePlus.2 ⟨y, mem_latticeMinus.1 hy⟩

variable [Fintype X]

/-- The projection to `X^⊥` is self-adjoint for the form of `V`. -/
lemma formFin_stringProj (y z : ι → 𝔸f E) :
    V.formFin (Y.stringProj y) z = V.formFin y (Y.stringProj z) := by
  -- The Gram matrix has no entries between `X` and the string.
  simp [Space.formFin, Y.gram_eq, gradedGram, dotProduct, mulVec, ← Y.indexEquiv.sum_comp,
    stringProj_apply_inl, stringProj_apply_inr, Finset.mul_sum]

/-- A vector `z` of `X^⊥` lies in the intersection `Λ'⁻` of the lattice of `x` with `X^⊥` if and
only if its products with the projection `Λ'⁺` of this lattice to `X^⊥` are integral. -/
lemma mem_latticeMinus_iff_formFin (hz : Y.stringProj z = z) :
    z ∈ Y.latticeMinus x ↔ ∀ y ∈ Y.latticePlus x, V.formFin y z ∈ Ô E := by
  rw [mem_latticeMinus, and_iff_left hz, Space.mem_lattice_iff_formFin]
  simp [mem_latticePlus, formFin_stringProj, hz]

/-- The form of `V` is nondegenerate on `X^⊥`: vectors with the same products against `X^⊥` have the
same projection to `X^⊥`. -/
lemma stringProj_eq_of_formFin_eq {z' : ι → 𝔸f E}
    (h_eq : ∀ y : ι → 𝔸f E, Y.stringProj y = y → V.formFin y z = V.formFin y z') :
    Y.stringProj z = Y.stringProj z' := by
  -- The Gram matrix is invertible, so it suffices to compare the images under it.
  refine mulVec_injective_of_isUnit (V.isUnit_J.map (algebraMap E (𝔸f E)).mapMatrix) (funext
    fun i ↦ ?_)
  have h_form : V.formFin (Pi.single i 1) (Y.stringProj z) =
      V.formFin (Pi.single i 1) (Y.stringProj z') := by
    rw [← formFin_stringProj, ← formFin_stringProj, h_eq _ (stringProj_stringProj _)]
  simpa [Space.formFin] using h_form

variable (Y x) in
omit [Fintype X] in
/-- The space `X^⊥` has a basis `B` that is primitive in the lattice of `x`: read in the frame
`V.xFin * x`, the matrix `B` is integral with an integral left inverse. -/
lemma exists_isPrimitiveMatrix_basis :
    ∃ B : Matrix ι (Fin s) (𝔸f E), IsPrimitiveMatrix (Ô E) ((V.xFin * x.val)⁻¹.val * B) ∧
      ∀ y : ι → 𝔸f E, Y.stringProj y = y ↔ ∃ c : Fin s → 𝔸f E, B *ᵥ c = y := by
  -- The string vectors form a basis `S`. Some invertible `b` makes the coordinates of `S * b` in
  -- the frame of `x` primitive.
  let S : Matrix ι (Fin s) (𝔸f E) := inclMatrix (𝔸f E) fun b ↦ Y.indexEquiv (.inr b)
  have h_left : Sᵀ * S = 1 := by
    ext1 a b
    simp [S, inclMatrix, mul_apply, one_apply, eq_comm]
  have h_proj (y : ι → 𝔸f E) : Y.stringProj y = S *ᵥ Sᵀ *ᵥ y := by
    ext1 i
    obtain ⟨a | a, rfl⟩ := Y.indexEquiv.surjective i <;>
      simp [S, inclMatrix, mulVec, dotProduct, one_apply, stringProj_apply_inl,
        stringProj_apply_inr]
  have h_inv : HasLeftInv ((V.xFin * x.val)⁻¹.val * S) :=
    ⟨Sᵀ * (V.xFin * x.val).val, by simpa [Matrix.mul_assoc] using h_left⟩
  obtain ⟨b, -, hb⟩ := isValuationPair_Ô.exists_isPrimitiveMatrix_mul h_inv
  refine ⟨S * b.val, by rwa [← Matrix.mul_assoc], fun y ↦ ?_⟩
  rw [h_proj, mulVec_mulVec]
  refine ⟨fun hy ↦ ⟨(b⁻¹.val * Sᵀ) *ᵥ y, ?_⟩, ?_⟩
  · simpa [Matrix.mul_assoc] using hy
  · rintro ⟨c, rfl⟩
    simp [← Matrix.mul_assoc, h_left, Matrix.mul_assoc S]

/-- A vector `z` of `X^⊥` lies in the projection `Λ'⁺` of the lattice of `x` to `X^⊥` if and only
if its products with the intersection `Λ'⁻` of this lattice with `X^⊥` are integral. -/
lemma mem_latticePlus_iff_formFin (hz : Y.stringProj z = z) :
    z ∈ Y.latticePlus x ↔ ∀ y ∈ Y.latticeMinus x, V.formFin y z ∈ Ô E := by
  refine ⟨fun hz_mem y hy ↦ ?_, fun h ↦ ?_⟩
  · rw [← Space.star_formFin]
    exact star_mem_Ô ((mem_latticeMinus_iff_formFin (mem_latticeMinus.1 hy).right).1 hy z hz_mem)
  -- The products `t` of `z` with a primitive basis `B` of `X^⊥` are integral. An integral left
  -- inverse `L` of `g⁻¹ B`, for the frame `g` of `x`, gives a vector `w` of the lattice with
  -- the same products.
  obtain ⟨B, hB, hB_span : ∀ y : ι → 𝔸f E, Y.stringProj y = y ↔ ∃ c : Fin s → 𝔸f E, B *ᵥ c = y⟩ :=
    Y.exists_isPrimitiveMatrix_basis x
  set g : GL ι (𝔸f E) := V.xFin * x.val
  obtain ⟨hB_int : IsIntMatrix (Ô E) (g⁻¹.val * B), L, hL_int : IsIntMatrix (Ô E) L,
    hLB : L * (g⁻¹.val * B) = 1⟩ := hB
  let J : Matrix ι ι (𝔸f E) := V.J.map (algebraMap E (𝔸f E))
  have h_basis (c : Fin s → 𝔸f E) (w : ι → 𝔸f E) :
      V.formFin (B *ᵥ c) w = star c ⬝ᵥ (Bᴴ * J) *ᵥ w := by
    rw [Space.formFin, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  let t : Fin s → 𝔸f E := (Bᴴ * J) *ᵥ z
  have ht : t ∈ intVectors (Ô E) (Fin s) := fun j ↦ by
    have h_col : B *ᵥ Pi.single j 1 ∈ Y.latticeMinus x := by
      rw [mem_latticeMinus, Space.mem_lattice, mulVec_mulVec]
      exact ⟨hB_int.mulVec (single_mem_intVectors j), (hB_span _).2 ⟨Pi.single j 1, rfl⟩⟩
    simpa only [h_basis, Pi.star_single, star_one, single_one_dotProduct] using h _ h_col
  let w : ι → 𝔸f E := g.val *ᵥ Lᴴ *ᵥ t
  have hw : w ∈ V.lattice x := Space.mulVec_mem_lattice.2 (hL_int.conjTranspose.mulVec ht)
  have h_gram : g⁻¹.valᴴ * g⁻¹.val = J := Space.gram_frame_inv x
  have h_adj : Bᴴ * J * g.val * Lᴴ = 1 :=
    calc _ = Bᴴ * (g⁻¹.valᴴ * (g⁻¹.val * g.val * Lᴴ)) := by simp only [← h_gram, Matrix.mul_assoc]
      _ = (L * (g⁻¹.val * B))ᴴ := by simp [Matrix.mul_assoc]
      _ = 1 := by rw [hLB, conjTranspose_one]
  have h_products (y : ι → 𝔸f E) (hy : Y.stringProj y = y) : V.formFin y w = V.formFin y z := by
    obtain ⟨c, rfl⟩ := (hB_span y).1 hy
    rw [h_basis, h_basis, mulVec_mulVec, mulVec_mulVec, h_adj, one_mulVec]
  exact mem_latticePlus.2 ⟨w, hw, (stringProj_eq_of_formFin_eq h_products).trans hz⟩

/-- Let `Λ'⁻` and `Λ'⁺` be the intersection with `X^⊥` and the projection to `X^⊥` of the lattice
of `x`. If `c A ⊆ Λ'⁻`, then every vector of `c̄ Λ'⁺` has integral products with the vectors of
`A`. -/
lemma formFin_star_smul_mem {A : Submodule (Ô E) (ι → 𝔸f E)} (h_le : c • A ≤ Y.latticeMinus x)
    (hz : z ∈ Y.latticePlus x) : ∀ y ∈ A, V.formFin y (star c • z) ∈ Ô E := fun y hy ↦ by
  rw [Space.formFin_star_smul]
  exact (mem_latticePlus_iff_formFin (stringProj_eq_of_mem_latticePlus hz)).1 hz _
    (smul_le_iff_forall.1 h_le y hy)

/-- Let `Λ₁⁻`, `Λ₂⁻` be the intersections with `X^⊥` of the lattices of `x`, `x'`, and `Λ₁⁺`,
`Λ₂⁺` their projections to `X^⊥`. An inclusion `c Λ₁⁻ ⊆ Λ₂⁻` gives `c̄ Λ₂⁺ ⊆ Λ₁⁺` by duality. -/
lemma star_smul_latticePlus_le (h_le : c • Y.latticeMinus x ≤ Y.latticeMinus x') :
    star c • Y.latticePlus x' ≤ Y.latticePlus x :=
  smul_le_iff_forall.2 fun _ hz ↦ (mem_latticePlus_iff_formFin
    (stringProj_smul_of_mem_latticePlus hz)).2 (formFin_star_smul_mem h_le hz)

/-- Let `Λ'⁻` and `Λ'⁺` be the intersection with `X^⊥` and the projection to `X^⊥` of the lattice
of `x`. An inclusion `c Λ'⁺ ⊆ Λ'⁻` gives `c̄ Λ'⁺ ⊆ Λ'⁻` by duality. -/
lemma star_smul_latticePlus_le_latticeMinus (h_le : c • Y.latticePlus x ≤ Y.latticeMinus x) :
    star c • Y.latticePlus x ≤ Y.latticeMinus x :=
  smul_le_iff_forall.2 fun _ hz ↦ (mem_latticeMinus_iff_formFin
    (stringProj_smul_of_mem_latticePlus hz)).2 (formFin_star_smul_mem h_le hz)

/-- A finite point `g` whose matrix `V.ratCoordMatrixFin g` in rational coordinates fixes `X^⊥`
(the span of the string) pointwise is in the image of the embedding `Y.inclXFin` of the unitary
group of `X`. -/
lemma exists_inclXFin_eq_of_mulVec_eq {g : Gf E ι}
    (hg : ∀ y : ι → 𝔸f E, Y.stringProj y = y → V.ratCoordMatrixFin g *ᵥ y = y) :
    ∃ a : Gf E X, Y.inclXFin a = g := by
  -- The matrix `M` of `g` is an isometry and is the identity on `X^⊥`, so it is block diagonal
  -- with an isometry `A` of `X` in the first block.
  let M : Matrix ι ι (𝔸f E) := V.ratCoordMatrixFin g
  -- For `y` in `X^⊥` we have `⟨y, M z⟩ = ⟨M y, M z⟩ = ⟨y, z⟩`, so `M z - z` lies in `X`.
  have h_proj (z : ι → 𝔸f E) : Y.stringProj (M *ᵥ z) = Y.stringProj z := by
    refine stringProj_eq_of_formFin_eq fun y hy ↦ ?_
    calc V.formFin y (M *ᵥ z) = V.formFin (M *ᵥ y) (M *ᵥ z) := by rw [hg y hy]
      _ = V.formFin y z := by
        rw [Space.formFin, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec,
          Space.ratCoordMatrixFin_isometry, Space.formFin]
  let A : Matrix X X (𝔸f E) := of fun a b ↦ M (Y.indexEquiv (.inl a)) (Y.indexEquiv (.inl b))
  have h_row (a : Fin s) (j : ι) :
      M (Y.indexEquiv (.inr a)) j = (1 : Matrix ι ι (𝔸f E)) (Y.indexEquiv (.inr a)) j := by
    simpa [stringProj_apply_inr, one_apply, Pi.single_apply] using
      congrFun (h_proj (Pi.single j 1)) (Y.indexEquiv (.inr a))
  have h_col (i : ι) (b : Fin s) :
      M i (Y.indexEquiv (.inr b)) = (1 : Matrix ι ι (𝔸f E)) i (Y.indexEquiv (.inr b)) := by
    simpa [one_apply, Pi.single_apply] using congrFun
      (hg (Pi.single (Y.indexEquiv (.inr b)) 1) (stringProj_eq_self_iff.2 (by simp))) i
  have h_blocks : M = gradedBlocks Y.indexEquiv Y.indexEquiv A 1 := by
    ext1 i j
    obtain ⟨i' | i', rfl⟩ := Y.indexEquiv.surjective i <;>
      obtain ⟨j' | j', rfl⟩ := Y.indexEquiv.surjective j <;> simp [A, h_row, h_col, one_apply]
  have hA : Aᴴ * 1 * A = 1 := by
    have h_isom := Space.ratCoordMatrixFin_isometry (V := V) g
    rw [show V.ratCoordMatrixFin g = _ from h_blocks, Y.gram_eq] at h_isom
    -- Read off the block of `X`, on which the form is standard (the Gram matrix is `1`).
    simpa [gradedGram, ← submatrix_map, fromBlocks_map, submatrix_mul_equiv, fromBlocks_multiply,
      fromBlocks_conjTranspose] using
      congrArg (fun Z ↦ (Z.submatrix Y.indexEquiv Y.indexEquiv).toBlocks₁₁) h_isom
  let a : Gf E X := ⟨(Units.mkOfMulEqOne (Aᴴ * 1) A hA)⁻¹, hA⟩
  -- The points have the same matrix, and conjugation by `V.xFin` is injective.
  exact ⟨a, Subtype.ext (mul_left_cancel (mul_right_cancel (b := V.xFin⁻¹) (Units.ext
    ((Y.ratCoordMatrixFin_inclXFin a).trans h_blocks.symm))))⟩

/-- Assume that `E` contains a primitive root of unity of order 5040
(`[HasPrimitiveRoot5040 E]`). If the lattices of two points have the same intersection with
`X^⊥`, then some finite point `a` of the unitary group of `X`, embedded by `Y.inclXFin` in that of
`V`, carries one lattice to the other. -/
lemma exists_lattice_inclXFin_mul_eq [HasPrimitiveRoot5040 E]
    (h_minus : Y.latticeMinus x = Y.latticeMinus x') :
    ∃ a : Gf E X, V.lattice (Y.inclXFin a * x) = V.lattice x' := by
  -- A basis `B` of `X^⊥` that is primitive for `x` spans the common intersection, so it is
  -- primitive for `x'`. Witt's theorem over `Ô` gives `k` that carries the coordinates of `B` for
  -- `x` to those for `x'`, so `x' * k * x⁻¹` fixes `B`.
  obtain ⟨B, hB, hB_span⟩ := Y.exists_isPrimitiveMatrix_basis x
  let T (u : Gf E ι) : Matrix ι (Fin s) (𝔸f E) := (V.xFin * u.val)⁻¹.val * B
  have h_mem (u : Gf E ι) (c : Fin s → 𝔸f E) :
      B *ᵥ c ∈ Y.latticeMinus u ↔ ∀ i : ι, (T u *ᵥ c) i ∈ Ô E := by
    simp only [T, mem_latticeMinus, and_iff_left ((hB_span _).2 ⟨c, rfl⟩), Space.mem_lattice,
      mulVec_mulVec]
  have hB' : IsPrimitiveMatrix (Ô E) (T x') := by
    obtain ⟨hB_int, L, hL_int, hLB : L * T x = 1⟩ := hB
    have h_inv : HasLeftInv (T x') := ⟨L * (V.xFin * x.val)⁻¹.val * (V.xFin * x'.val).val,
      by simpa [T, Matrix.mul_assoc] using hLB⟩
    refine isPrimitiveMatrix_of_mulVec_mem_iff h_inv fun c ↦ ?_
    rw [← h_mem, ← h_minus, h_mem]
    exact ⟨fun hc j ↦ by simpa [hLB] using hL_int.mulVec hc j, hB_int.mulVec⟩
  have h_gram (u : Gf E ι) : (T u)ᴴ * T u = Bᴴ * V.J.map (algebraMap E (𝔸f E)) * B := by
    simp only [T, ← Space.gram_frame_inv u, conjTranspose_mul, Matrix.mul_assoc]
  obtain ⟨k, hk, hkB⟩ : ∃ k ∈ stdLevel E ι, k.val.val * T x = T x' :=
    witt_Ô hB hB' ((h_gram x).trans (h_gram x').symm)
  have h_fix : V.ratCoordMatrixFin (x' * k * x⁻¹) * B = B :=
    calc V.ratCoordMatrixFin (x' * k * x⁻¹) * B = (V.xFin * x'.val).val * (k.val.val * T x) := by
          simp [T, Space.ratCoordMatrixFin, Matrix.mul_assoc]
      _ = B := by rw [hkB, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  obtain ⟨a, ha⟩ : ∃ a : Gf E X, Y.inclXFin a = x' * k * x⁻¹ := by
    refine exists_inclXFin_eq_of_mulVec_eq fun y hy ↦ ?_
    obtain ⟨c, rfl⟩ := (hB_span y).1 hy
    rw [mulVec_mulVec, h_fix]
  refine ⟨a, (Space.lattice_eq_iff.2 ?_).symm⟩
  rwa [ha, inv_mul_cancel_right, inv_mul_cancel_left]

end Grading

end New

end
