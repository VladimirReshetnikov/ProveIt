import New.Spanning.RemainingTerms.Data
import New.Spanning.RemainingTerms.FrameCount

/-!
# The part in `X₀` of a frame, moves, and lifts of a lattice

The lemmas that are used to count, round by round, the frames over a lattice `L ⊆ Λ ∩ X₀`, where `Λ`
is the lattice of a class. A move is a unipotent element of the congruence level `M` that fixes the
standard frame. For a term, `Ξ₀` consists of the first `ϱ` rows of the matrix of products, and `δ`
is the leading minor of that matrix whose order is the cell rank of the term.

Notions from other files:
* The frame is `e₁, …, e_ϱ, z`, `A` is the isotropic space spanned by the `e_i`, and `X₀` is the
  space with the indices `𝔰.κ`; `frameMiddle` takes the coordinates in `X₀ ⊕ Ez` of a frame.
* `frameProducts γ` is the matrix of products of the frame with its image under `γ`.
* `translateByClassReps c c' γ` is `h_c⁻¹ γ h_c'`, and `γ ∈ termsOver c s c'` says that it
  stabilises the standard lattice and has the reduction `s`.
* `classCoordX₀ c` gives the coordinates of vectors of `X₀` in the lattice `Λ` of the class `c`;
  `classLatticeX₀ c` is `Λ ∩ X₀`.
* `termLattice c c' γ` consists of the vectors `v` of `Λ ∩ X₀` such that some vector of
  `v + M (Λ ∩ A)` is orthogonal to the frame of `γ`.

## Main definitions and results

* `New.Filling.exists_framePartX₀_mul_eq_sub_smul`: every row `η` of vectors of `Λ ∩ X₀` gives a
  move, which subtracts `M η Ξ₀` from the part in `X₀` of a frame.
* `New.Filling.exists_isLift`, `New.Filling.exists_conjTranspose_mul_eq_of_row_mem`: if `L` lies in
  the lattice of a term, it lifts linearly to vectors orthogonal to the frame; two lifts in one
  coset of the products with vectors of `L` differ by the products with a rational row `η`.
* `New.Filling.complementLattice`: the lattice `P = Λ ∩ X₀ ∩ L^⊥`, which has the corank of `L` as
  its rank.
* `New.Filling.HasCellRank.exists_framePartX₀_sub_eq`: parts in `X₀` that are congruent modulo
  `M δ` differ by `M η Ξ₀`.
-/

namespace New.Filling

open NumberField Matrix Module Fintype ENNReal Pointwise

variable {E : Type} [Field E] [CMType E]

/-! ## Matrices and lattices over the finite adeles -/

lemma finAdeleMatrix_mul {l m n : Type} [Fintype m] (A : Matrix l m E) (B : Matrix m n E) :
    finAdeleMatrix (A * B) = finAdeleMatrix A * finAdeleMatrix B :=
  Matrix.map_mul (f := algebraMap E (𝔸f E))

lemma finAdeleMatrix_add {m n : Type} (A B : Matrix m n E) :
    finAdeleMatrix (A + B) = finAdeleMatrix A + finAdeleMatrix B :=
  Matrix.map_add _ (map_add (algebraMap E (𝔸f E))) A B

/-- A linear system `M w = T` over `E` that has a solution `s` over the finite adeles
(`finAdeleMatrix` reads a rational matrix there) has rational solutions near `s`: every open set
that contains `s` contains one. -/
lemma exists_mul_eq_of_finAdeleMatrix_mul_eq {m n ι : Type} [Fintype m] [Fintype n]
    {M : Matrix m n E}
    {T : Matrix m ι E} {U : Set (Matrix n ι (𝔸f E))} (hU : IsOpen U) {s : Matrix n ι (𝔸f E)}
    (hs : s ∈ U) (h_solves : finAdeleMatrix M * s = finAdeleMatrix T) :
    ∃ w : Matrix n ι E, finAdeleMatrix w ∈ U ∧ M * w = T := by
  -- Take a basis `y` of the kernel of `M` and write `1 = y e + b M`. The solutions are the matrices
  -- `y t + b T`, and `t` can be approximated by a rational matrix.
  classical
  let d : ℕ := finrank E M.mulVecLin.ker
  obtain ⟨y, -, hy⟩ : ∃ y : Matrix n (Fin d) E, HasLeftInv y ∧ colSpan y = M.mulVecLin.ker :=
    exists_hasLeftInv_colSpan_eq M.mulVecLin.ker
  obtain ⟨e, b, h_one⟩ : ∃ (e : Matrix (Fin d) n E) (b : Matrix n m E), y * e + b * M = 1 :=
    exists_mul_add_mul_eq_one hy.ge
  have h_ker : M * y = 0 := mul_eq_zero_of_colSpan_le_ker hy.le
  have h_split : finAdeleMatrix y * (finAdeleMatrix e * s) + finAdeleMatrix (b * T) = s :=
    calc finAdeleMatrix y * (finAdeleMatrix e * s) + finAdeleMatrix (b * T)
        = finAdeleMatrix (y * e + b * M) * s := by
          rw [finAdeleMatrix_mul b T, ← h_solves]
          simp [finAdeleMatrix_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = s := by simp [h_one]
  have h_special : M * (b * T) = T := by
    apply Matrix.map_injective (algebraMap E (𝔸f E)).injective
    calc finAdeleMatrix (M * (b * T))
        = finAdeleMatrix M *
          (finAdeleMatrix y * (finAdeleMatrix e * s) + finAdeleMatrix (b * T)) := by
          rw [Matrix.mul_add, ← Matrix.mul_assoc (finAdeleMatrix M), ← finAdeleMatrix_mul,
            ← finAdeleMatrix_mul, h_ker]
          simp
      _ = finAdeleMatrix T := by rw [h_split, h_solves]
  let V : Set (Matrix (Fin d) ι (𝔸f E)) := {t | finAdeleMatrix y * t + finAdeleMatrix (b * T) ∈ U}
  have h_mem : finAdeleMatrix e * s ∈ V := by rwa [Set.mem_ofPred_eq, h_split]
  have h_dense : DenseRange (finAdeleMatrix : Matrix (Fin d) ι E → Matrix (Fin d) ι (𝔸f E)) :=
    .piMap fun _ ↦ .piMap fun _ ↦ denseRange_algebraMap_finAdele
  obtain ⟨t, ht⟩ : ∃ t : Matrix (Fin d) ι E, finAdeleMatrix t ∈ V :=
    h_dense.exists_mem_open (hU.preimage (by fun_prop)) ⟨finAdeleMatrix e * s, h_mem⟩
  refine ⟨y * t + b * T, ?_, ?_⟩
  · rwa [finAdeleMatrix_add, finAdeleMatrix_mul]
  · rw [Matrix.mul_add, ← Matrix.mul_assoc, h_ker, Matrix.zero_mul, zero_add, h_special]

/-- A matrix whose columns lie in the column lattice of `ξ` is `ξ` times an integral matrix. -/
lemma exists_isIntMatrix_mul_eq_of_col_mem {σ τ ι : Type} [Fintype ι] {M : Matrix σ τ (𝔸f E)}
    {ξ : Matrix σ ι (𝔸f E)} (h_col : ∀ j : τ, M.col j ∈ colLattice (Ô E) ξ) :
    ∃ W : Matrix ι τ (𝔸f E), IsIntMatrix (Ô E) W ∧ ξ * W = M := by
  obtain ⟨w, hw⟩ : ∃ w : τ → ι → 𝔸f E, ∀ j : τ, w j ∈ intVectors (Ô E) ι ∧ ξ *ᵥ w j = M.col j :=
    Classical.skolem.1 h_col
  exact ⟨(of w)ᵀ, fun i j ↦ (hw j).left i, Matrix.ext fun i j ↦ congrFun (hw j).right i⟩

/-- Scaling a matrix by an idele scales the lattice spanned by its columns. -/
lemma colLattice_smul {σ ι : Type} [Fintype ι] (a : (𝔸f E)ˣ) (M : Matrix σ ι (𝔸f E)) :
    colLattice (Ô E) (a • M) = a • colLattice (Ô E) M := by
  ext w
  simp [colLattice, Submodule.mem_smul_pointwise_iff_exists, Units.smul_def]

/-- Multiplication by an adelic matrix with a left inverse is injective. -/
lemma injective_restrictScalars_mulVecLin {κ τ : Type} [Fintype κ] [Fintype τ] [DecidableEq τ]
    {m : Matrix κ τ (𝔸f E)} {l : Matrix τ κ (𝔸f E)} (hl : l * m = 1) :
    Function.Injective (m.mulVecLin.restrictScalars (Ô E)) :=
  Function.LeftInverse.injective (g := l.mulVec) fun v ↦ by simp [hl]

/-- Let the idele `d` be the nonzero number `δ`. If the columns of the rational matrix `v` lie in
`d` times the lattice of the vectors that `H` makes integral, then `H` makes `δ⁻¹ v` integral. -/
lemma isIntMatrix_mul_finAdeleMatrix_inv_smul {σ κ n : Type} [Fintype κ] {H : Matrix σ κ (𝔸f E)}
    {v : Matrix κ n E} {δ : E} (hδ : δ ≠ 0) {d : (𝔸f E)ˣ} (hd : d.val = δ)
    (h_mem : ∀ i : n, ((↑) : E → 𝔸f E) ∘ v.col i ∈ d • preimageLattice (Ô E) H) :
    IsIntMatrix (Ô E) (H * finAdeleMatrix (δ⁻¹ • v)) := by
  intro r i
  obtain ⟨x, hx, h_multiple⟩ := h_mem i
  have h_col : (finAdeleMatrix (δ⁻¹ • v)).col i = x := by
    funext a
    have h_entry : d.val * x a = v a i := congrFun h_multiple a
    change ((δ⁻¹ * v a i : E) : 𝔸f E) = x a
    rw [map_mul, ← h_entry, hd, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hδ, map_one, one_mul]
  change (H *ᵥ (finAdeleMatrix (δ⁻¹ • v)).col i) r ∈ Ô E
  rw [h_col]
  exact hx r

variable [HasPrimitiveRoot5040 E] {𝔰 : Shape} {S : Filling E 𝔰}

/-- Let `m` have a left inverse, and let `A` be invertible over the finite adeles, with integral
entries. Then the lattice spanned by the columns of `m A` has index `[det A]`, the generalised
index, in the lattice spanned by the columns of `m`. -/
lemma submoduleIndex_colLattice_mul {κ τ : Type} [Fintype κ] [Fintype τ] [DecidableEq τ]
    {m : Matrix κ τ (𝔸f E)} (hm : HasLeftInv m) {A : GL τ (𝔸f E)} (hA : IsIntMatrix (Ô E) A.val) :
    submoduleIndex (colLattice (Ô E) (m * A.val)) (colLattice (Ô E) m) = genIndex A.val.det := by
  obtain ⟨l, hl⟩ := hm
  have h_inj : Function.Injective (m.mulVecLin.restrictScalars (Ô E)).toAddMonoidHom :=
    injective_restrictScalars_mulVecLin hl
  have h_unfold : colLattice (Ô E) m =
      (intVectors (Ô E) τ).map (m.mulVecLin.restrictScalars (Ô E)) := rfl
  rw [← submoduleIndex_colLattice_intVectors hA, colLattice_mul, h_unfold, submoduleIndex,
    Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact congrArg Nat.cast (AddSubgroup.relIndex_map_map_of_injective _ _ h_inj)

/-- Let the columns of the rational matrix `y` be independent, and let `L` be the lattice with the
basis `B = y a`, where `Bᴴ B` is integral. The rows of the products of `B` with the vectors of `L`
are the integral combinations of the rows of `Bᴴ B`. Their index among all integral rows, that is
the index of `L` in its dual lattice, is the square of `discriminant r L`, which is by definition
the square root of the generalised index of the Gram determinant `det (Bᴴ B)`. -/
lemma submoduleIndex_colLattice_gram_transpose {κ : Type} [Fintype κ] [DecidableEq κ] {r : ℕ}
    {y : Matrix κ (Fin r) E} (hy : HasLeftInv y) (a : GL (Fin r) (𝔸f E))
    (h_int : IsIntMatrix (Ô E) ((finAdeleMatrix y * a.val)ᴴ * (finAdeleMatrix y * a.val))) :
    (submoduleIndex (colLattice (Ô E) ((finAdeleMatrix y * a.val)ᴴ * (finAdeleMatrix y * a.val))ᵀ)
        (intVectors (Ô E) (Fin r)) : ℝ) =
      discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ^ 2 := by
  have h_disc_pos : 0 < discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) :=
    IsLatticeOfRank.discriminant_pos ⟨y, a, hy, rfl⟩
  rw [discriminant_colLattice hy] at h_disc_pos ⊢
  set Γ : Matrix (Fin r) (Fin r) (𝔸f E) := (finAdeleMatrix y * a.val)ᴴ * (finAdeleMatrix y * a.val)
  have h_pos : 0 < genIndex Γ.det := Real.sqrt_pos.1 h_disc_pos
  obtain ⟨G, hG⟩ : IsUnit Γᵀ := (isUnit_transpose Γ).2
    ((isUnit_iff_isUnit_det Γ).2 (genIndex.apply_ne_zero_iff.1 h_pos.ne'))
  have hG_int : IsIntMatrix (Ô E) G.val := by
    rw [hG]
    exact h_int.transpose
  rw [Real.sq_sqrt h_pos.le, ← hG, submoduleIndex_colLattice_intVectors hG_int, hG, det_transpose]

section Saturated

variable {κ P : Type} [Fintype κ] [DecidableEq κ] [Fintype P] {H' : Matrix κ P (𝔸f E)}
  {H : Matrix P κ (𝔸f E)}

/-- Let the adelic matrix `H` have a left inverse. A rational vector of the subspace `V` that `H`
makes integral lies in the saturated lattice of `V`, the lattice of the vectors in the adelic span
of `V` that `H` makes integral. -/
lemma coe_mem_saturatedLattice (h_inv : H' * H = 1) {V : Submodule E (κ → E)} {v : κ → E}
    (hv : v ∈ V) (hv_int : ((↑) : E → 𝔸f E) ∘ v ∈ preimageLattice (Ô E) H) :
    ((↑) : E → 𝔸f E) ∘ v ∈ saturatedLattice h_inv V := by
  classical
  -- The vector has coordinates `s` in the basis `m` of the saturated lattice. They are integral,
  -- since `H m` has an integral left inverse `p`.
  let m : Matrix κ (Fin (finrank E V)) (𝔸f E) := (sublatticeBasis h_inv V).val
  obtain ⟨⟨-, p, hp_int, hp⟩, y, a, -, hy, hm⟩ : IsPrimitiveMatrix (Ô E) (H * m) ∧
      ∃ᵉ (y : Matrix κ (Fin (finrank E V)) E) (a : GL (Fin (finrank E V)) (𝔸f E)),
        HasLeftInv y ∧ colSpan y = V ∧ m = finAdeleMatrix y * a.val :=
    (sublatticeBasis h_inv V).property
  obtain ⟨t, rfl⟩ : ∃ t : Fin (finrank E V) → E, y *ᵥ t = v := hy.ge hv
  obtain ⟨s, hs⟩ : ∃ s : Fin (finrank E V) → 𝔸f E, m *ᵥ s = ((↑) : E → 𝔸f E) ∘ (y *ᵥ t) :=
    ⟨a⁻¹.val *ᵥ (((↑) : E → 𝔸f E) ∘ t), funext fun i ↦ by
      simp [hm, Matrix.mul_assoc, (algebraMap E (𝔸f E)).map_mulVec]⟩
  have hs_int : p *ᵥ H *ᵥ m *ᵥ s ∈ intVectors (Ô E) (Fin (finrank E V)) := by
    rw [hs]
    exact hp_int.mulVec hv_int
  rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hp, one_mulVec] at hs_int
  exact ⟨s, hs_int, hs⟩

/-- Let the adelic matrix `H` have the left inverse `H'`, and let `Λ` be the saturated lattice of
the subspace `V`, the lattice of the vectors in the adelic span of `V` that `H` makes integral. For
a finite idele `d` in `Ô`, the index of `d Λ` in `Λ` as additive groups is `[d] ^ dim V`. Here
`[d] = genIndex d` is the generalised index, the inverse of the factor by which `d` scales Haar
measure on the finite adeles. -/
lemma submoduleIndex_smul_saturatedLattice (h_inv : H' * H = 1) (V : Submodule E (κ → E))
    {d : (𝔸f E)ˣ} (hd : d.val ∈ Ô E) :
    (submoduleIndex (d • saturatedLattice h_inv V) (saturatedLattice h_inv V) : ℝ) =
      genIndex d.val ^ finrank E V := by
  -- If `m` is the basis of `Λ`, then `d Λ` has the basis `m A`, with `A` the scalar matrix of `d`.
  let m : Matrix κ (Fin (finrank E V)) (𝔸f E) := (sublatticeBasis h_inv V).val
  let A : GL (Fin (finrank E V)) (𝔸f E) := d • 1
  obtain ⟨p, -, hp : p * (H * m) = 1⟩ := (isPrimitiveMatrix_mul_sublatticeBasis h_inv V).right
  have hm : HasLeftInv m := ⟨p * H, by rw [Matrix.mul_assoc, hp]⟩
  have hA : A.val = d.val • 1 := rfl
  have h_basis : d • saturatedLattice h_inv V = colLattice (Ô E) (m * A.val) := by
    rw [hA, Matrix.mul_smul, Matrix.mul_one, saturatedLattice, ← colLattice_smul, Units.smul_def]
  calc (submoduleIndex (d • saturatedLattice h_inv V) (saturatedLattice h_inv V) : ℝ)
      = genIndex A.val.det := by
        rw [h_basis]
        exact submoduleIndex_colLattice_mul hm (.smul hd .one)
    _ = genIndex d.val ^ finrank E V := by simp [hA]

end Saturated

/-! ## The part in `X₀` of a frame, and moves -/

/-- The part in `X₀` of the frame of `γ`: the coordinates at the indices `𝔰.κ` of the images of the
frame vectors. -/
def framePartX₀ (γ : S.G E) : Matrix 𝔰.κ (Fin (𝔰.ϱ + 1)) E := (frameMiddle γ.val.val).toRows₁

omit [HasPrimitiveRoot5040 E] in
/-- The product of an isotropic frame vector with the image of a frame vector is the coordinate of
the image at the dual isotropic vector. -/
lemma frameProducts_castSucc_apply (γ : S.G E) (i : Fin 𝔰.ϱ) (a : Fin (𝔰.ϱ + 1)) :
    S.frameProducts γ i.castSucc a = γ.val.val (.inr (.inr i)) (𝔰.besselFrame a) := by
  simp [frameGram, Matrix.mul_apply]

omit [HasPrimitiveRoot5040 E] in
/-- The product of `z` with the image of a frame vector is `-N` times the coordinate of the image
along `z`. -/
lemma frameProducts_top_apply (γ : S.G E) (a : Fin (𝔰.ϱ + 1)) :
    S.frameProducts γ 𝔰.top a = -(S.N : E) * γ.val.val 𝔰.z (𝔰.besselFrame a) := by
  simp [frameGram, Shape.Form.splitGram, Shape.middleGram, Matrix.mul_apply]

omit [HasPrimitiveRoot5040 E] in
/-- Two frames with the same products and the same part in `X₀` agree outside the isotropic
space. -/
lemma apply_inr_besselFrame_eq {γ γ' : S.G E} (hZ : S.frameProducts γ' = S.frameProducts γ)
    (h_part : framePartX₀ γ' = framePartX₀ γ) (i : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) (a : Fin (𝔰.ϱ + 1)) :
    γ'.val (.inr i) (𝔰.besselFrame a) = γ.val (.inr i) (𝔰.besselFrame a) := by
  rcases i with (i | i) | i
  · exact congrFun₂ h_part i a
  · simpa [frameProducts_top_apply, S.N_prime.ne_zero] using congrFun₂ hZ 𝔰.top a
  · simpa [frameProducts_castSucc_apply] using congrFun₂ hZ i.castSucc a

/-- Let `E` contain a primitive 5040th root of unity, let `S` be a filling of shape `𝔰` with the
congruence level `M = S.M`, and let the `ϱ` columns of `η` be rational vectors of `Λ ∩ X₀`. Then
there is a move `u`, that is, a rational unipotent element of level `M` for `Λ` that fixes the
standard frame, with the following property. For every `γ`, the coordinates in `X₀` of the frame of
`u γ` (`framePartX₀`) are those of the frame of `γ` minus `M η Ξ₀`. -/
lemma exists_framePartX₀_mul_eq_sub_smul (c : S.Classes) {η : Matrix 𝔰.κ (Fin 𝔰.ϱ) E}
    (hη : IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix η)) :
    ∃ u ∈ S.classUnipotent₀ c, ∀ γ : S.G E,
      framePartX₀ (u * γ) = framePartX₀ γ - (S.M : E) •
        (η * isotropicRows (S.frameProducts γ)) := by
  -- The Eichler map made from `η` fixes the standard frame, as `η` is orthogonal to it.
  let v : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) E := fromRows 0 ((η.fromRows 0).fromRows 0)
  let x : Matrix 𝔰.BesselIndex (Fin 𝔰.ϱ) E := inclMatrix E Sum.inl
  have hv_int : IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix v) := by
    simpa [v, classCoord_eq_fromBlocks, IsIntMatrix, mul_apply] using hη
  have hv_frame (b : Fin 𝔰.ϱ) (a : Fin (𝔰.ϱ + 1)) :
      (vᴴ * S.ratGram) b (𝔰.besselFrame a) = 0 := by
    cases a using Fin.lastCases <;> simp [v, Shape.Form.splitGram, Shape.middleGram, mul_apply]
  obtain ⟨u, -, hu, τ, hu_eq⟩ : ∃ u ∈ S.classUnipotent c,
      ((∀ (b : Fin 𝔰.ϱ) (a : Fin (𝔰.ϱ + 1)), (vᴴ * S.ratGram) b (𝔰.besselFrame a) = 0) →
        u ∈ S.classUnipotent₀ c) ∧
      ∃ τ : E, u.val.val = 1 + (S.M : E) •
        (x * (vᴴ * S.ratGram) - (v + x * (τ • (vᴴ * S.ratGram * v) - 0)) * (xᴴ * S.ratGram)) :=
    S.exists_mem_classUnipotent_eq_one_add_smul c id v 0 (by simp [v]) (by simp) hv_int
      (by simp [IsIntMatrix]) rfl
  refine ⟨u, hu hv_frame, fun γ ↦ Matrix.ext fun i b ↦ ?_⟩
  -- In the coordinates of `X₀` the rows of `x` vanish, and those of `v` are those of `η`.
  change (u.val.val * frameImage γ.val.val) (𝔰.indexX₀ i) b =
    (framePartX₀ γ - (S.M : E) • (η * isotropicRows (S.frameProducts γ))) i b
  have h_products :
      xᴴ * (S.ratGram * frameImage γ.val.val) = isotropicRows (S.frameProducts γ) := by
    rw [← Matrix.mul_assoc, inclMatrix_conjTranspose_mul_frameImage]
  simp only [hu_eq, Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc,
    Matrix.one_mul, h_products]
  simp [x, v, framePartX₀, frameMiddle, inclMatrix, mul_apply, sub_eq_add_neg]

omit [HasPrimitiveRoot5040 E] in
/-- The middle part of the frame of the translate by class representatives `h_c⁻¹ γ h_c'`, in the
coordinates of the lattice of the class `c`: the part in `X₀` is carried over by `S.classCoordX₀ c`,
and the part along `z` stays. -/
lemma frameMiddle_translateByClassReps (c c' : S.Classes) (γ : S.G E) :
    frameMiddle (S.translateByClassReps c c' γ).val.val =
      (S.classCoordX₀ c).fromCols (fromRows 0 (1 : Matrix Unit Unit (𝔸f E))) *
        finAdeleMatrix (frameMiddle γ.val.val) := by
  refine Matrix.ext fun i b ↦ ?_
  simp [frameMiddle, frameImage_translateByClassReps, classCoord_eq_fromBlocks, mul_apply]

omit [HasPrimitiveRoot5040 E] in
/-- The `frameMiddle` of the translate gives the coordinates in `X₀ ⊕ Ez` of the image of the frame
under `γ`, in the basis of the lattice `h_c Λ₀` of `c`. Take the products of these vectors with the
columns of `S.classCoordX₀ c`, using the Gram matrix `S.latticeMiddle (𝔸f E)` of `X₀ ⊕ Ez` in the
lattice basis. They equal the conjugate transpose of `framePartX₀ γ`, the coordinates in `X₀` of
that image, embedded in the finite adeles. -/
lemma frameMiddle_translateByClassReps_mul_classCoordX₀ (c c' : S.Classes) (γ : S.G E) :
    (frameMiddle (S.translateByClassReps c c' γ).val.val)ᴴ * S.latticeMiddle (𝔸f E) *
        S.classCoordX₀ c =
      (finAdeleMatrix (framePartX₀ γ))ᴴ := by
  -- The basis of `X₀` is orthonormal and orthogonal to `z`.
  have h_gram : ((S.classCoordX₀ c).fromCols (fromRows 0 (1 : Matrix Unit Unit (𝔸f E))))ᴴ *
      S.latticeMiddle (𝔸f E) * S.classCoordX₀ c = (S.ratMiddle (𝔸f E)).toCols₁ := by
    refine Matrix.ext fun i k ↦ ?_
    have h_entry : ((S.classCoord c)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram * S.classCoord c)
        (.inr (.inl i)) (𝔰.indexX₀ k) =
          (S.ratMiddle (𝔸f E)).splitGram (.inr (.inl i)) (𝔰.indexX₀ k) :=
      congrFun₂ (classCoord_conj_splitGram c) _ _
    simpa [classCoord_eq_fromBlocks, splitGram, fromBlocks_conjTranspose, fromBlocks_multiply] using
      h_entry
  rw [frameMiddle_translateByClassReps, conjTranspose_mul,
    Matrix.mul_assoc _ _ (S.latticeMiddle (𝔸f E)),
    Matrix.mul_assoc, h_gram]
  refine Matrix.ext fun b k ↦ ?_
  simp [framePartX₀, middleGram, mul_apply, Matrix.one_apply]

omit [HasPrimitiveRoot5040 E] in
/-- Let `Λ` be the lattice of the class `c`. The parts in `X₀` of two frames of terms over `c` with
the same matrix of products differ by vectors of `Λ ∩ X₀`. -/
lemma col_framePartX₀_sub_mem {c c' c'' : S.Classes} {s s' : S.ResidueGL} {γ γ' : S.G E}
    (h_over : γ ∈ S.termsOver c s c') (h_over' : γ' ∈ S.termsOver c s' c'')
    (hZ : S.frameProducts γ' = S.frameProducts γ) (i : Fin (𝔰.ϱ + 1)) :
    ((↑) : E → 𝔸f E) ∘ (framePartX₀ γ' - framePartX₀ γ).col i ∈ S.classLatticeX₀ c := by
  -- Both frames lie in `Λ`, and they have the same part along `z`.
  have hz_eq : γ'.val.val 𝔰.z (𝔰.besselFrame i) = γ.val.val 𝔰.z (𝔰.besselFrame i) := by
    simpa [frameProducts_top_apply, S.N_prime.ne_zero] using congrFun₂ hZ 𝔰.top i
  intro k
  have h_entry : (S.classCoordX₀ c *ᵥ ((↑) : E → 𝔸f E) ∘ (framePartX₀ γ' - framePartX₀ γ).col i) k =
      frameMiddle (S.translateByClassReps c c'' γ').val.val k i -
        frameMiddle (S.translateByClassReps c c' γ).val.val k i := by
    rw [frameMiddle_translateByClassReps, frameMiddle_translateByClassReps]
    simp [framePartX₀, hz_eq, mul_apply, mulVec, dotProduct, mul_sub]
  change (S.classCoordX₀ c *ᵥ ((↑) : E → 𝔸f E) ∘ (framePartX₀ γ' - framePartX₀ γ).col i) k ∈ Ô E
  rw [h_entry]
  exact sub_mem (termsOver.isIntMatrix_translateByClassReps h_over' _ _)
    (termsOver.isIntMatrix_translateByClassReps h_over _ _)

/-! ## Lifts of a lattice -/

/-- Let `L` be the lattice with the basis `y a`, where `y` is rational and `a` is adelic, let
`e_1, …, e_ϱ` be the basis of the isotropic space `A` and of the lattice `Λ ∩ A`, and let `M = S.M`.
The matrix `w` gives a linear map from `L` to `M (Λ ∩ A)`, namely `y t ↦ M ∑ e_i (w t)_i`, such that
each vector of `L` plus its image is orthogonal to the frame of `γ`. -/
structure IsLift {r : ℕ} (γ : S.G E) (y : Matrix 𝔰.κ (Fin r) E) (a : GL (Fin r) (𝔸f E))
    (w : Matrix (Fin 𝔰.ϱ) (Fin r) E) : Prop where
  /-- The map takes the basis `y a` into `M (Λ ∩ A)`. -/
  isIntMatrix : IsIntMatrix (Ô E) (finAdeleMatrix w * a.val)
  /-- The lifted vectors are orthogonal to the frame of `γ`. -/
  orthogonal : (framePartX₀ γ)ᴴ * y + (S.M : E) • ((isotropicRows (S.frameProducts γ))ᴴ * w) = 0

omit [HasPrimitiveRoot5040 E] in
/-- The lattice `L_γ = S.termLattice c c' γ` consists of the vectors `v` of `Λ ∩ X₀` such that some
vector of `v + M (Λ ∩ A)` is orthogonal to the frame of `γ`. If the lattice spanned by the columns
of `y a` lies in `L_γ`, then it has a rational lift: a linear map to `M (Λ ∩ A)`, given by a
rational matrix `w`, such that each vector plus its image is orthogonal to the frame of `γ`. -/
lemma exists_isLift {c c' : S.Classes} {γ : S.G E} {r : ℕ} {y : Matrix 𝔰.κ (Fin r) E}
    {a : GL (Fin r) (𝔸f E)}
    (h_le : colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.termLattice c c' γ) :
    ∃ w : Matrix (Fin 𝔰.ϱ) (Fin r) E, IsLift γ y a w := by
  -- By the definition of `L_γ`, each vector of the basis `y a` has a lift over the finite adeles.
  let lift : Matrix (Fin (𝔰.ϱ + 1)) (Fin 𝔰.ϱ) E := (S.M : E) • (isotropicRows (S.frameProducts γ))ᴴ
  obtain ⟨W, hW_int, hW⟩ : ∃ W : Matrix (Fin 𝔰.ϱ) (Fin r) (𝔸f E), IsIntMatrix (Ô E) W ∧
      finAdeleMatrix lift * W =
        (finAdeleMatrix (framePartX₀ γ))ᴴ * (finAdeleMatrix y * a.val) := by
    refine exists_isIntMatrix_mul_eq_of_col_mem fun k ↦ ?_
    have h_lift : finAdeleMatrix lift =
        S.ideleM • (isotropicRows (finAdeleMatrix (S.frameProducts γ)))ᴴ := by
      ext b i
      simp [lift, Units.smul_def, ideleM_val]
    obtain ⟨-, h_mem⟩ := h_le (col_mem_colLattice k)
    rwa [frameGram_translateByClassReps, frameMiddle_translateByClassReps_mul_classCoordX₀,
      ← colLattice_smul, ← h_lift] at h_mem
  -- The lifts solve a rational linear system, so there is a rational one near `-W a⁻¹`.
  obtain ⟨w, hw_int, hw⟩ : ∃ w : Matrix (Fin 𝔰.ϱ) (Fin r) E,
      IsIntMatrix (Ô E) (finAdeleMatrix w * a.val) ∧ lift * w = -((framePartX₀ γ)ᴴ * y) := by
    refine exists_mul_eq_of_finAdeleMatrix_mul_eq (U := {s | IsIntMatrix (Ô E) (s * a.val)})
      (isOpen_Ô.matrix.preimage (by fun_prop)) (s := -(W * a⁻¹.val))
      (by simpa [Matrix.mul_assoc] using hW_int.neg) ?_
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, hW]
    simp [Matrix.mul_assoc, finAdeleMatrix_conjTranspose, Matrix.map_neg]
  exact ⟨w, hw_int, by rw [← Matrix.smul_mul, hw, add_neg_cancel]⟩

/-- Let `E` contain a primitive 5040th root of unity. Let `L ⊆ Λ ∩ X₀` have the basis `B = y a`,
where `Λ` is the lattice of the class `c` and the columns of `y` are independent. The lattice
spanned by the rows of `Bᴴ B` has the index `(disc L) ^ 2` in the integral rows: this is the index
of `L` in its dual. -/
lemma submoduleIndex_gram_eq_discriminant_sq {c : S.Classes} {r : ℕ} {y : Matrix 𝔰.κ (Fin r) E}
    {a : GL (Fin r) (𝔸f E)} (hy : HasLeftInv y)
    (h_le : colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.classLatticeX₀ c) :
    (submoduleIndex (colLattice (Ô E) ((finAdeleMatrix y * a.val)ᴴ * (finAdeleMatrix y * a.val))ᵀ)
        (intVectors (Ô E) (Fin r)) : ℝ) =
      discriminant r (colLattice (Ô E) (finAdeleMatrix y * a.val)) ^ 2 := by
  have h_int : IsIntMatrix (Ô E) (S.classCoordX₀ c * (finAdeleMatrix y * a.val)) :=
    colLattice_le_preimageLattice_iff.1 h_le
  exact submoduleIndex_colLattice_gram_transpose hy a
    (isIntMatrix_conjTranspose_mul_of_classCoordX₀ h_int h_int)

omit [HasPrimitiveRoot5040 E] in
/-- Let `Λ` be the lattice of the class `c`, and let `L ⊆ Λ ∩ X₀` have the basis `m = y a`, where
the columns of the rational matrix `y` are independent. Let `w` be a rational matrix such that each
row of `w a` is an integral combination of the rows of the Gram matrix `mᴴ m`; that is, the map
`y t ↦ w t` is given by products with vectors of `L` over the finite adeles. Then it is given by the
products with a row `η` of rational vectors of `Λ ∩ X₀`. -/
lemma exists_conjTranspose_mul_eq_of_row_mem {c : S.Classes} {r : ℕ} {y : Matrix 𝔰.κ (Fin r) E}
    {a : GL (Fin r) (𝔸f E)} {w : Matrix (Fin 𝔰.ϱ) (Fin r) E} (hy : HasLeftInv y)
    (h_le : colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.classLatticeX₀ c)
    (h_rows : ∀ i : Fin 𝔰.ϱ, (finAdeleMatrix w * a.val) i ∈
      colLattice (Ô E) ((finAdeleMatrix y * a.val)ᴴ * (finAdeleMatrix y * a.val))ᵀ) :
    ∃ η : Matrix 𝔰.κ (Fin 𝔰.ϱ) E,
      IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix η) ∧ ηᴴ * y = w := by
  -- The row `η = y (yᴴ y)⁻¹ wᴴ` is rational and has the products `w`. If `w a = tᴴ mᴴ m` with `t`
  -- integral, then `η = m t` over the finite adeles, so `η` lies in `L`.
  let m : Matrix 𝔰.κ (Fin r) (𝔸f E) := finAdeleMatrix y * a.val
  have h_unit : IsUnit (yᴴ * y).det := (det_gram_ne_zero hy).isUnit
  obtain ⟨T, hT_int, hT⟩ : ∃ T : Matrix (Fin r) (Fin 𝔰.ϱ) (𝔸f E),
      IsIntMatrix (Ô E) T ∧ (mᴴ * m)ᵀ * T = (finAdeleMatrix w * a.val)ᵀ :=
    exists_isIntMatrix_mul_eq_of_col_mem h_rows
  let t : Matrix (Fin r) (Fin 𝔰.ϱ) (𝔸f E) := Tᵀᴴ
  have h_products : finAdeleMatrix w = (m * t)ᴴ * finAdeleMatrix y := by
    refine a.val.mul_left_inj_of_invertible.1 ?_
    rw [← transpose_transpose (finAdeleMatrix w * a.val), ← hT, transpose_mul, transpose_transpose,
      conjTranspose_mul m, conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc]
  let η : Matrix 𝔰.κ (Fin 𝔰.ϱ) E := y * (yᴴ * y)⁻¹ * wᴴ
  have h_adelic : finAdeleMatrix η = m * t :=
    calc finAdeleMatrix η
        = finAdeleMatrix (y * (yᴴ * y)⁻¹) * ((finAdeleMatrix y)ᴴ * (m * t)) := by
          rw [finAdeleMatrix_mul, finAdeleMatrix_conjTranspose w, h_products, conjTranspose_mul,
            conjTranspose_conjTranspose]
      _ = finAdeleMatrix (y * ((yᴴ * y)⁻¹ * (yᴴ * y))) * a.val * t := by
        -- regroup, as `m = y a`
        simp only [m, Matrix.map_mul, finAdeleMatrix_conjTranspose, Matrix.mul_assoc]
      _ = m * t := by rw [nonsing_inv_mul _ h_unit, Matrix.mul_one]
  refine ⟨η, ?_, ?_⟩
  · rw [h_adelic, ← Matrix.mul_assoc]
    exact (colLattice_le_preimageLattice_iff.1 h_le).mul hT_int.transpose.conjTranspose
  · simp [η, conjTranspose_nonsing_inv, Matrix.mul_assoc, nonsing_inv_mul _ h_unit]

/-- Let `L ⊆ Λ ∩ X₀` have the basis `m = y a`, with `Λ` the lattice of the class `c` and the columns
of `y` independent. Let `M = S.M` be the congruence level, let `Ξ₀` be the first `ϱ` rows of the
matrix of products of the standard frame with its image under `γ`, and write `F(γ) = framePartX₀ γ`
for the coordinates in `X₀` of that image. Let `w` be a lift of `L` for `γ`: the matrix `w a` is
integral and `F(γ)ᴴ y + M Ξ₀ᴴ w = 0`. Let each row of `w' a - w a` be an integral combination of the
rows of `mᴴ m`. Then `F(u γ)ᴴ y = -M Ξ₀ᴴ w'` for some move `u ∈ S.classUnipotent₀ c`. -/
lemma IsLift.exists_conjTranspose_framePartX₀_mul_eq_neg {c : S.Classes} {r : ℕ}
    {y : Matrix 𝔰.κ (Fin r) E} {γ : S.G E} {a : GL (Fin r) (𝔸f E)}
    {w w' : Matrix (Fin 𝔰.ϱ) (Fin r) E}
    (hw : IsLift γ y a w) (hy : HasLeftInv y)
    (h_le : colLattice (Ô E) (finAdeleMatrix y * a.val) ≤ S.classLatticeX₀ c)
    (h_congr : ∀ i : Fin 𝔰.ϱ, (finAdeleMatrix w' * a.val) i - (finAdeleMatrix w * a.val) i ∈
      colLattice (Ô E) ((finAdeleMatrix y * a.val)ᴴ * (finAdeleMatrix y * a.val))ᵀ) :
    ∃ u ∈ S.classUnipotent₀ c,
      (framePartX₀ (u * γ))ᴴ * y = -((S.M : E) • ((isotropicRows (S.frameProducts γ))ᴴ * w')) := by
  have h_sub : finAdeleMatrix (w' - w) = finAdeleMatrix w' - finAdeleMatrix w :=
    Matrix.map_sub _ (map_sub (algebraMap E (𝔸f E))) w' w
  obtain ⟨η, hη, h_product⟩ : ∃ η : Matrix 𝔰.κ (Fin 𝔰.ϱ) E,
      IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix η) ∧ ηᴴ * y = w' - w := by
    refine exists_conjTranspose_mul_eq_of_row_mem hy h_le fun i ↦ ?_
    rw [h_sub, Matrix.sub_mul]
    exact h_congr i
  obtain ⟨u, hu, h_moved⟩ : ∃ u ∈ S.classUnipotent₀ c, ∀ γ : S.G E,
      framePartX₀ (u * γ) = framePartX₀ γ - (S.M : E) • (η * isotropicRows (S.frameProducts γ)) :=
    exists_framePartX₀_mul_eq_sub_smul c hη
  have h_orth : (framePartX₀ γ)ᴴ * y = -((S.M : E) • ((isotropicRows (S.frameProducts γ))ᴴ * w)) :=
    eq_neg_of_add_eq_zero_left hw.orthogonal
  refine ⟨u, hu, ?_⟩
  calc (framePartX₀ (u * γ))ᴴ * y
      = (framePartX₀ γ)ᴴ * y - (S.M : E) • ((isotropicRows (S.frameProducts γ))ᴴ * (ηᴴ * y)) := by
        simp [h_moved, Matrix.sub_mul, Matrix.mul_assoc]
    _ = -((S.M : E) • ((isotropicRows (S.frameProducts γ))ᴴ * w')) := by
        rw [h_orth, h_product, Matrix.mul_sub, smul_sub]
        abel

/-! ## The lattice orthogonal to `L` -/

/-- The lattice `P = Λ ∩ X₀ ∩ L^⊥`, where `Λ` is the lattice of the class `c` and the columns of `y`
span the same space as `L`. -/
noncomputable def complementLattice (S : Filling E 𝔰) {r : ℕ} (c : S.Classes)
    (y : Matrix 𝔰.κ (Fin r) E) : Submodule (Ô E) (𝔰.κ → 𝔸f E) :=
  saturatedLattice (S.gram_classCoordX₀ c) (LinearMap.ker yᴴ.mulVecLin)

/-- Let `Λ` be the lattice of the class `c`. A rational vector of `Λ ∩ X₀` that is orthogonal to the
columns of `y` lies in the lattice `P = complementLattice c y`. -/
lemma coe_mem_complementLattice {c : S.Classes} {r : ℕ} {y : Matrix 𝔰.κ (Fin r) E} {v : 𝔰.κ → E}
    (h_orthogonal : yᴴ *ᵥ v = 0) (hv : ((↑) : E → 𝔸f E) ∘ v ∈ S.classLatticeX₀ c) :
    ((↑) : E → 𝔸f E) ∘ v ∈ S.complementLattice c y :=
  coe_mem_saturatedLattice (S.gram_classCoordX₀ c) h_orthogonal hv

/-- Let `Λ` be the lattice of the class `c`, and let `P` be the lattice of the vectors of `Λ ∩ X₀`
orthogonal to the columns of `y`. If these `r` columns are independent and `r + l = k`, then `P` has
the rank `l`: for a finite idele `d` in `Ô`, the index of `d P` in `P` is `[d] ^ l`, where `[d]` is
the generalised index. -/
lemma submoduleIndex_smul_complementLattice {c : S.Classes} {r : ℕ} {y : Matrix 𝔰.κ (Fin r) E}
    {l : ℕ} (hy : HasLeftInv y) (h_rank : r + l = 𝔰.k) {d : (𝔸f E)ˣ} (hd : d.val ∈ Ô E) :
    (submoduleIndex (d • S.complementLattice c y) (S.complementLattice c y) : ℝ) =
      genIndex d.val ^ l := by
  rw [complementLattice, submoduleIndex_smul_saturatedLattice _ _ hd,
    finrank_ker_conjTranspose h_rank hy]

/-! ## Congruent parts in `X₀` -/

variable {c : S.Classes} {j : Fin (𝔰.ϱ + 2)} {γ γ' : S.G E}

omit [HasPrimitiveRoot5040 E] in
/-- Let `γ` and `γ'` have the same matrix `Z` of products of the standard frame with its image, and
the cell rank `j`. For `γ` this means, with `D_i` the leading minor of order `i` of `Z`: for some
`t` with `t star t = 1` and every index `a ≥ j`, the flags of the frame and of its image share a
vector with leading coefficients `t` and `1` at `a`; `D_j ≠ 0`; and
`S.termDisc γ = |D_{ϱ+1}|² - N² |D_ϱ|²`, with `N = S.N`, is nonzero exactly when `j = ϱ + 1`. Let
`Y` be the first `j` rows of `Z` completed by rows of `1`, and let `v` be the difference of the
coordinates in `X₀` of the two images of the frame. The last column and the columns `k ≥ j` of
`v Y⁻¹` have length below `1` under the complex embedding `Φ w` of every infinite place `w`, as each
is the difference of two vectors of squared length at most `1/5`. -/
lemma HasCellRank.sum_norm_sq_sub_mul_inv_lt_one (hγ : S.HasCellRank j γ)
    (hγ' : S.HasCellRank j γ') (hZ : S.frameProducts γ' = S.frameProducts γ) {k : Fin (𝔰.ϱ + 1)}
    (hk : j.val ≤ k.val ∨ k = 𝔰.top) (w : InfinitePlace E) :
    ∑ i : 𝔰.κ, ‖Φ w (((framePartX₀ γ' - framePartX₀ γ) *
      (paddedLeading j (S.frameProducts γ))⁻¹) i k)‖ ^ 2 < 1 := by
  let y (g : S.G E) (i : 𝔰.κ) : E :=
    (frameImage g.val.val *ᵥ (paddedLeading j (S.frameProducts γ))⁻¹.col k) (𝔰.indexX₀ i)
  have hk_top : k.val < j.val → k = 𝔰.top := fun h_lt ↦ hk.resolve_left h_lt.not_ge
  have h_short : 5 * ∑ i : 𝔰.κ, ‖Φ w (y γ i)‖ ^ 2 ≤ 1 :=
    (hγ.mulVec_eStar_eq_zero_and_sum_indexX₀_le k hk_top).right w
  have h_short' : 5 * ∑ i : 𝔰.κ, ‖Φ w (y γ' i)‖ ^ 2 ≤ 1 := by
    simpa only [y, hZ] using (hγ'.mulVec_eStar_eq_zero_and_sum_indexX₀_le k hk_top).right w
  have h_col (i : 𝔰.κ) : ((framePartX₀ γ' - framePartX₀ γ) *
      (paddedLeading j (S.frameProducts γ))⁻¹) i k = y γ' i - y γ i := by
    rw [Matrix.sub_mul]
    rfl
  calc ∑ i : 𝔰.κ, ‖Φ w (((framePartX₀ γ' - framePartX₀ γ) *
          (paddedLeading j (S.frameProducts γ))⁻¹) i k)‖ ^ 2
      = ∑ i : 𝔰.κ, ‖Φ w (y γ' i) - Φ w (y γ i)‖ ^ 2 := by simp only [h_col, map_sub]
    _ ≤ ∑ i : 𝔰.κ, 2 * (‖Φ w (y γ' i)‖ ^ 2 + ‖Φ w (y γ i)‖ ^ 2) := by
      grw [norm_sub_le, add_sq_le]
    _ < 1 := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      linarith

/-- Let `E` contain a primitive 5040th root of unity, and let `S` have the congruence level
`M = S.M`. Let `γ` and `γ'` have the same integral matrix `Z = S.frameProducts γ` of products of the
standard frame with its image, with the leading minor `δ` of order `j`. Let both have the cell rank
`j`: the flags of the frame and of its image share vectors at all indices from `j` on, up to a
number of norm one, `δ ≠ 0`, and `S.termDisc`, formed from the last two leading minors of `Z`, is
nonzero exactly when `j = ϱ + 1`. Let the idele `d` be the number `M δ`. If the coordinates in `X₀`
of the images of the frame under `γ'` and `γ` (`framePartX₀`) are congruent modulo `d (Λ ∩ X₀)`,
with `Λ` the lattice of the class `c`, then they differ by `M η Ξ₀`, where the columns of `η` are
rational vectors of `Λ ∩ X₀` and `Ξ₀` consists of the first `ϱ` rows of `Z`. -/
lemma HasCellRank.exists_framePartX₀_sub_eq {d : (𝔸f E)ˣ} (hγ : S.HasCellRank j γ)
    (hγ' : S.HasCellRank j γ') (hZ : S.frameProducts γ' = S.frameProducts γ)
    (hd : d.val = ((S.M * leadingMinor (S.frameProducts γ) j : E) : 𝔸f E))
    (hZ_int : ∀ a b : Fin (𝔰.ϱ + 1), IsIntegral ℤ (S.frameProducts γ a b))
    (h_congr : ∀ i : Fin (𝔰.ϱ + 1),
      ((↑) : E → 𝔸f E) ∘ (framePartX₀ γ' - framePartX₀ γ).col i ∈ d • S.classLatticeX₀ c) :
    ∃ η : Matrix 𝔰.κ (Fin 𝔰.ϱ) E, IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix η) ∧
      framePartX₀ γ' - framePartX₀ γ = (S.M : E) • (η * isotropicRows (S.frameProducts γ)) := by
  -- Let `v` be the difference and `Y` the first `j` rows of `Z` completed by rows of `1`. Then
  -- `v Y⁻¹ = M η'` with the columns of `η'` in `Λ ∩ X₀`. The last column and the columns `k ≥ j` of
  -- `M η'` are so short that they vanish.
  set Y : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E := paddedLeading j (S.frameProducts γ)
  set v : Matrix 𝔰.κ (Fin (𝔰.ϱ + 1)) E := framePartX₀ γ' - framePartX₀ γ
  have hM_ne : (S.M : E) ≠ 0 := Nat.cast_ne_zero.2 (zero_lt_two.trans_le two_le_M).ne'
  have hδ : Y.det = leadingMinor (S.frameProducts γ) j := det_paddedLeading
  have h_det : Y.det ≠ 0 := hδ.trans_ne hγ.leadingMinor_ne_zero
  rw [← hδ] at hd
  let η' : Matrix 𝔰.κ (Fin (𝔰.ϱ + 1)) E := (S.M * Y.det)⁻¹ • v * Y.adjugate
  have hη' : IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix η') := by
    rw [finAdeleMatrix_mul, ← Matrix.mul_assoc]
    exact (isIntMatrix_mul_finAdeleMatrix_inv_smul (mul_ne_zero hM_ne h_det) hd h_congr).mul
      (isIntMatrix_paddedLeading hZ_int).adjugate
  have h_inv : v * Y⁻¹ = (S.M : E) • η' := by
    simp only [η', Matrix.inv_def, Ring.inverse_eq_inv', Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, mul_inv, mul_inv_cancel_left₀ hM_ne]
  have h_int : IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix (v * Y⁻¹)) := by
    simpa [h_inv, finAdeleMatrix_smul] using hη'.smul (natCast_mem (Ô E) S.M)
  have h_zero (i : 𝔰.κ) (k : Fin (𝔰.ϱ + 1)) (hk : j.val ≤ k.val ∨ k = 𝔰.top) : η' i k = 0 := by
    have h_col : (v * Y⁻¹).col k = 0 :=
      col_eq_zero_of_norm_lt_one h_int (hγ.sum_norm_sq_sub_mul_inv_lt_one hγ' hZ hk)
    rw [h_inv] at h_col
    exact (smul_eq_zero_iff_right hM_ne).1 (congrFun h_col i)
  refine ⟨η'.submatrix id Fin.castSucc, fun r i ↦ hη' r i.castSucc, ?_⟩
  calc v = v * Y⁻¹ * Y := (Y.nonsing_inv_mul_cancel_right v h_det.isUnit).symm
    _ = (S.M : E) • (η'.submatrix id Fin.castSucc * isotropicRows (S.frameProducts γ)) := by
      rw [h_inv, Matrix.smul_mul, mul_paddedLeading_eq_submatrix_mul_isotropicRows h_zero]

/-- Let `γ` and `γ'` have the same matrix `Z = S.frameProducts γ`, with integral entries, of
hermitian products of the standard frame `(e₁, …, e_ϱ, z)` with its image under `γ`, and let `δ` be
the leading minor of `Z` of order `j`. Let both have cell rank `j` (`S.HasCellRank j`): the flags of
the frame and of its image share vectors at all indices from `j` on, up to a number of norm one,
`δ ≠ 0`, and `S.termDisc`, formed from the last two leading minors of `Z`, is nonzero exactly when
`j = ϱ + 1`. Let the idele `d` equal `M δ`. Suppose the coordinates in the definite summand `X₀` of
the images of the frame under `γ'` and `γ` (`framePartX₀`) are congruent modulo `d (Λ ∩ X₀)`. Then
`framePartX₀ (u γ') = framePartX₀ γ` for some `u ∈ S.classUnipotent₀ c`. -/
lemma HasCellRank.exists_framePartX₀_mul_eq_of_sub_mem {d : (𝔸f E)ˣ} (hγ : S.HasCellRank j γ)
    (hγ' : S.HasCellRank j γ') (hZ : S.frameProducts γ' = S.frameProducts γ)
    (hd : d.val = ((S.M * leadingMinor (S.frameProducts γ) j : E) : 𝔸f E))
    (hZ_int : ∀ a b : Fin (𝔰.ϱ + 1), IsIntegral ℤ (S.frameProducts γ a b))
    (h_congr : ∀ i : Fin (𝔰.ϱ + 1),
      ((↑) : E → 𝔸f E) ∘ (framePartX₀ γ' - framePartX₀ γ).col i ∈ d • S.classLatticeX₀ c) :
    ∃ u ∈ S.classUnipotent₀ c, framePartX₀ (u * γ') = framePartX₀ γ := by
  obtain ⟨η, hη, h_diff⟩ : ∃ η : Matrix 𝔰.κ (Fin 𝔰.ϱ) E,
      IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix η) ∧
        framePartX₀ γ' - framePartX₀ γ = (S.M : E) • (η * isotropicRows (S.frameProducts γ)) :=
    hγ.exists_framePartX₀_sub_eq hγ' hZ hd hZ_int h_congr
  obtain ⟨u, hu, h_moved⟩ : ∃ u ∈ S.classUnipotent₀ c, ∀ γ : S.G E,
      framePartX₀ (u * γ) = framePartX₀ γ - (S.M : E) • (η * isotropicRows (S.frameProducts γ)) :=
    exists_framePartX₀_mul_eq_sub_smul c hη
  exact ⟨u, hu, by rw [h_moved, hZ, ← h_diff, _root_.sub_sub_cancel]⟩

/-! ## The moduli of the second and the third round -/

variable [S.IsAdmissible]

omit [HasPrimitiveRoot5040 E] [S.IsAdmissible] in
/-- An element of `E` whose squared absolute value is at most `b ^ e` at every infinite place has
generalised index at most `b ^ (e f)`, where `b = S.b` and `f` is the number of infinite places. -/
lemma genIndex_algebraMap_le_pow_of_norm_sq_le {x : E} {e : ℕ}
    (h_place : ∀ v : InfinitePlace E, ‖Φ v x‖ ^ 2 ≤ S.b ^ e) :
    genIndex (x : 𝔸f E) ≤ S.b ^ (e * numInfPlaces E) := by
  grw [genIndex_algebraMap, abs_norm_eq_prod_norm_sq, pow_mul, h_place]
  simp

omit [HasPrimitiveRoot5040 E] in
/-- Let `S` be admissible, with size parameter `b = S.b` and `M = S.M`, the product of the two level
primes. Let `ϱ = 𝔰.ϱ` and `n = 𝔰.n = ϱ + 1`, and let `f` be the number of infinite places. Let `γ`
be near: for some archimedean point `y`, both `y` and `γ⁻¹ y` lie in `S.boxedPoints`. Let
`δ = leadingMinor (S.frameProducts γ) j` be the leading minor of order `j ≤ ϱ + 1` of the matrix of
products of the standard frame with its image under `γ`. The generalised index of `M δ`, the
absolute value of its norm to `ℚ`, is at most `b ^ (2 n³ f)`. -/
lemma IsNear.genIndex_M_mul_leadingMinor_le {γ : S.G E} (j : Fin (𝔰.ϱ + 2)) (h_near : S.IsNear γ) :
    genIndex ((S.M * leadingMinor (S.frameProducts γ) j : E) : 𝔸f E) ≤
      S.b ^ (2 * 𝔰.n ^ 3 * numInfPlaces E) := by
  have h_exponent : 23 * 2 + 270 * 𝔰.n ^ 2 ≤ 2 * 𝔰.n ^ 3 := by
    have h_cube : 300 * 𝔰.n ^ 2 ≤ 𝔰.n ^ 3 := S.mul_sq_le_cube (by norm_num)
    linarith [pow_pos 𝔰.ϱ.succ_pos 2]
  refine genIndex_algebraMap_le_pow_of_norm_sq_le fun v ↦ ?_
  calc ‖Φ v (S.M * leadingMinor (S.frameProducts γ) j)‖ ^ 2
      = S.M ^ 2 * ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ ^ 2 := by simp [mul_pow]
    _ ≤ (S.b ^ 23) ^ 2 * S.b ^ (270 * 𝔰.n ^ 2) := by
        grw [M_le_b_pow, h_near.norm_map_leadingMinor_sq_le]
    _ ≤ S.b ^ (2 * 𝔰.n ^ 3) := by
        rw [← pow_mul, ← pow_add]
        exact pow_le_pow_right₀ S.one_le_b h_exponent

omit [S.IsAdmissible] in
/-- If `Z` has integral entries, then the modulus `S.frameModulus j Z = M det (Y Yᴴ)` is integral,
where `M = S.M` and `Y` consists of the first `j` rows of `Z` completed by rows of `1`. -/
lemma frameModulus_mem_integralAdeles_of_isIntegral {j : Fin (𝔰.ϱ + 2)}
    {Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E}
    (hZ : ∀ a b : Fin (𝔰.ϱ + 1), IsIntegral ℤ (Z a b)) :
    (S.frameModulus j Z : 𝔸f E) ∈ Ô E := by
  let O : Subring E := (Ô E).comap (algebraMap E (𝔸f E))
  have : IsStarStable O := isStarStable_comap_Ô
  have hY : IsIntMatrix O (paddedLeading j Z) := isIntMatrix_paddedLeading hZ
  exact nsmul_mem (hY.mul hY.conjTranspose).det_mem S.M

omit [HasPrimitiveRoot5040 E] in
/-- Let `S` be admissible, with the size parameter `b = S.b` and the congruence level `M = S.M`, let
`n = ϱ + 1`, and let `f` be the number of infinite places. Let `γ` be near: for some archimedean
point `y`, both `y` and `γ⁻¹ y` lie in `S.boxedPoints`. Let `δ` be the leading minor of any order
`j ≤ ϱ + 1` of the matrix of products of the standard frame with its image under `γ`. The modulus
`S.frameModulus` is `M δ star δ`. Its generalised index, the absolute value of its norm to `ℚ`, is
at most `b ^ (2 n³ f)`. -/
lemma IsNear.genIndex_frameModulus_le {j : Fin (𝔰.ϱ + 2)} {γ : S.G E} (h_near : S.IsNear γ) :
    genIndex (S.frameModulus j (S.frameProducts γ) : 𝔸f E) ≤
      S.b ^ (2 * 𝔰.n ^ 3 * numInfPlaces E) := by
  have h_exponent : 23 * 2 + 270 * 𝔰.n ^ 2 * 2 ≤ 2 * 𝔰.n ^ 3 := by
    have h_cube : 300 * 𝔰.n ^ 2 ≤ 𝔰.n ^ 3 := S.mul_sq_le_cube (by norm_num)
    linarith [pow_pos 𝔰.ϱ.succ_pos 2]
  refine genIndex_algebraMap_le_pow_of_norm_sq_le fun v ↦ ?_
  have hb : 1 ≤ S.b := S.one_le_b
  calc ‖Φ v (S.frameModulus j (S.frameProducts γ))‖ ^ 2
      = (S.M * ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ ^ 2) ^ 2 := by
        simp [frameModulus, sq, mul_assoc]
    _ ≤ (S.b ^ 23 * S.b ^ (270 * 𝔰.n ^ 2)) ^ 2 := by
        grw [M_le_b_pow, h_near.norm_map_leadingMinor_sq_le]
    _ ≤ S.b ^ (2 * 𝔰.n ^ 3) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_add]
        exact pow_le_pow_right₀ hb h_exponent

end New.Filling
