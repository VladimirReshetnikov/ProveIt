import New.Spanning.RemainingTerms.Data
import New.Spanning.Unfolding.TermStructure

/-!
# The vectors `z⁺` and `Υ_γ⁻¹ z⁺`

Let `γ` be an element of the unitary group, with the link isometry `Υ_γ` of the positive space
`X₀ ⊥ E z⁺`. Let `z` be the last vector of the frame and let `A` be spanned by the others. The
vectors of the lattice `Λ` of a class `c` that are orthogonal to `A` and `γ A` have as their image a
lattice `L¹` in `X₀ ⊥ E z⁺`. It contains the lattice `L⁺_γ` of the vectors whose part in `A` is
divisible by the level `M = S.M`, so what lies in the dual of `L¹` lies in the dual of `L⁺_γ`.

* `New.Filling.linkVectors_mulVec_perpToPositive_mem`: if `γ` is a term over `(c, s, c')`, the
  products of `z⁺` and `Υ_γ⁻¹ z⁺` with `L¹` are integral.
* `New.Filling.linkVectors_mulVec_eq_zero_iff`: the orthogonal complement of the two vectors is
  `X₀^γ = X₀ ∩ Υ_γ⁻¹ X₀`.
* `New.Filling.exists_lift_mem_linkedX₀_iff_exists_orthogonal`: the vectors of `L⁺_γ ∩ X₀^γ`.
* `New.Filling.HasCellRank.exists_linkIsometry_symm_eq_smul`,
  `New.Filling.linearIndependent_linkVectors_and_prod_norm_det`: the two vectors are proportional if
  `γ` has a cell rank and the discriminant `𝗀` of the two frames is zero; if `𝗀` is not zero, they
  are independent, and their Gram determinant is computed
  (`New.Filling.linearIndependent_linkVectors`, `New.Filling.prod_norm_det_gram_linkVectors`).
* `New.Filling.linkVectorPairs`: the negatives of the two vectors, as pairs in the graph of `Υ_γ`;
  there they represent the products with `z` and `γ z`
  (`New.Filling.linkVectorPairs_mul_linkMetric_mul`).

Notions from other files:
* `S.G E`: the unitary group of the form `S.ratGram` on the space with the basis `e₁, …, e_ϱ`, a
  basis of `X₀`, `z`, `e*₁, …, e*_ϱ`; the frame is `(e₁, …, e_ϱ, z)`.
* `S.positiveGram`: the Gram matrix of `X₀ ⊥ E z⁺`, where `z⁺` has the norm `N = S.N`.
* `linkIsometry γ`: the isometry `Υ_γ` of `X₀ ⊥ E z⁺`.
* `S.HasCellRank j γ`: the term `γ` has the cell rank `j`, the order of a distinguished leading
  minor of the products of the frame with its image under `γ`.
* `perpToPositive γ`: the map from `isotropicPerp γ = (A + γ A)^⊥` to `X₀ ⊥ E z⁺`.
-/

noncomputable section

open Matrix Sum NumberField

namespace New.Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} {γ : S.G E}
  {j : Fin (𝔰.ϱ + 2)}

/-- The two vectors `z⁺` and `Υ_γ⁻¹ z⁺` of the positive space `X₀ ⊥ E z⁺`, as columns. Here
`Υ_γ = linkIsometry γ` is the link isometry of `γ`, and `inr ()` is the index of `z⁺`. -/
def linkVectors (γ : S.G E) : Matrix 𝔰.MiddleIndex (Fin 2) E :=
  (of ![Pi.single (inr ()) 1, (linkIsometry γ).symm (Pi.single (inr ()) 1)])ᵀ

/-- The two vectors `k z` and `z`, as columns, where `k` is in the unitary group of the form with
the middle block `T`, and `z` is the last vector of the frame `(e₁, …, e_ϱ, z)`. -/
abbrev lastFramePair {R : Type} [CommRing R] [StarRing R] {T : 𝔰.Form R} (k : T.G) :
    Matrix 𝔰.BesselIndex (Fin 2) R :=
  (framePair k).submatrix id ![inr 𝔰.top, inl 𝔰.top]

/-- The products of a vector `a` of `X₀ ⊥ E z⁺` with `z⁺` and `Υ_γ⁻¹ z⁺` are `N` times the
`z⁺`-coordinates of `a` and of `Υ_γ a`, where `Υ_γ` is the link isometry of `γ`. -/
lemma linkVectors_mulVec (γ : S.G E) (a : 𝔰.MiddleIndex → E) :
    ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ a =
      ![S.N * a (inr ()), S.N * linkIsometry γ a (inr ())] := by
  have h_single (b : 𝔰.MiddleIndex → E) :
      star (Pi.single (inr ()) 1 : 𝔰.MiddleIndex → E) ⬝ᵥ S.positiveGram *ᵥ b =
        S.N * b (inr ()) := by
    rw [dotProduct_positiveGram_mulVec_eq_sum_add]
    simp
  rw [← mulVec_mulVec]
  funext i
  fin_cases i
  · exact h_single a
  · change star ((linkIsometry γ).symm (Pi.single (inr ()) 1)) ⬝ᵥ S.positiveGram *ᵥ a =
      S.N * linkIsometry γ a (inr ())
    rw [← dotProduct_positiveGram_mulVec_linkIsometry γ, LinearEquiv.apply_symm_apply, h_single]

/-- The vectors `a` orthogonal, for `S.positiveGram`, to `z⁺` and `Υ_γ⁻¹ z⁺` in `X₀ ⊥ E z⁺` are
exactly the image under `inclPositive E 𝔰` of `X₀^γ = X₀ ∩ Υ_γ⁻¹ X₀` (`linkedX₀ γ`). -/
theorem linkVectors_mulVec_eq_zero_iff (γ : S.G E) (a : 𝔰.MiddleIndex → E) :
    ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ a = 0 ↔ a ∈ (linkedX₀ γ).map (inclPositive E 𝔰) := by
  have h_coords : ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ a = 0 ↔
      a (inr ()) = 0 ∧ linkIsometry γ a (inr ()) = 0 := by
    simp [linkVectors_mulVec, S.N_prime.ne_zero]
  rw [h_coords, ← mem_range_inclPositive]
  constructor
  · rintro ⟨⟨v, rfl⟩, h_link⟩
    exact ⟨v, mem_linkedX₀.2 h_link, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, rfl⟩, mem_linkedX₀.1 hv⟩

/-- A vector `y` is orthogonal to the frame `(γ e₁, …, γ e_ϱ, γ z)` if and only if the coordinates
of `γ⁻¹ y` at the dual basis vectors `e*_a` and at `z` vanish. -/
lemma frameImage_conjTranspose_mulVec_eq_zero_iff (γ : S.G E) (y : 𝔰.BesselIndex → E) :
    ((frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))ᴴ * S.ratGram) *ᵥ y = 0 ↔
      (∀ a : Fin 𝔰.ϱ,
        ((↑(γ⁻¹ : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ y) (eStar a) = 0) ∧
      ((↑(γ⁻¹ : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ y) 𝔰.z = 0 := by
  set x : 𝔰.BesselIndex → E := (↑(γ⁻¹ : S.G E) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E) *ᵥ y
    with hx
  have h_move : ((frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))ᴴ * S.ratGram) *ᵥ y =
      (S.ratGram *ᵥ x) ∘ 𝔰.besselFrame := by
    rw [hx, mulVec_mulVec, U.form_mul_inv_eq γ]
    rfl
  have h_dual (a : Fin 𝔰.ϱ) : (S.ratGram *ᵥ x) (𝔰.besselFrame a.castSucc) = x (eStar a) := by
    simp [Shape.besselFrame]
  have h_z : (S.ratGram *ᵥ x) (𝔰.besselFrame (Fin.last 𝔰.ϱ)) = -(S.N * x 𝔰.z) := by
    rw [splitGram_mulVec]
    simp [Shape.besselFrame, Shape.middleGram, mulVec, dotProduct]
  rw [h_move, funext_iff, Fin.forall_fin_succ']
  simp only [Function.comp_apply, h_dual, h_z]
  simp [S.N_prime.ne_zero]

/-- Let `A` be spanned by the vectors of the frame other than the last one, `z`. For `y` in
`isotropicPerp γ`, so orthogonal to `A` and `γ A`, let `v = perpToPositive γ y` be its image in
`X₀ ⊥ E z⁺`. Then the `z⁺`-coordinate (index `inr ()`) of `Υ_γ v = linkIsometry γ v` is the
`z`-coordinate of `y`. -/
lemma linkIsometry_perpToPositive_apply (γ : S.G E) (y : isotropicPerp γ) :
    linkIsometry γ (perpToPositive γ y) (inr ()) = y.val 𝔰.z := by
  have h_link : linkMatrix γ *ᵥ y.val ∈ link γ := ⟨y, y.prop, rfl⟩
  change linkIsometry γ (linkSource E 𝔰 (linkMatrix γ *ᵥ y.val)) (inr ()) = y.val 𝔰.z
  rw [linkIsometry_linkSource h_link, linkTarget_linkMatrix_mulVec, elim_inr]

/-- Let `A` be spanned by the vectors of the frame other than the last one, `z`. For `y` orthogonal
to `A` and `γ A`, with the image `v` in `X₀ ⊥ E z⁺`, the products of `v` with `z⁺` and `Υ_γ⁻¹ z⁺`
are minus those of `y` with `γ z` and `z`. -/
lemma linkVectors_mulVec_perpToPositive (γ : S.G E) (y : isotropicPerp γ) :
    ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ perpToPositive γ y =
      -(((lastFramePair γ)ᴴ * S.ratGram) *ᵥ y.val) := by
  -- The middle form has the value `-N` at `z`.
  have h_last (a : Unit ⊕ Unit) :
      S.N * (linkMatrix γ *ᵥ y.val) (a.map inr inr) =
        -((((framePair γ).submatrix id
          (Sum.map (fun _ : Unit ↦ 𝔰.top) fun _ : Unit ↦ 𝔰.top))ᴴ * S.ratGram) *ᵥ y.val) a := by
    rw [framePair_last_eq_zRowBlockDiagonal_mul, ← mulVec_mulVec]
    rcases a with a | a <;> simp [Shape.middleGram, mulVec, dotProduct]
  rw [linkVectors_mulVec, linkIsometry_perpToPositive_apply,
    show y.val 𝔰.z = (linkMatrix γ *ᵥ y.val) (inl (inr ())) by simp]
  funext i
  fin_cases i
  exacts [h_last (inr ()), h_last (inl ())]

/-- If `k` lies in the stabilizer of the standard lattice, the linear forms given by the products
with `k z` and `z`, in the lattice basis (where the middle block of the Gram matrix is
`S.latticeMiddle`), have coefficients in the integral finite adeles. -/
lemma isIntMatrix_lastFramePair_mul (k : S.latticeStabilizer) :
    IsIntMatrix (Ô E) ((lastFramePair k.val)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram) := by
  have h_pair : IsIntMatrix (Ô E) ((framePair k.val)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram) :=
    (isIntMatrix_framePair k.prop.isIntMatrix).conjTranspose.mul
      S.isUnimodular_latticeMiddle.splitGram.isIntMatrix
  exact fun i ↦ h_pair (![inr 𝔰.top, inl 𝔰.top] i)

/-- Let `γ` be a term over `(c, s, c')`: in the coordinates of the classes `c` and `c'` it
stabilizes the standard lattice and has the reduction `s`. Let `Λ` be the lattice of the class `c`,
and let `A` be spanned by the vectors of the frame other than the last one. The vectors `z⁺` and
`Υ_γ⁻¹ z⁺` have integral products with the image in `X₀ ⊥ E z⁺` of every vector `y` of `Λ` that is
orthogonal to `A` and `γ A`. -/
theorem linkVectors_mulVec_perpToPositive_mem {c c' : S.Classes} {s : S.ResidueGL}
    (hγ : γ ∈ S.termsOver c s c') (y : isotropicPerp γ)
    (hy : ((↑) : E → 𝔸f E) ∘ y.val ∈ preimageLattice (Ô E) (S.classCoord c)) :
    ((↑) : E → 𝔸f E) ∘ (((linkVectors γ)ᴴ * S.positiveGram) *ᵥ perpToPositive γ y) ∈
      intVectors (Ô E) (Fin 2) := by
  obtain ⟨k, -, hk⟩ :
      ∃ k : S.latticeStabilizer, S.reduction k = s ∧ k.val = S.translateByClassReps c c' γ := hγ
  have h_value : ((lastFramePair k.val)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram) *ᵥ
      S.classCoord c *ᵥ (((↑) : E → 𝔸f E) ∘ y.val) =
      ((↑) : E → 𝔸f E) ∘ (((lastFramePair γ)ᴴ * S.ratGram) *ᵥ y.val) := by
    rw [hk]
    funext i
    exact congrFun₂ (framePair_translateByClassReps_mul_classCoord c c' γ ![inr 𝔰.top, inl 𝔰.top]
      (replicateCol Unit y.val)) i ()
  have h_int : ((↑) : E → 𝔸f E) ∘ (((lastFramePair γ)ᴴ * S.ratGram) *ᵥ y.val) ∈
      intVectors (Ô E) (Fin 2) := by
    rw [← h_value]
    exact (isIntMatrix_lastFramePair_mul k).mulVec hy
  rw [linkVectors_mulVec_perpToPositive]
  exact fun i ↦ by simpa using h_int i

/-- Let `Λ` be the lattice of the class `c`. For `a` in the span of `e₁, …, e_ϱ` and `v` in
`X₀`, the vector `a + v` lies in `Λ` if and only if `a` has integral coordinates and `v` lies in
`Λ ∩ X₀`. -/
lemma elim_mem_preimageLattice_classCoord_iff (c : S.Classes) (a : Fin 𝔰.ϱ → E) (v : 𝔰.κ → E) :
    ((↑) : E → 𝔸f E) ∘ (a ⊕ᵥ ((v ⊕ᵥ 0) ⊕ᵥ 0) : 𝔰.BesselIndex → E) ∈
        preimageLattice (Ô E) (S.classCoord c) ↔
      (∀ i : Fin 𝔰.ϱ, (a i : 𝔸f E) ∈ Ô E) ∧ ((↑) : E → 𝔸f E) ∘ v ∈ S.classLatticeX₀ c := by
  simp [preimageLattice, classLatticeX₀, intVectors, classCoord_eq_fromBlocks, fromBlocks_mulVec,
    mulVec, dotProduct]

/-- Let `Λ` be the lattice of the class `c`, let `A` be spanned by the vectors of the frame other
than the last one, and let `L⁺_γ` be the image in `X₀ ⊥ E z⁺` of the vectors of `Λ` that are
orthogonal to `A` and `γ A` and whose part in `A` is divisible by the level `M = S.M`. A vector `v`
of `X₀` lies in `L⁺_γ` and in `X₀^γ = X₀ ∩ Υ_γ⁻¹ X₀` (`linkedX₀ γ`) if and only if it lies in `Λ`
and some vector of `v + M (Λ ∩ A)` is orthogonal to the image of the frame under `γ`. -/
theorem exists_lift_mem_linkedX₀_iff_exists_orthogonal (c : S.Classes) (γ : S.G E) (v : 𝔰.κ → E) :
    ((∃ y : isotropicPerp γ,
        ((↑) : E → 𝔸f E) ∘ y.val ∈ preimageLattice (Ô E) (S.classCoord c) ∧
        (∀ i : Fin 𝔰.ϱ, S.ideleM⁻¹ • (y.val (inl i) : 𝔸f E) ∈ Ô E) ∧
        perpToPositive γ y = v ⊕ᵥ 0) ∧
      v ∈ linkedX₀ γ) ↔
    (((↑) : E → 𝔸f E) ∘ v ∈ S.classLatticeX₀ c ∧
      ∃ a : Fin 𝔰.ϱ → E, (∀ i : Fin 𝔰.ϱ, S.ideleM⁻¹ • (a i : 𝔸f E) ∈ Ô E) ∧
        ((frameImage (γ : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E))ᴴ * S.ratGram) *ᵥ
          (a ⊕ᵥ ((v ⊕ᵥ 0) ⊕ᵥ 0)) = 0) := by
  set γInv : Matrix 𝔰.BesselIndex 𝔰.BesselIndex E := ↑(γ⁻¹ : S.G E)
  have h_source (y : isotropicPerp γ) :
      perpToPositive γ y = (y.val ∘ 𝔰.indexX₀) ⊕ᵥ fun _ : Unit ↦ (γInv *ᵥ y.val) 𝔰.z :=
    linkSource_linkMatrix_mulVec y.val
  rw [mem_linkedX₀]
  constructor
  · rintro ⟨⟨y, h_int, h_level, h_image⟩, h_zero⟩
    obtain ⟨h_dual, h_dual'⟩ : (∀ a : Fin 𝔰.ϱ, y.val (eStar a) = 0) ∧
        ∀ a : Fin 𝔰.ϱ, (γInv *ᵥ y.val) (eStar a) = 0 := mem_isotropicPerp.1 y.prop
    have h_z : y.val 𝔰.z = 0 := by rw [← linkIsometry_perpToPositive_apply, h_image, h_zero]
    rw [h_source] at h_image
    have h_eq : y.val = (fun a : Fin 𝔰.ϱ ↦ y.val (inl a)) ⊕ᵥ ((v ⊕ᵥ 0) ⊕ᵥ 0) := by
      ext (a | (i | i) | a)
      exacts [rfl, congrFun h_image (inl i), h_z, h_dual a]
    rw [h_eq, elim_mem_preimageLattice_classCoord_iff] at h_int
    refine ⟨h_int.2, fun a ↦ y.val (inl a), h_level, ?_⟩
    rw [← h_eq, frameImage_conjTranspose_mulVec_eq_zero_iff]
    exact ⟨h_dual', congrFun h_image (inr ())⟩
  · rintro ⟨h_int, a, ha, h_orth⟩
    let x : 𝔰.BesselIndex → E := a ⊕ᵥ ((v ⊕ᵥ 0) ⊕ᵥ 0)
    obtain ⟨h_dual', h_z'⟩ : (∀ b : Fin 𝔰.ϱ, (γInv *ᵥ x) (eStar b) = 0) ∧ (γInv *ᵥ x) 𝔰.z = 0 :=
      (frameImage_conjTranspose_mulVec_eq_zero_iff γ x).1 h_orth
    let y : isotropicPerp γ := ⟨x, mem_isotropicPerp.2 ⟨fun _ ↦ rfl, h_dual'⟩⟩
    have h_image : perpToPositive γ y = v ⊕ᵥ 0 := by
      rw [h_source, h_z']
      rfl
    have ha_int (i : Fin 𝔰.ϱ) : (a i : 𝔸f E) ∈ Ô E := by
      simpa [Units.smul_def] using mul_mem S.ideleM_mem (ha i)
    refine ⟨⟨y, (elim_mem_preimageLattice_classCoord_iff c a v).2 ⟨ha_int, h_int⟩, ha, h_image⟩, ?_⟩
    rw [← h_image, linkIsometry_perpToPositive_apply]
    rfl

/-- Let `γ` have a cell rank `j` (`HasCellRank`): it is in the normal form
`NormOnePairOccursFrom j γ`, the leading minor of order `j` of the products of the frame with its
image under `γ` is not zero, and `j` is the top index `ϱ + 1` exactly if the discriminant
`𝗀 = S.termDisc γ` of these two frames is not zero. If `𝗀 = 0`, then `Υ_γ⁻¹ z⁺` is a multiple of
`z⁺`. -/
theorem HasCellRank.exists_linkIsometry_symm_eq_smul (hγ : S.HasCellRank j γ)
    (h_disc : S.termDisc γ = 0) :
    ∃ μ : E, (linkIsometry γ).symm (Pi.single (inr ()) 1) = μ • Pi.single (inr ()) 1 := by
  -- Here `X₀^γ = X₀`, so the vector is orthogonal to `X₀`.
  set w : 𝔰.MiddleIndex → E := (linkIsometry γ).symm (Pi.single (inr ()) 1)
  have h_orth (v : 𝔰.κ → E) : star w ⬝ᵥ S.positiveGram *ᵥ (v ⊕ᵥ 0) = 0 := by
    have h_products : ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ (v ⊕ᵥ 0) = 0 :=
      (linkVectors_mulVec_eq_zero_iff γ _).2 ⟨v, by simp [hγ.linkedX₀_eq_top h_disc], rfl⟩
    rw [← mulVec_mulVec] at h_products
    exact congrFun h_products 1
  use w (inr ())
  ext (i | i)
  · have h_coord : star w ⬝ᵥ S.positiveGram *ᵥ (Pi.single i 1 ⊕ᵥ 0) = star (w (inl i)) := by
      rw [dotProduct_positiveGram_mulVec_eq_sum_add]
      simp [Pi.single_apply]
    rw [h_orth, eq_comm, star_eq_zero] at h_coord
    simp [h_coord]
  · simp

/-- Let `γ` have the cell rank `j`: it is in the normal form `NormOnePairOccursFrom j γ`, the
leading minor `δ_j` of order `j` of the products of the frame with its image under `γ` is not zero,
and `j` is the top index exactly if the discriminant `𝗀` of these two frames is not zero. Then
`𝗀 = |δ_j|² (1 - |u|²)`, where `u` is the `z⁺`-coordinate of `Υ_γ⁻¹ z⁺`, `Υ_γ` is the link
isometry of `γ`, and `|x|²` means `x x̄`. -/
lemma HasCellRank.termDisc_eq_mul_linkIsometry_symm (hγ : S.HasCellRank j γ) :
    S.termDisc γ =
      leadingMinor (S.frameProducts γ) j * star (leadingMinor (S.frameProducts γ) j) *
        (1 - star ((linkIsometry γ).symm (Pi.single (inr ()) 1) (inr ())) *
          (linkIsometry γ).symm (Pi.single (inr ()) 1) (inr ())) := by
  set w : 𝔰.MiddleIndex → E := (linkIsometry γ).symm (Pi.single (inr ()) 1) with hw
  have hN : (S.N : E) ≠ 0 := Nat.cast_ne_zero.2 S.N_prime.ne_zero
  by_cases h_disc : S.termDisc γ = 0
  · -- The vector `w` is `μ z⁺` and has the norm of `z⁺`, so `|μ| = 1`.
    obtain ⟨μ, hμ⟩ : ∃ μ : E, w = μ • Pi.single (inr ()) 1 :=
      hγ.exists_linkIsometry_symm_eq_smul h_disc
    have h_norm : star w ⬝ᵥ S.positiveGram *ᵥ w = S.N := by
      rw [← dotProduct_positiveGram_mulVec_linkIsometry γ, hw, LinearEquiv.apply_symm_apply,
        dotProduct_positiveGram_mulVec_eq_sum_add]
      simp
    rw [hμ, dotProduct_positiveGram_mulVec_eq_sum_add] at h_norm
    simp [h_disc, hμ, show star μ * μ = 1 by simpa [hN] using h_norm]
  · -- Let `δ` be the determinant of the products and `δ'` the minor before it. The link sends
    -- `y₀ + δ' z⁺` to `-(δ / N) z⁺` for some `y₀` in `X₀`, so `w = -(N / δ) (y₀ + δ' z⁺)`.
    obtain rfl : j = ⊤ := Fin.eq_last_of_not_lt (not_lt.2 (hγ.lt_iff_termDisc_ne_zero.2 h_disc))
    have hδ : (S.frameProducts γ).det ≠ 0 := ((termDisc_pos_or_eq_zero γ).resolve_right h_disc).2
    obtain ⟨y, hy, hy_top⟩ : ∃ y : Fin (𝔰.ϱ + 1) → E,
        S.frameProducts γ *ᵥ y = Pi.single 𝔰.top (S.frameProducts γ).det ∧
        y 𝔰.top = leadingMinor (S.frameProducts γ) 𝔰.top.castSucc :=
      exists_mulVec_eq_single_det (S.frameProducts γ)
    have h_image : linkIsometry γ (-(S.N / (S.frameProducts γ).det) •
        (((frameImage γ *ᵥ y) ∘ 𝔰.indexX₀) ⊕ᵥ fun _ : Unit ↦ y 𝔰.top)) = Pi.single (inr ()) 1 := by
      rw [map_smul, linkIsometry_frameImage_mulVec hy]
      ext (i | i) <;> simp [hN, hδ]
    have h_coord : w (inr ()) = -(S.N / (S.frameProducts γ).det) *
        leadingMinor (S.frameProducts γ) 𝔰.top.castSucc := by
      rw [hw, ← h_image, LinearEquiv.symm_apply_apply, ← hy_top]
      rfl
    have h_minor : leadingMinor (S.frameProducts γ) ⊤ = (S.frameProducts γ).det := rfl
    rw [h_coord, h_minor, termDisc, frameDisc, star_mul', star_neg, star_div₀, star_natCast]
    field_simp [star_ne_zero.2 hδ]

/-- The Gram matrix of `z⁺` and `Υ_γ⁻¹ z⁺` for the form `S.positiveGram` of the positive space
`X₀ ⊥ E z⁺`. Both diagonal entries are `N = S.N`, the norm of `z⁺`. The entries off the diagonal are
`N u` (row 1, column 2) and `N ū` (row 2, column 1), where `u` is the `z⁺`-coordinate of
`Υ_γ⁻¹ z⁺`. -/
lemma gram_linkVectors (γ : S.G E) :
    (linkVectors γ)ᴴ * S.positiveGram * linkVectors γ =
      !![(S.N : E), S.N * (linkIsometry γ).symm (Pi.single (inr ()) 1) (inr ());
        S.N * star ((linkIsometry γ).symm (Pi.single (inr ()) 1) (inr ())), S.N] := by
  set w : 𝔰.MiddleIndex → E := (linkIsometry γ).symm (Pi.single (inr ()) 1) with hw
  have h_first : ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ Pi.single (inr ()) 1 =
      ![(S.N : E), S.N * star (w (inr ()))] := by
    ext i
    fin_cases i <;> simp [linkVectors, positiveGram, Matrix.mul_apply, diagonal, hw, mul_comm]
  have h_second : ((linkVectors γ)ᴴ * S.positiveGram) *ᵥ w = ![S.N * w (inr ()), S.N] := by
    simp [linkVectors_mulVec, hw]
  ext i k
  fin_cases i <;> fin_cases k
  exacts [congrFun h_first 0, congrFun h_second 0, congrFun h_first 1, congrFun h_second 1]

/-- If `γ` has the cell rank `j` (`HasCellRank`), the Gram determinant of `z⁺` and `Υ_γ⁻¹ z⁺`,
times `|δ_j|²`, is `N² 𝗀`. Here `𝗀` is the discriminant of the frame and its image under `γ`, and
`δ_j` is the leading minor of order `j` of their products, which is not zero. -/
lemma HasCellRank.det_gram_linkVectors_mul (hγ : S.HasCellRank j γ) :
    ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det *
        (leadingMinor (S.frameProducts γ) j * star (leadingMinor (S.frameProducts γ) j)) =
      S.N ^ 2 * S.termDisc γ := by
  rw [gram_linkVectors, det_fin_two_of, hγ.termDisc_eq_mul_linkIsometry_symm]
  ring

/-- Let `γ` have the cell rank `j` (`HasCellRank`), so that the leading minor `δ_j` of order `j` of
the products of the frame with its image under `γ` is not zero, and let `𝗀` be the discriminant of
these two frames. At each infinite place `v` the Gram determinant of `z⁺` and `Υ_γ⁻¹ z⁺` has the
modulus `N² |𝗀|_v / |δ_j|_v²`. Here `|x|_v` is the modulus `‖Φ v x‖` under the complex embedding
chosen at `v`. -/
lemma HasCellRank.norm_det_gram_linkVectors (hγ : S.HasCellRank j γ) (v : InfinitePlace E) :
    ‖Φ v ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det‖ =
      S.N ^ 2 * ‖Φ v (S.termDisc γ)‖ / ‖Φ v (leadingMinor (S.frameProducts γ) j)‖ ^ 2 := by
  have h_det : ‖Φ v (((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det *
      (leadingMinor (S.frameProducts γ) j * star (leadingMinor (S.frameProducts γ) j)))‖ =
      ‖Φ v (S.N ^ 2 * S.termDisc γ)‖ := by
    rw [hγ.det_gram_linkVectors_mul]
  obtain ⟨-, h_minor : leadingMinor (S.frameProducts γ) j ≠ 0, -⟩ := hγ
  rw [eq_div_iff (by simpa using h_minor)]
  simpa [sq] using h_det

/-- If the discriminant `𝗀 = S.termDisc γ` of the frame and its image under `γ` is not zero, then
`z⁺` and `Υ_γ⁻¹ z⁺`, the columns of `linkVectors γ` (with `Υ_γ = linkIsometry γ`), are linearly
independent. -/
theorem linearIndependent_linkVectors (h_disc : S.termDisc γ ≠ 0) :
    LinearIndependent E (linkVectors γ).col := by
  have hγ : S.HasCellRank ⊤ γ := hasCellRank_last h_disc
  have h_det : ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det ≠ 0 := fun h_zero ↦ by
    simpa [h_zero, h_disc, S.N_prime.ne_zero] using hγ.det_gram_linkVectors_mul
  have h_ker (x : Fin 2 → E) (hx : linkVectors γ *ᵥ x = 0) : x = 0 := by
    refine eq_zero_of_mulVec_eq_zero h_det ?_
    rw [← mulVec_mulVec, hx, mulVec_zero]
  exact mulVec_injective_iff.1 ((injective_iff_map_eq_zero (linkVectors γ).mulVecLin).2 h_ker)

/-- If the discriminant `𝗀` of the frame and its image under `γ` is not zero, then the product over
the `f` infinite places `v` of the modulus of the Gram determinant of `z⁺` and `Υ_γ⁻¹ z⁺` under the
embedding `Φ v` is `N ^ f Nm 𝗀 / 𝗀♯`. Here `Υ_γ` is the link isometry of `γ`, the prime `N = S.N`
is the norm of `z⁺`, and `Nm 𝗀 = S.termDiscNorm γ` is the same product for `𝗀`. The gauge
`𝗀♯ = S.minorGauge ⊤ c c' γ` at the top cell rank is the absolute norm of the determinant of the
products of the two frames, divided by `N ^ f`: the two indices through which the gauge depends on
the classes `c` and `c'` are `1` at this rank. -/
theorem prod_norm_det_gram_linkVectors [HasPrimitiveRoot5040 E] (h_disc : S.termDisc γ ≠ 0)
    (c c' : S.Classes) :
    ∏ v : InfinitePlace E, ‖Φ v ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det‖ =
      S.N ^ numInfPlaces E * S.termDiscNorm γ / S.minorGauge ⊤ c c' γ := by
  have hγ : S.HasCellRank ⊤ γ := hasCellRank_last h_disc
  have h_top : ((⊤ : Fin (𝔰.ϱ + 2)) : ℕ) - 𝔰.ϱ = 1 := by simp
  -- At the top cell rank both indices in the gauge are `1`.
  have h_gauge : S.minorGauge ⊤ c c' γ =
      (∏ v : InfinitePlace E, ‖Φ v (leadingMinor (S.frameProducts γ) ⊤)‖ ^ 2) /
        S.N ^ numInfPlaces E := by
    rw [hγ.minorGauge_eq, isotropicRowsIndex_top, isotropicRowsIndex_top, minorNorm,
      abs_norm_eq_prod_norm_sq,
      h_top, mul_one, pow_mul', Nat.cast_one]
    field_simp [S.N_prime.ne_zero]
  simp only [hγ.norm_det_gram_linkVectors, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [h_gauge, termDiscNorm, Finset.prod_const, Finset.card_univ, div_div_eq_mul_div]
  ring

/-- Let `E` contain a primitive 5040th root of unity. If the discriminant `𝗀` of the frame and its
image under `γ` is not zero, then `z⁺` and `Υ_γ⁻¹ z⁺` are linearly independent, and the lattice that
they span has the discriminant `N ^ f Nm 𝗀 / 𝗀♯`. The discriminant is the product over the `f`
infinite places `v` of the modulus of the Gram determinant under the embedding `Φ v`,
`Nm 𝗀 = S.termDiscNorm γ` is the same product for `𝗀`, and `𝗀♯` is the gauge `minorGauge` at the top
cell rank, for any classes `c` and `c'`. -/
theorem linearIndependent_linkVectors_and_prod_norm_det [HasPrimitiveRoot5040 E]
    (h_disc : S.termDisc γ ≠ 0) (c c' : S.Classes) :
    LinearIndependent E (linkVectors γ).col ∧
    ∏ v : InfinitePlace E, ‖Φ v ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).det‖ =
      S.N ^ numInfPlaces E * S.termDiscNorm γ / S.minorGauge ⊤ c c' γ :=
  ⟨linearIndependent_linkVectors h_disc, prod_norm_det_gram_linkVectors h_disc c c'⟩

/-! ### The two vectors as pairs in the link -/

/-- The index in `linkVectors γ = (z⁺, Υ_γ⁻¹ z⁺)` of the vector that represents the product with
`z` on each half of a pair: `Υ_γ⁻¹ z⁺` for the first half and `z⁺` for the second half, on which
this is the product with `γ z` before the pair is formed. -/
def zFormIndex : Unit ⊕ Unit → Fin 2 := Sum.elim (fun _ ↦ 1) fun _ ↦ 0

lemma zFormIndex_injective : zFormIndex.Injective := by decide

/-- The two pairs in the link of `γ` (the graph of `Υ_γ`) with the sources `-Υ_γ⁻¹ z⁺` (column
`inl ()`) and `-z⁺` (column `inr ()`). -/
def linkVectorPairs (γ : S.G E) : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) (Unit ⊕ Unit) E :=
  (of fun a : Unit ⊕ Unit ↦
    ((linkSourceEquiv γ).symm (-(linkVectors γ).col (zFormIndex a))).val)ᵀ

lemma col_linkVectorPairs_mem (γ : S.G E) (a : Unit ⊕ Unit) : (linkVectorPairs γ).col a ∈ link γ :=
  ((linkSourceEquiv γ).symm (-(linkVectors γ).col (zFormIndex a))).prop

lemma linkSource_col_linkVectorPairs (γ : S.G E) (a : Unit ⊕ Unit) :
    linkSource E 𝔰 ((linkVectorPairs γ).col a) = -(linkVectors γ).col (zFormIndex a) :=
  (linkSourceEquiv γ).apply_symm_apply _

/-- The link of `γ` (`link γ`) consists of the pairs of the classes of `t` and `γ⁻¹ t` modulo `A`,
for `t` orthogonal to `A` and `γ A`. Write such a pair as `p = (y₀ + λ' z, y₀' + λ z)`, so that `λ'`
is the `z`-coordinate of the first class and `λ` that of the second; its source `linkSource E 𝔰 p`
is `y₀ + λ z⁺`. The two columns of `linkVectorPairs γ` are the pairs with the sources `-Υ_γ⁻¹ z⁺`
(column `inl ()`) and `-z⁺` (column `inr ()`). The product of column `a` with `p`, for the form
`S.linkMetric` on pairs, is minus the product of column `zFormIndex a` of `linkVectors γ` with
`y₀ + λ z⁺`, for the form `S.positiveGram` of `X₀ ⊥ E z⁺`. -/
lemma conjTranspose_linkVectorPairs_mul_mulVec_apply {p : 𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex → E}
    (hp : p ∈ link γ) (a : Unit ⊕ Unit) :
    (((linkVectorPairs γ)ᴴ * S.linkMetric) *ᵥ p) a =
      -(((linkVectors γ)ᴴ * S.positiveGram) *ᵥ linkSource E 𝔰 p) (zFormIndex a) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  change star ((linkVectorPairs γ).col a) ⬝ᵥ S.linkMetric *ᵥ p =
    -(star ((linkVectors γ).col (zFormIndex a)) ⬝ᵥ S.positiveGram *ᵥ linkSource E 𝔰 p)
  rw [linkMetric_form_of_mem_link (col_linkVectorPairs_mem γ a) hp, linkSource_col_linkVectorPairs,
    star_neg, neg_dotProduct]

omit [CMType E] in
lemma col_mem_of_colSpan_le {m σ : Type} [Fintype σ] {y : Matrix m σ E} {V : Submodule E (m → E)}
    (hy : colSpan y ≤ V) (a : σ) : y.col a ∈ V := by
  classical exact hy ⟨Pi.single a 1, y.mulVec_single_one a⟩

/-- Let the columns of `w` lie in the link of `γ`. Their products with the columns of
`linkVectorPairs γ` for `S.linkMetric` are the two rows `zRowBlockDiagonal (S.ratMiddle E)` applied
to them: the products with `z` on each half of a pair. -/
lemma linkVectorPairs_mul_linkMetric_mul {σ : Type} [Fintype σ]
    {w : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) σ E} (hw : colSpan w ≤ link γ) :
    (linkVectorPairs γ)ᴴ * S.linkMetric * w = zRowBlockDiagonal (S.ratMiddle E) * w := by
  ext a i
  have h_mem : w.col i ∈ link γ := col_mem_of_colSpan_le hw i
  change (((linkVectorPairs γ)ᴴ * S.linkMetric) *ᵥ w.col i) a =
    (zRowBlockDiagonal (S.ratMiddle E) *ᵥ w.col i) a
  rw [conjTranspose_linkVectorPairs_mul_mulVec_apply h_mem, linkVectors_mulVec,
    linkIsometry_linkSource h_mem]
  cases a <;> simp [zFormIndex, linkSource, linkTarget, Shape.middleGram, mulVec, dotProduct]

/-- The Gram matrix of the two columns of `linkVectorPairs γ` for `S.linkMetric` equals the Gram
matrix of `Υ_γ⁻¹ z⁺` and `z⁺` for `S.positiveGram`: that is, the Gram matrix of the columns of
`linkVectors γ`, reindexed by `zFormIndex`. -/
lemma gram_linkVectorPairs (γ : S.G E) :
    (linkVectorPairs γ)ᴴ * S.linkMetric * linkVectorPairs γ =
      ((linkVectors γ)ᴴ * S.positiveGram * linkVectors γ).submatrix zFormIndex zFormIndex := by
  ext a b
  change (((linkVectorPairs γ)ᴴ * S.linkMetric) *ᵥ (linkVectorPairs γ).col b) a =
    (((linkVectors γ)ᴴ * S.positiveGram) *ᵥ (linkVectors γ).col (zFormIndex b)) (zFormIndex a)
  rw [conjTranspose_linkVectorPairs_mul_mulVec_apply (col_linkVectorPairs_mem γ b),
    linkSource_col_linkVectorPairs,
    mulVec_neg, Pi.neg_apply, neg_neg]

end New.Filling
