import New.Spanning.RemainingTerms.Discriminants
import New.Spanning.RemainingTerms.OrthogonalLifts
import New.Spanning.Unfolding.ReducedPoints

/-!
# The lattice of a link

Let `γ` be a term of cell rank `j`, `Λ` the lattice of a class, `A` the span of `e₁, …, e_ϱ`,
`I = A ∩ γ A`, `z` the last vector of the frame, of norm `-N`, and `M = S.M` the level of the
congruence group. The vectors of `Λ` orthogonal to `A` and `γ A` give a lattice `L¹` in the link of
`γ`, and those whose `e_a`-coordinates are divisible by `M` give the lattice `L⁺_γ`. The lattice
`L¹` is realized as an orthogonal complement: adjoin two vectors `z'`, `z''` of norm `N` to the
unimodular lattice `(Λ ∩ I^⊥)/(Λ ∩ I)` (`New.IsQuotientBasis`), and take the complement of the
isotropic lists `(e_a, z + z')` and `(γ e_a, γ z + z'')`, `a < j`.

Notions from other files:
* `linkMatrix γ` sends `t` to the middle coordinates of `t` and `γ⁻¹ t`; `link γ` is its image of
  the orthogonal complement of `A + γ A`.
* `HasCellRank j γ` says that `γ` has cell rank `j`: `NormOnePairOccursFrom j γ`, the leading
  `j`-minor of the products of the two frames is nonzero, and `S.termDisc γ ≠ 0` exactly when
  `j = ϱ + 1`.
* `isotropicRowsIndex j k` is the index, among the products of `Λ ∩ A` with the frame of `k`, of
  those from the `e_a`, `a < j`; `torsionIndex k` is the index of the lattice spanned by the
  `e_a` and `k e_a` in the integral vectors of their span.
* `isotropicFramePair γ` has the columns `e₁, …, e_ϱ` and their images under `γ`.
* `New.Filling.IsOrthogonalLift` (earlier file): vectors orthogonal to `A` and `γ A` over the
  columns of `(0 | v)`, whose first columns are a basis of `I`.

## Main definitions and results

* `New.Filling.exists_lifts_linkDiscSq_le`: the discriminant of `L¹`.
* `New.Filling.exists_hasLevelLifts_linkDiscSq_le`: the discriminant of `L⁺_γ`.
-/

namespace New.Filling

open Matrix Fintype Equiv Fin Algebra Sum Submodule RingHom Pointwise

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {τ : Type}
  {S : Filling E 𝔰} {c c' : S.Classes} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}

/-! ### The discriminant of `L¹` -/

/-- The first columns of an orthogonal lift, a basis of `I = A ∩ γ A`, extend to a basis of `I^⊥`
over `E` for the form `S.ratGram`: for some `y` the columns of `(u₁ | y)`, with `u₁` these first
columns, have a left inverse, are orthogonal to `I`, and are as many as the dimension of `I^⊥`. -/
lemma IsOrthogonalLift.exists_basis_orthogonal {v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E}
    {u : Matrix 𝔰.BesselIndex (IndexNotBelow j ⊕ τ) E} (hu : IsOrthogonalLift j γ v u) :
    ∃ (r : ℕ) (y : Matrix 𝔰.BesselIndex (Fin r) E), HasLeftInv (fromCols u.toCols₁ y) ∧
      u.toCols₁ᴴ * S.ratGram * fromCols u.toCols₁ y = 0 ∧
      card 𝔰.BesselIndex = card (IndexNotBelow j ⊕ Fin r) + card (IndexNotBelow j) := by
  -- The pairing with `u₁` is onto, as the vectors `e*_b`, `b ≥ j`, are dual to `u₁`, so its kernel
  -- `I^⊥` has the codimension `card (IndexNotBelow j)`. It contains the columns of `u₁`.
  let φ : (𝔰.BesselIndex → E) →ₗ[E] IndexNotBelow j → E :=
    (u.toCols₁ᴴ * S.ratGram).mulVecLin
  have h_dual : (eStarCols E j)ᴴ * S.ratGram * u.toCols₁ = 1 := congrArg toCols₁ hu.dual
  have h_self : u.toCols₁ᴴ * S.ratGram * u.toCols₁ = 0 := congrArg toCols₁ hu.toCols₁_mul_self
  have h_le : colSpan u.toCols₁ ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    simp [φ, mulVec_mulVec, ← Matrix.mul_assoc, h_self]
  have h_det : ((eStarCols E j)ᴴ * S.ratGram * u.toCols₁).det ≠ 0 := by simp [h_dual]
  obtain ⟨r, y, h⟩ := exists_isKernelExtension h_det h_le
  refine ⟨r, y, h.hasLeftInv, mul_eq_zero_of_colSpan_le_ker h.colSpan_fromCols.le, ?_⟩
  have h_right : u.toCols₁ᴴ * S.ratGram * eStarCols E j = 1 := by
    simpa [Matrix.mul_assoc, Floors.IsHermitianUnit.conjTranspose_eq] using congrArg conjTranspose
      h_dual
  have h_range : φ.range = ⊤ := by
    refine LinearMap.range_eq_top.2 fun x ↦ ⟨eStarCols E j *ᵥ x, ?_⟩
    rw [mulVecLin_apply, mulVec_mulVec, h_right, one_mulVec]
  have h_ker : Module.finrank E φ.ker = card (IndexNotBelow j ⊕ Fin r) := by
    rw [card_eq_finrank_colSpan h.hasLeftInv, h.colSpan_fromCols]
  calc
    card 𝔰.BesselIndex = Module.finrank E (𝔰.BesselIndex → E) :=
      (Module.finrank_fintype_fun_eq_card E).symm
    _ = Module.finrank E φ.range + Module.finrank E φ.ker :=
      φ.finrank_range_add_finrank_ker.symm
    _ = card (IndexNotBelow j ⊕ Fin r) + card (IndexNotBelow j) := by
      rw [h_range, finrank_top, h_ker, Module.finrank_fintype_fun_eq_card, add_comm]

section Classes

variable {v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E}
  {u : Matrix 𝔰.BesselIndex (IndexNotBelow j ⊕ τ) E} {μ : Type} [Fintype μ] [DecidableEq μ]
  {a : GL (IndexNotBelow j) (𝔸f E)} {B : Matrix 𝔰.BesselIndex μ (𝔸f E)}
  {q : Matrix μ 𝔰.BesselIndex (𝔸f E)} {ρ ρ' : Type}
  {t : Matrix 𝔰.BesselIndex ρ E} {t' : Matrix 𝔰.BesselIndex ρ' E}

variable (c q) in
/-- The coordinates of the classes modulo `I` of the rational vectors `t`, where `q` reads the
coordinates in `(Λ ∩ I^⊥)/(Λ ∩ I)` for the lattice `Λ` of the class `c`. -/
noncomputable abbrev classOf (t : Matrix 𝔰.BesselIndex ρ E) : Matrix μ ρ (𝔸f E) :=
  q * (S.classCoord c * finAdeleMatrix t)

/-- Let the first columns `u₁` of `u` span `I`. If the rational vectors `t` are orthogonal to `I`,
then in the lattice coordinates `S.classCoord c` of the class `c` they are orthogonal to every
adelic basis `u₁ a` of `I`. -/
lemma classCoord_orthogonal (ht : u.toCols₁ᴴ * S.ratGram * t = 0)
    (a : GL (IndexNotBelow j) (𝔸f E)) :
    (S.classCoord c * finAdeleMatrix u.toCols₁ * a.val)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram *
      (S.classCoord c * finAdeleMatrix t) = 0 := by
  classical
  rw [conjTranspose_mul, Matrix.mul_assoc a.valᴴ, Matrix.mul_assoc a.valᴴ, classCoord_gram, ht]
  simp

/-- Let `c` be a class in `S.Classes`, `Λ` its lattice, and `I` the span of the first columns
`u.toCols₁` of the rational matrix `u`. In `S.classCoord c`-coordinates, the invertible `a` turns
`u.toCols₁` into a basis of `Λ ∩ I`. Let `B` be a basis of `(Λ ∩ I^⊥)/(Λ ∩ I)` with coordinates `q`.
Take rational `t`, `t'` orthogonal to `I` for `S.ratGram`. Then their classes `classOf c q t`,
`classOf c q t'` have products for `Bᴴ * splitGram * B` equal to `tᴴ * S.ratGram * t'`, embedded in
the finite adeles by `finAdeleMatrix`. -/
lemma gram_classOf
    (hq : IsQuotientBasis (Ô E) (S.latticeMiddle (𝔸f E)).splitGram
      (S.classCoord c * finAdeleMatrix u.toCols₁ * a.val) B q)
    (ht : u.toCols₁ᴴ * S.ratGram * t = 0) (ht' : u.toCols₁ᴴ * S.ratGram * t' = 0) :
    (classOf c q t)ᴴ * (Bᴴ * (S.latticeMiddle (𝔸f E)).splitGram * B) * classOf c q t' =
      finAdeleMatrix (tᴴ * S.ratGram * t') := by
  classical
  have h_herm : (S.latticeMiddle (𝔸f E)).splitGramᴴ = (S.latticeMiddle (𝔸f E)).splitGram :=
    (S.isUnimodular_latticeMiddle.splitGram (R := Ô E)).1
  rw [hq.gram_coord h_herm (classCoord_orthogonal ht a) (classCoord_orthogonal ht' a),
    classCoord_gram]

/-- If `u` is an orthogonal lift (`New.Filling.IsOrthogonalLift`), its first columns, a basis of
`I = A ∩ γ A`, are orthogonal to the others for the form `S.ratGram`. -/
lemma IsOrthogonalLift.toCols₁_mul_toCols₂ (hu : IsOrthogonalLift j γ v u) :
    u.toCols₁ᴴ * S.ratGram * u.toCols₂ = 0 :=
  congrArg toCols₂ hu.toCols₁_mul_self

/-- The first columns of an orthogonal lift are orthogonal to the `e_a` and the `γ e_a`. -/
lemma IsOrthogonalLift.toCols₁_mul_isotropicFramePair (hu : IsOrthogonalLift j γ v u) :
    u.toCols₁ᴴ * S.ratGram * isotropicFramePair γ = 0 :=
  -- These are columns of the frame pair of `γ`.
  Matrix.ext fun x _ ↦ congrFun₂ hu.toCols₁_mul_framePair x _

/-- The first columns of an orthogonal lift are orthogonal to `z` and `γ z`, for `z` the last
vector of the frame. -/
lemma IsOrthogonalLift.toCols₁_mul_lastPair (hu : IsOrthogonalLift j γ v u) :
    u.toCols₁ᴴ * S.ratGram * lastPair γ = 0 :=
  -- These are columns of the frame pair of `γ`.
  Matrix.ext fun x _ ↦ congrFun₂ hu.toCols₁_mul_framePair x _

/-- In the lattice coordinates of the class `c`, the vectors `e_a`, `γ e_a`, `a < j`, are the
vectors `e_a`, `k e_a` for `k = S.translateByClassReps c c' γ`. -/
lemma classCoord_mul_listPair :
    S.classCoord c * finAdeleMatrix (listPair j γ) = listPair j (S.translateByClassReps c c' γ) :=
  Matrix.ext fun x _ ↦ congrFun₂ classCoord_mul_isotropicFramePair x _

/-- Let `u` be an orthogonal lift of `v`, and let `B` be a basis with coordinates `q` of the
quotient `(Λ ∩ I^⊥)/(Λ ∩ I)` of the lattice `Λ` of the class `c`. The representatives `B q t` of the
classes of the lifts `t = u.toCols₂` of `v` are adelic combinations `u w` of the columns of `u`, and
`linkMatrix γ` again sends them to the columns of `v`. -/
lemma IsOrthogonalLift.exists_mul_classOf_eq_and_linkMatrix_mul_eq [Fintype τ] [DecidableEq τ]
    (hu : IsOrthogonalLift j γ v u)
    (hq : IsQuotientBasis (Ô E) (S.latticeMiddle (𝔸f E)).splitGram
      (S.classCoord c * finAdeleMatrix u.toCols₁ * a.val) B q) :
    ∃ w : Matrix (IndexNotBelow j ⊕ τ) τ (𝔸f E),
      B * classOf c q u.toCols₂ = S.classCoord c * finAdeleMatrix u * w ∧
      finAdeleMatrix (linkMatrix γ * u) * w = finAdeleMatrix v := by
  -- A vector `x` orthogonal to `I` is `ι (l x) + B (q x)`, for the basis `ι` of `I`.
  obtain ⟨l, -, hl⟩ := hq.exists_eq_add
  set t : Matrix 𝔰.BesselIndex τ (𝔸f E) := S.classCoord c * finAdeleMatrix u.toCols₂
  have h_split : S.classCoord c * finAdeleMatrix u =
      fromCols (S.classCoord c * finAdeleMatrix u.toCols₁) t :=
    (fromCols_toCols _).symm
  have h_class : t = S.classCoord c * finAdeleMatrix u.toCols₁ * a.val * (l * t) + B * (q * t) :=
    hl (classCoord_orthogonal hu.toCols₁_mul_toCols₂ a)
  refine ⟨fromRows (-(a.val * (l * t))) 1, ?_, ?_⟩
  · rw [h_split, fromCols_mul_fromRows, Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc _ a.val]
    exact eq_neg_add_of_add_eq h_class.symm
  · rw [hu.linkMatrix_mul, finAdeleMatrix, fromCols_map, fromCols_mul_fromRows]
    simp

/-- Let `u` be an orthogonal lift of `v` at `j`. Its first columns `u₁ = u.toCols₁`, one for each
`b ≥ j`, then lie in `A`. Let `a` be an invertible matrix over the finite adeles `𝔸f E`. Write the
columns of `u₁ a` in the basis of the lattice of `c`, by `S.classCoord c`, and suppose that their
entries lie in the ring `Ô E` of integral finite adeles. Then for every `k` in the finite-adelic
unitary group, each of these columns lies in the `Ô E`-span `colLattice` of the columns
`e₁, …, e_ϱ, k e₁, …, k e_ϱ` of `isotropicFramePair k`. -/
lemma IsOrthogonalLift.col_mem_colLattice_isotropicFramePair {τ : Type} {S : Filling E 𝔰}
    {c : S.Classes} {j : Fin (𝔰.ϱ + 2)} {γ : S.G E}
    {v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E}
    {u : Matrix 𝔰.BesselIndex (IndexNotBelow j ⊕ τ) E} {a : GL (IndexNotBelow j) (𝔸f E)}
    (hu : IsOrthogonalLift j γ v u)
    (h_int : IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix u.toCols₁ * a.val)) (k : S.GFin)
    (x : IndexNotBelow j) :
    (S.classCoord c * finAdeleMatrix u.toCols₁ * a.val).col x ∈
      colLattice (Ô E) (isotropicFramePair k) := by
  -- The column lies in `A`, so it is the combination of the `e_b` with its own integral entries.
  set ι : Matrix 𝔰.BesselIndex (IndexNotBelow j) (𝔸f E) :=
    S.classCoord c * finAdeleMatrix u.toCols₁ * a.val with hι
  have h_rows (b : 𝔰.MiddleIndex ⊕ Fin 𝔰.ϱ) : ι (inr b) x = 0 := by
    rw [hι, hu.toCols₁_eq_fromRows, classCoord_eq_fromBlocks]
    simp [Matrix.mul_apply]
  let y : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ → 𝔸f E := Sum.elim (fun b ↦ ι (inl b) x) 0
  have hy_int : y ∈ intVectors (Ô E) (Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ) := by
    rintro (b | b)
    · exact h_int (inl b) x
    · exact zero_mem (Ô E)
  have hy_eq : isotropicFramePair k *ᵥ y = ι.col x := by
    ext (b | b)
    · simp [y, mulVec, dotProduct, Matrix.one_apply]
    · simp [y, mulVec, dotProduct, h_rows]
  exact ⟨y, hy_int, hy_eq⟩

/-- Let `u` be an orthogonal lift of `v`, and let `B` be a basis with coordinates `q` of the
quotient `(Λ ∩ I^⊥)/(Λ ∩ I)`, with Gram matrix `J₀`. Let `p` be the classes of `z` and `γ z`, for
`z` the last vector of the frame, of norm `-N`. When `J₀` is bordered to `J₀ + N⁻¹ J₀ p p* J₀`, the
classes of the lifts `u.toCols₂` have the Gram matrix of `v` for `S.linkMetric`, the form on pairs
of middle coordinates that is half the sum of the two middle forms plus `N⁻¹` times the norms of the
products with `z`. -/
lemma IsOrthogonalLift.gram_classOf_add_border (hu : IsOrthogonalLift j γ v u)
    (hq : IsQuotientBasis (Ô E) (S.latticeMiddle (𝔸f E)).splitGram
      (S.classCoord c * finAdeleMatrix u.toCols₁ * a.val) B q)
    (hN : (S.N : E) ≠ 0) :
    let J₀ : Matrix μ μ (𝔸f E) := Bᴴ * (S.latticeMiddle (𝔸f E)).splitGram * B
    let p : Matrix μ (Unit ⊕ Unit) (𝔸f E) := classOf c q (lastPair γ)
    (classOf c q u.toCols₂)ᴴ * (J₀ + (principalIdele (.mk0 (S.N : E) hN))⁻¹ •
        (J₀ * p * pᴴ * J₀)) * classOf c q u.toCols₂ =
      finAdeleMatrix (vᴴ * S.linkMetric * v) := by
  intro J₀ p
  have h_lifts : u.toCols₁ᴴ * S.ratGram * u.toCols₂ = 0 := hu.toCols₁_mul_toCols₂
  have h_last : u.toCols₁ᴴ * S.ratGram * lastPair γ = 0 := hu.toCols₁_mul_lastPair
  have h_border : (classOf c q u.toCols₂)ᴴ * (J₀ * p * pᴴ * J₀) * classOf c q u.toCols₂ =
      (classOf c q u.toCols₂)ᴴ * J₀ * p * (pᴴ * J₀ * classOf c q u.toCols₂) := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h_border,
    gram_classOf hq h_lifts h_lifts, gram_classOf hq h_lifts h_last,
    gram_classOf hq h_last h_lifts, ← hu.gram_add_border]
  simp [Matrix.map_add, Units.smul_def, Matrix.mul_assoc, finAdeleMatrix_conjTranspose,
    Floors.IsHermitianUnit.conjTranspose_eq]

/-- **Jacobi's identity in the quotient.** Let the columns of `v` have the orthogonal lifts `u`, let
`k = S.translateByClassReps c c' γ` be the finite-adelic form of `γ`, and let `B` be a basis with
coordinates `q` of `(Λ ∩ I^⊥)/(Λ ∩ I)`. Suppose that `γ` has cell rank `j`, that the frame pair of
`k` is integral, that the rank of the quotient is twice the number of indices `i < j` plus the
number of columns of `v`, and that the classes of the lifts of `v e` form a primitive matrix. Let
`F` be the classes of the `e_i` and `k e_i` with `i < j`, and `latticeIndex` the index of their
lattice in the integral vectors of their span. Then the squared discriminant `S.linkDiscSq v e` of
the lattice with basis `v e` times `latticeIndex ^ 2` is the square of `S.minorNorm j γ`, the
normalized norm of the leading minor of order `j` of the frame products of `γ`, and `F` spans the
classes of all `e_i` and `k e_i`. -/
lemma IsOrthogonalLift.linkDiscSq_mul_sq_eq [HasPrimitiveRoot5040 E] [Fintype τ] [DecidableEq τ]
    (hu : IsOrthogonalLift j γ v u) (hq : IsQuotientBasis (Ô E) (S.latticeMiddle (𝔸f E)).splitGram
      (S.classCoord c * finAdeleMatrix u.toCols₁ * a.val) B q)
    (hj : S.HasCellRank j γ) (hk : IsIntMatrix (Ô E) (framePair (S.translateByClassReps c c' γ)))
    (h_rank : card μ = card (IndexBelow j ⊕ IndexBelow j) + card τ) {e : GL τ (𝔸f E)}
    (h_prim : IsPrimitiveMatrix (Ô E) (classOf c q u.toCols₂ * e.val)) :
    let F : Matrix μ (IndexBelow j ⊕ IndexBelow j) (𝔸f E) :=
      q * listPair j (S.translateByClassReps c c' γ)
    let latticeIndex : ℕ := submoduleIndex (intVectors (Ô E) (IndexBelow j ⊕ IndexBelow j))
      (preimageLattice (Ô E) F)
    S.linkDiscSq v e * latticeIndex ^ 2 = S.minorNorm j γ ^ 2 ∧
      ∀ x : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ,
        (q * isotropicFramePair (S.translateByClassReps c c' γ)).col x ∈ colSpan F := by
  -- In the quotient adjoin `z'`, `z''` of norm `N`. Jacobi's identity compares the Gram matrix `G`
  -- of the isotropic lists `(e_a, z + z')`, `(γ e_a, γ z + z'')`, `a < j`, with that of the lifts
  -- of `v e`, which are orthogonal to these lists.
  intro F latticeIndex
  set J₀ : Matrix μ μ (𝔸f E) := Bᴴ * (S.latticeMiddle (𝔸f E)).splitGram * B
  have h_isotropic : u.toCols₁ᴴ * S.ratGram * isotropicFramePair γ = 0 :=
    hu.toCols₁_mul_isotropicFramePair
  -- The two lists consist of columns of the isotropic pair.
  have h_list : u.toCols₁ᴴ * S.ratGram * listPair j γ = 0 :=
    Matrix.ext fun x b ↦ congrFun₂ h_isotropic x _
  have h_both : u.toCols₁ᴴ * S.ratGram * fromCols (listPair j γ) (lastPair γ) = 0 := by
    rw [mul_fromCols, h_list, hu.toCols₁_mul_lastPair, fromCols_zero]
  have h_lifts : u.toCols₁ᴴ * S.ratGram * u.toCols₂ = 0 := hu.toCols₁_mul_toCols₂
  have h_perp : (isotropicFramePair γ)ᴴ * S.ratGram * u.toCols₂ = 0 :=
    congrArg toCols₂ hu.orthogonal
  have h_perp_list : (listPair j γ)ᴴ * S.ratGram * u.toCols₂ = 0 :=
    Matrix.ext fun b x ↦ congrFun₂ h_perp _ x
  have hF : F = classOf c q (listPair j γ) := by rw [classOf, classCoord_mul_listPair]
  have hN : (S.N : E) ≠ 0 := by simp [Nat.Prime.ne_zero]
  let N : (𝔸f E)ˣ := principalIdele (.mk0 S.N hN)
  let G : Matrix ((IndexBelow j ⊕ IndexBelow j) ⊕ Unit ⊕ Unit)
      ((IndexBelow j ⊕ IndexBelow j) ⊕ Unit ⊕ Unit) E :=
    (fromCols (listPair j γ) (lastPair γ))ᴴ * S.ratGram *
      fromCols (listPair j γ) (lastPair γ) + fromBlocks 0 0 0 ((S.N : E) • 1)
  have hG : genIndex (finAdeleMatrix G).det =
      (S.N ^ (2 * numInfPlaces E) * S.minorNorm j γ) ^ 2 := by
    rw [← hj.abs_norm_subframeMinor, ← abs_norm_det_gram_eq_abs_norm_subframeMinor_sq,
      ← genIndex_algebraMap, RingHom.map_det]
    rfl
  have hG_gram : finAdeleMatrix G = (fromCols F (classOf c q (lastPair γ)))ᴴ * J₀ *
      fromCols F (classOf c q (lastPair γ)) + fromBlocks 0 0 0 (N • 1) := by
    rw [hF, ← mul_fromCols, ← mul_fromCols, ← fromCols_map, gram_classOf hq h_both h_both]
    simp [G, N, Matrix.map_add, fromBlocks_map, Units.smul_def]
  have h_orth : Fᴴ * J₀ * (classOf c q u.toCols₂ * e.val) = 0 := by
    rw [hF, ← Matrix.mul_assoc, gram_classOf hq h_list h_lifts, h_perp_list]
    simp
  have hG_ne : genIndex (finAdeleMatrix G).det ≠ 0 := by
    simp [hG, hj.minorNorm_pos.ne', Nat.Prime.ne_zero]
  have hJ₀ : IsUnimodular (Ô E) J₀ := hq.isUnimodular S.isUnimodular_latticeMiddle.splitGram
  have hF_int : IsIntMatrix (Ô E) F := hq.isIntMatrix_coord.mul fun x y ↦ hk x _
  let n : Matrix μ τ (𝔸f E) := classOf c q u.toCols₂ * e.val
  let p : Matrix μ (Unit ⊕ Unit) (𝔸f E) := classOf c q (lastPair γ)
  obtain ⟨h_span, h_jacobi⟩ :
      (∀ x : μ → 𝔸f E, nᴴ *ᵥ J₀ *ᵥ x = 0 → x ∈ colSpan F) ∧
        genIndex (nᴴ * (J₀ + N⁻¹ • (J₀ * p * pᴴ * J₀)) * n).det *
          latticeIndex ^ 2 *
          genIndex N.val ^ card (Unit ⊕ Unit) = genIndex (finAdeleMatrix G).det :=
    jacobi_perp_discriminant hJ₀ hF_int h_prim h_orth h_rank p N hG_gram (.inr hG_ne)
  constructor
  · -- The map to the complement of the two lists is an isometry for `S.linkMetric`.
    have h_det : (finAdeleMatrix (vᴴ * S.linkMetric * v)).det =
        algebraMap E (𝔸f E) (vᴴ * S.linkMetric * v).det := (RingHom.map_det _ _).symm
    rw [hG, gram_mul, genIndex_det_conj, hu.gram_classOf_add_border hq hN, h_det,
      genIndex_algebraMap] at h_jacobi
    have h_index : genIndex N.val = (S.N : ℝ) ^ (2 * numInfPlaces E) := by
      simp [N, genIndex_natCast, ← pow_mul, mul_comm 2]
    rw [h_index, card_sum, Fintype.card_unit] at h_jacobi
    refine mul_left_cancel₀ (a := ((S.N : ℝ) ^ (2 * numInfPlaces E)) ^ 2)
      (by simp [Nat.Prime.ne_zero]) ?_
    rw [← mul_pow, ← h_jacobi, linkDiscSq]
    ring
  · have h_zero : (classOf c q u.toCols₂ * e.val)ᴴ * J₀ *
        (q * isotropicFramePair (S.translateByClassReps c c' γ)) = 0 := by
      rw [← classCoord_mul_isotropicFramePair, conjTranspose_mul, Matrix.mul_assoc e.valᴴ,
        Matrix.mul_assoc e.valᴴ, gram_classOf hq h_lifts h_isotropic,
        orthogonal_symm Floors.IsHermitianUnit.conjTranspose_eq h_perp]
      simp
    intro x
    refine h_span _ ?_
    rw [mulVec_mulVec]
    exact funext fun b ↦ congrFun₂ h_zero b x

end Classes

variable [Fintype τ]

/-- Let `γ` be a rational element of cell rank `j` whose adelic form
`k = S.translateByClassReps c c' γ` keeps the standard lattice `Λ₀` and has the image `t` under the
reduction map `S.reduction` to the finite group `S.ResidueGL`. Let the columns of `v` be a basis of
the link of `γ`, and let `A` be the span of the isotropic `e₁, …, e_ϱ`. Let `w` be the product of
three lattice indices: `isotropicRowsIndex j k`, the same for `k⁻¹`, and `torsionIndex k`. Then for
some invertible finite-adelic `e` the columns of `v e` have integral lifts, and the squared
discriminant `linkDiscSq` of their lattice, times `w ^ 2`, is at most the square of
`S.minorNorm j γ`, which is `Nm (S.subframeMinor j γ) / N ^ (2 f)` for `-N` the norm of the last
frame vector and `f` the number of infinite places. Moreover `w ≠ 0`, that is, the three indices are
finite. -/
lemma exists_lifts_linkDiscSq_le [HasPrimitiveRoot5040 E] [DecidableEq τ]
    {t : S.ResidueGL} (hγ : γ ∈ S.termsOver c t c')
    (hj : S.HasCellRank j γ) {v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E}
    (hv : HasLeftInv v) (hL : colSpan v = link γ) :
    let k : S.GFin := S.translateByClassReps c c' γ
    let w : ℝ := S.isotropicRowsIndex j k * S.isotropicRowsIndex j k⁻¹ * S.torsionIndex k
    ∃ e : GL τ (𝔸f E),
      HasIntegralLifts c γ (finAdeleMatrix v * e.val) ∧
      S.linkDiscSq v e * w ^ 2 ≤ S.minorNorm j γ ^ 2 ∧
      w ≠ 0 := by
  -- Pass to the unimodular lattice `(Λ ∩ I^⊥)/(Λ ∩ I)`, and take for `v e` the lattice of the
  -- vectors whose lifts have integral classes.
  intro k w
  obtain ⟨u, hu⟩ : ∃ u : Matrix 𝔰.BesselIndex (IndexNotBelow j ⊕ τ) E,
      IsOrthogonalLift j γ v u :=
    exists_orthogonal_lift hj hL
  obtain ⟨r, y, ⟨l, hl⟩, hy_orth, h_card⟩ : ∃ (r : ℕ) (y : Matrix 𝔰.BesselIndex (Fin r) E),
      HasLeftInv (fromCols u.toCols₁ y) ∧ u.toCols₁ᴴ * S.ratGram * fromCols u.toCols₁ y = 0 ∧
        card 𝔰.BesselIndex = card (IndexNotBelow j ⊕ Fin r) + card (IndexNotBelow j) :=
    hu.exists_basis_orthogonal
  let ι₀ : Matrix 𝔰.BesselIndex (IndexNotBelow j) (𝔸f E) :=
    S.classCoord c * finAdeleMatrix u.toCols₁
  let y' : Matrix 𝔰.BesselIndex (Fin r) (𝔸f E) := S.classCoord c * finAdeleMatrix y
  have hy_inv : HasLeftInv (fromCols ι₀ y') := by
    refine ⟨finAdeleMatrix l * (classBasis c).val, ?_⟩
    rw [← mul_fromCols, ← fromCols_map]
    simp [classCoord, ← Matrix.map_mul, hl, Matrix.mul_assoc]
  have hy'_orth : ι₀ᴴ * (S.latticeMiddle (𝔸f E)).splitGram * fromCols ι₀ y' = 0 := by
    rw [← mul_fromCols, ← fromCols_map, classCoord_gram, hy_orth]
    simp
  obtain ⟨a, B, q, hι_int, hq⟩ : ∃ (a : GL (IndexNotBelow j) (𝔸f E))
      (B : Matrix 𝔰.BesselIndex (Fin r) (𝔸f E)) (q : Matrix (Fin r) 𝔰.BesselIndex (𝔸f E)),
      IsIntMatrix (Ô E) (ι₀ * a.val) ∧
        IsQuotientBasis (Ô E) (S.latticeMiddle (𝔸f E)).splitGram (ι₀ * a.val) B q :=
    exists_isQuotientBasis S.isUnimodular_latticeMiddle.splitGram hy_inv hy'_orth h_card
  obtain ⟨w', h_rep, h_image⟩ : ∃ w' : Matrix (IndexNotBelow j ⊕ τ) τ (𝔸f E),
      B * classOf c q u.toCols₂ = S.classCoord c * finAdeleMatrix u * w' ∧
        finAdeleMatrix (linkMatrix γ * u) * w' = finAdeleMatrix v :=
    hu.exists_mul_classOf_eq_and_linkMatrix_mul_eq hq
  have h_inv : HasLeftInv (classOf c q u.toCols₂) := by
    obtain ⟨l', hl'⟩ := hv
    have h_coord : finAdeleMatrix (linkMatrix γ) * (classBasis c).val *
        (S.classCoord c * finAdeleMatrix u) = finAdeleMatrix (linkMatrix γ * u) := by
      simp [classCoord, Matrix.mul_assoc]
    refine ⟨finAdeleMatrix l' * (finAdeleMatrix (linkMatrix γ) * (classBasis c).val * B), ?_⟩
    rw [Matrix.mul_assoc, Matrix.mul_assoc _ B, h_rep, ← Matrix.mul_assoc _ _ w', h_coord,
      h_image, ← Matrix.map_mul, hl']
    simp
  obtain ⟨e, -, h_prim⟩ : ∃ e : GL τ (𝔸f E),
      preimageLattice (Ô E) (classOf c q u.toCols₂) = colLattice (Ô E) e.val ∧
        IsPrimitiveMatrix (Ô E) (classOf c q u.toCols₂ * e.val) :=
    exists_preimageLattice_eq_colLattice h_inv
  have hk_int : IsIntMatrix (Ô E) (framePair k) :=
    isIntMatrix_framePair (termsOver.isIntMatrix_translateByClassReps hγ)
  have h_rank : card (Fin r) = card (IndexBelow j ⊕ IndexBelow j) + card τ := by
    have h_link : card τ = card 𝔰.κ + 1 := by rw [card_eq_finrank_colSpan hv, hL, finrank_link]
    have h_levels : card (IndexBelow j) + card (IndexNotBelow j) = 𝔰.ϱ := by
      rw [← card_sum, card_congr (sumCompl fun a : Fin 𝔰.ϱ ↦ a.1 < j), Fintype.card_fin]
    simp only [card_sum, Fintype.card_unit, Fintype.card_fin] at h_card ⊢
    omega
  let latticeIndex : ℕ := submoduleIndex (intVectors (Ô E) (IndexBelow j ⊕ IndexBelow j))
    (preimageLattice (Ô E) (q * listPair j k))
  obtain ⟨h_eq, h_span⟩ : S.linkDiscSq v e * latticeIndex ^ 2 = S.minorNorm j γ ^ 2 ∧
      ∀ x : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ, (q * isotropicFramePair k).col x ∈ colSpan (q * listPair j k) :=
    hu.linkDiscSq_mul_sq_eq hq hj hk_int h_rank h_prim
  have h_frames : (ι₀ * a.val)ᴴ * (S.latticeMiddle (𝔸f E)).splitGram * framePair k = 0 := by
    rw [← classCoord_mul_framePair (c := c) (c' := c')]
    exact classCoord_orthogonal hu.toCols₁_mul_framePair a
  have h_dvd : S.isotropicRowsIndex j k * S.isotropicRowsIndex j k⁻¹ * S.torsionIndex k ∣
      latticeIndex :=
    isotropicRowsIndex_mul_dvd_submoduleIndex hq hk_int h_frames
      (hu.col_mem_colLattice_isotropicFramePair hι_int k) h_span
  -- As the minor is not zero, the index is finite, so its divisor is nonzero and at most as large.
  have h_index_ne : latticeIndex ≠ 0 := by
    intro h_zero
    have h_minor : S.minorNorm j γ ^ 2 = 0 := by
      rw [← h_eq, h_zero]
      simp
    exact (pow_pos hj.minorNorm_pos 2).ne' h_minor
  obtain ⟨h_ne, h_le⟩ :
      S.isotropicRowsIndex j k * S.isotropicRowsIndex j k⁻¹ * S.torsionIndex k ≠ 0 ∧
        S.isotropicRowsIndex j k * S.isotropicRowsIndex j k⁻¹ * S.torsionIndex k ≤
          latticeIndex :=
    ne_zero_and_le_of_dvd h_index_ne h_dvd
  have h_lift_int : IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix u * (w' * e.val)) := by
    rw [← Matrix.mul_assoc, ← h_rep, Matrix.mul_assoc]
    obtain ⟨hn_int, -⟩ := h_prim
    exact hq.isIntMatrix_basis.mul hn_int
  have h_lift_image :
      finAdeleMatrix (linkMatrix γ * u) * (w' * e.val) = finAdeleMatrix v * e.val := by
    rw [← Matrix.mul_assoc, h_image]
  refine ⟨e, ⟨IndexNotBelow j ⊕ τ, inferInstance, u, w' * e.val, hu.orthogonal, h_lift_int,
    h_lift_image⟩, ?_, ?_⟩
  · unfold w
    rw [← h_eq, linkDiscSq]
    gcongr
    exact_mod_cast h_le
  · unfold w
    exact_mod_cast h_ne

/-- For a term `γ` of cell rank `j` from `c'` to `c`, with reduction `s`, the lattice indices
`isotropicRowsIndex` at `k = h_c⁻¹ γ h_c'` and at `k⁻¹` and `torsionIndex` at `k` are finite,
that is, nonzero (an infinite index is `0`). -/
lemma isotropicRowsIndex_mul_torsionIndex_ne_zero [HasPrimitiveRoot5040 E]
    {s : S.ResidueGL} (hγ : γ ∈ S.termsOver c s c') (hj : S.HasCellRank j γ) :
    S.isotropicRowsIndex j (S.translateByClassReps c c' γ) * S.isotropicRowsIndex j
      (S.translateByClassReps c c' γ)⁻¹ *
      S.torsionIndex (S.translateByClassReps c c' γ) ≠ 0 := by
  obtain ⟨v, hv_inv, hv_span⟩ : ∃ v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex)
      (Fin (Module.finrank E (link γ))) E, HasLeftInv v ∧ colSpan v = link γ :=
    exists_hasLeftInv_colSpan_eq (link γ)
  obtain ⟨-, -, -, h_ne⟩ := exists_lifts_linkDiscSq_le hγ hj hv_inv hv_span
  exact_mod_cast h_ne

/-- For a term of cell rank `j`, the index `isotropicRowsIndex` at `h_c⁻¹ γ h_c'` is finite, hence
positive. -/
lemma isotropicRowsIndex_pos [HasPrimitiveRoot5040 E] {s : S.ResidueGL}
    (hγ : γ ∈ S.termsOver c s c') (hj : S.HasCellRank j γ) :
    0 < S.isotropicRowsIndex j (S.translateByClassReps c c' γ) :=
  (left_ne_zero_of_mul (left_ne_zero_of_mul
    (isotropicRowsIndex_mul_torsionIndex_ne_zero hγ hj))).pos
/-- For a term of cell rank `j`, the index `isotropicRowsIndex` at the inverse of `h_c⁻¹ γ h_c'` is
finite, hence positive. -/
lemma isotropicRowsIndex_inv_pos [HasPrimitiveRoot5040 E] {s : S.ResidueGL}
    (hγ : γ ∈ S.termsOver c s c') (hj : S.HasCellRank j γ) :
    0 < S.isotropicRowsIndex j (S.translateByClassReps c c' γ)⁻¹ :=
  (right_ne_zero_of_mul (left_ne_zero_of_mul
    (isotropicRowsIndex_mul_torsionIndex_ne_zero hγ hj))).pos
/-- For a term `γ` over `(c, s, c')` (`termsOver`) of cell rank `j`, the index `torsionIndex` at
`h_c⁻¹ γ h_c'` is finite, hence positive. -/
lemma torsionIndex_pos [HasPrimitiveRoot5040 E] {s : S.ResidueGL} (hγ : γ ∈ S.termsOver c s c')
    (hj : S.HasCellRank j γ) :
    0 < S.torsionIndex (S.translateByClassReps c c' γ) :=
  (right_ne_zero_of_mul (isotropicRowsIndex_mul_torsionIndex_ne_zero hγ hj)).pos

/-- The gauge `maxGauge` of a term of cell rank `j` is positive: it is the larger of
`termDiscNorm` and `N ^ f` times the norm `minorNorm` of the leading minor (`f` the number of
infinite places), divided by two positive indices. -/
lemma maxGauge_pos [HasPrimitiveRoot5040 E] {s : S.ResidueGL} (hγ : γ ∈ S.termsOver c s c')
    (hj : S.HasCellRank j γ) :
    0 < S.maxGauge j c c' γ := by
  have h_minor : 0 < S.minorNorm j γ := hj.minorNorm_pos
  have hN : 0 < S.N := S.N_prime.pos
  have h_indices : 0 < (S.isotropicRowsIndex j (S.translateByClassReps c c' γ) : ℝ) *
      S.isotropicRowsIndex j (S.translateByClassReps c c' γ)⁻¹ :=
    mul_pos (Nat.cast_pos.2 (isotropicRowsIndex_pos hγ hj))
      (Nat.cast_pos.2 (isotropicRowsIndex_inv_pos hγ hj))
  have h_top : 0 < (S.N : ℝ) ^ numInfPlaces E * S.minorNorm j γ := by positivity
  rw [hj.maxGauge_eq]
  exact div_pos (lt_sup_of_lt_right h_top) h_indices

/-! ### The discriminant of `L⁺_γ` -/

variable (c γ) in
/-- The columns of `m` lie in the lattice `L⁺_γ`: they have integral lifts
(`New.Filling.HasIntegralLifts`) whose parts in the isotropic space `A` are divisible by the level
`M`. These are the lifts in `M (Λ ∩ A) ⊕ Λ⁺`, where `Λ` is the lattice of `c` and
`Λ⁺ = Λ ∩ (X₀ ⊕ E z)`, with `X₀ ⊕ E z` the middle space of the frame. -/
def HasLevelLifts (m : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ (𝔸f E)) : Prop :=
  ∃ ρ : Type, ∃ (_ : Fintype ρ) (t : Matrix 𝔰.BesselIndex ρ E) (w : Matrix ρ τ (𝔸f E)),
    (isotropicFramePair γ)ᴴ * S.ratGram * t = 0 ∧
    IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix t * w) ∧
    IsIntMatrix (Ô E) (S.ideleM⁻¹ • (S.classCoord c * finAdeleMatrix t * w).toRows₁) ∧
    finAdeleMatrix (linkMatrix γ * t) * w = m

section LevelLifts

variable {σ : Type} {m : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ (𝔸f E)}

omit [Fintype τ] in
/-- Columns in the lattice `L⁺_γ` (`HasLevelLifts`) have integral lifts. -/
lemma HasLevelLifts.hasIntegralLifts (h_lift : HasLevelLifts c γ m) : HasIntegralLifts c γ m := by
  obtain ⟨ρ, _, t, w, h_orth, h_int, -, h_eq⟩ := h_lift
  exact ⟨ρ, _, t, w, h_orth, h_int, h_eq⟩

/-- If the columns of `m` lie in the lattice `L⁺_γ` (`HasLevelLifts`), so do those of `m V` for
every integral `V`. -/
lemma HasLevelLifts.mul (h_lift : HasLevelLifts c γ m) {V : Matrix τ σ (𝔸f E)}
    (hV : IsIntMatrix (Ô E) V) : HasLevelLifts c γ (m * V) := by
  classical
  obtain ⟨ρ, _, t, w, h_orth, h_int, h_level, rfl⟩ := h_lift
  refine ⟨ρ, inferInstance, t, w * V, h_orth, ?_, ?_, (Matrix.mul_assoc ..).symm⟩
  · rw [← Matrix.mul_assoc]
    exact h_int.mul hV
  · have h_assoc : S.ideleM⁻¹ • (S.classCoord c * finAdeleMatrix t * (w * V)).toRows₁ =
        S.ideleM⁻¹ • (S.classCoord c * finAdeleMatrix t * w).toRows₁ * V := by
      rw [← Matrix.mul_assoc, Matrix.smul_mul]
      rfl
    rw [h_assoc]
    exact h_level.mul hV

omit [Fintype τ] in
/-- If the columns of `m` lie in the lattice `L⁺_γ` (`HasLevelLifts`), then so do the columns of
`m.submatrix id e`, the columns of `m` chosen by `e`. -/
lemma HasLevelLifts.submatrix (h_lift : HasLevelLifts c γ m) (e : σ → τ) :
    HasLevelLifts c γ (m.submatrix id e) := by
  obtain ⟨ρ, _, t, w, h_orth, h_int, h_level, rfl⟩ := h_lift
  refine ⟨ρ, inferInstance, t, w.submatrix id e, h_orth, ?_, ?_, rfl⟩
  · exact fun a b ↦ h_int a (e b)
  · exact fun a b ↦ h_level a (e b)

end LevelLifts

variable [DecidableEq τ]

section Index

variable {n l : Type} {M N K : Submodule (Ô E) (n → 𝔸f E)}

/-- Let `g = S.ideleM` be the level as a unit of the finite adeles `𝔸f E`, and let `L' ≤ L` be
submodules of `n → 𝔸f E` over the ring `Ô E` of integral finite adeles. If `L'` has finite index in
`L` (`submoduleIndex L' L ≠ 0`, an infinite index being `0`), then `[L : g L] = [L' : g L']`. -/
lemma submoduleIndex_ideleM_smul_eq {L L' : Submodule (Ô E) (n → 𝔸f E)}
    (h_index : submoduleIndex L' L ≠ 0) (h_le : L' ≤ L) :
    submoduleIndex (S.ideleM • L) L = submoduleIndex (S.ideleM • L') L' := by
  -- Both sides times `[L : L']` equal `[L : g L']` (`g = S.ideleM`), via `g L' ≤ g L ≤ L` and via
  -- `g L' ≤ L' ≤ L`.
  have h_smul_le (K : Submodule (Ô E) (n → 𝔸f E)) : S.ideleM • K ≤ K :=
    Submodule.smul_le_self_of_tower (⟨_, S.ideleM_mem⟩ : Ô E) K
  have h_scale : submoduleIndex (S.ideleM • L') (S.ideleM • L) = submoduleIndex L' L :=
    AddSubgroup.relIndex_pointwise_smul S.ideleM L'.toAddSubgroup L.toAddSubgroup
  refine mul_right_cancel₀ h_index ?_
  calc
    submoduleIndex (S.ideleM • L) L * submoduleIndex L' L =
        submoduleIndex (S.ideleM • L') (S.ideleM • L) * submoduleIndex (S.ideleM • L) L := by
      rw [h_scale, mul_comm]
    _ = submoduleIndex (S.ideleM • L') L :=
      AddSubgroup.relIndex_mul_relIndex _ _ _ (Set.smul_set_mono h_le) (h_smul_le L)
    _ = submoduleIndex (S.ideleM • L') L' * submoduleIndex L' L :=
      (AddSubgroup.relIndex_mul_relIndex _ _ _ (h_smul_le L') h_le).symm

/-- The index of `N ⊓ K` in `M` is that of `K` in `M ⊓ N` times that of `N` in `M`. -/
lemma submoduleIndex_inf (M N K : Submodule (Ô E) (n → 𝔸f E)) :
    submoduleIndex (N ⊓ K) M = submoduleIndex K (M ⊓ N) * submoduleIndex N M := by
  rw [inf_comm N, inf_comm M]
  exact (AddSubgroup.relIndex_inf_mul_relIndex K.toAddSubgroup N.toAddSubgroup M.toAddSubgroup).symm

/-- If `M ≤ N`, then `N ⊓ K` and `K` have the same index in `M`. -/
lemma submoduleIndex_inf_of_le (h_le : M ≤ N) : submoduleIndex (N ⊓ K) M = submoduleIndex K M := by
  have h_one : submoduleIndex N M = 1 := AddSubgroup.relIndex_eq_one.2 h_le
  rw [submoduleIndex_inf, h_one, mul_one, inf_of_le_left h_le]

/-- If `M ≤ N`, the index in `M` of the elements of `N` that `f` maps into `L` is the index of `L`
in the image `f M`. -/
lemma submoduleIndex_inf_comap [HasPrimitiveRoot5040 E] {L : Submodule (Ô E) (l → 𝔸f E)}
    (f : (n → 𝔸f E) →ₗ[Ô E] l → 𝔸f E) (h_le : M ≤ N) :
    submoduleIndex (N ⊓ L.comap f) M = submoduleIndex L (M.map f) := by
  rw [submoduleIndex_inf_of_le h_le]
  exact AddSubgroup.relIndex_comap L.toAddSubgroup f.toAddMonoidHom M.toAddSubgroup

end Index

/-- Let `γ` be a term of cell rank `j` from `c'` to `c`, and put
`k = S.translateByClassReps c c' γ`. Column `a` of `P` holds the products of `e_a` with the frame
`k e₁, …, k e_ϱ, k z`. The lattice `L` spanned by the columns is a copy of `(Λ ∩ A)/(Λ ∩ I)`, for
`Λ` the lattice of `c`, `A` the span of the `e_a` and `I = A ∩ γ A`. The index of `M L` in `L`
divides `M ^ (2 i f)`, where `M = S.M` is the level (`S.ideleM` as a finite idele), `i = min ϱ j`
and `f` is the number of infinite places. -/
lemma submoduleIndex_ideleM_smul_isotropicRows_dvd [HasPrimitiveRoot5040 E]
    {s : S.ResidueGL} (hγ : γ ∈ S.termsOver c s c') (hj : S.HasCellRank j γ) :
    let P : Matrix (Fin (𝔰.ϱ + 1)) (Fin 𝔰.ϱ) (𝔸f E) :=
      (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram (S.translateByClassReps c c' γ)))ᴴ
    submoduleIndex (S.ideleM • colLattice (Ô E) P) (colLattice (Ô E) P) ∣
      S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) := by
  -- The span `Lⱼ` of the columns `a < j` has finite index in `L` and at most `i` generators.
  let Z : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) (𝔸f E) :=
    (S.latticeMiddle (𝔸f E)).frameGram (S.translateByClassReps c c' γ)
  let L : Submodule (Ô E) (Fin (𝔰.ϱ + 1) → 𝔸f E) := colLattice (Ô E) (isotropicRows Z)ᴴ
  let Zⱼ : Matrix (Fin (𝔰.ϱ + 1)) (IndexBelow j) (𝔸f E) :=
    (Z.submatrix (fun a : IndexBelow j ↦ a.1.castSucc) id)ᴴ
  let Lⱼ : Submodule (Ô E) (Fin (𝔰.ϱ + 1) → 𝔸f E) := colLattice (Ô E) Zⱼ
  have h_le : Lⱼ ≤ L := colLattice_le fun a ↦ col_mem_colLattice a.1
  have h_finite : submoduleIndex Lⱼ L ≠ 0 := (isotropicRowsIndex_pos hγ hj).ne'
  have h_level : submoduleIndex (S.ideleM • intVectors (Ô E) (IndexBelow j))
      (intVectors (Ô E) (IndexBelow j)) = S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) := by
    rw [← Nat.cast_inj (R := ℝ), submoduleIndex_smul_intVectors S.ideleM_mem, S.ideleM_val,
      genIndex_natCast, Fintype.card_subtype, Fin.card_filter_val_lt]
    push_cast
    ring
  have h_image : S.ideleM • intVectors (Ô E) (IndexBelow j) ≤
      (S.ideleM • Lⱼ).comap (Zⱼ.mulVecLin.restrictScalars (Ô E)) := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨Zⱼ *ᵥ v, ⟨v, hv, rfl⟩, by simp⟩
  calc
    submoduleIndex (S.ideleM • L) L = submoduleIndex (S.ideleM • Lⱼ) Lⱼ :=
      submoduleIndex_ideleM_smul_eq h_finite h_le
    _ ∣ submoduleIndex (S.ideleM • intVectors (Ô E) (IndexBelow j))
        (intVectors (Ô E) (IndexBelow j)) := submoduleIndex_dvd_of_le _ h_image le_sup_left
    _ = S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) := h_level

omit [DecidableEq τ] [Fintype τ] in
/-- Let `A` be the span of `e₁, …, e_ϱ` and let `γ` have cell rank `j` (`S.HasCellRank j γ`). Let
`u` be an orthogonal lift of `v`. An adelic vector of `A` is a combination of the rational basis of
`I = A ∩ γ A` formed by the columns of `u.toCols₁` if its products with the rows `isotropicRows` of
`S.frameProducts γ` vanish. The columns of `ω`, in the coordinates of `A`, are such vectors. So `ω`
is `u.toCols₁.toRows₁` times its rows `b ≥ j`. -/
lemma IsOrthogonalLift.eq_mul_of_isotropicRows_mul_eq_zero {σ : Type}
    {v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E}
    {u : Matrix 𝔰.BesselIndex (IndexNotBelow j ⊕ τ) E} (hu : IsOrthogonalLift j γ v u)
    (hj : S.HasCellRank j γ) {ω : Matrix (Fin 𝔰.ϱ) σ (𝔸f E)}
    (hω : (isotropicRows (finAdeleMatrix (S.frameProducts γ)))ᴴ * ω = 0) :
    ω = finAdeleMatrix u.toCols₁.toRows₁ * ω.submatrix (fun a : IndexNotBelow j ↦ a.1) id := by
  -- The difference has no coordinates at the indices `≥ j`, and the leading minor is not `0`.
  classical
  set d : Matrix (Fin 𝔰.ϱ) σ (𝔸f E) :=
    ω - finAdeleMatrix u.toCols₁.toRows₁ * ω.submatrix (fun a : IndexNotBelow j ↦ a.1) id with hd
  have h_above (a : Fin 𝔰.ϱ) (ha : ¬a.1 < j) (b : σ) : d a b = 0 := by
    have h_row (x : IndexNotBelow j) : u (.inl a) (.inl x) = if ⟨a, ha⟩ = x then 1 else 0 :=
      (hu.apply_inl ⟨a, ha⟩).1 x
    rw [hd, Matrix.sub_apply, mul_apply]
    simp [h_row, apply_ite (algebraMap E (𝔸f E))]
  have h_orth : (isotropicRows (finAdeleMatrix (S.frameProducts γ)))ᴴ * d = 0 := by
    have h_shared :
        (isotropicRows (finAdeleMatrix (S.frameProducts γ)))ᴴ * finAdeleMatrix u.toCols₁.toRows₁ =
          0 := by
      change (finAdeleMatrix (isotropicRows (S.frameProducts γ)))ᴴ * finAdeleMatrix
        u.toCols₁.toRows₁ = 0
      rw [← finAdeleMatrix_conjTranspose, ← Matrix.map_mul,
        hu.conjTranspose_isotropicRows_mul_eq_zero]
      simp
    rw [hd, Matrix.mul_sub, hω, ← Matrix.mul_assoc, h_shared, Matrix.zero_mul, sub_zero]
  let Y : Matrix (Fin (𝔰.ϱ + 1)) (Fin (𝔰.ϱ + 1)) E := paddedLeading j (S.frameProducts γ)
  have h_padded : (isotropicRows (finAdeleMatrix Y))ᴴ * d = 0 := by
    rw [← h_orth]
    refine Matrix.ext fun a b ↦ ?_
    rw [mul_apply, mul_apply]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases hx : x.1 < j
    · simp [Y, paddedLeading, hx]
    · simp [h_above x hx]
  have h_left : (finAdeleMatrix Y⁻¹)ᴴ.submatrix castSucc id * (isotropicRows (finAdeleMatrix Y))ᴴ =
    1 := by
    have h_inv : (finAdeleMatrix Y⁻¹)ᴴ * (finAdeleMatrix Y)ᴴ = 1 := by
      rw [← conjTranspose_mul, ← Matrix.map_mul, hj.paddedLeading_mul_inv]
      simp
    calc
      _ = ((finAdeleMatrix Y⁻¹)ᴴ * (finAdeleMatrix Y)ᴴ).submatrix castSucc castSucc := rfl
      _ = 1 := by rw [h_inv, submatrix_one _ (castSucc_injective _)]
  rw [← sub_eq_zero, ← hd, ← Matrix.one_mul d, ← h_left, Matrix.mul_assoc, h_padded,
    Matrix.mul_zero]

omit [Fintype τ] [DecidableEq τ] in
/-- Let `γ` have cell rank `j`, and let the columns of `t w`, adelic combinations of rational
vectors orthogonal to `A` and `γ A`, be integral in the lattice `Λ` of `c`. Suppose that the part in
`A` of each has the same products with the frame of `γ` as some vector of `M (Λ ∩ A)`. Then their
images in the link lie in `L⁺_γ`, the lattice of the images of vectors of `Λ` orthogonal to `A` and
`γ A` whose part in `A` is divisible by `M` (`HasLevelLifts`): adding vectors of `I = A ∩ γ A` makes
the parts in `A` divisible by `M`. -/
lemma hasLevelLifts_of_col_mem (hj : S.HasCellRank j γ) {ρ : Type} [Fintype ρ]
    {t : Matrix 𝔰.BesselIndex ρ E} {w : Matrix ρ τ (𝔸f E)}
    (h_orth : (isotropicFramePair γ)ᴴ * S.ratGram * t = 0)
    (h_int : IsIntMatrix (Ô E) (S.classCoord c * finAdeleMatrix t * w))
    (h_mem : ∀ b : τ, (isotropicRows (finAdeleMatrix (S.frameProducts γ)))ᴴ *ᵥ
        (S.classCoord c * finAdeleMatrix t * w).toRows₁.col b ∈
      S.ideleM • colLattice (Ô E) (isotropicRows (finAdeleMatrix (S.frameProducts γ)))ᴴ) :
    HasLevelLifts c γ (finAdeleMatrix (linkMatrix γ * t) * w) := by
  classical
  obtain ⟨v, -, hv⟩ : ∃ v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex)
      (Fin (Module.finrank E (link γ))) E, HasLeftInv v ∧ colSpan v = link γ :=
    exists_hasLeftInv_colSpan_eq (link γ)
  obtain ⟨u, hu⟩ : ∃ u : Matrix 𝔰.BesselIndex
      (IndexNotBelow j ⊕ Fin (Module.finrank E (link γ))) E, IsOrthogonalLift j γ v u :=
    exists_orthogonal_lift hj hv
  set n : Matrix 𝔰.BesselIndex τ (𝔸f E) := S.classCoord c * finAdeleMatrix t * w with hn
  set P : Matrix (Fin (𝔰.ϱ + 1)) (Fin 𝔰.ϱ) (𝔸f E) :=
    (isotropicRows (finAdeleMatrix (S.frameProducts γ)))ᴴ
  have h_exists (b : τ) : ∃ ω ∈ intVectors (Ô E) (Fin 𝔰.ϱ),
      P *ᵥ n.toRows₁.col b = S.ideleM • (P *ᵥ ω) := by
    obtain ⟨_, ⟨ω, hω, rfl⟩, h_products⟩ := h_mem b
    exact ⟨ω, hω, h_products.symm⟩
  choose ω hω h_products using h_exists
  -- `ι`, the part in `A` minus `M ω`, is orthogonal to the frame of `γ`, so it lies in `I`.
  let ι : Matrix (Fin 𝔰.ϱ) τ (𝔸f E) := n.toRows₁ - S.ideleM • (of ω)ᵀ
  have hι : ι = finAdeleMatrix u.toCols₁.toRows₁ * ι.submatrix (fun a : IndexNotBelow j ↦ a.1)
    id := by
    refine hu.eq_mul_of_isotropicRows_mul_eq_zero hj (ext_col fun b ↦ ?_)
    change P *ᵥ (n.toRows₁.col b - S.ideleM • ω b) = 0
    rw [mulVec_sub, h_products b, mulVec_smul, sub_self]
  have h_shared :
      S.classCoord c * finAdeleMatrix u.toCols₁ = fromRows (finAdeleMatrix u.toCols₁.toRows₁)
        0 := by
    rw [hu.toCols₁_eq_fromRows, classCoord_eq_fromBlocks]
    ext (a | a) b <;> simp [mul_apply, Matrix.one_apply]
  have h_new : S.classCoord c * finAdeleMatrix (fromCols t u.toCols₁) *
      fromRows w (-ι.submatrix (fun a : IndexNotBelow j ↦ a.1) id) =
        fromRows (S.ideleM • (of ω)ᵀ) n.toRows₂ := by
    rw [finAdeleMatrix, fromCols_map, mul_fromCols, fromCols_mul_fromRows, h_shared, ← hn,
      fromRows_mul, Matrix.mul_neg, ← hι, Matrix.zero_mul]
    ext (a | a) b <;> simp [ι]
  have hω_int : IsIntMatrix (Ô E) (of ω)ᵀ := fun a b ↦ hω b a
  refine ⟨ρ ⊕ IndexNotBelow j, inferInstance, fromCols t u.toCols₁,
    fromRows w (-ι.submatrix (fun a : IndexNotBelow j ↦ a.1) id), ?_, ?_, ?_, ?_⟩
  · rw [mul_fromCols, h_orth, hu.orthogonal_toCols₁, fromCols_zero]
  · rw [h_new]
    rintro (a | a) b
    · exact hω_int.smul S.ideleM_mem a b
    · exact h_int (.inr a) b
  · rwa [h_new, toRows₁_fromRows, inv_smul_smul]
  · rw [mul_fromCols, hu.linkMatrix_mul_toCols₁, finAdeleMatrix, fromCols_map,
    fromCols_mul_fromRows]
    simp

variable [HasPrimitiveRoot5040 E]

/-- Let `γ` be a term of cell rank `j` from `c'` to `c`, put `k = S.translateByClassReps c c' γ`,
and let `m` have integral entries. Column `a` of `P` holds the products of `e_a` with the frame
`k e₁, …, k e_ϱ, k z`; let `L` be the lattice spanned by the columns. Then some invertible integral
`B` has `P m x ∈ M L` for each of its columns `x`, and `genIndex (det B)`, the index of its lattice
in the integral vectors, is at most `M ^ (2 i f)`. Here `M = S.M` is the level, `i = min ϱ j` and
`f` is the number of infinite places. -/
lemma exists_basis_mulVec_mem_ideleM_smul {s : S.ResidueGL} (hγ : γ ∈ S.termsOver c s c')
    (hj : S.HasCellRank j γ) {m : Matrix (Fin 𝔰.ϱ) τ (𝔸f E)} (hm : IsIntMatrix (Ô E) m) :
    let P : Matrix (Fin (𝔰.ϱ + 1)) (Fin 𝔰.ϱ) (𝔸f E) :=
      (isotropicRows ((S.latticeMiddle (𝔸f E)).frameGram (S.translateByClassReps c c' γ)))ᴴ
    ∃ B : GL τ (𝔸f E), IsIntMatrix (Ô E) B.val ∧
      (∀ b : τ, P *ᵥ (m *ᵥ B.val.col b) ∈ S.ideleM • colLattice (Ô E) P) ∧
      genIndex B.val.det ≤ S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) := by
  intro P
  let F : (τ → 𝔸f E) →ₗ[Ô E] Fin (𝔰.ϱ + 1) → 𝔸f E := (P * m).mulVecLin.restrictScalars (Ô E)
  let K : Submodule (Ô E) (τ → 𝔸f E) :=
    intVectors (Ô E) τ ⊓ (S.ideleM • colLattice (Ô E) P).comap F
  have h_image : (intVectors (Ô E) τ).map F ≤ colLattice (Ô E) P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨m *ᵥ x, hm.mulVec hx, mulVec_mulVec x P m⟩
  have h_dvd : submoduleIndex K (intVectors (Ô E) τ) ∣ S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) :=
    calc
      submoduleIndex K (intVectors (Ô E) τ) =
          submoduleIndex (S.ideleM • colLattice (Ô E) P) ((intVectors (Ô E) τ).map F) :=
        submoduleIndex_inf_comap F le_rfl
      _ ∣ submoduleIndex (S.ideleM • colLattice (Ô E) P) (colLattice (Ô E) P) :=
        submoduleIndex_dvd_of_le .id le_rfl
          (le_sup_of_le_left (h_image.trans_eq (Submodule.map_id _).symm))
      _ ∣ S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) :=
        submoduleIndex_ideleM_smul_isotropicRows_dvd hγ hj
  have hM : S.M ≠ 0 := by simp [Nat.Prime.ne_zero]
  obtain ⟨h_index_ne, h_index_le⟩ := ne_zero_and_le_of_dvd (pow_ne_zero _ hM) h_dvd
  obtain ⟨B, hB⟩ : ∃ B : GL τ (𝔸f E), colLattice (Ô E) B.val = K :=
    exists_colLattice_eq_of_submoduleIndex_ne_zero inf_le_left h_index_ne
  have hB_mem (b : τ) : B.val.col b ∈ K := hB.le (col_mem_colLattice b)
  have hB_int : IsIntMatrix (Ô E) B.val := fun a b ↦ (mem_inf.1 (hB_mem b)).1 a
  refine ⟨B, hB_int, fun b ↦ ?_, ?_⟩
  · rw [mulVec_mulVec]
    exact (mem_inf.1 (hB_mem b)).2
  · rw [← submoduleIndex_colLattice_intVectors hB_int, hB]
    exact_mod_cast h_index_le

/-- **The lattice of a link.** Let `E` be a CM field with a primitive root of unity of order `5040`,
and let `S : Filling E 𝔰` be data of the filling theorem. Let `γ` be a term from `c'` to `c` of cell
rank `j`, and let the columns of `v` be a basis of its link. For some invertible finite-adelic `e`
the columns of `v e` lie in the lattice `L⁺_γ`, and the torsion index `S.torsionIndex` times the
discriminant of their lattice is at most `M ^ (2 i f) 𝗀♯ / N ^ f`. Here `M = S.M` is the level,
`N = S.N` is minus the norm of the last frame vector, `i = min ϱ j`, `f` is the number of infinite
places and `𝗀♯ = S.minorGauge j c c' γ` is `Nm (S.subframeMinor j γ) / N ^ f` divided by the two
indices `isotropicRowsIndex` at `S.translateByClassReps c c' γ` and at its inverse. -/
theorem exists_hasLevelLifts_linkDiscSq_le {s : S.ResidueGL} (hγ : γ ∈ S.termsOver c s c')
    (hj : S.HasCellRank j γ) {v : Matrix (𝔰.MiddleIndex ⊕ 𝔰.MiddleIndex) τ E} (hv : HasLeftInv v)
    (hL : colSpan v = link γ) :
    ∃ e : GL τ (𝔸f E), HasLevelLifts c γ (finAdeleMatrix v * e.val) ∧
      S.torsionIndex (S.translateByClassReps c c' γ) ^ 2 * S.linkDiscSq v e ≤
        (S.M ^ (2 * min 𝔰.ϱ j * numInfPlaces E) * S.minorGauge j c c' γ /
          S.N ^ numInfPlaces E) ^ 2 := by
  -- Start from the lattice `v e` with integral lifts `t w`, whose part in `A` is `m`. The vectors
  -- `x` for which `m x` is divisible by `M` modulo `A ∩ γ A` have a basis `B` of index at most
  -- `M ^ (2 i f)`, so the lattice of `v e B` is the one sought.
  obtain ⟨e, ⟨ρ, _, t, w, h_orth, h_int, h_eq⟩, h_disc, h_ne⟩ :=
    exists_lifts_linkDiscSq_le hγ hj hv hL
  let m : Matrix (Fin 𝔰.ϱ) τ (𝔸f E) := (S.classCoord c * finAdeleMatrix t * w).toRows₁
  have hm : IsIntMatrix (Ô E) m := fun a b ↦ h_int (.inl a) b
  obtain ⟨B, hB_int, hB_mem, hB_det⟩ := exists_basis_mulVec_mem_ideleM_smul hγ hj hm
  refine ⟨e * B, ?_, ?_⟩
  · rw [Units.val_mul, ← Matrix.mul_assoc, ← h_eq, Matrix.mul_assoc]
    refine hasLevelLifts_of_col_mem (c := c) hj h_orth ?_ fun b ↦ ?_
    · rw [← Matrix.mul_assoc]
      exact h_int.mul hB_int
    · rw [← Matrix.mul_assoc, ← frameGram_translateByClassReps (c := c) (c' := c')]
      exact hB_mem b
  · have h_mul : S.linkDiscSq v (e * B) = S.linkDiscSq v e * genIndex B.val.det ^ 2 := by
      simp [linkDiscSq, mul_pow, mul_assoc]
    have h_nonneg : 0 ≤ S.linkDiscSq v e := by
      rw [linkDiscSq]
      positivity
    have h_det : 0 < genIndex B.val.det := genIndex_pos B.det
    have hN : (S.N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 S.N_prime.ne_zero
    set i₁ : ℝ := (S.isotropicRowsIndex j (S.translateByClassReps c c' γ) : ℝ)
    set i₂ : ℝ := (S.isotropicRowsIndex j (S.translateByClassReps c c' γ)⁻¹ : ℝ)
    set i₃ : ℝ := (S.torsionIndex (S.translateByClassReps c c' γ) : ℝ)
    set G : ℝ := (S.M : ℝ) ^ (2 * min 𝔰.ϱ j * numInfPlaces E)
    have h_indices : i₁ * i₂ ≠ 0 := left_ne_zero_of_mul h_ne
    calc
      i₃ ^ 2 * S.linkDiscSq v (e * B)
        ≤ i₃ ^ 2 * (S.linkDiscSq v e * G ^ 2) := by grw [h_mul, hB_det]
      _ = G ^ 2 * (S.linkDiscSq v e * (i₁ * i₂ * i₃) ^ 2) / (i₁ * i₂) ^ 2 := by
        rw [eq_div_iff (pow_ne_zero 2 h_indices)]
        ring
      _ ≤ G ^ 2 * S.minorNorm j γ ^ 2 / (i₁ * i₂) ^ 2 := by grw [h_disc]
      _ = (G * S.minorGauge j c c' γ / S.N ^ numInfPlaces E) ^ 2 := by
        have h_gauge : S.minorGauge j c c' γ =
            (S.N : ℝ) ^ numInfPlaces E * S.minorNorm j γ / (i₁ * i₂) := hj.minorGauge_eq c c'
        rw [h_gauge]
        field_simp

end New.Filling
