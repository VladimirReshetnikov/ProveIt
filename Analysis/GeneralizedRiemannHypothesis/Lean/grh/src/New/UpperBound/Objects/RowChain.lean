import New.UpperBound.Objects.Rows

/-!
# The chain of theta lifts ι_μ along the spaces Y_j: level, character and 𝖦-equivariance

This file defines the theta lifts `New.Data.liftY` from forms on Y_j to forms on Y_{j+1} and their
composite, the chain ι_μ = `New.Data.lowerChain`, for a tame character ϑ with modulus Q. It
determines the level and character of the image on Y_m and shows that the chain commutes with
𝖦 = ∏ GL_r(𝔽_w). The basis of Y_j is indexed by `New.BlockIndex`, a block 0 of size r followed by
j blocks of size t; `New.blockNumber` is the number of the block.

## Main definitions and results

* `New.Data.lowerChain`, `New.Data.lowerChainAtLevel`: the chain; it lands in the level
  `New.Data.lastLevel`, cut out by `New.Data.lastResidueLevel`, with the character
  `New.Data.lastLevelChar`.
* `New.Data.algFormRep_lowerChain`: how block triangular elements act on the image;
  `New.Data.lowerChain_principalRep`: the chain commutes with 𝖦 = ∏ GL_r(𝔽_w) (`New.Data.chosenGL`).

Notions from other files:
* `New.Data.TameChar`: a character of U(1)(𝔸) of weight 0 with tame part supported on a finite set Q
  of places of norm prime to MN, Q disjoint from its conjugate.
* `New.algFormRep`: right translation by the finite adelic unitary group on algebraic forms of a
  given weight; the weight λ° on Y_m has column numbers `New.Data.columnsY` and determinant exponent
  `New.Data.lastEntry` m.
* `New.Data.spaceY`: the hermitian space Y_j with its lattice 𝖬_j.
* `New.Data.levelPlaces`: the chosen places above p₀, p₁ and the places of the modulus Q of ϑ.
* `New.Data.pointDatumY`: the finite datum on Hom(Y_j, Y_{j+1}), the indicator of the inclusion
  modulo the level places and the vacuum elsewhere.
-/

noncomputable section

section RowChain

open New Space LevelPlaces Matrix Fin Units

/-- The number, from 0 to j, of the block containing an index: 0 on R and l on the l-th copy of
T. -/
def New.blockNumber {R T : Type} : ∀ j : ℕ, BlockIndex R T j → Fin (j + 1)
  | 0 => 0
  | j + 1 => castSucc ∘ blockNumber j ⊕ᵥ fun _ ↦ last (j + 1)

/-- An index has block number 0 if and only if it lies in the image of the first block R. -/
lemma New.blockNumber_eq_zero_iff {R T : Type} (j : ℕ) :
    ∀ i : BlockIndex R T j, blockNumber j i = 0 ↔ i ∈ Set.range (BlockIndex.firstBlock j) := by
  induction j with
  | zero => tauto
  | succ j ih =>
    -- `BlockIndex.firstBlock (j + 1)` is `Sum.inl` after `BlockIndex.firstBlock j`.
    change ∀ i : BlockIndex R T (j + 1),
      blockNumber (j + 1) i = 0 ↔ ∃ r : R, Sum.inl (BlockIndex.firstBlock j r) = i
    simpa!

namespace New.Data

variable {P : Parameters} {D : Data P}

instance (j : ℕ) : Nonempty (D.Y j) := .map (BlockIndex.firstBlock j) inferInstance

/-- The forms on U(Y_j) of the type given by the parameter `New.Data.paramY` and the signs of Y_j,
with the Petersson product. -/
abbrev FormY (j : ℕ) : Type := (D.spaceY j).Form (typeKernel (D.paramY j) (D.signsY j))

variable (D) in
/-- The joint harmonic of lift j + 1: the product over the infinite places of the chosen joint
harmonics for the parameters and signs of Y_j and Y_{j+1}. The splitting character on a space of
rank n has weight ⌊n/2⌋ − w_{j+1}(τ) at τ. -/
abbrev harmonicY (j : ℕ) : MvPolynomial (NumberField.InfinitePlace D.E × D.Y (j + 1) × D.Y j) ℂ :=
  jointHarmonic (D.gridWeight true j (D.Y j)) (D.gridWeight true j (D.Y (j + 1)))
    (D.paramY j) (D.paramY (j + 1)) (D.signsY j) (D.signsY (j + 1))

/-- The datum φ ⊗ Υ on Hom(Y_j, Y_{j+1}) of lift j + 1: the joint harmonic at infinity and the
finite datum `New.Data.pointDatumY`. -/
abbrev datumY (ϑ : D.TameChar) (j : ℕ) : 𝒮 ((D.spaceY j).hom (D.spaceY (j + 1))) :=
  (hom (D.spaceY j) (D.spaceY (j + 1))).integrated
    (Fock.polyVector _ (D.harmonicY j)) (pointDatumY ϑ j).val

/-- For j < m the doubled parameters `New.Data.paramY` of Y_j and Y_(j+1), with their signs,
correspond (`New.ParamsCorrespond`) for the weights `New.Data.gridWeight` of the characters of lift
j + 1. -/
lemma paramsCorrespond_paramY {j : ℕ} (hj : j < D.m) :
    ParamsCorrespond (D.gridWeight true j (D.Y j)) (D.gridWeight true j (D.Y (j + 1)))
      (D.paramY j) (D.paramY (j + 1)) (D.signsY j) (D.signsY (j + 1)) :=
  -- The node `(0, j)` of the grid is the space `Y_j`, and lift `j + 1` is a step of the grid.
  D.paramsCorrespond_grid_succ_right false 0 0 j D.m.zero_le hj (.inl rfl)

/-- For j < m the datum `New.Data.datumY` ϑ j of lift j + 1 is an arrow (`New.IsArrow`: a kernel
whose lifts take forms of the source type to forms of the target type) both ways: (a) from forms on
Y_j to forms on Y_(j+1), and (b) for the swapped Weil representation, from forms of the conjugate
type on Y_(j+1) to forms of the conjugate type on Y_j. -/
lemma isArrow_datumY (ϑ : D.TameChar) {j : ℕ} (hj : j < D.m) :
    -- (a)
    IsArrow (thetaKernelY ϑ j) (typeKernel (D.paramY j) (D.signsY j))
      (typeKernel (D.paramY (j + 1)) (D.signsY (j + 1))) (datumY ϑ j) ∧
    -- (b)
    IsArrow (thetaKernelY ϑ j).swap (star (typeKernel (D.paramY (j + 1)) (D.signsY (j + 1))))
      (star (typeKernel (D.paramY j) (D.signsY j))) (datumY ϑ j) :=
  -- The parameters of `Y_j` and `Y_(j+1)` correspond, so the joint harmonic is an edge; an edge
  -- tensored with a finite datum is an arrow both ways.
  (paramsCorrespond_paramY hj).isEdge_jointHarmonic.isArrow _ _ (pointDatumY ϑ j).prop

/-- For j < m the datum `New.Data.datumY` ϑ j of lift j + 1 is an arrow from forms on Y_j to forms
on Y_(j+1). -/
lemma isArrow_thetaKernelY_datumY (ϑ : D.TameChar) {j : ℕ} (hj : j < D.m) :
    IsArrow (thetaKernelY ϑ j) (typeKernel (D.paramY j) (D.signsY j))
      (typeKernel (D.paramY (j + 1)) (D.signsY (j + 1))) (datumY ϑ j) :=
  (isArrow_datumY ϑ hj).left

/-- For j < m the datum `New.Data.datumY` ϑ j of lift j + 1 is an arrow for the swapped Weil
representation, from forms of the conjugate type on Y_(j+1) to forms of the conjugate type on
Y_j. -/
lemma isArrow_swap_thetaKernelY_datumY (ϑ : D.TameChar) {j : ℕ} (hj : j < D.m) :
    IsArrow (thetaKernelY ϑ j).swap (star (typeKernel (D.paramY (j + 1)) (D.signsY (j + 1))))
      (star (typeKernel (D.paramY j) (D.signsY j))) (datumY ϑ j) :=
  (isArrow_datumY ϑ hj).right

/-- Lift j + 1, from forms on Y_j to forms on Y_{j+1}: the theta lift with datum `New.Data.datumY`,
multiplied by the index in K₀ of the level `New.Data.levelY`. -/
def liftY (ϑ : D.TameChar) (j : ℕ) : D.FormY j →ₗ[ℂ] D.FormY (j + 1) :=
  (stdLevelIndex (levelY ϑ j) : ℂ) •
    formLift (thetaKernelY ϑ j) (typeKernel (D.paramY j) (D.signsY j))
      (typeKernel (D.paramY (j + 1)) (D.signsY (j + 1))) (datumY ϑ j)

/-- The group of reductions that cuts out the level on Y_m: the families in ∏_w GL(Y_m mod w), w
over the level places, that are 1 at the chosen places above p₀, p₁ (the left summand) and block
upper triangular at the places of Q (the right summand). -/
def lastResidueLevel (ϑ : D.TameChar) :
    Subgroup
      (∀ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
        GL (D.Y D.m) (ResField ((D.levelPlaces ϑ).placeAt x))) :=
  Subgroup.pi Set.univ fun
    | Sum.inl _ => ⊥
    | Sum.inr _ => parabolic (blockNumber D.m)

/-- A family lies in `New.Data.lastResidueLevel` if and only if it is 1 at the chosen places above
p₀, p₁ and block upper triangular at the places of Q. -/
lemma mem_lastResidueLevel (ϑ : D.TameChar) {g : LevelReductionsY ϑ D.m} :
    g ∈ lastResidueLevel ϑ ↔
      (∀ x : (D.levelPlaces ϑ).ChosenIndex, g (Sum.inl x) = 1) ∧
      ∀ x : (D.levelPlaces ϑ).TwistIndex, g (Sum.inr x) ∈ parabolic (blockNumber D.m) := by
  simp only [lastResidueLevel, Subgroup.mem_pi, Set.mem_univ, forall_const, Sum.forall,
    Subgroup.mem_bot]

/-- A family in `New.Data.lastResidueLevel` is 1 at the chosen places above p₀, p₁. -/
lemma eq_one_of_mem_lastResidueLevel (ϑ : D.TameChar) {g : LevelReductionsY ϑ D.m}
    (hg : g ∈ lastResidueLevel ϑ) (x : (D.levelPlaces ϑ).ChosenIndex) :
    g (Sum.inl x) = 1 :=
  ((mem_lastResidueLevel ϑ).mp hg).left x

/-- For a tame character ϑ, the component of a family in `New.Data.lastResidueLevel` at any level
place (a chosen place above p₀, p₁ or a place of the modulus Q of ϑ) is block upper triangular for
the blocks `New.blockNumber` of Y_m. -/
lemma mem_parabolic_of_mem_lastResidueLevel (ϑ : D.TameChar) {g : LevelReductionsY ϑ D.m}
    (hg : g ∈ lastResidueLevel ϑ)
    (x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex) :
    g x ∈ parabolic (blockNumber D.m) := by
  obtain ⟨h_one, h_tri⟩ := (mem_lastResidueLevel ϑ).mp hg
  cases x with
  | inl x =>
    rw [h_one x]
    exact one_mem _
  | inr x => exact h_tri x

/-- The level J_m on the last space Y_m of the chain: the elements of K₀ = `New.stdLevel` that are 1
modulo the chosen places above p₀, p₁ and block upper triangular modulo each place of Q. -/
abbrev lastLevel (ϑ : D.TameChar) : Subgroup (Gf D.E (D.Y D.m)) :=
  levelOf (D.levelPlaces ϑ).placeAt (lastResidueLevel ϑ)

/-- The composite of the first j theta lifts along Y₀, …, Y_j for the twist ϑ, from forms of
principal level at the chosen places on Y₀ to forms on Y_j. -/
def lowerChainUpTo (ϑ : D.TameChar) (j : ℕ) : D.principalForms (D.spaceY 0) →ₗ[ℂ] D.FormY j :=
  compUpTo (liftY ϑ) j ∘ₗ (D.principalForms (D.spaceY 0)).subtype

/-- The map ι_μ for the twist ϑ: the composite of the m lifts from forms of principal level at the
chosen places on Y₀ to forms on Y_m, read as algebraic forms of weight λ°. The subscript μ stands
for the characters μ_j⁰ϑ^j = `D.chainChar ϑ j` (1 ≤ j ≤ m) of the lifts. -/
def lowerChain (ϑ : D.TameChar) :
    D.principalForms (D.spaceY 0) →ₗ[ℂ] AlgForm (D.Y D.m) D.columnsY (D.lastEntry D.m) :=
  (toAlgForm (D.spaceY D.m) D.isHCParam_paramY).toLinearMap ∘ₗ lowerChainUpTo ϑ D.m

/-- The determinants of the diagonal blocks of the upper left corner of a matrix on `j + 2` blocks
are those of its first `j + 1` diagonal blocks. -/
lemma det_toSquareBlock_toBlocks₁₁ (j : ℕ) {R : Type*} [CommRing R]
    (M : Matrix (D.Y (j + 1)) (D.Y (j + 1)) R) (l : Fin (j + 1)) :
    (M.toBlocks₁₁.toSquareBlock (blockNumber j) l).det =
      (M.toSquareBlock (blockNumber (j + 1)) l.castSucc).det := by
  let σ : {a : D.Y j // blockNumber j a = l} ≃ {a // blockNumber (j + 1) a = l.castSucc} :=
    .trans (.ofInjective _ (Sum.inl_injective.comp Subtype.val_injective))
      (.subtypeEquivRight (by simp! [eq_comm]))
  exact det_submatrix_equiv_self σ (M.toSquareBlock (blockNumber (j + 1)) l.castSucc)

/-- The determinant of a block upper triangular matrix on `j + 2` blocks is that of its upper left
corner times that of its last diagonal block. -/
lemma det_eq_det_toBlocks₁₁_mul (j : ℕ) {R : Type*} [CommRing R]
    {M : Matrix (D.Y (j + 1)) (D.Y (j + 1)) R} (hM : M.BlockTriangular (blockNumber (j + 1))) :
    M.det = M.toBlocks₁₁.det * (M.toSquareBlock (blockNumber (j + 1)) (last (j + 1))).det := by
  have h_corner : M.toBlocks₁₁.BlockTriangular (blockNumber j) :=
    fun a b hab ↦ hM (castSucc_lt_castSucc_iff.2 hab)
  simp [hM.det_fintype, prod_univ_castSucc, h_corner.det_fintype, det_toSquareBlock_toBlocks₁₁]

/-- Fix a tame character `ϑ` and assume that the datum of lift `j + 1` for `ϑ` is an arrow. Let `k`,
`k'` be integral finite points of `U(Y_(j+1))`, `U(Y_j)` with reductions `g`, `g'` at the level
places such that `g ι = ι g'` at each of them, for `ι` the matrix of the inclusion `Y_j → Y_(j+1)`.
Then the translate by `k` of the lift `liftY ϑ j z` of a form `z` is the lift of the translate of
`z` by `k'`, times the product over the level places of `ψ (det g) / ψ (det g')`, where
`ψ = chainTamePart ϑ j` is the tame part of the character of the lift. -/
lemma formRep_liftY (ϑ : D.TameChar) (j : ℕ)
    (h_arr : IsArrow (thetaKernelY ϑ j) (typeKernel (D.paramY j) (D.signsY j))
      (typeKernel (D.paramY (j + 1)) (D.signsY (j + 1))) (datumY ϑ j))
    {k : stdLevel D.E (D.Y (j + 1))} {k' : stdLevel D.E (D.Y j)}
    {g : LevelReductionsY ϑ (j + 1)} {g' : LevelReductionsY ϑ j}
    (hk : stdLevel.reduceFamily (D.levelPlaces ϑ).placeAt k = g)
    (hk' : stdLevel.reduceFamily (D.levelPlaces ϑ).placeAt k' = g')
    (h_incl : ∀ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
      (g x).val.submatrix id (D.inclY j) =
        inclMatrix (ResField ((D.levelPlaces ϑ).placeAt x)) (D.inclY j) * (g' x).val)
    (z : D.FormY j) :
    (D.spaceY (j + 1)).formRep (typeKernel (D.paramY (j + 1)) (D.signsY (j + 1))) k.val
        (liftY ϑ j z) =
      (∏ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
          chainTamePart ϑ j ((D.levelPlaces ϑ).placeAt x) (g x).val.det /
            chainTamePart ϑ j ((D.levelPlaces ϑ).placeAt x) (g' x).val.det) •
        liftY ϑ j ((D.spaceY j).formRep (typeKernel (D.paramY j) (D.signsY j)) k'.val z) := by
  set c : ℂ := ∏ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
    chainTamePart ϑ j ((D.levelPlaces ϑ).placeAt x) (g x).val.det /
      chainTamePart ϑ j ((D.levelPlaces ϑ).placeAt x) (g' x).val.det
  -- Translation by `k` moves through the lift to `k'` on the form and `(k', k)` on the datum.
  have h_datum : (thetaKernelY ϑ j).ω ((1, k'.val), 1, k.val) (datumY ϑ j) = c • datumY ϑ j := by
    rw [datumY, pairWeil_integrated_fin, thetaKernelY_omega_pointDatumY_eq_smul ϑ j hk' hk h_incl,
      map_smul]
  simp only [liftY, LinearMap.smul_apply, map_smul, h_arr.formRep_formLift k'.val k.val, h_datum]
  exact smul_comm _ _ _

/-- Fix a tame character `ϑ` and `j ≤ m`. Let `k` be an element of K₀ (`stdLevel`, the stabiliser of
the standard lattice) on `Y_j` (`D.spaceY j`) whose reductions `g` at the level places are block
upper triangular and have block 0 equal to `s` (in `chosenGL`) at the chosen places. Then the
translate by `k` of `lowerChainUpTo ϑ j y`, the composite of the first `j` lifts applied to `y`, is
that composite applied to `c • (s · y)`, where `s · y` is the action `principalRep`. Here `c` is the
product over the level places and `l < j` of the tame character `chainTamePart ϑ l` of lift `l + 1`
at the determinant of the diagonal block `l + 1` of `g`. -/
lemma formRep_lowerChainUpTo_eq_lowerChainUpTo_smul (ϑ : D.TameChar) {j : ℕ} (hj : j ≤ D.m)
    (s : D.chosenGL)
    (y : D.principalForms (D.spaceY 0)) (k : stdLevel D.E (D.Y j)) (g : LevelReductionsY ϑ j)
    (hk : stdLevel.reduceFamily (D.levelPlaces ϑ).placeAt k = g)
    (h_tri : ∀ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
      (g x).val.BlockTriangular (blockNumber j))
    (h_first : ∀ x : (D.levelPlaces ϑ).ChosenIndex,
      (g (Sum.inl x)).val.submatrix (BlockIndex.firstBlock j) (BlockIndex.firstBlock j) =
        (s x).val) :
    (D.spaceY j).formRep (typeKernel (D.paramY j) (D.signsY j)) k.val (lowerChainUpTo ϑ j y) =
      lowerChainUpTo ϑ j
        ((∏ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex, ∏ l : Fin j,
            chainTamePart ϑ l ((D.levelPlaces ϑ).placeAt x)
              ((g x).val.toSquareBlock (blockNumber j) l.succ).det) •
          D.principalRep (D.spaceY 0) s y) := by
  -- Induction on `j`: the last lift turns the action of `k` into that of a lift of the upper left
  -- block of `g`, up to the character value on the last diagonal block.
  induction j with
  | zero =>
    -- On `Y₀` the element `k` reduces to `s`, so it acts as the chosen lift of `s` does.
    have h_red : stdLevel.reduceFamily D.chosenPlace k = s := by
      subst hk
      exact funext fun x ↦ Units.ext (h_first x)
    rw [Finset.prod_eq_one fun x _ ↦ prod_univ_zero _, one_smul]
    exact (apply_liftResidue_eq (W := D.FormY 0) y k h_red).symm
  | succ j ih =>
    -- The upper left block `A x` of `g x` has the same diagonal blocks as `g x`, except the last.
    let ι : Type := (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex
    let A (x : ι) : Matrix (D.Y j) (D.Y j) (ResField ((D.levelPlaces ϑ).placeAt x)) :=
      (g x).val.toBlocks₁₁
    have hA_tri (x : ι) : (A x).BlockTriangular (blockNumber j) :=
      fun a b hab ↦ h_tri x (castSucc_lt_castSucc_iff.2 hab)
    have h_det (x : ι) : (g x).val.det =
        (A x).det * ((g x).val.toSquareBlock (blockNumber (j + 1)) (last (j + 1))).det :=
      det_eq_det_toBlocks₁₁_mul j (h_tri x)
    have hA_det (x : ι) : (A x).det ≠ 0 :=
      left_ne_zero_of_mul ((h_det x).symm.trans_ne (g x).det_ne_zero)
    let g' : LevelReductionsY ϑ j := fun x ↦ GeneralLinearGroup.mkOfDetNeZero (A x) (hA_det x)
    -- The lower left block of `g x` vanishes.
    have h_incl (x : ι) : (g x).val.submatrix id (D.inclY j) =
        inclMatrix (ResField ((D.levelPlaces ϑ).placeAt x)) (D.inclY j) * (g' x).val := by
      refine (eq_inclMatrix_mul_iff (D.inclY j)).2 ?_
      rintro (a | b) ha c
      · exact absurd ⟨a, rfl⟩ ha
      · exact h_tri x (castSucc_lt_last (blockNumber j c))
    let c_last : ℂ := ∏ x : ι, chainTamePart ϑ j ((D.levelPlaces ϑ).placeAt x) (g x).val.det /
      chainTamePart ϑ j ((D.levelPlaces ϑ).placeAt x) (g' x).val.det
    let c_init : ℂ := ∏ x : ι, ∏ l : Fin j,
      chainTamePart ϑ l ((D.levelPlaces ϑ).placeAt x)
        ((g' x).val.toSquareBlock (blockNumber j) l.succ).det
    -- By `h_det` the new factor is `chainTamePart ϑ j` at the determinant of the last block.
    have h_scalar : c_last * c_init = ∏ x : ι, ∏ l : Fin (j + 1),
        chainTamePart ϑ l ((D.levelPlaces ϑ).placeAt x)
          ((g x).val.toSquareBlock (blockNumber (j + 1)) l.succ).det := by
      rw [mul_comm, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x _ ↦ ?_
      simp [g', A, prod_univ_castSucc, det_toSquareBlock_toBlocks₁₁, h_det, hA_det,
        MulChar.apply_eq_zero_iff]
    calc (D.spaceY (j + 1)).formRep (typeKernel (D.paramY (j + 1)) (D.signsY (j + 1))) k.val
          (liftY ϑ j (lowerChainUpTo ϑ j y))
      _ = c_last • liftY ϑ j ((D.spaceY j).formRep (typeKernel (D.paramY j) (D.signsY j))
            (liftResidue g').val (lowerChainUpTo ϑ j y)) :=
        formRep_liftY ϑ j (isArrow_thetaKernelY_datumY ϑ hj) hk (reduceFamily_liftResidue g') h_incl
          (lowerChainUpTo ϑ j y)
      _ = c_last • liftY ϑ j (lowerChainUpTo ϑ j (c_init • D.principalRep (D.spaceY 0) s y)) := by
        rw [ih (Nat.le_of_succ_le hj) _ g' (reduceFamily_liftResidue g') hA_tri h_first]
      _ = liftY ϑ j (lowerChainUpTo ϑ j ((c_last * c_init) • D.principalRep (D.spaceY 0) s y)) := by
        rw [map_smul, map_smul, map_smul, map_smul, smul_smul]
      _ = lowerChainUpTo ϑ (j + 1)
            ((∏ x : ι, ∏ l : Fin (j + 1), chainTamePart ϑ l ((D.levelPlaces ϑ).placeAt x)
                ((g x).val.toSquareBlock (blockNumber (j + 1)) l.succ).det) •
              D.principalRep (D.spaceY 0) s y) := by
        rw [h_scalar]
        rfl

/-- The law of the chain ι_μ = `lowerChain ϑ` of the m lifts with characters μ_j⁰ϑ^j, for a tame
character ϑ with modulus Q. Let k ∈ K₀ on Y_m have reductions g = (g_w) at the level places w that
are block upper triangular at every w and have block 0 equal to s ∈ 𝖦 at the chosen places. Then
k·ι_μ(y) = c · ι_μ(s·y), where c is the product over all w and all l < m of the tame character
`chainTamePart ϑ l` of lift l + 1 at w, evaluated on the determinant of the diagonal block l + 1 of
g_w. -/
lemma algFormRep_lowerChain (ϑ : D.TameChar) (s : D.chosenGL) (y : D.principalForms (D.spaceY 0))
    (k : stdLevel D.E (D.Y D.m)) (g : LevelReductionsY ϑ D.m)
    (hk : stdLevel.reduceFamily (D.levelPlaces ϑ).placeAt k = g)
    (h_tri : ∀ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
      (g x).val.BlockTriangular (blockNumber D.m))
    (h_first : ∀ x : (D.levelPlaces ϑ).ChosenIndex,
      (g (Sum.inl x)).val.submatrix (BlockIndex.firstBlock D.m) (BlockIndex.firstBlock D.m) =
        (s x).val) :
    algFormRep D.columnsY (D.lastEntry D.m) k.val (lowerChain ϑ y) =
      (∏ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex, ∏ l : Fin D.m,
          chainTamePart ϑ l ((D.levelPlaces ϑ).placeAt x)
            ((g x).val.toSquareBlock (blockNumber D.m) l.succ).det) •
        lowerChain ϑ (D.principalRep (D.spaceY 0) s y) := by
  -- Pass from algebraic forms back to forms on `Y_m`; `toAlgForm` commutes with translation.
  let toAlg : D.FormY D.m ≃ₗ[ℂ] AlgForm (D.Y D.m) D.columnsY (D.lastEntry D.m) :=
    (D.spaceY D.m).toAlgForm D.isHCParam_paramY
  rw [← map_smul]
  calc algFormRep D.columnsY (D.lastEntry D.m) k.val (toAlg (lowerChainUpTo ϑ D.m y))
    _ = toAlg ((D.spaceY D.m).formRep (typeKernel (D.paramY D.m) (D.signsY D.m)) k.val
          (lowerChainUpTo ϑ D.m y)) :=
      (toAlgForm_formRep D.isHCParam_paramY k.val (lowerChainUpTo ϑ D.m y)).symm
    _ = toAlg (lowerChainUpTo ϑ D.m
          ((∏ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex, ∏ l : Fin D.m,
              chainTamePart ϑ l ((D.levelPlaces ϑ).placeAt x)
                ((g x).val.toSquareBlock (blockNumber D.m) l.succ).det) •
            D.principalRep (D.spaceY 0) s y)) :=
      congrArg toAlg (formRep_lowerChainUpTo_eq_lowerChainUpTo_smul ϑ le_rfl s y k g hk h_tri
        h_first)

/-- The character of the level on Y_m: k ↦ ∏_w ∏_{l<m} ψ_{l,w}(det k_w^{(l+1)}), where w runs over
all level places (the chosen ones above p₀, p₁ and those of Q), k_w^{(l+1)} is the diagonal block
l + 1 of the component k_w (`New.blockHom`) and ψ_l = `New.Data.chainTamePart` ϑ l is the tame
character of lift l + 1. The chain of compositions reads from the right: component at w, block,
determinant, character. -/
def lastLevelChar (ϑ : D.TameChar) : lastResidueLevel ϑ →* ℂ :=
  ∏ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex, ∏ l : Fin D.m,
    (chainTamePart ϑ l ((D.levelPlaces ϑ).placeAt x)).toMonoidHom.comp
      (detMonoidHom.comp
        ((coeHom _).comp
          ((blockHom (blockNumber D.m) l.succ).comp
            ((Pi.evalMonoidHom _ x).restrict fun _ hg ↦
              mem_parabolic_of_mem_lastResidueLevel ϑ hg x))))

/-- Let ϑ be a tame character with modulus Q and y a form on Y₀ of principal level at the chosen
places. The level `lastLevel ϑ` consists of the k ∈ K₀ on Y_m that reduce to 1 at the chosen places
and are block upper triangular modulo the places of Q. Such a k multiplies the algebraic form
ι_μ(y) = `lowerChain ϑ y` by the value of `lastLevelChar ϑ` at the reductions (k_w) of k: the
product, over these places w and over l < m, of the tame character `chainTamePart ϑ l` of lift l + 1
at w, evaluated on the determinant of the diagonal block l + 1 of k_w. -/
lemma lowerChain_mem_levelSpace (ϑ : D.TameChar) (y : D.principalForms (D.spaceY 0)) :
    lowerChain ϑ y ∈ levelSpace (algFormRep D.columnsY (D.lastEntry D.m))
      (lastLevel ϑ)
      ((lastLevelChar ϑ).comp (levelOf.reduction (D.levelPlaces ϑ).placeAt
        (lastResidueLevel ϑ))) := by
  refine mem_levelSpace.2 fun k ↦ ?_
  -- The reduction `g` of `k` is block triangular, and trivial at the chosen places.
  obtain ⟨hk, hg_mem⟩ := mem_levelOf.1 k.prop
  set g : LevelReductionsY ϑ D.m :=
    stdLevel.reduceFamily (D.levelPlaces ϑ).placeAt ⟨k.val, hk⟩
  have h_tri (x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex) :
      (g x).val.BlockTriangular (blockNumber D.m) :=
    mem_parabolic_of_mem_lastResidueLevel ϑ hg_mem x
  have h_first (x : (D.levelPlaces ϑ).ChosenIndex) :
      (g (Sum.inl x)).val.submatrix (BlockIndex.firstBlock D.m) (BlockIndex.firstBlock D.m) =
        ((1 : D.chosenGL) x).val := by
    rw [eq_one_of_mem_lastResidueLevel ϑ hg_mem x]
    exact submatrix_one_embedding _
  -- Take `s = 1` in the law of the chain; its scalar is the value of `lastLevelChar` at `g`.
  have h_scalar : lastLevelChar ϑ ⟨g, hg_mem⟩ =
      ∏ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex, ∏ l : Fin D.m,
        chainTamePart ϑ l ((D.levelPlaces ϑ).placeAt x)
          ((g x).val.toSquareBlock (blockNumber D.m) l.succ).det := by
    simp only [lastLevelChar, MonoidHom.finsetProd_apply]
    rfl
  refine (algFormRep_lowerChain ϑ 1 y ⟨k.val, hk⟩ g rfl h_tri h_first).trans ?_
  rw [← h_scalar, map_one, Module.End.one_apply]
  rfl

/-- The map ι_μ with its target restricted to the space of algebraic forms on Y_m with level J_m
(`New.Data.lastLevel`) and the character `New.Data.lastLevelChar`. -/
def lowerChainAtLevel (ϑ : D.TameChar) :
    D.principalForms (D.spaceY 0) →ₗ[ℂ]
      LevelForm (D.levelPlaces ϑ) (lastResidueLevel ϑ) (lastLevelChar ϑ) D.columnsY
        (D.lastEntry D.m) :=
  (lowerChain ϑ).codRestrict _ (lowerChain_mem_levelSpace ϑ)

/-- For s in 𝖦, a chosen element of K₀ on Y_m reducing to diag(s, 1) at the chosen places above p₀,
p₁ and to 1 at Q. -/
def firstBlockLift (ϑ : D.TameChar) (s : D.chosenGL) :
    stdLevel D.E (BlockIndex D.RowIndex (Fin D.t) D.m) :=
  liftResidue (firstBlockHom (D.levelPlaces ϑ) (BlockIndex.firstBlock (T := Fin D.t) D.m) s)

/-- For a tame character ϑ with modulus Q, the chain ι_μ = `lowerChain ϑ` of the m lifts with
characters μ_j⁰ϑ^j commutes with the group 𝖦 = `D.chosenGL`: for s in 𝖦 and a form y of principal
level on Y₀, ι_μ(s·y) is the right translate of ι_μ(y) by `firstBlockLift ϑ s`, an element of K₀ on
Y_m that reduces to diag(s, 1) at the chosen places and to 1 at Q. -/
lemma lowerChain_principalRep (ϑ : D.TameChar) (s : D.chosenGL)
    (y : D.principalForms (D.spaceY 0)) :
    lowerChain ϑ (D.principalRep (D.spaceY 0) s y) =
      algFormRep D.columnsY (D.lastEntry D.m) (firstBlockLift ϑ s) (lowerChain ϑ y) := by
  -- Apply `algFormRep_lowerChain` to `g = diag (s, 1)`, whose diagonal blocks after the first are
  -- `1`.
  let g : LevelReductionsY ϑ D.m :=
    firstBlockHom (D.levelPlaces ϑ) (BlockIndex.firstBlock (T := Fin D.t) D.m) s
  have h_row (x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex) (a b : D.Y D.m)
      (ha : blockNumber D.m a ≠ 0) : g x a b = if a = b then 1 else 0 := by
    cases x with
    | inl x => exact extendGL_apply_of_notMem_range _ (s x) (by rwa [← blockNumber_eq_zero_iff]) b
    | inr x => rfl
  have h_first (x : (D.levelPlaces ϑ).ChosenIndex) :
      (g (Sum.inl x)).val.submatrix (BlockIndex.firstBlock D.m) (BlockIndex.firstBlock D.m) =
        (s x).val :=
    submatrix_extendGL _ (s x)
  have h_tri (x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex) :
      (g x).val.BlockTriangular (blockNumber D.m) := by
    -- An entry below the diagonal blocks lies off the diagonal, in a row outside block 0.
    intro a b hab
    rw [h_row x a b (Fin.ne_zero_of_lt hab), ite_eq_right fun h_eq : a = b ↦ hab.ne (by rw [h_eq])]
  have h_block (x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex)
      (l : Fin D.m) : (g x).val.toSquareBlock (blockNumber D.m) l.succ = 1 := by
    simp +contextual [← ext_iff, one_apply, toSquareBlock_def, h_row]
  -- So all the character values in the law of the chain are 1.
  have h_scalar : ∏ x : (D.levelPlaces ϑ).ChosenIndex ⊕ (D.levelPlaces ϑ).TwistIndex,
      ∏ l : Fin D.m, chainTamePart ϑ l ((D.levelPlaces ϑ).placeAt x)
        ((g x).val.toSquareBlock (blockNumber D.m) l.succ).det = 1 := by
    simp [h_block]
  refine Eq.symm ((algFormRep_lowerChain ϑ s y (firstBlockLift ϑ s) g (reduceFamily_liftResidue g)
    h_tri h_first).trans ?_)
  rw [h_scalar, one_smul]

end New.Data

end RowChain

end
