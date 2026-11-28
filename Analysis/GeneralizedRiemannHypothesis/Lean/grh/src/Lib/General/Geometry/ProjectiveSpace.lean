import Lib.General.Geometry.LineBundles

/-!
# Projective space, linear systems and projective embeddings, with Segre and Veronese

This file treats projective space `New.ProjSpace ι = Proj ℤ[X i]` and maps to it through ring-valued
points. A linear system (`New.LineBundle.IsLinearSystem`) is a line bundle given by a cover `U i`
and functions `g i j`. Each `g i j` is regular on all of `U i` and plays the part of `s j / s i`. A
projective embedding is a linear system `L` on `X` with a proper morphism `s : X ⟶ S`. In it, two
points of one chart with the same coordinates and the same image in `S` are equal. The file shows
that such embeddings determine morphisms and pass to closed subschemes and composites.

## Main definitions and results

* `New.ProjSpace.hyperplaneBundle`, `New.ProjSpace.isLinearSystem_hyperplaneBundle`: the standard
  charts with `g i j = X j / X i` form a linear system.
* `New.LineBundle.IsHomogeneousCoords`: homogeneous coordinates of a point. Under a projective
  embedding, a point that lies in some chart is determined by its coordinates and its image in the
  base (`New.LineBundle.IsProjEmbedding.eq_of_isHomogeneousCoords`). A vector with a unit entry is a
  vector of coordinates of some point of projective space
  (`New.ProjSpace.exists_isHomogeneousCoords`).
* `New.LineBundle.IsProjEmbedding`, `New.isProjEmbedding_projSpace`: projective embeddings, by
  linear systems that separate points. Projective space over a base, with a finite index set, is
  one.
* `New.LineBundle.exists_picClass_eq_pull_hyperplane`,
  `New.LineBundle.IsLinearSystem.exists_hom_projSpace`: finite families of sections without common
  zero, and finite linear systems, come from maps to projective space.
* `New.LineBundle.IsProjEmbedding.exists_isClosedImmersion`: for finite `ι`, an embedding is a
  closed immersion into ℙ^ι × S.
* `New.LineBundle.isProjEmbedding_pi` (Segre), `New.LineBundle.IsProjEmbedding.pow` (Veronese): a
  proper scheme with finitely many jointly separating maps to embedded schemes embeds, and the
  `m`-th tensor power of a projective embedding is one for `m ≠ 0`.

Notions from other files:
* `New.PointFn`: a function on ring-valued points of X attaches an element of A to every point Spec
  A → X, for every ring A, with no compatibility required. It is regular on an open U if its value
  at Spec φ ≫ t is φ of its value at t, for every t landing in U and every ring map φ.
* `New.LineBundle.IsSection`: the family (s_i) is a global section of L: each s_i is regular on U_i,
  and s_i = g_ij s_j at points landing in U_i and U_j.
* `New.LandsIn`: the morphism t : Y → X lands in the open U, that is, t⁻¹U is all of Y.
* `New.PointFn.ofSection`: a section s over U as a function on ring-valued points: its value at t :
  Spec A → X is t*s in A if t lands in U, and 0 otherwise.
-/

noncomputable section

namespace New

/-! ## Projective space, homogeneous coordinates and linear systems -/

section ProjectiveSpace

open CategoryTheory AlgebraicGeometry Limits PointFn Finset Proj Int Algebra CommRingCat
  IsLocalization MvPolynomial HomogeneousLocalization Localization MorphismProperty prod Ring

variable {X Y S : Scheme} {ι κ : Type} {A : CommRingCat} {i j k l : ι} {L M : LineBundle X ι}
  {N : LineBundle X κ} {t : Spec A ⟶ X} {v : ι → A} {p : Y ⟶ X} {s : X ⟶ S}

attribute [local instance] gradedAlgebra

/-- The value of a homogeneous polynomial `a` of degree `n`, with coefficients mapped by `f`, at the
scaled point `c • v` is `c ^ n` times its value at `v`. -/
lemma eval₂_mul_of_isHomogeneous {σ R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    {a : MvPolynomial σ R} (ha : a.IsHomogeneous n) (f : R →+* S) (c : S) (v : σ → S) :
    eval₂ f (fun i : σ ↦ c * v i) a = c ^ n * eval₂ f v a := by
  rw [eval₂_eq, eval₂_eq, mul_sum]
  refine sum_congr rfl fun d hd ↦ ?_
  -- Each monomial `d` of `a` has degree `n`.
  have h_scale : ∏ i ∈ d.support, (c * v i) ^ d i = c ^ n * ∏ i ∈ d.support, v i ^ d i := by
    simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, ← ha.degree_eq_sum_deg_support hd]
  rw [h_scale, mul_left_comm]

/-! ### Projective space and its charts -/

lemma ProjSpace.X_mem_homogeneousSubmodule (i : ι) :
    MvPolynomial.X i ∈ homogeneousSubmodule ι ℤ 1 := isHomogeneous_X ℤ i

open ProjSpace

/-- Projective space over ℤ with homogeneous coordinates X_i, i in ι: the scheme Proj ℤ[X_i]. -/
abbrev ProjSpace (ι : Type) : Scheme := Proj (homogeneousSubmodule.{0} ι ℤ)

/-- The fraction X_j/X_i in the degree-zero part of the localization of ℤ[X] at X_i. -/
abbrev ProjSpace.coordFraction (i j : ι) :
    HomogeneousLocalization.Away (homogeneousSubmodule ι ℤ) (MvPolynomial.X i) :=
  Away.isLocalizationElem (X_mem_homogeneousSubmodule i) (X_mem_homogeneousSubmodule j)

/-- The fraction X_j/X_i as a section over the standard chart D₊(X_i) of projective space. -/
abbrev ProjSpace.coordSection (i j : ι) :
    Γ(ProjSpace ι, basicOpen (homogeneousSubmodule ι ℤ) (MvPolynomial.X i)) :=
  awayToSection (homogeneousSubmodule ι ℤ) (MvPolynomial.X i) (coordFraction i j)

/-- The function X_j/X_i on ring-valued points of projective space landing in D₊(X_i), and zero
at the other points. -/
abbrev ProjSpace.coordRatio (i j : ι) : PointFn (Proj (homogeneousSubmodule ι ℤ)) :=
  ofSection (awayToSection (homogeneousSubmodule ι ℤ) (MvPolynomial.X i)
    (Away.isLocalizationElem (X_mem_homogeneousSubmodule i) (X_mem_homogeneousSubmodule j)))

/-- On an open `U` contained in D₊(X_i) and D₊(X_j), the restrictions of the sections X_j/X_i and
X_k/X_j multiply to the restriction of X_k/X_i. -/
lemma ProjSpace.map_coordSection_mul (i j k : ι) {U : (ProjSpace ι).Opens}
    (hi : U ≤ basicOpen (homogeneousSubmodule ι ℤ) (MvPolynomial.X i))
    (hj : U ≤ basicOpen (homogeneousSubmodule ι ℤ) (MvPolynomial.X j)) :
    (ProjSpace ι).presheaf.map (homOfLE hi).op (coordSection i j) *
        (ProjSpace ι).presheaf.map (homOfLE hj).op (coordSection j k) =
      (ProjSpace ι).presheaf.map (homOfLE hi).op (coordSection i k) := by
  -- Sections are families of fractions, one at each point `x`, in the localization at `x`. There
  -- `coordSection a b` is `X b ^ 1 / X a ^ 1`, and fractions multiply term by term.
  refine Subtype.ext (funext fun x ↦ val_injective _ ?_)
  change Localization.mk (X j ^ 1 * X k ^ 1) ⟨X i ^ 1 * X j ^ 1, _⟩ =
    Localization.mk (X k ^ 1) ⟨X i ^ 1, _⟩
  exact mk_eq_mk_iff.2 (r_of_eq (mul_assoc (X i ^ 1) (X j ^ 1) (X k ^ 1)).symm)

/-- At a point of projective space that lands in D₊(X_i) ∩ D₊(X_j) the functions X_j/X_i and
X_k/X_j multiply to X_k/X_i. -/
@[simp]
lemma ProjSpace.coordRatio_mul (i j k : ι) (t : Spec A ⟶ Proj (homogeneousSubmodule ι ℤ))
    (ht : LandsIn t (basicOpen (homogeneousSubmodule ι ℤ) (MvPolynomial.X i) ⊓
      basicOpen (homogeneousSubmodule ι ℤ) (MvPolynomial.X j))) :
    coordRatio i j A t * coordRatio j k A t = coordRatio i k A t := by
  -- Restrict the three sections to the intersection of the two charts, in which `t` lands.
  unfold coordRatio
  rw [← ofSection_map (coordSection i j) (homOfLE inf_le_left).op ht,
    ← ofSection_map (coordSection j k) (homOfLE inf_le_right).op ht,
    ← ofSection_map (coordSection i k) (homOfLE inf_le_left).op ht,
    ← map_coordSection_mul i j k inf_le_left inf_le_right]
  simp only [ofSection_eq ht, map_mul]

/-- The line bundle O(1) on projective space, with the standard cover D₊(X_i) and transition
functions X_j/X_i. -/
def ProjSpace.hyperplaneBundle (ι : Type) : LineBundle (ProjSpace ι) ι where
  opens i := basicOpen (homogeneousSubmodule ι ℤ) (MvPolynomial.X i)
  transition := coordRatio
  cover := by
    -- The `X i` are homogeneous and generate the ring over its degree zero part, already over `ℤ`.
    refine iSup_basicOpen_eq_top' _ _ (⟨1, X_mem_homogeneousSubmodule ·⟩) ?_
    rw [← adjoin_adjoin_of_tower ℤ]
    simp
  regular := by simp [(isRegularOn_ofSection _).mono]
  transition_self i := by
    have h_one : coordFraction i i = 1 := by aesop
    simp +contextual [ofSection_eq, h_one]

/-- The standard chart D₊(X_i) of projective space is affine. -/
lemma ProjSpace.isAffineOpen_chart (i : ι) : IsAffineOpen ((hyperplaneBundle ι).opens i) :=
  isAffineOpen_basicOpen _ _ (X_mem_homogeneousSubmodule i) one_pos

/-- A point `t` of the chart D₊(X_i) lands in the chart D₊(X_j) exactly when the value of X_j/X_i at
`t` is a unit. -/
lemma ProjSpace.landsIn_chart_iff_isUnit {t : Spec A ⟶ ProjSpace ι}
    (ht : LandsIn t ((hyperplaneBundle ι).opens i)) :
    LandsIn t ((hyperplaneBundle ι).opens j) ↔
      IsUnit ((hyperplaneBundle ι).transition i j A t) := by
  refine ⟨(hyperplaneBundle ι).isUnit_transition ht, fun h_unit x hx ↦ ?_⟩
  let y : (hyperplaneBundle ι).opens i := ⟨t x, ht hx⟩
  -- The prime ideal of `y` in the ring of sections over the chart does not contain `X j / X i`.
  have h_prime : y ∈ Scheme.Opens.toSpecΓ _ ⁻¹ᵁ PrimeSpectrum.basicOpen (coordSection i j) :=
    (Scheme.Opens.toSpecΓ_preimage_basicOpen _ _).ge
      ((landsIn_basicOpen ht (coordSection i j)).2 h_unit hx)
  -- A fraction lies in that prime exactly when its numerator lies in the homogeneous prime `y`.
  change .X j ∉ (t x).asHomogeneousIdeal
  rw [← pow_one (MvPolynomial.X j)]
  exact fun h_num ↦ h_prime ((ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply _ y _).2 h_num)

namespace LineBundle

/-- v is a vector of homogeneous coordinates of the point t for L: t lands in U_j exactly when v_j
is a unit, and then g_jk(t) = v_k/v_j. -/
def IsHomogeneousCoords (L : LineBundle X ι) (t : Spec A ⟶ X) (v : ι → A) : Prop :=
  ∀ j : ι, (LandsIn t (L.opens j) ↔ IsUnit (v j)) ∧
    ∀ k : ι, IsUnit (v j) → L.transition j k A t = v k * (v j)⁻¹ʳ

lemma IsHomogeneousCoords.landsIn_iff_isUnit (hv : L.IsHomogeneousCoords t v) (j : ι) :
    LandsIn t (L.opens j) ↔ IsUnit (v j) := (hv j).1

/-- If v is a vector of homogeneous coordinates of t and v_j is a unit, then g_jk(t) = v_k/v_j. -/
lemma IsHomogeneousCoords.transition_eq_mul_inverse (hv : L.IsHomogeneousCoords t v)
    (hj : IsUnit (v j)) (k : ι) : L.transition j k A t = v k * (v j)⁻¹ʳ := (hv j).2 k hj

lemma IsHomogeneousCoords.intro (h_lands : ∀ j : ι, LandsIn t (L.opens j) ↔ IsUnit (v j))
    (h_ratio : ∀ j k : ι, IsUnit (v j) → L.transition j k A t = v k * (v j)⁻¹ʳ) :
    L.IsHomogeneousCoords t v := fun j ↦ ⟨h_lands j, h_ratio j⟩

/-- A point lands in the chart (i, k) of the tensor product of L and N exactly when it lands in the
chart i of L and in the chart k of N. -/
lemma landsIn_mul_opens_iff {a : ι × κ} :
    LandsIn t ((L.mul N).opens a) ↔ LandsIn t (L.opens a.1) ∧ LandsIn t (N.opens a.2) := landsIn_inf

/-- `L` is a linear system, that is, the data of a map to projective space. The model is
`L.transition i j = s j / s i` on the chart `L.opens i` where `s i` does not vanish, for sections
`s i` without common zero. -/
structure IsLinearSystem (L : LineBundle X ι) : Prop where
  /-- The function `L.transition i j` is regular on the whole chart `L.opens i`. -/
  isRegularOn_transition (i j : ι) : (L.transition i j).IsRegularOn (L.opens i)
  /-- The function `L.transition i j` vanishes at the points that do not land in `L.opens i`. -/
  transition_eq_zero {A : CommRingCat} {i : ι} (j : ι) {t : Spec A ⟶ X}
    (ht : ¬LandsIn t (L.opens i)) : L.transition i j A t = 0
  /-- The values `L.transition i j A t`, as `j` varies, are homogeneous coordinates of every point
  `t` of the chart `L.opens i`. -/
  isHomogeneousCoords_transition {A : CommRingCat} {i : ι} {t : Spec A ⟶ X}
    (ht : LandsIn t (L.opens i)) : L.IsHomogeneousCoords t fun j : ι ↦ L.transition i j A t

/-- The standard charts D₊(X_i) with the functions X_j/X_i form a linear system on projective
space. -/
lemma _root_.New.ProjSpace.isLinearSystem_hyperplaneBundle :
    (hyperplaneBundle ι).IsLinearSystem where
  isRegularOn_transition i j := isRegularOn_ofSection (coordSection i j)
  transition_eq_zero j t ht := dite_eq_right ht
  isHomogeneousCoords_transition {A i t} ht := by
    refine .intro (fun j ↦ landsIn_chart_iff_isUnit ht) fun j k h_unit ↦ ?_
    -- On both charts, `transition j k = transition i k / transition i j` is the cocycle condition.
    rw [eq_mul_inverse_iff_mul_eq _ _ _ h_unit, mul_comm]
    exact coordRatio_mul i j k t (le_inf ht ((landsIn_chart_iff_isUnit ht).2 h_unit))

/-- Two linear systems L, M on X with one index set are equal if g^M_jk = g^M_ji · g^L_ik for all k
at every point landing in U_i of L and in U_j of M. -/
lemma IsLinearSystem.ext_of_transition_eq_mul (hL : L.IsLinearSystem) (hM : M.IsLinearSystem)
    (h_mul : ∀ (i j k : ι) (A : CommRingCat) (t : Spec A ⟶ X), LandsIn t (L.opens i) →
      LandsIn t (M.opens j) → M.transition j k A t = M.transition j i A t * L.transition i k A t) :
    M = L := by
  -- At a point of the i-th chart of L and the j-th chart of M, h_mul with k = j exhibits both
  -- M.transition j i and L.transition i j as units, so the covers agree.
  have h_one (i j : ι) {A : CommRingCat} {t : Spec A ⟶ X} (hLt : LandsIn t (L.opens i))
      (hMt : LandsIn t (M.opens j)) : M.transition j i A t * L.transition i j A t = 1 := by
    rw [← h_mul i j j A t hLt hMt, M.transition_self j A t hMt]
  have hU : M.opens = L.opens := by
    refine le_antisymm (fun i ↦ le_of_cover L.isOpenCover fun j A t hLt hMt ↦ ?_)
      fun i ↦ le_of_cover M.isOpenCover fun j A t hMt hLt ↦ ?_
    · exact ((hL.isHomogeneousCoords_transition hLt).landsIn_iff_isUnit i).2
        (.of_mul_eq_one_right _ (h_one j i hLt hMt))
    · exact ((hM.isHomogeneousCoords_transition hMt).landsIn_iff_isUnit i).2
        (.of_mul_eq_one _ (h_one i j hLt hMt))
  refine LineBundle.ext hU ?_
  funext i k A t
  by_cases hMt : LandsIn t (M.opens i)
  · rw [h_mul i i k A t (by rwa [← hU]) hMt, M.transition_self i A t hMt, one_mul]
  · rw [hM.transition_eq_zero k hMt, hL.transition_eq_zero k (by rwa [← hU])]

/-- For a linear system L with transition functions g_ij and a fixed j, the family (g_ij)_i is a
global section of L: each g_ij is regular on U_i, and g_ij = g_ik g_kj on U_i ∩ U_k. -/
lemma IsLinearSystem.isSection (j : ι) {L : LineBundle X ι} (hL : L.IsLinearSystem) :
    L.IsSection fun i : ι ↦ L.transition i j := by
  refine ⟨fun i ↦ hL.isRegularOn_transition i j, fun i k A t hi hk ↦ ?_⟩
  have h_unit : IsUnit (L.transition i k A t) := L.isUnit_transition hi hk
  have h_ratio : L.transition k j A t = L.transition i j A t * (L.transition i k A t)⁻¹ʳ :=
    (hL.isHomogeneousCoords_transition hi).transition_eq_mul_inverse h_unit j
  change L.transition i j A t = L.transition i k A t * L.transition k j A t
  rw [h_ratio, mul_left_comm, Ring.mul_inverse_cancel _ h_unit, mul_one]

/-- The pull-back of a linear system along a morphism is a linear system. -/
lemma IsLinearSystem.pull (p : Y ⟶ X) (hL : L.IsLinearSystem) : (L.pull p).IsLinearSystem where
  isRegularOn_transition i j := (hL.isRegularOn_transition i j).pull p
  transition_eq_zero j t ht := hL.transition_eq_zero j (t := t ≫ p) ht
  isHomogeneousCoords_transition {_A _i t} ht := hL.isHomogeneousCoords_transition (t := t ≫ p) ht

/-- The products v_i w_k of homogeneous coordinates v and w of a point t for L and for N are
homogeneous coordinates of t for the tensor product of L and N. -/
lemma isHomogeneousCoords_mul_prod (hv : L.IsHomogeneousCoords t v) {w : κ → A}
    (hw : N.IsHomogeneousCoords t w) :
    (L.mul N).IsHomogeneousCoords t fun i : ι × κ ↦ v i.1 * w i.2 := by
  refine .intro (fun a ↦ ?_) fun a k h_unit ↦ ?_
  · rw [landsIn_mul_opens_iff, hv.landsIn_iff_isUnit, hw.landsIn_iff_isUnit, IsUnit.mul_iff]
  · obtain ⟨ha, hb⟩ : IsUnit (v a.1) ∧ IsUnit (w a.2) := IsUnit.mul_iff.1 h_unit
    simp [hv.transition_eq_mul_inverse ha, hw.transition_eq_mul_inverse hb, mul_inverse_rev,
      mul_mul_mul_comm, mul_comm]

/-- The tensor product of two linear systems is a linear system. -/
lemma IsLinearSystem.mul (hL : L.IsLinearSystem) (hN : N.IsLinearSystem) :
    (L.mul N).IsLinearSystem where
  isRegularOn_transition i j :=
    (hL.isRegularOn_transition i.1 j.1).mul (hN.isRegularOn_transition i.2 j.2)
  transition_eq_zero {A i} j t ht := by
    obtain hLt | hNt := not_and_or.1 (landsIn_mul_opens_iff.not.1 ht)
    · simp [hL.transition_eq_zero j.1 hLt]
    · simp [hN.transition_eq_zero j.2 hNt]
  isHomogeneousCoords_transition {A i t} ht := by
    obtain ⟨hLt, hNt⟩ := landsIn_mul_opens_iff.1 ht
    exact isHomogeneousCoords_mul_prod (hL.isHomogeneousCoords_transition hLt)
      (hN.isHomogeneousCoords_transition hNt)

namespace IsHomogeneousCoords

/-- A vector v gives homogeneous coordinates of t for the pull-back of L along p exactly when it
gives homogeneous coordinates of t ≫ p for L. -/
lemma pull_iff {t : Spec A ⟶ Y} :
    (L.pull p).IsHomogeneousCoords t v ↔ L.IsHomogeneousCoords (t ≫ p) v := .rfl

lemma smul (hv : L.IsHomogeneousCoords t v) {u : A} (hu : IsUnit u) :
    L.IsHomogeneousCoords t (u • v) := by
  refine .intro (fun j ↦ by simp [hu, hv.landsIn_iff_isUnit]) fun j k h_unit ↦ ?_
  have hj : IsUnit (v j) := by simpa [hu] using h_unit
  simp only [Pi.smul_apply, smul_eq_mul, hv.transition_eq_mul_inverse hj, mul_inverse_rev]
  linear_combination (-(v k * (v j)⁻¹ʳ)) * Ring.mul_inverse_cancel u hu

/-- Let v be homogeneous coordinates of the point t for a linear system L, with a unit entry v_i.
For a ring map φ from A to R, the vector φ(v) gives homogeneous coordinates of the induced
R-valued point. -/
lemma map (hv : L.IsHomogeneousCoords t v) {R : CommRingCat} (hL : L.IsLinearSystem)
    (hi : IsUnit (v i)) (φ : A ⟶ R) :
    L.IsHomogeneousCoords (Spec.map (R := A) (S := R) φ ≫ t) (φ ∘ v) := by
  -- In the chart i the vector v is v i times the coordinates g_ij, which are regular there.
  have h_chart : LandsIn t (L.opens i) := (hv.landsIn_iff_isUnit i).2 hi
  have h_scale (j : ι) : v j = v i * L.transition i j A t := by
    simp [hv.transition_eq_mul_inverse hi, mul_left_comm (v i), Ring.mul_inverse_cancel _ hi]
  have h_eq : φ ∘ v = φ (v i) • fun j : ι ↦ L.transition i j R (Spec.map φ ≫ t) :=
    funext fun j ↦ by simp [hL.isRegularOn_transition i j φ t h_chart, h_scale j]
  rw [h_eq]
  exact (hL.isHomogeneousCoords_transition (h_chart.comp _)).smul (hi.map φ.hom)

/-- The products of homogeneous coordinates of a point for L and for N are homogeneous coordinates
of it for the tensor product of L and N. -/
lemma mul (hv : L.IsHomogeneousCoords t v) {w : κ → A} (hw : N.IsHomogeneousCoords t w) :
    (L.mul N).IsHomogeneousCoords t fun i : ι × κ ↦ v i.1 * w i.2 :=
      isHomogeneousCoords_mul_prod hv hw

lemma exists_ne_zero [IsLocalRing A] (hv : L.IsHomogeneousCoords t v) : ∃ i : ι, v i ≠ 0 := by
  obtain ⟨i, hi⟩ := L.exists_landsIn t
  exact ⟨i, ((hv.landsIn_iff_isUnit i).1 hi).ne_zero⟩

lemma ne_zero [IsLocalRing A] (hv : L.IsHomogeneousCoords t v) : v ≠ 0 :=
  Function.ne_iff.2 hv.exists_ne_zero

end IsHomogeneousCoords

/-- For a vector `v` in `A ^ ι` with a unit entry `v i` there is a ring map `φ` from the sections
over the chart D₊(X_i) to `A` that sends X_j/X_i to `v j / v i`. -/
lemma _root_.New.ProjSpace.exists_hom_mul_coordSection_eq (hi : IsUnit (v i)) :
    ∃ φ : Γ(ProjSpace ι, basicOpen (homogeneousSubmodule ι ℤ) (MvPolynomial.X i)) ⟶ A,
      ∀ j : ι, v i * φ (coordSection i j) = v j := by
  -- Substituting `v` makes `X i` a unit, so it extends to the localization at `X i`; restrict it
  -- to the degree-zero part, which is the ring of sections of the chart.
  let ev : MvPolynomial ι ℤ →+* A := eval₂Hom (castRingHom A) v
  have h_inv : ev (X i) * (v i)⁻¹ʳ = 1 := by simp [ev, Ring.mul_inverse_cancel _ hi]
  let ψ : HomogeneousLocalization.Away (homogeneousSubmodule ι ℤ) (X i) →+* A :=
    (awayLift ev (X i) (.of_mul_eq_one _ h_inv)).comp (algebraMap _ (Localization.Away (X i)))
  let e := basicOpenIsoAway _ _ (X_mem_homogeneousSubmodule i) one_pos
  refine ⟨e.inv ≫ ofHom ψ, fun j ↦ ?_⟩
  have h_value : ψ (coordFraction i j) = ev (X j ^ 1) * (v i)⁻¹ʳ ^ 1 :=
    awayLift_mk ev (X i) (X j ^ 1) _ h_inv 1
  change v i * ψ (e.inv (e.hom (coordFraction i j))) = v j
  simp [h_value, ev, mul_left_comm (v i), Ring.mul_inverse_cancel _ hi]

/-- A vector `v` in `A ^ ι` with a unit entry `v i` is a vector of homogeneous coordinates of an
`A`-valued point of projective space over `S` lying over any given point `b` of `S`. -/
lemma _root_.New.ProjSpace.exists_isHomogeneousCoords (b : Spec A ⟶ S) (hi : IsUnit (v i)) :
    ∃ s : Spec A ⟶ ProjSpace ι ⨯ S, s ≫ snd = b ∧
      ((hyperplaneBundle ι).pull fst).IsHomogeneousCoords s v := by
  obtain ⟨φ, hφ⟩ := exists_hom_mul_coordSection_eq hi
  let x : Spec A ⟶ ProjSpace ι := Spec.map φ ≫ (isAffineOpen_chart i).fromSpec
  have hx : LandsIn x ((hyperplaneBundle ι).opens i) := landsIn_fromSpec (isAffineOpen_chart i) _
  have h_coord (j : ι) : (hyperplaneBundle ι).transition i j A x = φ (coordSection i j) :=
    ofSection_map_fromSpec (isAffineOpen_chart i) (coordSection i j) φ
  -- The `transition i j` are coordinates of `x`; scale them by `v i`.
  have h_v : v = v i • fun j : ι ↦ (hyperplaneBundle ι).transition i j A x :=
    funext fun j ↦ by rw [Pi.smul_apply, smul_eq_mul, h_coord, hφ]
  refine ⟨lift x b, lift_snd x b, ?_⟩
  rw [IsHomogeneousCoords.pull_iff, lift_fst, h_v]
  exact (isLinearSystem_hyperplaneBundle.isHomogeneousCoords_transition hx).smul hi

/-- `L` embeds `X` in projective space over `S`: it is a linear system that separates the
ring-valued points of `X` over `S` chart by chart, and `s : X ⟶ S` is proper. -/
structure IsProjEmbedding (L : LineBundle X ι) (s : X ⟶ S) : Prop where
  /-- `L` is a linear system. -/
  isLinearSystem : L.IsLinearSystem
  /-- `X` is proper over `S`. -/
  isProper : IsProper s
  /-- Two points of one chart with the same affine coordinates and the same image in `S` are
  equal. -/
  eq_of_transition_eq {i : ι} {A : CommRingCat} {a b : Spec A ⟶ X} (ha : LandsIn a (L.opens i))
    (hb : LandsIn b (L.opens i)) (h_coord : ∀ j : ι, L.transition i j A a = L.transition i j A b)
    (h_base : a ≫ s = b ≫ s) : a = b

/-- Under a projective embedding, two points a and t with the same homogeneous coordinates v and the
same image in the base are equal, provided a lands in some chart (as it does when A is a local
ring). -/
lemma IsProjEmbedding.eq_of_isHomogeneousCoords {a : Spec A ⟶ X} (hL : L.IsProjEmbedding s)
    (h_base : a ≫ s = t ≫ s) (ha : L.IsHomogeneousCoords a v) (ht : L.IsHomogeneousCoords t v)
    (h_chart : ∃ i : ι, LandsIn a (L.opens i)) : a = t := by
  obtain ⟨i, ha_chart⟩ := h_chart
  -- `v i` is a unit, so `t` lands in the same chart and both have affine coordinates `v j / v i`.
  have h_unit : IsUnit (v i) := (ha.landsIn_iff_isUnit i).1 ha_chart
  refine hL.eq_of_transition_eq ha_chart ((ht.landsIn_iff_isUnit i).2 h_unit) (fun j ↦ ?_) h_base
  rw [ha.transition_eq_mul_inverse h_unit, ht.transition_eq_mul_inverse h_unit]

/-- Base change: if L embeds X over S and Y is the fibre product of s : X ⟶ S and
b : T ⟶ S, with projections p : Y ⟶ X and t : Y ⟶ T, then the pull-back of L along p
embeds Y over T. -/
protected lemma IsProjEmbedding.of_isPullback {T : Scheme} {p : Y ⟶ X} {t : Y ⟶ T} {b : T ⟶ S}
    (hL : L.IsProjEmbedding s) (h_sq : IsPullback p t s b) : (L.pull p).IsProjEmbedding t where
  isLinearSystem := hL.isLinearSystem.pull p
  isProper := of_isPullback h_sq hL.isProper
  eq_of_transition_eq {i A x y} hx hy h_coord h_base := by
    -- Two points of the fibre product agree if they agree in X and in T.
    have h_over : (x ≫ p) ≫ s = (y ≫ p) ≫ s := by simp [h_sq.w, reassoc_of% h_base]
    exact h_sq.hom_ext (hL.eq_of_transition_eq hx hy h_coord h_over) h_base

/-- The degree-zero localization of `ℤ[X]` at `X i` is generated as a ring by the fractions
`X j / X i` (`coordFraction i j`). -/
lemma _root_.New.ProjSpace.surjective_eval₂Hom_coordFraction (i : ι) :
    Function.Surjective (eval₂Hom
      (castRingHom (HomogeneousLocalization.Away (homogeneousSubmodule ι ℤ) (MvPolynomial.X i)))
      fun j : ι ↦ coordFraction i j) := by
  -- An element is `a / X i ^ n` with `a` homogeneous of degree `n`; it is the image of `a`.
  intro x
  obtain ⟨n, a, ha, rfl⟩ := x.mk_surjective _ (X_mem_homogeneousSubmodule i)
  -- Compare in the full localization and clear the denominator: by homogeneity,
  -- `X i ^ n * a (X j / X i) = a (X j)`.
  let φ : MvPolynomial ι ℤ →+* Localization.Away (X i : MvPolynomial ι ℤ) := algebraMap _ _
  have h_frac (j : ι) : φ (X i) * (coordFraction i j).val = φ (X j) := by simp [φ, mk_eq_mk']
  have h_clear (f : ℤ →+* Localization.Away (X i : MvPolynomial ι ℤ)) :
      φ (X i) ^ n * eval₂ f (fun j : ι ↦ (coordFraction i j).val) a = φ a := by
    simp only [← eval₂_mul_of_isHomogeneous (a := a) (n := n) (by simpa using ha), h_frac]
    exact eval₂Hom_X f φ a
  refine ⟨a, val_injective _ ?_⟩
  rw [← HomogeneousLocalization.algebraMap_apply, map_eval₂Hom]
  simpa [φ, mk_eq_mk', eq_mk'_iff_mul_eq, mul_comm] using h_clear _

/-- Two ring maps from the sections over the chart D₊(X_i) that agree on all X_j/X_i are equal. -/
lemma _root_.New.ProjSpace.hom_ext_of_coordSection_eq
    {f g : Γ(ProjSpace ι, basicOpen (homogeneousSubmodule ι ℤ) (MvPolynomial.X i)) ⟶ A}
    (h_coord : ∀ j : ι, f (coordSection i j) = g (coordSection i j)) : f = g := by
  -- The ring of sections is the degree-zero localization at `X i`, generated by the `X j / X i`.
  rw [← cancel_epi (basicOpenIsoAway _ _ (X_mem_homogeneousSubmodule i) one_pos).hom,
    CommRingCat.hom_ext_iff, ← RingHom.cancel_right (surjective_eval₂Hom_coordFraction i)]
  ext j
  · simp
  · simpa [basicOpenIsoAway_hom] using h_coord j

/-- Projective space with a finite index set is proper over `Spec ℤ`. -/
lemma _root_.New.ProjSpace.isProper_specZIsTerminal_from [Finite κ] :
    IsProper (specZIsTerminal.from (ProjSpace κ)) := by
  -- `Proj` is proper over the spectrum of the degree zero part, which is finite over `ℤ`.
  let c : of ℤ ⟶ of (homogeneousSubmodule κ ℤ 0) := ofHom (algebraMap ℤ _)
  have h_finite : IsFinite (Spec.map c) := (IsFinite.SpecMap_iff c).2
    (RingHom.finite_algebraMap.2 (.of_fg (homogeneousSubmodule_fg κ ℤ 0)))
  have : FiniteType (homogeneousSubmodule κ ℤ 0) (MvPolynomial κ ℤ) :=
    .of_restrictScalars_finiteType ℤ _ _
  rw [specZIsTerminal.hom_ext (specZIsTerminal.from _) (toSpecZero _ ≫ Spec.map c)]
  infer_instance

/-- For a finite index set κ and a scheme S, the pull-back of O(1) to ℙ^κ × S is a projective
embedding over S for the second projection. -/
lemma _root_.New.isProjEmbedding_projSpace {κ : Type} [Finite κ] {S : Scheme} :
    IsProjEmbedding (S := S) ((hyperplaneBundle κ).pull fst) snd := by
  -- It is the base change of projective space over `Spec ℤ`, the terminal scheme.
  suffices h : (hyperplaneBundle κ).IsProjEmbedding (specZIsTerminal.from (ProjSpace κ)) from
    h.of_isPullback (.of_is_product' (prodIsProd (ProjSpace κ) S) specZIsTerminal)
  refine ⟨isLinearSystem_hyperplaneBundle, isProper_specZIsTerminal_from, ?_⟩
  rintro i A a b ha hb h_coord -
  -- The chart is affine, so `a` and `b` are determined by their evaluation maps on its sections,
  -- and the values of these maps at the `X j / X i` are the affine coordinates.
  have h_eval : evalSection a ha = evalSection b hb :=
    hom_ext_of_coordSection_eq fun j ↦
      calc _ = (hyperplaneBundle κ).transition i j A a := (ofSection_eq ha _).symm
        _ = (hyperplaneBundle κ).transition i j A b := h_coord j
        _ = evalSection b hb (coordSection i j) := ofSection_eq hb _
  rw [← map_evalSection_fromSpec (isAffineOpen_chart i) ha, h_eval, map_evalSection_fromSpec]

/-! ### Maps to projective space -/

/-- Gluing of points with given coordinates. Let `s j` (`j : κ`, with `κ` finite) be sections of
the line bundle `L`, where `s j i` is the function of `s j` on `L.opens i`. Let `C` be a line bundle
indexed by pairs, used only for its cover, such that `C.opens (i, j)` lies in `L.opens i` and
`s j i` is a unit on it. Then there is a map `f` from `X` to projective space such that, at each
point `t` of `C.opens (i, j)`, the values `s k i (t)` are homogeneous coordinates of `t ≫ f`. -/
lemma exists_hom_isHomogeneousCoords_of_cover [Finite κ] {s : κ → ι → PointFn X}
    (hs : ∀ j : κ, L.IsSection (s j)) (C : LineBundle X (ι × κ))
    (hC_le : ∀ {a : ι × κ} {A : CommRingCat} {t : Spec A ⟶ X},
      LandsIn t (C.opens a) → LandsIn t (L.opens a.1))
    (hC_unit : ∀ {a : ι × κ} {A : CommRingCat} {t : Spec A ⟶ X},
      LandsIn t (C.opens a) → IsUnit (s a.2 a.1 A t)) :
    ∃ f : X ⟶ ProjSpace κ, ∀ (a : ι × κ) (A : CommRingCat) (t : Spec A ⟶ X), LandsIn t (C.opens a) →
      (hyperplaneBundle κ).IsHomogeneousCoords (t ≫ f) fun k : κ ↦ s k a.1 A t := by
  obtain ⟨h_reg, h_trans⟩ := forall_and.1 hs
  let H : LineBundle (ProjSpace κ ⨯ X) κ := (hyperplaneBundle κ).pull fst
  have hH : H.IsProjEmbedding snd := isProjEmbedding_projSpace
  have h_local (a : ι × κ) (A : CommRingCat) (t : Spec A ⟶ X) (ht : LandsIn t (C.opens a)) :
      ∃ x : Spec A ⟶ ProjSpace κ ⨯ X, x ≫ snd = t ∧ H.IsHomogeneousCoords x fun k ↦ s k a.1 A t :=
    exists_isHomogeneousCoords (i := a.2) t (hC_unit ht)
  choose F hF_snd hF using h_local
  -- On overlaps the coordinate vectors differ by the unit `L.transition`, so the points agree.
  have h_compat (a b : ι × κ) (A B : CommRingCat) (φ : A ⟶ B) (t : Spec A ⟶ X)
      (ha : LandsIn t (C.opens a)) (hb : LandsIn (Spec.map φ ≫ t) (C.opens b)) :
      F b B (Spec.map φ ≫ t) hb = Spec.map φ ≫ F a A t ha := by
    have haL : LandsIn (Spec.map φ ≫ t) (L.opens a.1) := (hC_le ha).comp _
    have h_scale : (fun k ↦ s k b.1 B (Spec.map φ ≫ t)) =
        L.transition b.1 a.1 B (Spec.map φ ≫ t) • (φ ∘ fun k ↦ s k a.1 A t) :=
      funext fun k ↦ by simp [h_trans k b.1 a.1 B _ (hC_le hb) haL, h_reg k a.1 φ t (hC_le ha)]
    refine hH.eq_of_isHomogeneousCoords (by simp [hF_snd]) (hF b B _ hb) ?_
      ⟨b.2, ((hF b B _ hb).landsIn_iff_isUnit b.2).2 (hC_unit hb)⟩
    simpa only [h_scale] using ((hF a A t ha).map hH.isLinearSystem (hC_unit ha) φ).smul
      (L.isUnit_transition (hC_le hb) haL)
  obtain ⟨f, hf⟩ := exists_hom_of_cover C.isOpenCover F h_compat
  refine ⟨f ≫ fst, fun a A t ht ↦ ?_⟩
  simpa only [← Category.assoc, hf a A t ht] using IsHomogeneousCoords.pull_iff.1 (hF a A t ht)

/-- Let `s j` (`j : κ`) be sections of the line bundle `L` on `X`, where `s j i` is the function of
`s j` on the chart `L.opens i`. Suppose that they have no common zero at the field-valued points
that factor through a surjective `p : Y ⟶ X`. Then the opens of the `L.opens i` where `s j i` is a
unit cover `X`; the cover is given as that of a line bundle `C` indexed by the pairs `(i, j)`. -/
lemma exists_landsIn_opens_iff_isUnit (p : Y ⟶ X) [hp : Surjective p] {s : κ → ι → PointFn X}
    (hs : ∀ j : κ, L.IsSection (s j))
    (h_nz : ∀ (i : ι) (K : Type) [Field K] (t : Spec (of K) ⟶ Y),
      LandsIn (t ≫ p) (L.opens i) → ∃ j : κ, s j i (of K) (t ≫ p) ≠ 0) :
    ∃ C : LineBundle X (ι × κ), ∀ {a : ι × κ} {A : CommRingCat} {t : Spec A ⟶ X},
      LandsIn t (C.opens a) ↔ LandsIn t (L.opens a.1) ∧ IsUnit (s a.2 a.1 A t) := by
  have h_open (i : ι) (j : κ) : ∃ W : X.Opens, ∀ {A : CommRingCat} {t : Spec A ⟶ X},
      LandsIn t W ↔ LandsIn t (L.opens i) ∧ IsUnit (s j i A t) := by
    obtain ⟨σ, hσ⟩ := ((hs j).1 i).exists_ofSection
    -- On `L.opens i` the function `s j i` is that of the section `σ`; take its basic open.
    refine ⟨X.basicOpen σ, fun {A t} ↦ ?_⟩
    rw [← and_iff_right_of_imp fun ht : LandsIn t _ ↦ ht.mono (X.basicOpen_le σ)]
    exact and_congr_right fun ht ↦ by rw [landsIn_basicOpen ht, hσ A t ht]
  choose W hW using h_open
  -- At the residue field of a point `y` of `Y` some `s j i` is nonzero, so a unit.
  have h_mem (y : Y) : ∃ (i : ι) (j : κ), p y ∈ W i j := by
    obtain ⟨i, hi⟩ := L.exists_landsIn (Y.fromSpecResidueField y ≫ p)
    obtain ⟨j, hj⟩ := h_nz i _ _ hi
    have h_in : ⊤ ≤ (Y.fromSpecResidueField y ≫ p) ⁻¹ᵁ W i j := (hW i j).2 ⟨hi, hj.isUnit⟩
    exact ⟨i, j, by simpa using h_in (x := default) trivial⟩
  have h_top : ⨆ a : ι × κ, W a.1 a.2 = ⊤ := by simpa [SetLike.ext_iff, hp.surj.forall] using h_mem
  -- The trivial line bundle carries this cover.
  exact ⟨{ opens := fun a ↦ W a.1 a.2, transition := 1, cover := h_top }, hW _ _⟩

/-- Let `s j` (`j : κ`) be sections of the line bundle `L` on `X` such that, at each point `t` of
`L.opens i`, the values `s j i (t)` are homogeneous coordinates of `t` for the line bundle `N`. Then
`L` and `N` have the same class in the Picard group. -/
lemma picClass_eq_of_isHomogeneousCoords {N : LineBundle X κ} {s : κ → ι → PointFn X}
    (hs : ∀ j : κ, L.IsSection (s j))
    (h_coords : ∀ (i : ι) (A : CommRingCat) (t : Spec A ⟶ X), LandsIn t (L.opens i) →
      N.IsHomogeneousCoords t fun j : κ ↦ s j i A t) :
    L.picClass = N.picClass := by
  obtain ⟨h_reg, h_trans⟩ := forall_and.1 hs
  -- The `s j i` form a nowhere vanishing section of `L ⊗ N⁻¹`, which is thus trivial.
  have h_unit (a : ι × κ) (A : CommRingCat) (t : Spec A ⟶ X)
      (ht : LandsIn t (L.opens a.1 ⊓ N.opens a.2)) : IsUnit (s a.2 a.1 A t) :=
    ((h_coords a.1 A t (ht.mono inf_le_left)).landsIn_iff_isUnit a.2).1 (ht.mono inf_le_right)
  refine picClass_eq_iff.2 ⟨fun a ↦ s a.2 a.1,
    ⟨fun a ↦ (h_reg a.2 a.1).mono inf_le_left, fun a b A t ha hb ↦ ?_⟩, h_unit⟩
  -- `s a.2 a.1 = L.transition a.1 b.1 * s a.2 b.1`, and `s a.2 b.1 / s b.2 b.1` is
  -- `N.transition b.2 a.2`.
  change s a.2 a.1 A t = L.transition a.1 b.1 A t * N.transition b.2 a.2 A t * s b.2 b.1 A t
  have hbL : LandsIn t (L.opens b.1) := hb.mono inf_le_left
  rw [(h_coords b.1 A t hbL).transition_eq_mul_inverse (h_unit b A t hb), mul_assoc,
    inverse_mul_cancel_right _ _ (h_unit b A t hb), h_trans a.2 _ _ A t (ha.mono inf_le_left) hbL]

/-- Let `s j` (`j : κ`, with `κ` finite) be sections of the line bundle `L` on `X`, where `s j i` is
the function of `s j` on the chart `L.opens i`. Suppose that they have no common zero at the
field-valued points that factor through a surjective `p : Y ⟶ X`. Then there is a map `f` from `X`
to projective space such that (a) `L` has the same class in the Picard group as the pull-back of
O(1) = `New.ProjSpace.hyperplaneBundle κ` along `f` and (b) at each point `t` of `L.opens i` the
values `s j i (t)` are homogeneous coordinates of `t` for that pull-back. -/
lemma exists_picClass_eq_pull_hyperplane (p : Y ⟶ X) [Finite κ] [hp : Surjective p]
    {s : κ → ι → PointFn X} (hs : ∀ j : κ, L.IsSection (s j))
    (h_nz : ∀ (i : ι) (K : Type) [Field K] (t : Spec (of K) ⟶ Y),
      LandsIn (t ≫ p) (L.opens i) → ∃ j : κ, s j i (of K) (t ≫ p) ≠ 0) :
    ∃ f : X ⟶ ProjSpace κ,
      L.picClass = ((hyperplaneBundle κ).pull f).picClass ∧
      ∀ (i : ι) (A : CommRingCat) (t : Spec A ⟶ X), LandsIn t (L.opens i) →
        ((hyperplaneBundle κ).pull f).IsHomogeneousCoords t fun j : κ ↦ s j i A t := by
  -- The opens `C.opens (i, j)` of `L.opens i` where `s j i` is a unit cover `X`. On them the
  -- vectors `(s · i)` give points of projective space, which glue to a map `f`.
  obtain ⟨C, hC⟩ := exists_landsIn_opens_iff_isUnit p hs h_nz
  obtain ⟨f, hf⟩ :=
    exists_hom_isHomogeneousCoords_of_cover hs C (fun ht ↦ (hC.1 ht).1) fun ht ↦ (hC.1 ht).2
  let H : LineBundle X κ := (hyperplaneBundle κ).pull f
  -- The points of `L.opens i` that `f` sends to the `j`-th chart lie in `C.opens (i, j)`, as one
  -- checks on the cover.
  have h_le (i : ι) (j : κ) : L.opens i ⊓ H.opens j ≤ C.opens (i, j) := by
    refine le_of_cover C.isOpenCover fun b A t hb ht ↦ ?_
    obtain ⟨hi, hj⟩ := landsIn_inf.1 ht
    -- `s j i = L.transition i b.1 * s j b.1` is a product of two units.
    have h_unit : IsUnit (s j b.1 A t) := ((hf b A t hb).landsIn_iff_isUnit j).1 hj
    grind [IsSection, isUnit_transition, IsUnit.mul]
  have h_coords (i : ι) (A : CommRingCat) (t : Spec A ⟶ X) (ht : LandsIn t (L.opens i)) :
      H.IsHomogeneousCoords t fun j : κ ↦ s j i A t := by
    -- Where `s j i` is a unit the point lies in `C.opens (i, j)`, so `hf` applies.
    have h_of_unit {j : κ} (h : IsUnit (s j i A t)) :
        H.IsHomogeneousCoords t fun k : κ ↦ s k i A t := hf (i, j) A t (hC.2 ⟨ht, h⟩)
    refine .intro (fun j ↦ ⟨fun hj ↦ ?_, fun h ↦ ((h_of_unit h).landsIn_iff_isUnit j).2 h⟩)
      fun j k h ↦ (h_of_unit h).transition_eq_mul_inverse h k
    exact (hC.1 ((landsIn_inf.2 ⟨ht, hj⟩).mono (h_le i j))).2
  exact ⟨f, picClass_eq_of_isHomogeneousCoords hs h_coords, h_coords⟩

/-- Let `N` be a linear system on `X` indexed by a finite set `κ`, and let `s : X ⟶ S` be any
morphism. Then `N` is the pull-back of O(1), cover and transition functions included, along some
morphism `j` from `X` to `ProjSpace κ ⨯ S` over `S`. -/
lemma IsLinearSystem.exists_hom_projSpace [Finite κ] (hN : N.IsLinearSystem) (s : X ⟶ S) :
    ∃ j : X ⟶ ProjSpace κ ⨯ S, j ≫ snd = s ∧ ((hyperplaneBundle κ).pull fst).pull j = N := by
  -- The sections `N.transition · j` have no common zero, since `N.transition i i = 1` on the
  -- `i`-th chart; the map they define pulls `hyperplaneBundle κ` back to `N`.
  obtain ⟨f, -, hf⟩ := exists_picClass_eq_pull_hyperplane (𝟙 X) hN.isSection
    fun i K _ t ht ↦ ⟨i, (N.transition_self i _ _ ht).trans_ne one_ne_zero⟩
  have h_pull : (hyperplaneBundle κ).pull f = N := by
    refine hN.ext_of_transition_eq_mul (isLinearSystem_hyperplaneBundle.pull f)
      fun i j k A t hi hj ↦ ?_
    -- Both transition functions of the pull-back are ratios of the coordinates given by `hf`.
    have h_unit : IsUnit (N.transition i j A t) := ((hf i A t hi).landsIn_iff_isUnit j).1 hj
    grind [(hf i A t hi).transition_eq_mul_inverse h_unit, N.transition_self i A t hi]
  exact ⟨lift f s, lift_snd f s, by rw [← pull_comp, lift_fst, h_pull]⟩

/-- The morphism `s : X ⟶ S` has a projective embedding with finitely many coordinates; then `X` is
a closed subscheme of a projective space over `S`
(`New.LineBundle.IsProjEmbedding.exists_isClosedImmersion`). -/
@[mk_iff]
class inductive _root_.New.Variety.HasProjEmbedding (s : X ⟶ S) : Prop
  /-- A projective embedding with finitely many coordinates. -/
  | mk {I : Type} {P : LineBundle X I} [Finite I] (h : P.IsProjEmbedding s)

end LineBundle

end ProjectiveSpace

/-!
## Properties of projective embeddings

`New.LineBundle.IsProjEmbedding L s` says three things. The line bundle `L` on `X` is a linear
system, so that `L.transition i j` is the affine coordinate `x_j / x_i` on the chart `L.opens i`.
The morphism `s : X ⟶ S` is proper. Two ring-valued points of one chart with the same coordinates
and the same image in `S` are equal.

* `New.LineBundle.IsProjEmbedding.exists_affine_chart`: over an affine base the charts are affine,
  with coordinate rings generated by the coordinates.
-/

section Embeddings

open CategoryTheory AlgebraicGeometry Spec CommRingCat Limits prod PointFn MvPolynomial ProjSpace
  Function MorphismProperty

variable {X Y S : Scheme} {ι κ : Type} {L : LineBundle X ι} {s : X ⟶ S}

/-- A morphism with a projective embedding is proper. -/
instance [h : Variety.HasProjEmbedding s] : IsProper s := by
  obtain ⟨h_emb⟩ := h
  exact h_emb.isProper

namespace LineBundle.IsProjEmbedding

/-- If `L` embeds `X` over `S`, two morphisms `a b : Y ⟶ X` that agree over `S` and pull `L` back
to the same cover and transition functions are equal. -/
lemma ext (h : L.IsProjEmbedding s) {a b : Y ⟶ X} (h_pull : L.pull a = L.pull b)
    (h_base : a ≫ s = b ≫ s) : a = b := by
  -- Test on ring-valued points `t` of a chart: `t ≫ a` and `t ≫ b` have the same coordinates.
  refine hom_ext_of_isOpenCover (L.pull a).isOpenCover fun i A t ha ↦ ?_
  refine h.eq_of_transition_eq ha (by rwa [h_pull] at ha) (fun j ↦ ?_) (by simp [h_base])
  exact congrArg (fun M : LineBundle Y ι ↦ M.transition i j A t) h_pull

/-- If `L` embeds `X` projectively over `S` along `s` and `p : Y ⟶ X` is a closed immersion, then
the pull-back of `L` along `p` embeds `Y` projectively over `S` along `p ≫ s`. -/
lemma comp (h : L.IsProjEmbedding s) (p : Y ⟶ X) [IsClosedImmersion p] :
    (L.pull p).IsProjEmbedding (p ≫ s) :=
  ⟨h.isLinearSystem.pull p, comp_mem _ p s inferInstance h.isProper, fun ha hb h_coord h_base ↦
    (cancel_mono p).1 (h.eq_of_transition_eq ha hb h_coord (by simpa using h_base))⟩

/-- Segre embedding of a tower: if `L` embeds `X` over `S` along `s`, and `N` embeds `S` over `Y`
along `b`, then the tensor product of `L` with the pull-back of `N` along `s` embeds `X` over `Y`
along `s ≫ b`. -/
lemma mul {N : LineBundle S κ} {b : S ⟶ Y} (hL : L.IsProjEmbedding s) (hN : N.IsProjEmbedding b) :
    (L.mul (N.pull s)).IsProjEmbedding (s ≫ b) := by
  refine ⟨hL.isLinearSystem.mul (hN.isLinearSystem.pull s),
    comp_mem _ s b hL.isProper hN.isProper, ?_⟩
  rintro ⟨i, k⟩ A x y hx hy h_coord h_over
  obtain ⟨hxL, hxN⟩ : LandsIn x (L.opens i) ∧ LandsIn (x ≫ s) (N.opens k) := by simpa using hx
  obtain ⟨hyL, hyN⟩ : LandsIn y (L.opens i) ∧ LandsIn (y ≫ s) (N.opens k) := by simpa using hy
  -- A Segre coordinate with one index on the diagonal is a coordinate of the other factor.
  have hN_coord (j : κ) : N.transition k j A (x ≫ s) = N.transition k j A (y ≫ s) := by
    simpa [transition_self, hxL, hyL] using h_coord (i, j)
  have hL_coord (j : ι) : L.transition i j A x = L.transition i j A y := by
    simpa [transition_self, hxN, hyN] using h_coord (j, k)
  exact hL.eq_of_transition_eq hxL hyL hL_coord (hN.eq_of_transition_eq hxN hyN hN_coord (by simpa))

variable [Finite ι]

/-- If `L`, with a finite set `ι` of coordinates, is a projective embedding for `s : X ⟶ S`, then
`L` is the pull-back of O(1), cover and transition functions included, along a closed immersion `j`
of `X` into `ProjSpace ι ⨯ S` over `S`. -/
lemma exists_isClosedImmersion (h : L.IsProjEmbedding s) :
    ∃ j : X ⟶ ProjSpace ι ⨯ S,
      IsClosedImmersion j ∧ j ≫ snd = s ∧ ((hyperplaneBundle ι).pull fst).pull j = L := by
  obtain ⟨j, hj_snd, hj_pull⟩ := h.isLinearSystem.exists_hom_projSpace s
  -- `j ≫ snd = s` is proper and `snd` is proper, so separated.
  have h_comp : IsProper (j ≫ snd) := by simpa only [hj_snd] using h.isProper
  have h_snd : IsProper (snd : ProjSpace ι ⨯ S ⟶ S) := isProjEmbedding_projSpace.isProper
  -- If `a ≫ j = b ≫ j`, then `a` and `b` pull `L` back alike and agree over `S`.
  have h_mono : Mono j := ⟨fun a b hab ↦
    h.ext (by simp only [← hj_pull, ← pull_comp _ j, hab]) (by rw [← hj_snd, reassoc_of% hab])⟩
  exact ⟨j, (IsClosedImmersion.iff_isProper_and_mono j).2 ⟨.of_comp j snd, h_mono⟩, hj_snd, hj_pull⟩

/-- Let `L`, with finitely many coordinates, embed `X` projectively over `Spec R`. Then each chart
`L.opens i` is affine and there is a ring map `φ` from `R[X_j]` to the sections over it that (a)
is surjective, (b) induces the structure map of the chart on constants (`specMap` is `Spec` of a
ring map), and (c) sends `P` to a section whose value at each ring-valued point `t` of the chart is
`P` evaluated at the coordinates `X_j = L.transition i j (t)`, the coefficients of `P` being mapped
by the ring map `preimage (t ≫ s)` that induces `t ≫ s`. -/
lemma exists_affine_chart {R : CommRingCat} {s : X ⟶ Spec R} (h : L.IsProjEmbedding s) (i : ι) :
    ∃ (hU : IsAffineOpen (L.opens i)) (φ : MvPolynomial ι R →+* Γ(X, L.opens i)),
      Function.Surjective φ ∧
      specMap (φ.comp C) = hU.fromSpec ≫ s ∧
      ∀ {A : CommRingCat} {t : Spec A ⟶ X}, LandsIn t (L.opens i) → ∀ P : MvPolynomial ι R,
        ofSection (φ P) A t =
          eval₂Hom (preimage (t ≫ s)).hom (fun j : ι ↦ L.transition i j A t) P := by
  classical
  -- By `exists_isClosedImmersion`, `X` is closed in `ℙ × Spec R` and `L.opens i` is the preimage of
  -- the standard chart `N.opens i`, which is affine.
  let N : LineBundle (ProjSpace ι ⨯ Spec R) ι := (hyperplaneBundle ι).pull fst
  have hN : N.IsProjEmbedding snd := isProjEmbedding_projSpace
  have h_fst : IsAffineHom (fst : ProjSpace ι ⨯ Spec R ⟶ ProjSpace ι) :=
    of_isPullback (.flip (.of_hasBinaryProduct' (ProjSpace ι) (Spec R))) inferInstance
  have hW : IsAffineOpen (N.opens i) := (isAffineOpen_chart i).preimage fst
  obtain ⟨f, hf_closed, hf_snd, rfl⟩ := h.exists_isClosedImmersion
  set L : LineBundle X ι := N.pull f
  have hU : IsAffineOpen (L.opens i) := hW.preimage f
  have hU_in : LandsIn hU.fromSpec (L.opens i) := by simpa using landsIn_fromSpec hU (𝟙 _)
  -- `φ` sends `X j` to the coordinate `L.transition i j` of the tautological point `hU.fromSpec`.
  let φ : of (MvPolynomial ι R) ⟶ Γ(X, L.opens i) :=
    ofHom (eval₂Hom (preimage (hU.fromSpec ≫ s)).hom fun j ↦ L.transition i j _ hU.fromSpec)
  refine ⟨hU, φ.hom, ?_, by simp [φ, specMap], fun {A t} ht P ↦ ?_⟩
  · -- Let `t` be the point of `N.opens i` over `R[X]` with coordinates `X j` (and `1` at `i`).
    obtain ⟨t, ht_snd, ht⟩ : ∃ t : Spec (of (MvPolynomial ι R)) ⟶ ProjSpace ι ⨯ Spec R,
        t ≫ snd = specMap C ∧ N.IsHomogeneousCoords t (update .X i 1) :=
      exists_isHomogeneousCoords (i := i) _ (by simp)
    have ht_in : LandsIn t (N.opens i) := (ht.landsIn_iff_isUnit i).2 (by simp)
    -- Its image under `φ` is the tautological point of `L.opens i`, followed by `f`: both points
    -- have the affine coordinates `φ (update X i 1 k)` in the chart `N.opens i`.
    have h_eq (k : ι) : N.transition i k _ (Spec.map φ ≫ t) = L.transition i k _ hU.fromSpec := by
      rw [hN.isLinearSystem.isRegularOn_transition i k φ t ht_in,
        ht.transition_eq_mul_inverse (by simp) k]
      obtain rfl | hk := eq_or_ne k i
      · simp [L.transition_self k _ _ hU_in]
      · simp [φ, hk]
    have h_image : Spec.map φ ≫ t = hU.fromSpec ≫ f := hN.eq_of_transition_eq (ht_in.comp _) hU_in
      h_eq (by simp [φ, ht_snd, hf_snd, ← map_comp, ← ofHom_comp])
    -- Sections over `L.opens i` lift to sections `r` over `N.opens i`, and `φ (r t)` is the
    -- pull-back of `r`.
    refine (f.app_surjective _ hW).forall.2 fun r ↦ ⟨ofSection r _ t, ?_⟩
    change φ (ofSection r _ t) = f.app (N.opens i) r
    rw [← isRegularOn_ofSection r φ t ht_in, h_image, ← Category.id_comp hU.fromSpec, ← Spec.map_id]
    exact ofSection_map_fromSpec hU (f.app (N.opens i) r) (𝟙 _)
  · -- A point of `L.opens i` factors through `hU.fromSpec`, and the coordinates are regular.
    rw [← map_evalSection_fromSpec hU ht]
    simp [φ, hom_eval₂,
      fun j ↦ h.isLinearSystem.isRegularOn_transition i j (evalSection t ht) _ hU_in]

end LineBundle.IsProjEmbedding

end Embeddings

end New

/-!
## Tensor products and powers of line bundles

`New.LineBundle` is a line bundle given by a cover with a cocycle. `New.LineBundle.picClass` is its
class in the Picard group, written additively.

* `New.LineBundle.pi`, `New.LineBundle.pow`: the product of a family, and the `m`-th power, indexed
  by tuples.
-/

namespace New.LineBundle

open CategoryTheory AlgebraicGeometry PointFn Finset Over Function TopologicalSpace

variable {X Y S : Scheme} {ι Λ : Type} [Fintype Λ] {ν : Λ → Type}
  (N : ∀ l : Λ, LineBundle X (ν l)) (L : LineBundle X ι) (m : ℕ) (p : Y ⟶ X)

/-- The tensor product of the line bundles `N a` over `a` in `s` (by default all `a`), on the common
refinement of all covers; for linear systems and `s` the set of all `a`, the Segre product. -/
@[simps -fullyApplied]
noncomputable def pi (s : Finset Λ := univ) : LineBundle X (∀ l : Λ, ν l) where
  opens i := ⨅ a : Λ, (N a).opens (i a)
  transition i j := ∏ a ∈ s, (N a).transition (i a) (j a)
  regular i j := by simp_all [PointFn.IsRegularOn, LineBundle.regular _ _ _ _, landsIn_iInf]
  transition_self := by simp +contextual [transition_self, landsIn_iInf]
  transition_trans i j k A t hi hj hk := by
    simp_all [landsIn_iInf, ← prod_mul_distrib, (N _).transition_trans]

/-- The `m`-th tensor power of `L`, indexed by `m`-tuples of indices; for a linear system, the
Veronese system of all monomials of degree `m`. -/
noncomputable def pow : LineBundle X (Fin m → ι) := pi fun _ : Fin m ↦ L

variable {N L}

/-- The class in the Picard group of the product of the `N l`, `l ∈ s`, is the sum of their
classes. -/
@[simp]
lemma picClass_pi (s : Finset Λ) : (pi N s).picClass = ∑ l ∈ s, (N l).picClass := by
  -- Induction on `s`. The trivial bundle, and the product of one factor with the rest, are compared
  -- with `pi N _` on its cover, which refines theirs and carries the same transition functions;
  -- such a refinement has the same class (`picClass_eq_of_le`).
  symm
  induction s using cons_induction with
  | empty => exact picClass_eq_of_le (fun _ ↦ ()) (by simp) (by simp)
  | cons a s ha ih =>
    rw [sum_cons, ih, ← picClass_mul]
    exact picClass_eq_of_le (fun i ↦ (i a, i)) (by simp [iInf_le]) (by simp)

/-- The Segre product of a finite family of linear systems is a linear system. -/
lemma IsLinearSystem.pi (h : ∀ a : Λ, (N a).IsLinearSystem) : (pi N).IsLinearSystem where
  isRegularOn_transition i j A B φ t ht := by
    -- A product of regular functions is regular.
    have h_reg (a : Λ) : (N a).transition (i a) (j a) B (Spec.map φ ≫ t) =
        φ ((N a).transition (i a) (j a) A t) :=
      (h a).isRegularOn_transition (i a) (j a) φ t ((landsIn_iInf t).1 ht a)
    simp [h_reg]
  transition_eq_zero {A i} j t ht := by
    -- Off `⨅ a, (N a).opens (i a)` one of the factors vanishes.
    obtain ⟨a, ha⟩ : ∃ a : Λ, ¬LandsIn t ((N a).opens (i a)) := by simpa [landsIn_iInf] using ht
    simpa using prod_eq_zero (mem_univ a) ((h a).transition_eq_zero (j a) ha)
  isHomogeneousCoords_transition {A i t} ht := by
    -- A product is a unit exactly when each factor is, and coordinates multiply factor by factor.
    have h_coords (a : Λ) : (N a).IsHomogeneousCoords t ((N a).transition (i a) · A t) :=
      (h a).isHomogeneousCoords_transition ((landsIn_iInf t).1 ht a)
    refine .intro (fun j ↦ ?_) fun j k h_unit ↦ ?_
    · simp [landsIn_iInf, fun a : Λ ↦ (h_coords a).landsIn_iff_isUnit]
    · have h_factor (a : Λ) : IsUnit ((N a).transition (i a) (j a) A t) :=
        IsUnit.prod_univ_iff.1 (by simpa using h_unit) a
      have h_mul (a : Λ) : (N a).transition (j a) (k a) A t * (N a).transition (i a) (j a) A t =
          (N a).transition (i a) (k a) A t := by
        rw [(h_coords a).transition_eq_mul_inverse (h_factor a),
          Ring.inverse_mul_cancel_right _ _ (h_factor a)]
      rw [Ring.eq_mul_inverse_iff_mul_eq _ _ _ h_unit]
      simp [← prod_mul_distrib, h_mul]

lemma pull_pi : (pi N).pull p = pi fun l : Λ ↦ (N l).pull p := by ext <;> simp [Opens.coe_iInf]

/-- Segre embedding: let `W` be proper over `S`, with finitely many `S`-maps `π l : W ⟶ Z l` that
jointly separate morphisms into `W` over `S`. If each `N l` is a projective embedding of `Z l` over
`S`, then the product of the pull-backs of the `N l` along the `π l` is a projective embedding of
`W` over `S`. -/
lemma isProjEmbedding_pi {W : Over S} [IsProper W.hom] {Z : Λ → Over S} (π : ∀ l : Λ, W ⟶ Z l)
    {N : (l : Λ) → LineBundle (Z l).left (ν l)} (hN : ∀ l : Λ, (N l).IsProjEmbedding (Z l).hom)
    (h_sep : ∀ {T : Over S} {x y : T ⟶ W}, (∀ l : Λ, x ≫ π l = y ≫ π l) → x = y) :
    (pi fun l : Λ ↦ (N l).pull (π l).left).IsProjEmbedding W.hom := by
  classical
  refine ⟨.pi fun l ↦ (hN l).isLinearSystem.pull (π l).left, inferInstance, ?_⟩
  intro c A a b ha hb h_coord h_base
  have ha_in (l : Λ) : LandsIn (a ≫ (π l).left) ((N l).opens (c l)) := (landsIn_iInf a).1 ha l
  have hb_in (l : Λ) : LandsIn (b ≫ (π l).left) ((N l).opens (c l)) := (landsIn_iInf b).1 hb l
  -- The coordinate `j` of the factor `l` is the Segre coordinate `update c l j`, as the other
  -- factors of the product are `1`.
  have h_factor (l : Λ) (j : ν l) : (N l).transition (c l) j A (a ≫ (π l).left) =
      (N l).transition (c l) j A (b ≫ (π l).left) := by
    simpa +contextual [prod_eq_single l, transition_self, ha_in, hb_in] using h_coord (update c l j)
  -- So `a` and `b` have the same image in each `Z l`. View them over `S` and apply `h_sep`.
  have h_over : homMk (U := .mk (b ≫ W.hom)) a h_base = homMk b :=
    h_sep fun l ↦ OverMorphism.ext <|
      (hN l).eq_of_transition_eq (ha_in l) (hb_in l) (h_factor l) (by simpa using h_base)
  exact congrArg CommaMorphism.left h_over

@[simp]
lemma picClass_pow : (L.pow m).picClass = m • L.picClass := by simp [pow]

/-- Veronese embedding: if `L` is a projective embedding of `X` over `S`, so is its `m`-th tensor
power for `m ≠ 0`. -/
lemma IsProjEmbedding.pow {s : X ⟶ S} (h : L.IsProjEmbedding s) {m : ℕ} (hm : m ≠ 0) :
    (L.pow m).IsProjEmbedding s := by
  -- The case of `isProjEmbedding_pi` where all the maps are the identity of `X`.
  have h_proper : IsProper (Over.mk s).hom := h.isProper
  exact isProjEmbedding_pi (W := .mk s) (fun _ : Fin m ↦ 𝟙 _) (fun _ ↦ h)
    fun hxy ↦ by simpa using hxy ⟨0, hm.pos⟩

end New.LineBundle

end
