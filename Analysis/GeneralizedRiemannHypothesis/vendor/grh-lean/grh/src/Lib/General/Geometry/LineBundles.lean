import Lib.Base

/-!
# Line bundles on schemes via ring-valued points: descent and the Picard group

Line bundles on a scheme `X` are described through ring-valued points `t : Spec A ⟶ X`, so that
restriction maps disappear. A function `f : New.PointFn X` gives an element of `A` for every such
point. `New.LandsIn t U` says that `t` lands in the open `U`, and `f` is regular on `U` when it is
natural in `A` on the points of `U`. The file shows that regular functions come from sections and
that functions, sections and frames descend along flat, surjective, quasi-compact morphisms, and it
defines the Picard group with its pull-back.

## Main definitions and results

* `New.LineBundle`: a line bundle as an open cover with a cocycle of regular functions, with the
  operations `New.LineBundle.pull`, `New.LineBundle.one`, `New.LineBundle.inv`,
  `New.LineBundle.mul`.
* `New.LineBundle.IsSection`, `New.LineBundle.IsFrame`, `New.LineBundle.IsIsomorphic`,
  `New.LineBundle.H0`: sections, nowhere vanishing sections, isomorphism, and the module of
  sections.
* `New.PointFn.exists_ofSection_glue`: descent of functions along a flat, surjective, quasi-compact
  morphism.
* `New.LineBundle.exists_isSection_eq_mul`, `New.LineBundle.exists_isFrame_of_fpqc`: descent of
  sections and of frames along a flat, surjective, quasi-compact morphism.
* `New.Pic`, `New.LineBundle.picClass`, `New.Pic.pull`: the Picard group, written additively, the
  class of a line bundle, and the pull-back along a morphism.
* `New.Pic.eq_zero_of_isLocalRing`: the Picard group of the spectrum of a local ring is trivial.

## Relation to the literature

These are standard facts on line bundles and faithfully flat descent, in the language of ring-valued
points.
-/

noncomputable section

/-! ## Functions on points, line bundles as cocycles, sections and frames -/

section LineBundles

open CategoryTheory AlgebraicGeometry Spec RingHom

namespace New

variable {X Y Z : Scheme.{0}} {ι κ : Type}

/-! ### Functions on ring-valued points -/

/-- For a ring homomorphism `φ : R →+* B`, the induced morphism of schemes `Spec B ⟶ Spec R`. -/
abbrev specMap {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B) :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom φ)

/-- The morphism `t : Y ⟶ X` lands in the open `U`, that is, `t ⁻¹ᵁ U` is all of `Y`. -/
def LandsIn (t : Y ⟶ X) (U : X.Opens) : Prop := ⊤ ≤ t ⁻¹ᵁ U

/-- Functions on ring-valued points of `X`: rules attaching an element of `A` to every point
`Spec A ⟶ X`, for every ring `A`, with no compatibility required. -/
abbrev PointFn (X : Scheme) : Type 1 := ∀ A : CommRingCat, (Spec.{0} A ⟶ X) → A

variable {t : Y ⟶ X} {U : X.Opens} (f : PointFn X)

@[simp]
lemma landsIn_inf {V : X.Opens} : LandsIn t (U ⊓ V) ↔ LandsIn t U ∧ LandsIn t V := by
  rw [LandsIn, Scheme.Hom.preimage_inf, le_inf_iff, LandsIn, LandsIn]

@[simp]
lemma landsIn_top : LandsIn t ⊤ := le_rfl

@[simp]
lemma landsIn_preimage {s : Z ⟶ Y} : LandsIn s (t ⁻¹ᵁ U) ↔ LandsIn (s ≫ t) U := .rfl

lemma LandsIn.comp (ht : LandsIn t U) (a : Z ⟶ Y) : LandsIn (Y := Z) (a ≫ t) U := by
  simpa [LandsIn] using a.preimage_mono ht

/-- The function `f` is regular on `U`: for points `t : Spec A ⟶ X` landing in `U`, its value
commutes with all ring maps `φ : A ⟶ B`. -/
def PointFn.IsRegularOn (U : X.Opens) : Prop :=
  ∀ ⦃A B : CommRingCat⦄ (φ : A ⟶ B) (t : Spec A ⟶ X), LandsIn t U → f B (Spec.map φ ≫ t) = φ (f A t)

/-- For a point `t : Spec A ⟶ X` landing in `U`, the ring map `Γ(X, U) ⟶ A` evaluating sections
at `t`. -/
def PointFn.evalSection {A : CommRingCat} (t : Spec A ⟶ X) (h : LandsIn t U) : Γ(X, U) ⟶ A :=
  t.appLE U ⊤ h ≫ (Scheme.ΓSpecIso A).hom

open scoped Classical in
/-- The function on points given by a section `s` over `U`: its value at `t` is the pull-back of
`s` along `t` if `t` lands in `U`, and `0` otherwise. -/
def PointFn.ofSection : Γ(X, U) →ₙ+* PointFn X where
  toFun s _ t := if h : LandsIn t U then evalSection t h s else 0
  map_mul' := by aesop
  map_zero' := by aesop
  map_add' := by aesop

variable (X ι) in
/-- A line bundle on X as an open cover U_i with transition functions g_ij regular on U_i ∩ U_j,
satisfying g_ii = 1 and g_ij g_jk = g_ik (`opens i` is U_i, `transition i j` is g_ij). -/
@[ext]
structure LineBundle where
  /-- The open sets on which the bundle is trivialised. -/
  opens : ι → X.Opens
  /-- The transition functions, as functions on ring-valued points of `X`. -/
  transition : ι → ι → PointFn X
  /-- The open sets cover `X`. -/
  cover : ⨆ i : ι, opens i = ⊤ := by simp [← iSup_inf_iSup, ← iInf_iSup_eq_of_finite,
    LineBundle.cover]
  /-- The transition function g_ij is regular on U_i ∩ U_j. -/
  regular (i j : ι) : (transition i j).IsRegularOn (opens i ⊓ opens j) := by
    simp_all [PointFn.IsRegularOn, LineBundle.regular _ _ _ _]
  /-- The function g_ii is 1 at the points of U_i. -/
  transition_self (i : ι) (A : CommRingCat) (t : Spec A ⟶ X) :
      LandsIn t (opens i) → transition i i A t = 1 := by
    simp +contextual [LineBundle.transition_self]
  /-- The cocycle condition g_ij g_jk = g_ik at the points of U_i ∩ U_j ∩ U_k. -/
  transition_trans (i j k : ι) (A : CommRingCat) (t : Spec A ⟶ X) :
      LandsIn t (opens i) → LandsIn t (opens j) → LandsIn t (opens k) →
      transition i j A t * transition j k A t = transition i k A t := by
    (try simp +contextual [LineBundle.transition_trans, ← Finset.prod_mul_distrib]) <;>
      grind [LineBundle.transition_trans]

variable (L : LineBundle X ι) (M : LineBundle X κ) (R : Type) [CommRing R] [X.Over (Spec ⟨R⟩)]
  (p : Y ⟶ X)

/-- For `p : Y ⟶ X` and a function `f` on ring-valued points of `X`, the function
`t ↦ f (t ≫ p)` on ring-valued points of `Y`. -/
@[simp]
def PointFn.pull (f : PointFn X) : PointFn Y :=
  fun (A : CommRingCat) (t : Spec A ⟶ Y) ↦ f A (t ≫ p)

/-- For a scheme `X` over `R`, a point `t : Spec A ⟶ X` makes `A` an `R`-algebra, and a scalar
`r : R` gives the function sending each such `t` to the image of `r` in `A`. -/
instance : Algebra R (PointFn X) :=
  toAlgebra (.pi fun _ ↦ .pi (· ≫ X ↘ Spec ⟨R⟩ |> preimage |>.hom))

namespace LineBundle

/-! ### Operations on line bundles -/

/-- The pull-back of the line bundle (U_i, g_ij) along p: Y → X, with cover p⁻¹U_i and
transition functions p*g_ij. -/
@[simps]
def pull : LineBundle Y ι where
  opens i := p ⁻¹ᵁ L.opens i
  transition i j := (L.transition i j).pull p
  cover := p.iSup_preimage_eq_top L.cover

/-- The trivial line bundle on X: the single open set X and the transition function 1. -/
@[simps]
def one {X : Scheme} : LineBundle X Unit where
  opens _ := ⊤
  transition _ _ := 1

/-- The dual line bundle: the same cover, with (i, j) transition function g_ji. -/
@[simps]
def inv : LineBundle X ι where
  opens := L.opens
  transition i j := L.transition j i

/-- The tensor product L ⊗ M: the cover by the intersections of an open of L with an open of M, with
products of transition functions. -/
@[simps]
def mul : LineBundle X (ι × κ) where
  opens i := L.opens i.1 ⊓ M.opens i.2
  transition i j := L.transition i.1 j.1 * M.transition i.2 j.2

/-! ### Sections -/

/-- The family (s_i) is a global section of L: each s_i is regular on U_i, and s_i = g_ij s_j at
points landing in U_i and U_j. -/
def IsSection (s : ι → PointFn X) : Prop :=
  (∀ i : ι, (s i).IsRegularOn (L.opens i)) ∧
  ∀ (i j : ι) (A : CommRingCat) (t : Spec A ⟶ X), LandsIn t (L.opens i) → LandsIn t (L.opens j) →
    s i A t = L.transition i j A t * s j A t

/-- The family s is a nowhere vanishing global section of L: a section with s_i a unit at every
point landing in U_i. -/
def IsFrame (s : ι → PointFn X) : Prop :=
  L.IsSection s ∧
  ∀ (i : ι) (A : CommRingCat) (t : Spec A ⟶ X), LandsIn t (L.opens i) → IsUnit (s i A t)

/-- The line bundles L and M are isomorphic: L ⊗ M⁻¹ has a nowhere vanishing global section. -/
def IsIsomorphic : Prop := ∃ u : ι × κ → PointFn X, (L.mul M.inv).IsFrame u

/-- The R-module of global sections of L, for a scheme X over R. Each s_i is normalised to be zero
at the points that do not land in U_i. -/
def H0 : Submodule R (ι → PointFn X) where
  carrier :=
    {s : ι → PointFn X |
      L.IsSection s ∧
      ∀ (i : ι) (A : CommRingCat) (t : Spec A ⟶ X), ¬LandsIn t (L.opens i) → s i A t = 0}
  add_mem' := by
    simp [IsSection, PointFn.IsRegularOn]
    grind
  zero_mem' := by simp [IsSection, PointFn.IsRegularOn]
  smul_mem' := by
    -- at a point `t` a scalar acts by multiplication with its image in the ring of `t`
    simp [IsSection, PointFn.IsRegularOn, HSMul.hSMul, SMul.smul]
    grind

variable {L R} in
lemma mem_H0 {s : ι → PointFn X} :
    s ∈ L.H0 R ↔
      L.IsSection s ∧
      ∀ (i : ι) (A : CommRingCat) (t : Spec A ⟶ X), ¬LandsIn t (L.opens i) → s i A t = 0 :=
  Iff.rfl

end LineBundle

end New

end LineBundles

namespace New

/-!
## Gluing of morphisms, evaluation of sections and fpqc descent

* `New.PointFn.IsRegularOn.ext_of_dominant_of_isOpenCover`: regular functions are determined by
  their pull-backs along a quasi-compact, scheme-theoretically dominant morphism.
-/

section PointFunctions

open CategoryTheory AlgebraicGeometry TopologicalSpace.Opens Scheme TopCat.Presheaf Hom Spec
  Limits.pullback EffectiveEpi Category IsLocalRing IsOpenImmersion
open TopologicalSpace (IsOpenCover)

variable {X Y : Scheme} {κ : Type}
  {U : X.Opens} {A B : CommRingCat} {f g : PointFn X} {t : Spec A ⟶ X} (p : Y ⟶ X) (s : Γ(X, U))

/-! ### Points that land in an open -/

lemma LandsIn.mono {t : Y ⟶ X} {V : X.Opens} (ht : LandsIn t U) (h_le : U ≤ V) : LandsIn t V :=
  ht.trans (t.preimage_mono h_le)

/-- For a local ring `B`, a point `z : Spec B ⟶ X` lands in `U` exactly when the image of the closed
point lies in `U`. -/
lemma landsIn_iff_mem {z : Spec B ⟶ X} [IsLocalRing B] : LandsIn z U ↔ z (closedPoint B) ∈ U :=
  top_le_iff.trans closed_point_mem_iff.symm

/-- For a local ring `B`, a point `t : Spec B ⟶ Y` lands in some member of an open cover `V` of
`Y`. -/
lemma exists_landsIn_of_isOpenCover {V : κ → Y.Opens} (hV : IsOpenCover V) [IsLocalRing B]
    (t : Spec B ⟶ Y) : ∃ i : κ, LandsIn t (V i) := by
  simpa only [landsIn_iff_mem] using hV.exists_mem (t (closedPoint B))

lemma LineBundle.isOpenCover (M : LineBundle Y κ) : IsOpenCover M.opens := M.cover

/-- For a local ring `B`, a point `t : Spec B ⟶ Y` lands in some member of the open cover
`M.opens` of `Y`. -/
lemma LineBundle.exists_landsIn (M : LineBundle Y κ) [IsLocalRing B] (t : Spec B ⟶ Y) :
    ∃ i : κ, LandsIn t (M.opens i) := exists_landsIn_of_isOpenCover M.isOpenCover t

/-- A morphism that factors through `Spec Γ(X, U) ⟶ X`, for an affine open `U`, lands in `U`. -/
lemma landsIn_fromSpec (hU : IsAffineOpen U) (t : Y ⟶ Spec Γ(X, U)) :
    LandsIn (Y := Y) (t ≫ hU.fromSpec) U := by simp [LandsIn, hU.fromSpec_preimage_self]

/-- A point lands in the image of an open immersion `c : Spec R ⟶ X` exactly when it factors
through `c`. -/
lemma landsIn_opensRange {R : CommRingCat} {c : Spec R ⟶ X} [IsOpenImmersion c] :
    LandsIn t c.opensRange ↔ ∃ φ : R ⟶ A, Spec.map φ ≫ c = t := by
  refine ⟨fun ht ↦ ?_, fun ⟨φ, hφ⟩ ↦ by simp [← hφ, LandsIn]⟩
  have h_range : Set.range t ⊆ Set.range c := Set.range_subset_iff.2 fun y ↦ ht (mem_top y)
  exact ⟨preimage (IsOpenImmersion.lift c t h_range), by simp⟩

/-- A morphism that factors through the inclusion of `U` lands in `U`. -/
lemma landsIn_comp_incl {t : Y ⟶ U} : LandsIn (Y := Y) (t ≫ U.ι) U := by simp [LandsIn]

lemma landsIn_iInf {V : κ → X.Opens} (p : Y ⟶ X) [Finite κ] :
    LandsIn p (iInf V) ↔ ∀ a : κ, LandsIn p (V a) := by simp [LandsIn, ← coe_inj, coe_iInf]

/-! ### Testing and gluing on a cover -/

lemma isOpenCover_top : IsOpenCover fun _ : Unit ↦ (⊤ : Y.Opens) := iSup_const

lemma isOpenCover_preimage {V : κ → X.Opens} (hV : IsOpenCover V) (p : Y ⟶ X) :
    IsOpenCover fun i : κ ↦ p ⁻¹ᵁ V i := p.iSup_preimage_eq_top hV

/-- The intersections of the members of two open covers form an open cover. -/
lemma isOpenCover_inf {ι : Type} {V : κ → Y.Opens} {W : ι → Y.Opens} (hV : IsOpenCover V)
    (hW : IsOpenCover W) : IsOpenCover fun i : κ × ι ↦ V i.1 ⊓ W i.2 := by
  rw [IsOpenCover, ← iSup_inf_iSup, hV.iSup_eq_top, hW.iSup_eq_top, top_inf_eq]

/-- Two morphisms from `Y` are equal if they agree on every ring-valued point that lands in a member
of an open cover `V` of `Y`. -/
lemma hom_ext_of_isOpenCover {V : κ → Y.Opens} (hV : IsOpenCover V) {f g : Y ⟶ X}
    (h : ∀ (i : κ) (A : CommRingCat) (t : Spec A ⟶ Y), LandsIn t (V i) → t ≫ f = t ≫ g) :
    f = g := by
  -- The members of an affine refinement of the cover are such points.
  let 𝒰 : Y.OpenCover := (Y.openCoverOfIsOpenCover V hV).affineRefinement.openCover
  exact 𝒰.hom_ext f g fun k ↦ h k.1 _ (𝒰.f k) landsIn_comp_incl

lemma hom_ext_of_points {f g : Y ⟶ X}
    (h : ∀ (A : CommRingCat) (t : Spec A ⟶ Y), t ≫ f = t ≫ g) : f = g :=
  hom_ext_of_isOpenCover isOpenCover_top fun _ A t _ ↦ h A t

/-- Two morphisms from `Y` are equal if they agree on every ring-valued point that lands in a
trivialising open of a line bundle `M` on `Y`. -/
lemma hom_ext_of_cover (M : LineBundle Y κ) {f g : Y ⟶ X}
    (h : ∀ (i : κ) (A : CommRingCat) (t : Spec A ⟶ Y), LandsIn t (M.opens i) → t ≫ f = t ≫ g) :
    f = g :=
  hom_ext_of_isOpenCover M.isOpenCover h

/-- Gluing on an open cover `V` of `Y`. Attach to each point `t : Spec A ⟶ Y` landing in
`V i` (that is, with image inside it) a morphism `F i A t _ : Spec A ⟶ X`, compatibly with
ring maps `φ : A ⟶ B` and change of the index `i`. Then some `f : Y ⟶ X` has `t ≫ f = F i A t _`
for all such `t`. -/
lemma exists_hom_of_cover {V : κ → Y.Opens} (hV : IsOpenCover V)
    (F : (i : κ) → (A : CommRingCat) → (t : Spec A ⟶ Y) → LandsIn t (V i) → (Spec A ⟶ X))
    (h : ∀ (i j : κ) (A B : CommRingCat) (φ : A ⟶ B) (t : Spec A ⟶ Y)
      (hi : LandsIn t (V i)) (hj : LandsIn (Spec.map φ ≫ t) (V j)),
      F j B (Spec.map φ ≫ t) hj = Spec.map φ ≫ F i A t hi) :
    ∃ f : Y ⟶ X, ∀ (i : κ) (A : CommRingCat) (t : Spec A ⟶ Y) (hi : LandsIn t (V i)),
      t ≫ f = F i A t hi := by
  -- Every morphism of affine schemes comes from a ring map, so `h` applies to it.
  have h_hom (i j : κ) {A B : CommRingCat} (x : Spec B ⟶ Spec A) {t : Spec A ⟶ Y}
      (hi : LandsIn t (V i)) (hj : LandsIn (x ≫ t) (V j)) :
      x ≫ F i A t hi = F j B (x ≫ t) hj := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective x
    exact (h i j A B φ t hi hj).symm
  -- Two points `t`, `s` give morphisms that agree on the fibre product of `t` and `s`: test on
  -- ring-valued points `r` of it, where both are `F j` of the common point.
  have agree {i j : κ} {A B : CommRingCat} {t : Spec A ⟶ Y} {s : Spec B ⟶ Y}
      (hi : LandsIn t (V i)) (hj : LandsIn s (V j)) :
      fst t s ≫ F i A t hi = snd t s ≫ F j B s hj := by
    refine hom_ext_of_points fun C r ↦ ?_
    have hj_fst : LandsIn ((r ≫ fst t s) ≫ t) (V j) := by
      simpa [condition] using hj.comp (r ≫ snd t s)
    rw [← assoc, ← assoc, h_hom i j _ hi hj_fst, h_hom j j _ hj (hj.comp _)]
    simp only [assoc, condition]
  -- Glue along an affine refinement of the cover.
  let 𝒰 : Y.OpenCover := (Y.openCoverOfIsOpenCover V hV).affineRefinement.openCover
  let G (k : 𝒰.I₀) : 𝒰.X k ⟶ X := F k.1 _ (𝒰.f k) landsIn_comp_incl
  have hG (k l : 𝒰.I₀) : fst (𝒰.f k) (𝒰.f l) ≫ G k = snd (𝒰.f k) (𝒰.f l) ≫ G l :=
    agree landsIn_comp_incl landsIn_comp_incl
  refine ⟨𝒰.glueMorphisms G hG, fun i A t hi ↦ ?_⟩
  -- Compare the glued morphism with `F i A t hi` on the pull-back of the cover along `t`.
  refine Cover.hom_ext (𝒰.pullback₁ t) _ _ fun k : 𝒰.I₀ ↦ ?_
  change fst t (𝒰.f k) ≫ t ≫ 𝒰.glueMorphisms G hG = fst t (𝒰.f k) ≫ F i A t hi
  rw [condition_assoc, 𝒰.ι_glueMorphisms]
  exact (agree hi landsIn_comp_incl).symm

/-- `U ≤ W` holds if every ring-valued point that lands in `U` and in a member of an open cover
`V` of `Y` lands in `W`. -/
lemma le_of_cover {V : κ → Y.Opens} (hV : IsOpenCover V) {U W : Y.Opens}
    (h : ∀ (i : κ) (A : CommRingCat) (t : Spec A ⟶ Y), LandsIn t (V i) → LandsIn t U →
      LandsIn t W) : U ≤ W := by
  -- Test on the point `Spec 𝒪_x → Y`, which lies in an open exactly when `x` does.
  intro x hx
  obtain ⟨i, hi⟩ := exists_landsIn_of_isOpenCover hV (Y.fromSpecStalk x)
  simpa [landsIn_iff_mem] using h i _ _ hi (by simpa [landsIn_iff_mem] using hx)

/-! ### Effective epimorphisms -/

/-- A quasi-compact effective epimorphism of schemes is scheme-theoretically dominant. -/
instance [EffectiveEpi p] [QuasiCompact p] : IsSchemeTheoreticallyDominant p := by
  -- `p` factors through the closed immersion of its image, which is thus an isomorphism.
  have : IsIso p.imageι := ExtremalEpi.isIso p p.toImage p.imageι p.toImage_imageι
  have h_ker : p.imageι.ker = ⊥ := p.imageι.ker_eq_bot_of_isIso
  exact ⟨by rwa [IdealSheafData.ker_subschemeι] at h_ker⟩

namespace PointFn

/-! ### Evaluation of sections -/

/-- At a point `t` that lands in `U`, the function of a section `s` is evaluation of `s` at `t`. -/
lemma ofSection_eq (h : LandsIn t U) (s : Γ(X, U)) : ofSection s A t = evalSection t h s :=
  dite_eq_left h

lemma ofSection_eq_zero (h : ¬LandsIn t U) (s : Γ(X, U)) : ofSection s A t = 0 := dite_eq_right h

/-- Let `W ≤ p ⁻¹ᵁ U`, let `s` be a section over `U`, and let the point `x` land in `W`. The value
at `x` of the pull-back of `s` along `p`, restricted to `W`, is the value of `s` at `x ≫ p`. -/
lemma ofSection_appLE {x : Spec A ⟶ Y} (p : Y ⟶ X) {W : Y.Opens} (h_le : W ≤ p ⁻¹ᵁ U)
    (s : Γ(X, U)) (h : LandsIn x W) :
    ofSection (p.appLE U W h_le s) A x = ofSection s A (x ≫ p) := by
  have h_comp : LandsIn (x ≫ p) U := landsIn_preimage.1 (h.mono h_le)
  have h_eval : evalSection (x ≫ p) h_comp = p.appLE U W h_le ≫ evalSection x h :=
    (appLE_comp_appLE_assoc x p U W ⊤ h_le h (ΓSpecIso A).hom).symm
  simp [ofSection_eq h, ofSection_eq h_comp, h_eval]

lemma isRegularOn_ofSection : (ofSection s).IsRegularOn U := by
  intro A B φ t ht
  have h_eval : evalSection (Spec.map φ ≫ t) (ht.comp _) = evalSection t ht ≫ φ := by
    rw [evalSection, evalSection, assoc, ← ΓSpecIso_naturality, appTop, app_eq_appLE]
    exact (appLE_comp_appLE_assoc (Spec.map φ) t U ⊤ ⊤ ht le_rfl (ΓSpecIso B).hom).symm
  simp [ofSection_eq (ht.comp _), ofSection_eq ht, h_eval]

/-- At a point that lands in `V`, a section over `U` and its restriction to `V` have the same
value. -/
lemma ofSection_map {V : X.Opens} (i : Opposite.op U ⟶ Opposite.op V) (ht : LandsIn t V) :
    ofSection (U := V) (X.presheaf.map i s) A t = ofSection s A t := by
  -- restriction is pull-back along the identity of `X`
  have h_res : X.presheaf.map i = appLE (𝟙 X) U V (leOfHom i.unop) := by
    rw [appLE, Subsingleton.elim i (homOfLE (leOfHom i.unop)).op]
    exact (id_comp _).symm
  rw [h_res, ofSection_appLE (𝟙 X) _ s ht, comp_id]

/-- For `x ∈ U`, the point `Spec 𝒪_x ⟶ X` lands in `U`. -/
lemma landsIn_fromSpecStalk {x : X} (hx : x ∈ U) : LandsIn (X.fromSpecStalk x) U := by
  simpa [landsIn_iff_mem] using hx

/-- A point of an affine open `U` is `Spec` of its evaluation map, followed by
`Spec Γ(X, U) → X`. -/
lemma map_evalSection_fromSpec (hU : IsAffineOpen U) (h : LandsIn t U) :
    Spec.map (evalSection t h) ≫ hU.fromSpec = t := by
  simp [evalSection, hU.SpecMap_appLE_fromSpec t (isAffineOpen_top _) h, IsAffineOpen.fromSpec_top]

/-- Two `A`-valued points of an affine open `U` are equal if all sections over `U` have the same
value at them. -/
lemma point_eq_of_ofSection_eq {x t : Spec A ⟶ X} (hU : IsAffineOpen U) (ht : LandsIn t U)
    (hx : LandsIn x U) (h_val : ∀ s : Γ(X, U), ofSection s A t = ofSection s A x) : t = x := by
  have h_eval : evalSection t ht = evalSection x hx :=
    ConcreteCategory.hom_ext _ _ fun s ↦ by rw [← ofSection_eq ht, ← ofSection_eq hx, h_val]
  rw [← map_evalSection_fromSpec hU ht, h_eval, map_evalSection_fromSpec hU hx]

/-- At the point of an affine open `U` given by a ring map `φ : Γ(X, U) ⟶ A`, the value of `s` is
`φ s`. -/
@[simp]
lemma ofSection_map_fromSpec (hU : IsAffineOpen U) (s : Γ(X, U)) (φ : Γ(X, U) ⟶ A) :
    ofSection s A (Spec.map φ ≫ hU.fromSpec) = φ s := by
  have h_eval : evalSection (Spec.map φ ≫ hU.fromSpec) (landsIn_fromSpec hU _) = φ := by
    apply map_injective
    rw [← cancel_mono hU.fromSpec, map_evalSection_fromSpec]
  rw [ofSection_eq (landsIn_fromSpec hU _), h_eval]

/-- For `x ∈ U`, the value of a section `s` over `U` at the point `Spec 𝒪_x ⟶ X` is the germ of
`s` at `x`. -/
lemma ofSection_fromSpecStalk {x : X} (hx : x ∈ U) (s : Γ(X, U)) :
    ofSection s (X.presheaf.stalk x) (X.fromSpecStalk x) = X.presheaf.germ U x hx s := by
  have h_eval : evalSection (X.fromSpecStalk x) (landsIn_fromSpecStalk hx) =
      X.presheaf.germ U x hx := by
    -- the two restriction maps that occur compose to the identity of `Γ(Spec 𝒪_x, ⊤)`
    simp [evalSection, appLE, fromSpecStalk_app hx, ← Functor.map_comp_assoc,
      Subsingleton.elim _ (𝟙 _)]
  rw [ofSection_eq (landsIn_fromSpecStalk hx), h_eval]

/-- A point of `U` lands in the basic open of the section `s` exactly when the value of `s` there
is a unit. -/
lemma landsIn_basicOpen (h : LandsIn t U) (s : Γ(X, U)) :
    LandsIn t (X.basicOpen s) ↔ IsUnit (ofSection s A t) := by
  -- The preimage of the basic open of `s` is the basic open of its value `a` in `A`, and the
  -- latter is all of `Spec A` exactly when `a` generates the unit ideal.
  have h_preimage : t ⁻¹ᵁ X.basicOpen s = PrimeSpectrum.basicOpen (evalSection t h s) := by
    rw [← top_inf_eq (t ⁻¹ᵁ X.basicOpen s), ← basicOpen_appLE t ⊤ U h s]
    exact basicOpen_eq_of_affine' (t.appLE U ⊤ h s)
  have h_unit (a : A) : PrimeSpectrum.basicOpen a = ⊤ ↔ IsUnit a := by
    simpa using PrimeSpectrum.iSup_basicOpen_eq_top_iff (f := ![a])
  rw [LandsIn, top_le_iff, h_preimage, ofSection_eq h]
  exact h_unit _

/-- The value at `t` of the pull-back of a global section `c` along `p : Y ⟶ X` is the value of `c`
at `t ≫ p`. -/
lemma ofSection_appTop (c : Γ(X, ⊤)) (A : CommRingCat) (t : Spec A ⟶ Y) :
    ofSection (p.appTop c) A t = ofSection c A (t ≫ p) := rfl

/-- An element `r` of a ring `B`, read as a global section of `Spec B`, has the value `φ r` at the
point given by a ring map `φ : B ⟶ A`. -/
lemma ofSection_ΓSpecIso_inv (φ : B ⟶ A) (r : B) :
    ofSection ((ΓSpecIso B).inv r) A (Spec.map φ) = φ r := by
  have h_eval : evalSection (Spec.map φ) landsIn_top = (ΓSpecIso B).hom ≫ φ :=
    ΓSpecIso_naturality φ
  rw [ofSection_eq landsIn_top, h_eval, CommRingCat.comp_apply, Iso.inv_hom_id_apply]

/-- A global section `c` of the open subscheme `U`, read as a section of `X` over `U`, has at
`x ≫ U.ι` the value of `c` at `x`. -/
lemma ofSection_topIso_hom (c : Γ(U, ⊤)) (x : Spec A ⟶ U.toScheme) :
    ofSection (U.topIso.hom c) A (x ≫ U.ι) = ofSection c A x := by
  have h_pull : U.ι.appLE U ⊤ (by simp) = U.topIso.inv := U.ι_appLE U ⊤ (by simp)
  rw [← ofSection_appLE U.ι (by simp) _ landsIn_top, h_pull, Iso.hom_inv_id_apply]

/-- Descent of functions along a flat, surjective, quasi-compact `p : Y ⟶ X`. Let `V` be an open
cover of `Y`. If the functions `f a`, regular on `p ⁻¹ᵁ U ⊓ V a`, agree at points with the same
image in `X`, they are pull-backs of one section over `U`. -/
lemma exists_ofSection_glue (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {V : κ → Y.Opens} (hV : IsOpenCover V) (f : κ → PointFn Y)
    (hf : ∀ a : κ, IsRegularOn (f a) (p ⁻¹ᵁ U ⊓ V a))
    (h : ∀ (a b : κ) (A : CommRingCat) (t s : Spec A ⟶ Y), t ≫ p = s ≫ p → LandsIn (t ≫ p) U →
      LandsIn t (V a) → LandsIn s (V b) → f a A t = f b A s) :
    ∃ s : Γ(X, U), ∀ (a : κ) (A : CommRingCat) (t : Spec A ⟶ Y),
      LandsIn (t ≫ p) U → LandsIn t (V a) → ofSection s A (t ≫ p) = f a A t := by
  -- A function is a morphism to the affine line `𝔸 = Spec ℤ[T]`. Glue the `f a` to a morphism
  -- `q` on `p ⁻¹ᵁ U`, descend it along the effective epimorphism `p ⁻¹ᵁ U → U`, and pull back `T`.
  have in_U {Z : Scheme} (r : Z ⟶ Limits.pullback p U.ι) : LandsIn ((r ≫ fst p U.ι) ≫ p) U := by
    simpa only [assoc, condition] using landsIn_comp_incl (t := r ≫ snd p U.ι)
  let 𝔸 : Scheme := Spec (CommRingCat.of (FreeCommRing (Fin 1)))
  obtain ⟨q, hq⟩ : ∃ q : Limits.pullback p U.ι ⟶ 𝔸,
      ∀ (a : κ) (A : CommRingCat) (t : Spec A ⟶ Limits.pullback p U.ι),
        LandsIn t (fst p U.ι ⁻¹ᵁ V a) →
        t ≫ q = specMap (FreeCommRing.lift ![f a A (t ≫ fst p U.ι)]) := by
    refine exists_hom_of_cover (isOpenCover_preimage hV _) _ fun i j A B φ t hi hj ↦ ?_
    have natural : f j B ((map φ ≫ t) ≫ fst p U.ι) = φ (f i A (t ≫ fst p U.ι)) := by
      rw [← hf i φ _ (landsIn_inf.2 ⟨in_U t, landsIn_preimage.1 hi⟩), ← assoc]
      exact h j i B _ _ rfl (in_U _) hj (landsIn_preimage.1 (hi.comp _))
    rw [← map_comp]
    -- both ring maps send the variable to the value in `natural`
    refine congrArg Spec.map (CommRingCat.hom_ext (FreeCommRing.hom_ext fun k ↦ ?_))
    simpa using natural
  -- By `h`, the morphism `q` is constant on the fibres of `p`.
  have descends {Z : Scheme} (a b : Z ⟶ Limits.pullback p U.ι)
      (hab : a ≫ snd p U.ι = b ≫ snd p U.ι) : a ≫ q = b ≫ q := by
    refine hom_ext_of_isOpenCover (isOpenCover_inf (isOpenCover_preimage hV (a ≫ fst p U.ι))
      (isOpenCover_preimage hV (b ≫ fst p U.ι))) fun i A r hr ↦ ?_
    -- At a point `r` of `Z`, `hq` computes both sides; `r ≫ a` and `r ≫ b` have the same image
    -- in `X` by `hab` and `condition`, so the values of the `f` there agree by `h`.
    obtain ⟨ha, hb⟩ : LandsIn ((r ≫ a) ≫ fst p U.ι) (V i.1) ∧
        LandsIn ((r ≫ b) ≫ fst p U.ι) (V i.2) := by simpa using hr
    have h_image : ((r ≫ a) ≫ fst p U.ι) ≫ p = ((r ≫ b) ≫ fst p U.ι) ≫ p := by
      simp [condition, reassoc_of% hab]
    rw [← assoc, ← assoc, hq i.1 A _ ha, hq i.2 A _ hb, h i.1 i.2 A _ _ h_image (in_U _) ha hb]
  let d : U.toScheme ⟶ 𝔸 := desc (snd p U.ι) q descends
  let T : Γ(𝔸, ⊤) := (ΓSpecIso _).inv (FreeCommRing.of 0)
  refine ⟨U.topIso.hom (d.appTop T), fun a A t ht hta ↦ ?_⟩
  -- Factor `t ≫ p` through `U`, and `t` through the fibre product.
  obtain ⟨tU, htU⟩ : ∃ tU : Spec A ⟶ U.toScheme, tU ≫ U.ι = t ≫ p :=
    ⟨_, IsOpenImmersion.lift_fac U.ι (t ≫ p)
      (by simpa [Set.range_subset_iff] using fun y ↦ ht (mem_top y))⟩
  have value : tU ≫ d = specMap (FreeCommRing.lift ![f a A t]) := by
    rw [← lift_snd t tU htU.symm, assoc, fac,
      hq a A (Limits.pullback.lift t tU htU.symm) (by rwa [landsIn_preimage, lift_fst]), lift_fst]
  -- The value of `d^* T` at `tU` is the value of `T` at `tU ≫ d`, which is `f a A t` by `value`.
  rw [← htU, ofSection_topIso_hom, ofSection_appTop, value, ofSection_ΓSpecIso_inv]
  simp

namespace IsRegularOn

/-! ### Regular functions -/

/-- A function that is regular on `U` agrees, at the points of `U`, with the function of a section
over `U`. -/
lemma exists_ofSection (hf : f.IsRegularOn U) :
    ∃ s : Γ(X, U), ∀ (A : CommRingCat) (t : Spec A ⟶ X), LandsIn t U → ofSection s A t = f A t := by
  -- this is descent along the identity of `X`, with the cover of `X` by one open
  simpa using exists_ofSection_glue (𝟙 X) isOpenCover_top (fun _ ↦ f)
    (fun _ ↦ by simpa [IsRegularOn] using hf) (by simp +contextual)

/-- If `f` is regular on `U`, its pull-back along `p : Y ⟶ X` is regular on the preimage of `U`. -/
lemma pull (hf : f.IsRegularOn U) : (f.pull p).IsRegularOn (p ⁻¹ᵁ U) := by aesop_cat

lemma mono (hf : f.IsRegularOn U) {V : X.Opens} (h_le : V ≤ U) : f.IsRegularOn V :=
  fun _ _ φ t ht ↦ hf φ t (ht.mono h_le)

lemma mul (hf : f.IsRegularOn U) {V : X.Opens} (hg : g.IsRegularOn V) :
    (f * g).IsRegularOn (U ⊓ V) := by
  intro A B φ t ht
  obtain ⟨htU, htV⟩ : LandsIn t U ∧ LandsIn t V := landsIn_inf.1 ht
  simp [hf φ t htU, hg φ t htV]

/-- Let `p : Y ⟶ X` be quasi-compact and scheme-theoretically dominant, and let `V` be an open
cover of `Y`. Functions `f`, `g` regular on `U` agree at the points of `U` if their pull-backs
agree at the points of each `p ⁻¹ᵁ U ⊓ V a`. -/
lemma ext_of_dominant_of_isOpenCover (p : Y ⟶ X) [IsSchemeTheoreticallyDominant p]
    [QuasiCompact p] (hf : f.IsRegularOn U) (hg : g.IsRegularOn U)
    {V : κ → Y.Opens} (hV : IsOpenCover V)
    (h : ∀ (a : κ) (A : CommRingCat) (t : Spec A ⟶ Y), LandsIn (t ≫ p) U → LandsIn t (V a) →
      f A (t ≫ p) = g A (t ≫ p))
    (A : CommRingCat) (t : Spec A ⟶ X) (ht : LandsIn t U) : f A t = g A t := by
  -- `f` and `g` come from sections `s`, `s'` over `U`, and pulling back sections along `p` is
  -- injective. The pull-backs have the same germ at every point `x` of `p ⁻¹ᵁ U`.
  obtain ⟨s, hs⟩ := hf.exists_ofSection
  obtain ⟨s', hs'⟩ := hg.exists_ofSection
  have sections_eq : s = s' := by
    refine p.app_injective _ (section_ext Y.sheaf _ _ _ fun x hx ↦ ?_)
    have in_U : LandsIn (Y.fromSpecStalk x) (p ⁻¹ᵁ U) := landsIn_fromSpecStalk hx
    obtain ⟨a, ha⟩ := exists_landsIn_of_isOpenCover hV (Y.fromSpecStalk x)
    -- germs are values at the point `Spec 𝒪_x → Y`, where `h` applies
    change Y.presheaf.germ (p ⁻¹ᵁ U) x hx (p.app U s) = Y.presheaf.germ (p ⁻¹ᵁ U) x hx (p.app U s')
    rw [← ofSection_fromSpecStalk hx, ← ofSection_fromSpecStalk hx, app_eq_appLE,
      ofSection_appLE p le_rfl s in_U, ofSection_appLE p le_rfl s' in_U, hs _ _ in_U, hs' _ _ in_U]
    exact h a _ _ in_U ha
  rw [← hs A t ht, ← hs' A t ht, sections_eq]

/-- Let `p : Y ⟶ X` be quasi-compact and scheme-theoretically dominant, and let `M` be a line
bundle on `Y`. Functions `f`, `g` regular on `U` agree at the points of `U` if their pull-backs
agree at the points of each `p ⁻¹ᵁ U ⊓ M.opens a`. -/
lemma ext_of_dominant (p : Y ⟶ X) (hf : f.IsRegularOn U) (hg : g.IsRegularOn U)
    (M : LineBundle Y κ) [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    (h : ∀ (a : κ) (A : CommRingCat) (t : Spec A ⟶ Y), LandsIn (t ≫ p) U → LandsIn t (M.opens a) →
      f A (t ≫ p) = g A (t ≫ p))
    (A : CommRingCat) (t : Spec A ⟶ X) (ht : LandsIn t U) : f A t = g A t :=
  hf.ext_of_dominant_of_isOpenCover p hg M.isOpenCover h A t ht

end IsRegularOn

end PointFn

end PointFunctions

/-!
## Descent of sections and frames, the Picard group and its pull-back

* `New.LineBundle.IsIsomorphic.exists_isFrame`, `New.LineBundle.IsIsomorphic.mul`: having a frame
  is invariant under isomorphism, and isomorphism is compatible with tensor products.
-/

section PicardGroup

open CategoryTheory AlgebraicGeometry PointFn Ring LandsIn LineBundle

variable {X Y Z : Scheme} {ι κ : Type}
  {A : CommRingCat} {L : LineBundle X ι} {M : LineBundle X κ} {u s : ι → PointFn X}
  (K : LineBundle X ι) (p : Y ⟶ X) (q : Z ⟶ Y)

namespace LineBundle

/-- At the points of `K.opens i ⊓ K.opens j` the transition functions `K.transition i j` and
`K.transition j i` of a line bundle are inverse to each other. -/
lemma transition_mul_transition {i j : ι} {t : Spec A ⟶ X} (hi : LandsIn t (K.opens i))
    (hj : LandsIn t (K.opens j)) : K.transition i j A t * K.transition j i A t = 1 := by
  rw [K.transition_trans i j i A t hi hj hi, K.transition_self i A t hi]

/-- A transition function `K.transition i j` of a line bundle is a unit at the points of
`K.opens i ⊓ K.opens j`. -/
lemma isUnit_transition {i j : ι} {t : Spec A ⟶ X} (hi : LandsIn t (K.opens i))
    (hj : LandsIn t (K.opens j)) : IsUnit (K.transition i j A t) :=
  IsUnit.of_mul_eq_one (K.transition j i A t) (transition_mul_transition K hi hj)

@[simp]
lemma pull_comp : K.pull (q ≫ p) = (K.pull p).pull q := rfl

@[simp]
lemma pull_id : K.pull (𝟙 X) = K := rfl

/-- Let `π : Y ⟶ X` be flat, surjective and quasi-compact, and let `u` be a section of the
pullback of `M ⊗ L⁻¹` along `π` whose value at a point of `Y` depends only on its image in `X`.
Then the product of `u` with a section `s` of `L` descends to a section `r` of `M`, with `r i`
zero at the points that do not land in `M.opens i`. -/
lemma exists_isSection_eq_mul (π : Y ⟶ X) [Flat π] [Surjective π] [QuasiCompact π]
    {u : κ × ι → PointFn Y} (hu : ((M.mul L.inv).pull π).IsSection u) (hs : L.IsSection s)
    (h_fibre : ∀ (i : κ × ι) (B : CommRingCat) (t t' : Spec B ⟶ Y), t ≫ π = t' ≫ π →
      LandsIn (t ≫ π) ((M.mul L.inv).opens i) → u i B t = u i B t') :
    ∃ r : κ → PointFn X,
      M.IsSection r ∧
      (∀ (i : κ) (A : CommRingCat) (t : Spec A ⟶ X), ¬LandsIn t (M.opens i) → r i A t = 0) ∧
      ∀ (i : κ) (a : ι) (A : CommRingCat) (t : Spec A ⟶ Y),
        LandsIn (t ≫ π) (M.opens i) → LandsIn (t ≫ π) (L.opens a) →
          r i A (t ≫ π) = u (i, a) A t * s a A (t ≫ π) := by
  obtain ⟨u_regular, u_eq⟩ := hu
  obtain ⟨s_regular, s_eq⟩ := hs
  -- For fixed `i`, the products `u (i, a) * s a` agree at points with the same image, so they
  -- descend to one function `r i` over `M.opens i`.
  have h_descend (i : κ) : ∃ r : Γ(X, M.opens i),
      ∀ (a : ι) (A : CommRingCat) (t : Spec A ⟶ Y),
        LandsIn (t ≫ π) (M.opens i) → LandsIn (t ≫ π) (L.opens a) →
          ofSection r A (t ≫ π) = u (i, a) A t * s a A (t ≫ π) := by
    refine exists_ofSection_glue π (L.pull π).isOpenCover (fun a ↦ u (i, a) * (s a).pull π) ?_ ?_
    · exact fun a ↦ ((u_regular (i, a)).mul ((s_regular a).pull π)).mono
        (le_inf le_rfl inf_le_right)
    · intro a b B t t' h_image hi ha hb
      have ha' : LandsIn (t ≫ π) (L.opens a) := by simpa using ha
      have hb' : LandsIn (t ≫ π) (L.opens b) := by simpa [h_image] using hb
      have hu_eq : u (i, a) B t = L.transition b a B (t ≫ π) * u (i, b) B t := by
        simpa [M.transition_self i B _ hi] using
          u_eq (i, a) (i, b) B t (by simp [hi, ha']) (by simp [hi, hb'])
      have hs_eq : s a B (t ≫ π) = L.transition a b B (t ≫ π) * s b B (t ≫ π) :=
        s_eq a b B _ ha' hb'
      have h_transition : L.transition b a B (t ≫ π) * L.transition a b B (t ≫ π) = 1 :=
        transition_mul_transition L hb' ha'
      have h_same : u (i, b) B t = u (i, b) B t' :=
        h_fibre (i, b) B t t' h_image (by simp [hi, hb'])
      simp only [Pi.mul_apply, PointFn.pull, ← h_image, hu_eq, hs_eq, ← h_same]
      linear_combination (u (i, b) B t * s b B (t ≫ π)) * h_transition
  choose r hr using h_descend
  have r_sec : M.IsSection fun i : κ ↦ ofSection (r i) := by
    refine ⟨fun i ↦ isRegularOn_ofSection _, fun i j A t hi hj ↦ ?_⟩
    -- `r i = transition i j * r j` can be tested after composing with `π`, on the cover of
    -- `L.pull π`
    have h_right : (M.transition i j * ofSection (r j)).IsRegularOn (M.opens i ⊓ M.opens j) :=
      ((M.regular i j).mul (isRegularOn_ofSection (r j))).mono (by simp)
    refine ((isRegularOn_ofSection (r i)).mono inf_le_left).ext_of_dominant_of_isOpenCover π h_right
      (L.pull π).isOpenCover (fun a B x hx ha ↦ ?_) A t (landsIn_inf.2 ⟨hi, hj⟩)
    obtain ⟨hxi, hxj⟩ := landsIn_inf.1 hx
    have hxa : LandsIn (x ≫ π) (L.opens a) := by simpa using ha
    have hu_eq : u (i, a) B x = M.transition i j B (x ≫ π) * u (j, a) B x := by
      simpa [L.transition_self a B _ hxa] using
        u_eq (i, a) (j, a) B x (by simp [hxi, hxa]) (by simp [hxj, hxa])
    rw [Pi.mul_apply, Pi.mul_apply, hr i a B x hxi hxa, hr j a B x hxj hxa, hu_eq, mul_assoc]
  exact ⟨fun i ↦ ofSection (r i), r_sec, fun i A t ht ↦ ofSection_eq_zero ht (r i), hr⟩

/-- Let `p : Y ⟶ X` be surjective. A section `r` of `M` is a frame if its pullback along `p` is
the product of a frame `u` of the pullback of `M ⊗ L⁻¹` and the pullback of a frame `s` of `L`. -/
lemma IsSection.isFrame_of_eq_mul (p : Y ⟶ X) [Surjective p] {r : κ → PointFn X}
    (hr : M.IsSection r) {u : κ × ι → PointFn Y} (hu : ((M.mul L.inv).pull p).IsFrame u)
    (hs : L.IsFrame s)
    (h_eq : ∀ (i : κ) (a : ι) (A : CommRingCat) (t : Spec A ⟶ Y),
      LandsIn (t ≫ p) (M.opens i) → LandsIn (t ≫ p) (L.opens a) →
        r i A (t ≫ p) = u (i, a) A t * s a A (t ≫ p)) :
    M.IsFrame r := by
  obtain ⟨-, u_unit⟩ := hu
  obtain ⟨-, s_unit⟩ := hs
  refine ⟨hr, fun i A t ht ↦ ?_⟩
  obtain ⟨c, hc⟩ := (hr.1 i).exists_ofSection
  -- Upstairs `c` is a product of two units, so the preimage of the open set where `c` is a
  -- unit contains the preimage of `M.opens i`; as `p` is surjective, the same holds in `X`.
  have h_preimage : p ⁻¹ᵁ M.opens i ≤ p ⁻¹ᵁ X.basicOpen c := by
    refine le_of_cover (L.pull p).isOpenCover fun a B x ha hx ↦ ?_
    have hxa : LandsIn (x ≫ p) (L.opens a) := by simpa using ha
    have hxi : LandsIn (x ≫ p) (M.opens i) := by simpa using hx
    rw [landsIn_preimage, landsIn_basicOpen hxi, hc B _ hxi, h_eq i a B x hxi hxa]
    exact (u_unit (i, a) B x (by simp [hxi, hxa])).mul (s_unit a B (x ≫ p) hxa)
  have h_le : M.opens i ≤ X.basicOpen c := p.surjective.forall.2 h_preimage
  rw [← hc A t ht]
  exact (landsIn_basicOpen ht c).1 (ht.mono h_le)

/-- Let `π : Y ⟶ X` be flat, surjective and quasi-compact, and let `u` be a section of the
pullback of `M ⊗ L⁻¹` along `π` whose value at a point of `Y` depends only on its image in `X`.
Then the product of `u` with a section `s` of `L` descends to a section `r` of `M`, with `r i`
zero off `M.opens i`, which is a frame if `u` and `s` are frames. -/
lemma exists_section_mul (π : Y ⟶ X) [Flat π] [Surjective π] [QuasiCompact π]
    {u : κ × ι → PointFn Y} (hu : ((M.mul L.inv).pull π).IsSection u) (hs : L.IsSection s)
    (h_fibre : ∀ (i : κ × ι) (B : CommRingCat) (t t' : Spec B ⟶ Y), t ≫ π = t' ≫ π →
      LandsIn (t ≫ π) ((M.mul L.inv).opens i) → u i B t = u i B t') :
    ∃ r : κ → PointFn X,
      (M.IsSection r ∧ ∀ (i : κ) (A : CommRingCat) (t : Spec A ⟶ X),
        ¬LandsIn t (M.opens i) → r i A t = 0) ∧
      (∀ (i : κ) (a : ι) (A : CommRingCat) (t : Spec A ⟶ Y),
        LandsIn (t ≫ π) (M.opens i) → LandsIn (t ≫ π) (L.opens a) →
          r i A (t ≫ π) = u (i, a) A t * s a A (t ≫ π)) ∧
      (((M.mul L.inv).pull π).IsFrame u → L.IsFrame s → M.IsFrame r) := by
  obtain ⟨r, r_sec, r_zero, r_eq⟩ := exists_isSection_eq_mul π hu hs h_fibre
  exact ⟨r, ⟨r_sec, r_zero⟩, r_eq,
    fun u_frame s_frame ↦ r_sec.isFrame_of_eq_mul π u_frame s_frame r_eq⟩

/-- fpqc descent: a line bundle L on X has a nowhere vanishing global section if its pull-back
along a flat, surjective, quasi-compact π: Y → X has one whose values at ring-valued points
depend only on their images under π. -/
lemma exists_isFrame_of_fpqc (π : Y ⟶ X) [Flat π] [Surjective π] [QuasiCompact π]
    {u : ι → PointFn Y} (hu : (L.pull π).IsFrame u)
    (h_fibre : ∀ (i : ι) (B : CommRingCat) (t t' : Spec B ⟶ Y), t ≫ π = t' ≫ π →
      LandsIn (t ≫ π) (L.opens i) → u i B t = u i B t') :
    ∃ s : ι → PointFn X, L.IsFrame s := by
  -- Read `u` as a frame of the pull-back of `L ⊗ one⁻¹` and multiply it by the frame `1` of
  -- `one`.
  have u_frame : ((L.mul one.inv).pull π).IsFrame fun a ↦ u a.1 := by
    aesop (add simp [IsFrame, IsSection, IsRegularOn])
  have one_frame : (one : LineBundle X Unit).IsFrame 1 := by simp [IsFrame, IsSection, IsRegularOn]
  obtain ⟨s, s_sec, -, s_eq⟩ := exists_isSection_eq_mul π u_frame.1 one_frame.1
    fun a B t t' h_image ha ↦ h_fibre a.1 B t t' h_image (landsIn_inf.1 ha).1
  exact ⟨s, s_sec.isFrame_of_eq_mul π u_frame one_frame s_eq⟩

/-- Every line bundle is isomorphic to itself. -/
lemma IsIsomorphic.refl : K.IsIsomorphic K := by
  -- the transition functions `transition i j` form a frame of `K ⊗ K⁻¹`
  refine ⟨K.transition.uncurry, ⟨fun i ↦ K.regular i.1 i.2, ?_⟩, ?_⟩
  · rintro ⟨a, b⟩ ⟨c, d⟩ A t hi hj
    obtain ⟨ha, hb⟩ : LandsIn t (K.opens a) ∧ LandsIn t (K.opens b) := by simpa using hi
    obtain ⟨hc, hd⟩ : LandsIn t (K.opens c) ∧ LandsIn t (K.opens d) := by simpa using hj
    simp only [mul_transition, inv_transition, Function.uncurry, Pi.mul_apply]
    rw [← K.transition_trans a c b A t ha hc hb, ← K.transition_trans c d b A t hc hd hb]
    ring
  · rintro ⟨a, b⟩ A t hi
    obtain ⟨ha, hb⟩ : LandsIn t (K.opens a) ∧ LandsIn t (K.opens b) := by simpa using hi
    exact isUnit_transition K ha hb

/-- A line bundle `L` that is isomorphic to a line bundle `M` with a frame has a frame itself. -/
lemma IsIsomorphic.exists_isFrame (h_iso : L.IsIsomorphic M)
    (h_frame : ∃ s : κ → PointFn X, M.IsFrame s) : ∃ r : ι → PointFn X, L.IsFrame r := by
  obtain ⟨u, hu⟩ := h_iso
  obtain ⟨s, hs⟩ := h_frame
  obtain ⟨r, r_sec, -, r_eq⟩ := exists_isSection_eq_mul (𝟙 X) hu.1 hs.1 (h_fibre := by simp)
  exact ⟨r, r_sec.isFrame_of_eq_mul (𝟙 X) hu hs r_eq⟩

/-- Pulling back a section of a line bundle gives a section of the pulled-back bundle. -/
lemma IsSection.pull (hs : L.IsSection s) (p : Y ⟶ X) :
    (L.pull p).IsSection fun i : ι ↦ (s i).pull p := by
  aesop (add simp [IsSection, IsRegularOn])

/-- Pulling back a frame of a line bundle gives a frame of the pulled-back bundle. -/
lemma IsFrame.pull (hu : L.IsFrame u) (p : Y ⟶ X) :
    (L.pull p).IsFrame fun i : ι ↦ (u i).pull p := by
  aesop (add simp [IsFrame, IsSection, IsRegularOn])

/-- The pointwise inverse of a frame `u` of `L` is a frame of the dual bundle `L.inv`. -/
lemma IsFrame.inv (hu : L.IsFrame u) :
    L.inv.IsFrame fun (i : ι) (A : CommRingCat) (t : Spec A ⟶ X) ↦ inverse (u i A t) := by
  obtain ⟨⟨u_regular, u_eq⟩, u_unit⟩ := hu
  refine ⟨⟨fun i A B φ t ht ↦ ?_, fun i j A t hi hj ↦ ?_⟩,
    fun i A t hi ↦ (u_unit i A t hi).ringInverse⟩
  · -- a ring map sends the inverse of a unit to the inverse of its image
    have h_map_unit : IsUnit (φ (u i A t)) := (u_unit i A t ht).map φ.hom
    simp only [u_regular i φ t ht]
    apply h_map_unit.mul_left_cancel
    rw [mul_inverse_cancel _ h_map_unit, ← map_mul, mul_inverse_cancel _ (u_unit i A t ht), map_one]
  · -- both sides are inverse to `u i`
    have hj_inv : u j A t * inverse (u j A t) = 1 := mul_inverse_cancel _ (u_unit j A t hj)
    apply (u_unit i A t hi).mul_left_cancel
    rw [mul_inverse_cancel _ (u_unit i A t hi), u_eq i j A t hi hj, inv_transition]
    linear_combination
      -(u j A t * inverse (u j A t)) * transition_mul_transition L hi hj - hj_inv

/-- The products of the values of a frame of `L` and a frame of `M` form a frame of `L.mul M`. -/
lemma IsFrame.mul (hu : L.IsFrame u) {v : κ → PointFn X} (hv : M.IsFrame v) :
    (L.mul M).IsFrame fun i : ι × κ ↦ u i.1 * v i.2 := by
  obtain ⟨⟨u_regular, u_eq⟩, u_unit⟩ := hu
  obtain ⟨⟨v_regular, v_eq⟩, v_unit⟩ := hv
  refine ⟨⟨fun i ↦ (u_regular i.1).mul (v_regular i.2), ?_⟩, ?_⟩
  · rintro ⟨a, b⟩ ⟨c, d⟩ A t hi hj
    obtain ⟨ha, hb⟩ : LandsIn t (L.opens a) ∧ LandsIn t (M.opens b) := by simpa using hi
    obtain ⟨hc, hd⟩ : LandsIn t (L.opens c) ∧ LandsIn t (M.opens d) := by simpa using hj
    simp [u_eq a c A t ha hc, v_eq b d A t hb hd, mul_mul_mul_comm]
  · rintro ⟨a, b⟩ A t hi
    obtain ⟨ha, hb⟩ : LandsIn t (L.opens a) ∧ LandsIn t (M.opens b) := by simpa using hi
    exact (u_unit a A t ha).mul (v_unit b A t hb)

/-- Let `e : κ → ι` send each open of `M` into an open of `L`, and let the transition function
`M.transition a b` agree with `L.transition (e a) (e b)` at the points of
`M.opens a ⊓ M.opens b`. Then a frame `u` of `L` restricts to the frame `u ∘ e` of `M`. -/
lemma IsFrame.comp_of_le (hu : L.IsFrame u) (e : κ → ι)
    (h_le : ∀ a : κ, M.opens a ≤ L.opens (e a))
    (h_transition : ∀ (a b : κ) (A : CommRingCat) (t : Spec A ⟶ X),
      LandsIn t (M.opens a) → LandsIn t (M.opens b) →
        M.transition a b A t = L.transition (e a) (e b) A t) :
    M.IsFrame (u ∘ e) := by
  obtain ⟨⟨u_regular, u_eq⟩, u_unit⟩ := hu
  refine ⟨⟨fun a ↦ (u_regular (e a)).mono (h_le a), fun a b A t ha hb ↦ ?_⟩,
    fun a A t ha ↦ u_unit (e a) A t (ha.mono (h_le a))⟩
  rw [h_transition a b A t ha hb]
  exact u_eq (e a) (e b) A t (ha.mono (h_le a)) (hb.mono (h_le b))

/-- Isomorphism of line bundles is compatible with tensor products: if `L ≅ M` and `N ≅ P`, then
`L.mul N` is isomorphic to `M.mul P`. -/
lemma IsIsomorphic.mul {μ ν : Type} {N : LineBundle X μ} {P : LineBundle X ν}
    (hLM : L.IsIsomorphic M) (hNP : N.IsIsomorphic P) : (L.mul N).IsIsomorphic (M.mul P) := by
  obtain ⟨u, hu⟩ : ∃ u : ι × κ → PointFn X, (L.mul M.inv).IsFrame u := hLM
  obtain ⟨v, hv⟩ : ∃ v : μ × ν → PointFn X, (N.mul P.inv).IsFrame v := hNP
  -- `(L ⊗ N) ⊗ (M ⊗ P)⁻¹` is `(L ⊗ M⁻¹) ⊗ (N ⊗ P⁻¹)` up to reindexing the cover
  refine ⟨_, (hu.mul hv).comp_of_le (Equiv.prodProdProdComm ι μ κ ν) ?_ ?_⟩
  · rintro ⟨⟨a, b⟩, c, d⟩
    simp [inf_inf_inf_comm (L.opens a)]
  · rintro ⟨⟨a, b⟩, c, d⟩ ⟨⟨a', b'⟩, c', d'⟩ A t - -
    simp [mul_mul_mul_comm]

/-- If `u` is a frame of `L`, every section `s` of `L` is `c * u` at the points of the cover, for a
global function `c` on `X`. -/
lemma IsFrame.exists_eq_mul (hu : L.IsFrame u) (hs : L.IsSection s) :
    ∃ c : Γ(X, ⊤), ∀ (i : ι) (A : CommRingCat) (t : Spec A ⟶ X), LandsIn t (L.opens i) →
      s i A t = (ofSection c * u i) A t := by
  -- the quotients `s i / u i` agree on overlaps, so they glue to a global function `c`
  obtain ⟨⟨inv_regular, inv_eq⟩, -⟩ := hu.inv
  obtain ⟨s_regular, s_eq⟩ := hs
  have h_agree (a b : ι) (A : CommRingCat) (t : Spec A ⟶ X) (ha : LandsIn t (L.opens a))
      (hb : LandsIn t (L.opens b)) :
      inverse (u a A t) * s a A t = inverse (u b A t) * s b A t := by
    have h_inv : inverse (u a A t) = L.transition b a A t * inverse (u b A t) :=
      inv_eq a b A t ha hb
    rw [h_inv, s_eq a b A t ha hb]
    linear_combination (inverse (u b A t) * s b A t) * transition_mul_transition L hb ha
  obtain ⟨c, hc⟩ : ∃ c : Γ(X, ⊤), ∀ (a : ι) (A : CommRingCat) (t : Spec A ⟶ X),
      LandsIn t (L.opens a) → ofSection c A t = inverse (u a A t) * s a A t := by
    simpa using exists_ofSection_glue (𝟙 X) (U := ⊤) L.isOpenCover
      (fun a A t ↦ inverse (u a A t) * s a A t)
      (fun a ↦ ((inv_regular a).mul (s_regular a)).mono (by simp)) (by simpa using h_agree)
  refine ⟨c, fun i A t hi ↦ ?_⟩
  rw [Pi.mul_apply, Pi.mul_apply, hc i A t hi, mul_right_comm,
    inverse_mul_cancel _ (hu.2 i A t hi), one_mul]

end LineBundle

open Equiv IsIsomorphic Quotient

/-- Isomorphism of line bundles is symmetric: inverting a frame of `L ⊗ M⁻¹` gives `L⁻¹ ≅ M⁻¹`,
so `M ⊗ L⁻¹ ≅ M ⊗ M⁻¹`, and the latter has a frame. -/
protected lemma LineBundle.IsIsomorphic.symm (h_iso : L.IsIsomorphic M) : M.IsIsomorphic L := by
  obtain ⟨v, hv⟩ := h_iso
  have h_mul : (M.mul L.inv).IsIsomorphic (M.mul M.inv) := (IsIsomorphic.refl M).mul ⟨_, hv.inv⟩
  exact h_mul.exists_isFrame (IsIsomorphic.refl M)

/-- Isomorphism of line bundles is transitive: `L ≅ M` gives `L ⊗ N⁻¹ ≅ M ⊗ N⁻¹`, and the latter
has a frame if `M ≅ N`. -/
protected lemma LineBundle.IsIsomorphic.trans {μ : Type} {N : LineBundle X μ}
    (hLM : L.IsIsomorphic M) (hMN : M.IsIsomorphic N) : L.IsIsomorphic N :=
  (hLM.mul (IsIsomorphic.refl N.inv)).exists_isFrame hMN

/-! ### The Picard group -/

/-- The Picard group of `X`: line bundles given by a cover and a cocycle, modulo isomorphism. The
group law is written additively. -/
def Pic (X : Scheme) : Type 1 :=
  Quotient (α := Σ ι : Type, LineBundle X ι)
    { r := fun L M ↦ L.2.IsIsomorphic M.2
      iseqv :=
        { refl := fun L ↦ IsIsomorphic.refl L.2
          symm := IsIsomorphic.symm
          trans := IsIsomorphic.trans } }

/-- The class of the line bundle K in the Picard group of X. -/
def LineBundle.picClass : Pic X := ⟦⟨ι, K⟩⟧

/-- Two line bundles have the same class in the Picard group if and only if they are isomorphic. -/
lemma LineBundle.picClass_eq_iff : L.picClass = M.picClass ↔ L.IsIsomorphic M := eq

/-- Let `e : κ → ι` send each open of `M` into an open of `L`, that is, `M.opens a ≤ L.opens (e a)`.
Suppose that at every point in `M.opens a` the transition functions agree:
`M.transition a b = L.transition (e a) (e b)`. Then `L` and `M` have the same class in the Picard
group. -/
lemma LineBundle.picClass_eq_of_le (e : κ → ι) (h_le : ∀ a : κ, M.opens a ≤ L.opens (e a))
    (h_transition : ∀ (a b : κ) (A : CommRingCat) (t : Spec A ⟶ X), LandsIn t (M.opens a) →
      M.transition a b A t = L.transition (e a) (e b) A t) :
    L.picClass = M.picClass := by
  -- a frame of `L ⊗ L⁻¹`, read at the indices `(i, e a)`, is a frame of `L ⊗ M⁻¹`
  obtain ⟨u, hu⟩ : ∃ u : ι × ι → PointFn X, (L.mul L.inv).IsFrame u := IsIsomorphic.refl L
  have h_frame : (L.mul M.inv).IsFrame (u ∘ Prod.map id e) := by
    refine hu.comp_of_le (Prod.map id e) (fun i ↦ inf_le_inf le_rfl (h_le i.2)) ?_
    rintro ⟨i, a⟩ ⟨j, b⟩ A t - hj
    simp [h_transition b a A t (landsIn_inf.1 hj).2]
  exact picClass_eq_iff.2 ⟨_, h_frame⟩

/-- The tensor product of line bundles is associative up to isomorphism. -/
lemma LineBundle.picClass_mul_assoc {μ : Type} (N : LineBundle X μ) :
    ((L.mul M).mul N).picClass = (L.mul (M.mul N)).picClass :=
  picClass_eq_of_le (fun a ↦ ((a.1, a.2.1), a.2.2)) (by simp [inf_assoc]) (by simp [mul_assoc])

/-- The tensor product of line bundles is commutative up to isomorphism. -/
lemma LineBundle.picClass_mul_comm : (L.mul M).picClass = (M.mul L).picClass :=
  picClass_eq_of_le (fun a ↦ (a.2, a.1)) (by simp) (by simp [mul_comm])

/-- The trivial line bundle is neutral for the tensor product up to isomorphism. -/
lemma LineBundle.picClass_mul_one : (L.mul one).picClass = L.picClass :=
  picClass_eq_of_le (fun a ↦ (a, ())) (by simp) (by simp)

/-- The tensor product of a line bundle with its dual is isomorphic to the trivial bundle. -/
lemma LineBundle.picClass_mul_inv :
    (L.mul L.inv).picClass = (one : LineBundle X Unit).picClass := by
  -- a frame of `L ⊗ L⁻¹` is also a frame of `(L ⊗ L⁻¹) ⊗ one⁻¹`
  obtain ⟨u, hu⟩ : ∃ u : ι × ι → PointFn X, (L.mul L.inv).IsFrame u := IsIsomorphic.refl L
  exact picClass_eq_iff.2 ⟨u ∘ Prod.fst, hu.comp_of_le _ (fun _ ↦ inf_le_left) (by simp)⟩

/-- The sum in the Picard group is the tensor product of line bundles. -/
instance : Add (Pic X) where
  add := Quotient.map₂ (fun L M ↦ ⟨L.fst × M.fst, L.snd.mul M.snd⟩)
    fun _ _ hL _ _ hM ↦ IsIsomorphic.mul hL hM

/-- The negative in the Picard group is the dual line bundle. -/
instance : Neg (Pic X) where
  neg := Quotient.map (fun L ↦ ⟨L.fst, L.snd.inv⟩) fun _ _ ⟨_, hu⟩ ↦ ⟨_, hu.inv⟩

/-- Zero in the Picard group is the class of the trivial line bundle. -/
instance : Zero (Pic X) where
  zero := one.picClass

instance : AddCommGroup (Pic X) where
  toAddGroup := AddGroup.ofRightAxioms
    (fun a b c ↦ Quotient.inductionOn₃ a b c fun _ _ N ↦ picClass_mul_assoc N.2)
    (Quotient.ind fun _ ↦ picClass_mul_one) (Quotient.ind fun _ ↦ picClass_mul_inv)
  add_comm a b := Quotient.inductionOn₂ a b fun _ _ ↦ picClass_mul_comm

@[simp]
lemma LineBundle.picClass_mul : (L.mul M).picClass = L.picClass + M.picClass := rfl

lemma LineBundle.picClass_one : (one : LineBundle X Unit).picClass = 0 := rfl

lemma Pic.exists_picClass_eq (c : Pic X) : ∃ (ι : Type) (L : LineBundle X ι), L.picClass = c := by
  obtain ⟨ι, L⟩ := c
  exact ⟨ι, L, rfl⟩

/-- A line bundle with zero class in the Picard group has a nowhere vanishing section. -/
lemma LineBundle.exists_isFrame_of_picClass_eq_zero (h_zero : L.picClass = 0) :
    ∃ s : ι → PointFn X, L.IsFrame s :=
  (picClass_eq_iff.1 (h_zero.trans picClass_one.symm)).exists_isFrame
    ⟨1, by simp [IsFrame, IsSection, IsRegularOn]⟩

namespace Pic

/-- For p: Y → X, the homomorphism Pic X → Pic Y sending the class of a line bundle to the class
of its pull-back. -/
def pull : Pic X →+ Pic Y :=
  AddMonoidHom.mk' (Quotient.map (fun L ↦ ⟨L.fst, L.2.pull p⟩) fun _ _ ⟨_, h⟩ ↦ ⟨_, h.pull p⟩) <| by
    rintro ⟨L⟩ ⟨M⟩
    rfl

@[simp]
lemma pull_picClass : pull p K.picClass = (K.pull p).picClass := rfl

/-- Pull-back along `q ≫ p` is pull-back along `p` followed by pull-back along `q`. -/
lemma pull_comp (c : Pic X) : pull (q ≫ p) c = pull q (pull p c) := by
  obtain ⟨L⟩ := c
  rfl

@[simp]
lemma pull_id (c : Pic X) : pull (𝟙 X) c = c := by
  obtain ⟨L⟩ := c
  rfl

/-- The Picard group of the spectrum of a local ring `A` is trivial. -/
lemma eq_zero_of_isLocalRing (c : Pic (Spec A)) [IsLocalRing A] : c = 0 := by
  obtain ⟨ι, L, rfl⟩ := c.exists_picClass_eq
  -- As `A` is local, some member `L.opens i` of the cover is the whole of `Spec A`. So the trivial
  -- bundle is `L` restricted to the single chart `i`, where the transition function is 1.
  obtain ⟨i, hi⟩ := L.exists_landsIn (𝟙 (Spec A))
  have h_top : ⊤ ≤ L.opens i := by simpa [LandsIn] using hi
  rw [← picClass_one]
  exact picClass_eq_of_le (fun _ ↦ i) (fun _ ↦ h_top)
    fun _ _ B t _ ↦ (L.transition_self i B t (landsIn_top.mono h_top)).symm

end Pic

end PicardGroup

end New

end
