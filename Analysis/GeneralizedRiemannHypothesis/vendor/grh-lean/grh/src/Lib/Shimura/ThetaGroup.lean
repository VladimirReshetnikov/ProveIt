import Lib.Shimura.AbelianScheme.Pairings

/-!
# Lifts of morphisms to sections of line bundles, and theta structures on abelian schemes

A morphism `f : X' → X` and an isomorphism `f^* L ≅ L'` induce a map on global sections
`Φ : H⁰(L) → H⁰(L')`. Over a local ring `R`, these maps let translations of an abelian scheme act on
sections of a line bundle. For a theta structure on `N` indexed by a group `H`, it also gives a
bound on the exponent of `K([N])`, under further hypotheses.

## Main definitions and results

* `New.Variety.IsSectionLift`: `Φ` comes from some isomorphism `f^* L ≅ L'`;
  `New.Variety.IsTranslationLift` is the case of a translation; `New.Variety.coordSection` is the
  `j`-th coordinate section of a linear system.
* `New.Variety.exists_isSectionLift`, `New.Variety.IsSectionLift.picClass_eq`: a lift exists when
  `[L'] = f^* [L]`, and only then.
* `New.Variety.IsTranslationLift.mul`, `New.Variety.IsTranslationLift.pow`,
  `New.Variety.exists_isTranslationLift_iff`: lifts of translations multiply, and the translation by
  `z` lifts to `L`, over a local ring `R`, exactly when the pairing `New.Pic.pairing` of `[L]`
  vanishes on `z` and the identity, that is, when `z` lies in the kernel `K([L])`.
* `New.Variety.IsThetaStructure`: a linear system with coordinates indexed by a group `H`, permuted
  up to a cocycle by lifts of the maps `y ↦ ± y + η s`.
* `New.Variety.IsThetaStructure.pull_eq_of_picClass_eq`: rigidity of theta structures along a
  homomorphism.
* `New.Variety.IsThetaStructure.card_nsmul_eq_zero_of_isTranslationLift`: the order of `H` kills
  every section whose translation lifts to `N`, when `N` is a projective embedding; over a local
  ring these are the sections in `K([N])`.

Notions from other files:
* `New.LineBundle.pull`: the pull-back of the line bundle (U_i, g_ij) along p: Y → X, with cover
  p⁻¹U_i and transition functions p*g_ij.
* `New.LineBundle.IsLinearSystem`: L is a linear system, the model being g_ij = s_j / s_i on
  U_i = {s_i ≠ 0} for sections s_i without common zero.
* `New.HasConstFunctions`: for s : X → S, a function regular on all of X takes equal values at two
  ring-valued points with the same image under s.

## Relation to the literature

Known; see `Lib.Shimura.IntegralModel.UniversalFamily` for sources.
-/

namespace New.Variety

/-!
## Lifts of a morphism to global sections

A line bundle `New.LineBundle` is a cover `U i` with a cocycle `g i j` of functions on ring-valued
points (`New.PointFn`); a section `s` (`IsSection`) has each `s i` regular on `U i` (`IsRegularOn`),
with `s i = g i j * s j` on `U i ∩ U j`; it lies in `H0` if also `s i = 0` off `U i`; an isomorphism
`M ≅ L` is a frame (`New.LineBundle.IsFrame`) of `L.mul M.inv`.
-/

section SectionLifts

open CategoryTheory AlgebraicGeometry LineBundle PointFn Spec AddMonObj

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {X : Over (Spec (CommRingCat.of R))} {X' : Over (Spec (CommRingCat.of R'))} {ι κ : Type}
  (L' : LineBundle X'.left κ) (L : LineBundle X.left ι) (f : X'.left ⟶ X.left)
  (Φ : L.H0 R → L'.H0 R') {Y : Over (Spec (CommRingCat.of R))} (F : Y ⟶ X) (h : L.IsLinearSystem)
  {N : LineBundle Y.1 κ} (φ : R →+* R') (hf : f ≫ X.hom = X'.hom ≫ Spec.map (CommRingCat.ofHom φ))
  {M : LineBundle X'.left ι} (e : M = L.pull f)

/-- The map `Φ` on global sections is pull-back along `f` followed by `u`. Here `u` is a frame of
`L' ⊗ (f^* L)⁻¹`, that is, an isomorphism `f^* L ≅ L'`. At every point that lands in the chart `i`
of `L'` and whose image lands in the chart `a` of `L`, one has `(Φ s)_i = u_(i,a) · f^* s_a`. -/
@[simp]
def IsPullbackVia (u : κ × ι → PointFn X'.left) : Prop :=
  -- `u` trivialises `L' ⊗ (f^* L)⁻¹`
  (L'.mul (L.pull f).inv).IsFrame u ∧
  -- in local coordinates `Φ s` is `u` times the pull-back of `s`
  ∀ (s : L.H0 R) (i : κ) (a : ι) (B : CommRingCat) (t : Spec B ⟶ X'.left), LandsIn t (L'.opens i) →
    LandsIn (t ≫ f) (L.opens a) → (Φ s).val i B t = u (i, a) B t * s.val a B (t ≫ f)

/-- The condition that the map Φ : H⁰(L) → H⁰(L') is pull-back along f : X' → X followed by some
isomorphism f^*L ≅ L'. -/
def IsSectionLift : Prop := ∃ u : κ × ι → PointFn X'.left, IsPullbackVia L' L f Φ u

/-- The R-linear endomorphism Φ of H⁰(L) is pull-back along the translation t_z by the section z
followed by some isomorphism t_z^*L ≅ L. -/
abbrev IsTranslationLift [AddObj X]
    (z : MonoidalCategoryStruct.tensorUnit (Over (Spec (CommRingCat.of R))) ⟶ X)
    (Φ : Module.End R (L.H0 R)) : Prop :=
  IsSectionLift L L (translation z).left Φ

variable {L' L f Φ}

/-- For a linear system L on an R-scheme and an index j, the j-th coordinate as an element of
the R-module H⁰(L) of global sections. -/
def coordSection (j : ι) : L.H0 R :=
  ⟨fun i ↦ L.transition i j, h.isSection j, fun _ _ _ ht ↦ h.transition_eq_zero j ht⟩

lemma coordSection_val (i j : ι) : (coordSection h j).val i = L.transition i j :=
  rfl

lemma isSection_val (s : L.H0 R) : L.IsSection s.val :=
  s.prop.1

/-- Two sections of `L` are equal if they agree on each chart `L.opens i`. Only charts on which both
`i`-th components are regular need to be checked, and there they must agree at all points that land
in the chart. -/
lemma H0_ext {r s : L.H0 R}
    (h_agree : ∀ {i : ι}, (r.val i).IsRegularOn (L.opens i) → (s.val i).IsRegularOn (L.opens i) →
      ∀ (B : CommRingCat) (t : Spec B ⟶ X.left), LandsIn t (L.opens i) →
        r.val i B t = s.val i B t) :
    r = s := by
  obtain ⟨⟨hr_reg, -⟩, hr_zero⟩ := r.prop
  obtain ⟨⟨hs_reg, -⟩, hs_zero⟩ := s.prop
  ext i B t
  -- on `L.opens i` this is `h_agree`; off it the `i`-th components of both sections vanish
  by_cases ht : LandsIn t (L.opens i)
  · exact h_agree (hr_reg i) (hs_reg i) B t ht
  · rw [hr_zero i B t ht, hs_zero i B t ht]

@[local simp]
lemma H0_smul (a : R) (s : L.H0 R) (i : ι) (B : CommRingCat) (t : Spec B ⟶ X.left) :
    (a • s).val i B t = (preimage (t ≫ X.hom)).hom a * s.val i B t :=
  rfl

/-- A lift `Φ` along `f` from sections of `L` to sections of `L'` exists only if `[L'] = f^* [L]` in
the Picard group. -/
lemma IsSectionLift.picClass_eq : IsSectionLift L' L f Φ → L'.picClass = L.picClass.pull f :=
  fun ⟨u, hu_frame, _⟩ ↦ picClass_eq_iff.mpr ⟨u, hu_frame⟩

/-! ### Construction of lifts -/

/-- For f : X' → X lying over the ring map φ : R → R' and M = f^*L, the φ-semilinear pull-back
of global sections H⁰(L) → H⁰(M). -/
@[simps! apply_coe]
noncomputable def pullSections : L.H0 R →ₛₗ[φ] M.H0 R' where
  toFun s :=
    ⟨fun i ↦ PointFn.pull f (s.1 i), by
      subst e
      exact ⟨s.2.1.pull f, fun i A t ht ↦ s.2.2 i A (t ≫ f) ht⟩⟩
  map_add' s s' := by
    ext
    simp
  map_smul' a s := by
    ext i A t
    -- By `hf`, the image of `a` along `t ≫ f ≫ X.hom` is the image of `φ a` along `t ≫ X'.hom`.
    rw [H0_smul]
    simp [hf]
    simp [← Category.assoc]

/-- A frame `u` of `N ⊗ (F^* L)⁻¹` gives the `R`-linear map `s ↦ u * F^* s` on sections, which is
pull-back along `F` followed by `u`. -/
lemma exists_isPullbackVia (u : κ × ι → PointFn Y.left)
    (hu : (N.mul (L.pull F.left).inv).IsFrame u) :
    ∃ Φ : ↥(L.H0 R) →ₗ[R] ↥(N.H0 R), IsPullbackVia N L F.left Φ u := by
  obtain ⟨hu_sec, hu_unit⟩ := hu
  -- for each `s`: a section `r s` of `N` (`hr`) with `r s = u * F^* s` locally (`h_eq`)
  choose r hr h_eq _ using fun s : L.H0 R ↦
    exists_section_mul (𝟙 Y.left) hu_sec ((isSection_val s).pull F.left) (h_fibre := by simp)
  simp only [Category.comp_id] at h_eq
  -- it is additive and `R`-linear in `s`, as the local formula `h_eq` is
  refine ⟨⟨⟨fun s ↦ ⟨r s, hr s⟩, fun s s' ↦ ?_⟩, fun c s ↦ ?_⟩, ⟨hu_sec, hu_unit⟩, h_eq⟩
  all_goals
    refine H0_ext fun h₁ h₂ ↦ h₁.ext_of_dominant (𝟙 _) h₂ (L.pull F.left) fun a ↦ ?_
    simp +contextual [h_eq _ _ a, mul_add, mul_left_comm]

/-- If `[N] = F^* [L]` in the Picard group, there is an `R`-linear lift `Φ` of `F` from sections
of `L` to sections of `N`. -/
lemma exists_isSectionLift (h_cls : N.picClass = L.picClass.pull F.left) :
    ∃ Φ : L.H0 R →ₗ[R] N.H0 R, IsSectionLift N L F.left Φ := by
  -- an isomorphism `F^* L ≅ N` is a frame `u` of `N ⊗ (F^* L)⁻¹`
  obtain ⟨u, hu⟩ := picClass_eq_iff.mp h_cls
  obtain ⟨Φ, hΦ⟩ := exists_isPullbackVia F u hu
  exact ⟨Φ, u, hΦ⟩

/-- If a lift `Φ` along `f` sends each coordinate of `L` to `a` times the corresponding coordinate
of `L'`, then `f^* L = L'` as linear systems. -/
lemma IsSectionLift.pull_eq_of_coordSection {L' : LineBundle X'.left ι}
    (h' : L'.IsLinearSystem) {Φ : ↥(L.H0 R) → ↥(L'.H0 R')} {a : R'}
    (hΦ_lift : IsSectionLift L' L f Φ)
    (h_coord : ∀ j : ι, Φ (coordSection h j) = a • coordSection h' j) :
    L.pull f = L' := by
  obtain ⟨u, ⟨-, hu_unit⟩, hΦ⟩ := hΦ_lift
  -- two linear systems are equal once their coordinates are proportional at each point
  refine h'.ext_of_transition_eq_mul (h.pull f) fun i j k A t hi hj ↦ ?_
  -- the value of `Φ (coordSection h k)` at `t`, read on `L'` and on `L.pull f`
  let α : A := (preimage (t ≫ X'.hom)).hom a
  have h_val (k : ι) :
      α * L'.transition i k A t = u (i, j) A t * (L.pull f).transition j k A t :=
    calc α * L'.transition i k A t = (Φ (coordSection h k)).val i A t := by
          rw [h_coord, H0_smul, coordSection_val]
      _ = u (i, j) A t * (L.pull f).transition j k A t := hΦ (coordSection h k) i j A t hi hj
  -- at `k = i` this says `α = u (i, j) * transition j i`; cancel the unit `u (i, j)`
  have h_unit : IsUnit (u (i, j) A t) := hu_unit (i, j) A t (by tauto)
  rw [← h_unit.mul_right_inj, ← h_val, ← mul_assoc, ← h_val, L'.transition_self i A t hi, mul_one]

/-- Let `L` be a linear system on `X`, `F : Y ⟶ X`, and `s j` sections of `N` indexed like the
coordinates of `L`. Suppose that at each point in `N.opens i` whose image lies in `L.opens a`, (a)
some `s j` is a unit and (b) `s j = s a * F^* (L.transition a j)`. Then there is an `R`-linear lift
`Φ` of `F` that sends the `j`-th coordinate of `L` to `s j`. -/
lemma exists_isSectionLift_coordSection {s : ι → N.H0 R}
    (hs : ∀ (i : κ) (a : ι) (B : CommRingCat) (t : Spec B ⟶ Y.left), LandsIn t (N.opens i) →
      LandsIn (t ≫ F.left) (L.opens a) →
      (∃ j : ι, IsUnit ((s j).val i B t)) ∧
      ∀ j : ι, (s j).val i B t = (s a).val i B t * L.transition a j B (t ≫ F.left)) :
    ∃ Φ : L.H0 R →ₗ[R] N.H0 R,
      IsSectionLift N L F.left Φ ∧ ∀ j : ι, Φ (coordSection h j) = s j := by
  -- the components `(s a).val i` form a frame of `N ⊗ (F^* L)⁻¹`: by `hs` they transform
  -- correctly, and `(s a).val i` divides the unit `(s j).val i`
  have h_frame : (N.mul (L.pull F.left).inv).IsFrame fun (i, a) ↦ (s a).val i := by
    have h_sec (j : ι) : N.IsSection (s j).val := isSection_val (s j)
    simp_all [IsSection, IsRegularOn, IsFrame]
    grind
  obtain ⟨Φ, hΦ_frame, hΦ_eq⟩ := exists_isPullbackVia F (fun (i, a) ↦ (s a).val i) h_frame
  refine ⟨Φ, ⟨fun (i, a) ↦ (s a).val i, hΦ_frame, hΦ_eq⟩, fun j ↦ H0_ext fun {i} h₁ h₂ ↦
    h₁.ext_of_dominant (𝟙 _) h₂ (L.pull F.left) ?_⟩
  -- remove the identity and read the charts of `L.pull F.left` on `L`; then compare with `hs`
  simp
  intro a B t ht hta
  rw [hΦ_eq (coordSection h j) i a B t ht hta, coordSection_val, ((hs i a B t ht hta).2 j).symm]

/-- The pull-back of sections `pullSections φ hf e` along `f` is a lift of `f` from sections of `L`
to sections of `M = f^* L`. -/
lemma isSectionLift_pullSections : IsSectionLift M L f (pullSections φ hf e) := by
  -- The isomorphism is the identity of `M = L.pull f`, given by the transition functions of `M`;
  -- in local coordinates this is the cocycle rule of a section `s` of `L`.
  subst e
  refine ⟨(L.pull f).transition.uncurry, ?_, fun s i a B t ↦ ?_⟩
  · simp_all [L.regular _ _ _, LineBundle.transition_trans, isUnit_transition, mul_right_comm,
      IsFrame, IsSection, IsRegularOn]
  · obtain ⟨⟨-, hs_cocycle⟩, -⟩ := s.prop
    exact hs_cocycle i a B (t ≫ f)

/-! ### Composition, uniqueness and injectivity -/

/-- The pull-back of the `i`-th coordinate section of `L` is the `i`-th coordinate section of the
pulled-back linear system `M`, where `e : M = L.pull f`. -/
lemma pullSections_coordSection (i : ι) :
    pullSections φ hf e (coordSection h i) = coordSection (e ▸ h.pull f) i := by
  aesop

/-- Here `IsSectionLift L' L f Φ` means that `Φ : H⁰(L) → H⁰(L')` is pull-back of sections along
`f : X' ⟶ X` followed by some isomorphism `f^*L ≅ L'`. If `Θ` lifts `g : X'' ⟶ X'` from sections of
`L'` to sections of `L''` (over `R''`), and `Φ` lifts `f : X' ⟶ X` from sections of `L` to sections
of `L'`, then `Θ ∘ Φ` lifts the composite `g ≫ f` from sections of `L` to sections of `L''`. -/
lemma IsSectionLift.comp {X'' : Over (Spec (CommRingCat.of R''))} {μ : Type}
    {L'' : LineBundle X''.left μ} {g : X''.left ⟶ X'.left} {Θ : ↥(L'.H0 R') → ↥(L''.H0 R'')}
    (hΘ : IsSectionLift (R' := R'') (X' := X'') (κ := μ) L'' L' g Θ)
    (hΦ : IsSectionLift L' L f Φ) :
    IsSectionLift L'' L (g ≫ f) (Θ ∘ Φ) := by
  obtain ⟨v, hv⟩ := hΘ
  obtain ⟨u, hu⟩ := hΦ
  -- Let `T` be the trivial bundle on the cover of `L'.pull g`. The products
  -- `v (i, b) * g^* u (b, a)` form a frame of `M ⊗ T⁻¹`, where `M = L'' ⊗ ((g ≫ f)^* L)⁻¹`.
  let T : LineBundle X''.left κ := mk _ 1 (L'.pull g).cover
  let M := L''.mul (L.pull (g ≫ f)).inv
  have h_frame : ((M.mul T.inv).pull (𝟙 _)).IsFrame
      fun ((i, a), b) ↦ v (i, b) * pull g (u (b, a)) := by
    simp [M, T, IsFrame, IsSection, IsRegularOn] at hu hv ⊢
    grind [L'.transition_trans]
  -- Applied to the frame `1` of `T`, they glue to a frame `w` of `M`.
  have h_one : T.IsFrame 1 := by simp [T, IsFrame, IsSection, IsRegularOn]
  obtain ⟨w, ⟨⟨hw_reg, -⟩, -⟩, hw_eq, hw_frame⟩ :=
    exists_section_mul (𝟙 X''.left) h_frame.left h_one.left (h_fibre := by simp)
  refine ⟨w, hw_frame h_frame h_one, fun s i a ↦ ?_⟩
  -- Both sides are regular on `M.opens (i, a)`, and on the `b`-th member of the cover of
  -- `L'.pull g` both are `v (i, b) * g^* u (b, a) * (g ≫ f)^* s`.
  obtain ⟨⟨hΘΦ_reg, -⟩, -⟩ := (Θ (Φ s)).prop
  obtain ⟨⟨hs_reg, -⟩, -⟩ := s.prop
  have h_left : ((Θ (Φ s)).val i).IsRegularOn (M.opens (i, a)) := (hΘΦ_reg i).mono inf_le_left
  have h_right : (w (i, a) * pull (g ≫ f) (s.val a)).IsRegularOn (M.opens (i, a)) :=
    ((hw_reg (i, a)).mul ((hs_reg a).pull (g ≫ f))).mono (le_inf le_rfl inf_le_right)
  have h_local (b : κ) (A : CommRingCat) (t : Spec A ⟶ X''.left)
      (ht : LandsIn (t ≫ 𝟙 X''.left) (M.opens (i, a))) (htb : LandsIn t ((L'.pull g).opens b)) :
      (Θ (Φ s)).val i A (t ≫ 𝟙 X''.left) =
        (w (i, a) * pull (g ≫ f) (s.val a)) A (t ≫ 𝟙 X''.left) := by
    simp [M, T, IsFrame, IsSection, IsRegularOn] at hu hv hw_eq ht htb ⊢
    grind
  simpa [M] using h_left.ext_of_dominant (𝟙 _) h_right (L'.pull g) h_local

/-- If X' is a commutative group scheme over R' whose global functions are constant, two maps
Φ, Ψ: H⁰(L) → H⁰(L'), each pull-back along f followed by some isomorphism f^*L ≅ L', are
proportional: Φ(s) = cΨ(s) for all s, for some c in R'. -/
lemma IsSectionLift.exists_eq_smul {Ψ : L.H0 R → L'.H0 R'} [AddObj X']
    (hX : HasConstFunctions X'.hom) (hΦ_lift : IsSectionLift L' L f Φ)
    (hΨ_lift : IsSectionLift L' L f Ψ) :
    ∃ c : R', ∀ s : L.H0 R, Φ s = c • Ψ s := by
  obtain ⟨u, hu, hΦ⟩ := hΦ_lift
  obtain ⟨v, hv, hΨ⟩ := hΨ_lift
  -- The two frames differ by a global function: `u = c * v`; take its value at the zero section.
  obtain ⟨c, hc⟩ := hv.exists_eq_mul hu.left
  let zero : Spec (.of R') ⟶ X'.left := (0 : Over.mk (𝟙 _) ⟶ X').left
  refine ⟨PointFn.ofSection c _ zero, fun s ↦ H0_ext fun {i} h₁ h₂ ↦
    h₁.ext_of_dominant (𝟙 _) h₂ (L.pull f) fun a B t hi ha ↦ ?_⟩
  -- `c` is constant on fibres, so its value at `t` is the image of its value at zero.
  have hconst :
      (preimage (t ≫ X'.hom)).hom (PointFn.ofSection c _ zero) = PointFn.ofSection c B t := by
    simp [zero, ← isRegularOn_ofSection _ _, hX c _ _ t]
  rw [Category.comp_id] at hi ⊢
  have h_lands : LandsIn t ((L'.mul (L.pull f).inv).opens (i, a)) := by tauto
  simp [hconst, hΦ s i a B t hi ha, hΨ s i a B t hi ha, hc (i, a) B t h_lands, mul_assoc]

/-- A lift along a quasi-compact, scheme-theoretically dominant morphism `f` is injective: a section
is determined by its pull-back along `f`. -/
lemma IsSectionLift.injective [IsSchemeTheoreticallyDominant f] [QuasiCompact f]
    (hΦ : IsSectionLift L' L f Φ) :
    Φ.Injective := by
  obtain ⟨u, ⟨-, hu_unit⟩, hΦ_eq⟩ := hΦ
  intro s s' h_eq
  -- as `f` is dominant it suffices to compare the pull-backs of `s` and `s'` along `f`;
  -- these agree after multiplication by the unit `u`
  refine H0_ext fun {i} h₁ h₂ ↦ h₁.ext_of_dominant f h₂ L' fun a A t hti hta ↦ ?_
  have h_pull : u (a, i) A t * s.val i A (t ≫ f) = u (a, i) A t * s'.val i A (t ≫ f) := by
    rw [← hΦ_eq s a i A t hta hti, ← hΦ_eq s' a i A t hta hti, h_eq]
  exact (hu_unit (a, i) A t (by tauto)).mul_right_inj.mp h_pull

end SectionLifts

/-!
## Lifts of translations and theta structures

Rigidity and the bound on `K([N])` reduce to `New.Variety.IsThetaStructure.pull_eq_of_intertwines`.
-/

section ThetaStructure

open CategoryTheory AlgebraicGeometry CartesianMonoidalCategory Over Submodule Module Set AddChar
open scoped MonoidalCategory

attribute [local instance low] Fintype.ofFinite
open Nat (card)

variable {R : Type} [CommRing R] {A : Over (Spec ⟨R⟩)} {ι : Type}
  {L : LineBundle A.1 ι} [AddObj A] {z : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A}
  {Φ : Module.End R ↥(L.H0 R)} {H : Type} [AddCommGroup H]

/-- Lifts `Φ` and `Ψ` of the translations by `z` and by `w` compose to the lift `Φ * Ψ` of the
translation by `z + w`. -/
lemma IsTranslationLift.mul {w : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A}
    {Ψ : Module.End R ↥(L.H0 R)} (hΦ : IsTranslationLift L z Φ) (hΨ : IsTranslationLift L w Ψ) :
    IsTranslationLift L (z + w) (Φ * Ψ) := by
  simpa [← comp_left, add_assoc, IsTranslationLift, comp_add, Module.End.coe_mul] using hΦ.comp hΨ

lemma IsTranslationLift.pow (hΦ : IsTranslationLift L z Φ) (k : ℕ) :
    IsTranslationLift L (k • z) (Φ ^ k) := by
  induction k with
  | zero =>
    -- the pull-back of sections along the identity is the identity map `1`
    have h_id : ⇑(pullSections (f := 𝟙 A.left) (RingHom.id R) (by simp) (.refl L) :
        L.H0 R →ₗ[R] L.H0 R) = ⇑(1 : Module.End R (L.H0 R)) := by
      ext s i B t
      exact congrArg (s.val i B) (Category.comp_id t)
    simpa [IsTranslationLift, ← h_id] using
      isSectionLift_pullSections (f := 𝟙 A.left) (RingHom.id R) (by simp) (.refl L)
  | succ k ih => simpa [succ_nsmul, pow_succ] using ih.mul hΦ

/-- The translation by `z` lifts to `L` if and only if `z ∈ K([L])`, that is, the class
`⟨z, 𝟙 A⟩ = t_z^*[L] - [L]` vanishes in `Pic A`; the terms pulled back from the base are trivial
over the local ring `R`. -/
lemma exists_isTranslationLift_iff [IsLocalRing R] :
    (∃ Φ : Module.End R ↥(L.H0 R), IsTranslationLift L z Φ) ↔
      L.picClass.pairing (toUnit A ≫ z) (𝟙 A) = 0 := by
  -- both sides say that the translation by `z` keeps the class of `L`
  have h_cls : (∃ Φ : Module.End R ↥(L.H0 R), IsTranslationLift L z Φ) ↔
      L.picClass = L.picClass.pull (translation z).left :=
    ⟨fun ⟨_, hΦ⟩ ↦ hΦ.picClass_eq, exists_isSectionLift (translation z)⟩
  -- the pairing is `t_z^*[L] - [L]`: the terms at the section `z` and at `0` vanish
  have h_pair : L.picClass.pairing (toUnit A ≫ z) (𝟙 A) =
      L.picClass.atPoint (translation z) - L.picClass.atPoint (𝟙 A) := by
    simp [Pic.pairing, atPoint_toUnit_comp_eq_zero, atPoint_zero, add_comm]
  rw [h_cls, h_pair, Pic.atPoint, Pic.atPoint, Over.id_left, Pic.pull_id, sub_eq_zero, eq_comm]

/-! ### Theta structures -/

/-- A theta structure on a linear system `N` on `A` whose coordinates `X t = coordSection hN t` are
indexed by an abelian group `H` of order invertible in `R`. Each map `y ↦ ± y + η s` has a lift
to `N` that sends `X t` to `c s t • X (±(s + t))`, where `c s` is a character of `H` and
`c s (-t) = c t s`. For the subgroup `Lg`: `X s = X 0` for `s ∈ Lg`, and the sum of `c s l ^ 2`
over `l ∈ Lg` vanishes for `s ∉ Lg`. -/
structure IsThetaStructure (Lg : AddSubgroup H)
    (η : H →+ (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A))
    {N : LineBundle A.left H} (hN : N.IsLinearSystem) (c : H → AddChar H R) where
  /-- The symmetry `c s (-t) = c t s` of the cocycle `c`. -/
  neg_eq_swap (s t : H) : c s (-t) = c t s
  /-- The theta law: the map `y ↦ ± y + η s` has a lift to `N` that sends the coordinate `X t` to
  `c s t • X (±(s + t))`. -/
  theta_law (m : ℤˣ) (s : H) : ∃ Φ : Module.End R (N.H0 R),
    IsSectionLift N N (((m : ℤ) • 𝟙 A) ≫ translation (η s)).left Φ ∧
    ∀ t : H, Φ (coordSection hN t) = c s t • coordSection hN ((m : ℤ) • (s + t))
  /-- The coordinates indexed by `Lg` all equal `X 0`. -/
  coordSection_eq_of_mem : ∀ s ∈ Lg, coordSection hN s = coordSection hN 0
  /-- The order of `H` is a unit of `R`. -/
  isUnit_card : IsUnit (card H : R)
  /-- For `s ∉ Lg` the sum of `c s l ^ 2` over `l ∈ Lg` vanishes. -/
  sum_sq_eq_zero [Fintype Lg] : ∀ s ∉ Lg, ∑ l : Lg, c s l ^ 2 = 0

variable {Lg : AddSubgroup H} {η : H →+ (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A)}
  {N : LineBundle A.left H} {hN : N.IsLinearSystem} {c : H → AddChar H R}

/-- Write `X t` and `X' t` for the coordinates `coordSection hN t` and `coordSection hN' t` of the
theta structures `h` and `h'`. Assume that the coordinates of `N` span `H⁰(N)` (`h_span`). Let
`U s` send `X t` to `c s t • X (s + t)`, and let `T : H⁰(N') → H⁰(N)` be a lift of `f : A ⟶ A'` with
`T (X' s) = U s (T (X' 0))` for all `s`. Then `f^* N' = N` as linear systems. -/
lemma IsThetaStructure.pull_eq_of_intertwines (h : IsThetaStructure Lg η hN c) [Finite H]
    (h_span : span R (range (coordSection hN)) = ⊤)
    {A' : Over (Spec (CommRingCat.of R))} [AddObj A']
    {η' : H →+ (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A')}
    {N' : LineBundle A'.left H} {hN' : N'.IsLinearSystem} {c' : H → AddChar H R}
    (h' : IsThetaStructure Lg η' hN' c') {f : A.left ⟶ A'.left}
    {T : ↥(N'.H0 R) → ↥(N.H0 R)} {U : H → Module.End R (N.H0 R)}
    (hU : ∀ s t : H, U s (coordSection hN t) = c s t • coordSection hN (s + t))
    (hT : IsSectionLift N N' f T)
    (h_intertwine : ∀ s : H, T (coordSection hN' s) = U s (T (coordSection hN' 0))) :
    N'.pull f = N := by
  -- It is enough that `T (X' 0)` is a multiple `a • X 0`: by `h_intertwine` and `hU`, `T` then
  -- sends `X' s` to `a • X s`. To find `a`, apply the sum `P` of the `U (-l)`, `l ∈ Lg`, to
  -- `T (X' 0)`. First apply `U t` to `X l = X 0`.
  have h_shift (l : H) (hl : l ∈ Lg) (t : H) :
      coordSection hN (t + l) = c t (-l) • coordSection hN t := by
    -- `U t` sends `X l = X 0` to `c t l • X (t + l)` and to `c t 0 • X t = X t`
    have h_Ut : c t (-l) • U t (coordSection hN l) = c t (-l) • U t (coordSection hN 0) := by
      rw [h.coordSection_eq_of_mem l hl]
    simpa [hU, ← map_add_eq_mul, smul_smul] using h_Ut
  let P : End R (N.H0 R) := ∑ l : Lg, U (-l)
  -- by `h_shift`, `P` multiplies `X t` by `∑ l, c t l ^ 2`, which is `0` for `t ∉ Lg`
  -- (`h.sum_sq_eq_zero`); for `t ∈ Lg` the coordinate `X t` is `X 0`
  have hP_coord (t : H) : P (coordSection hN t) ∈ R ∙ coordSection hN 0 := by
    by_cases ht : t ∈ Lg
    · simp_all [P, h.coordSection_eq_of_mem, nsmul_mem]
    · simp_all [P, ← sq, h.sum_sq_eq_zero, ← h.neg_eq_swap t, add_comm _ t, ← Finset.sum_smul,
        smul_smul]
  -- the coordinates span, so the image of `P` lies in the line through `X 0`
  have h_le : span R (range (coordSection hN)) ≤ (R ∙ coordSection hN 0).comap P :=
    span_le.mpr (forall_mem_range.mpr hP_coord)
  have hP : P (T (coordSection hN' 0)) ∈ R ∙ coordSection hN 0 := h_le (h_span.ge mem_top)
  -- `U (-l) (T (X' 0)) = T (X' (-l)) = T (X' 0)`, so `P` multiplies `T (X' 0)` by the order of
  -- `Lg`, a unit of `R`
  have h_unit : IsUnit (card Lg : R) :=
    isUnit_of_dvd_unit Lg.card_addSubgroup_dvd_card.natCast h.isUnit_card
  obtain ⟨a, ha⟩ : ∃ a : R, a • coordSection hN 0 = T (coordSection hN' 0) := by
    rw [← mem_span_singleton, ← smul_mem_iff_of_isUnit _ h_unit]
    simpa [P, ← h_intertwine, h'.coordSection_eq_of_mem, Nat.cast_smul_eq_nsmul] using hP
  -- a lift of `f` that sends each `X' s` to `a • X s` forces `f^* N' = N`
  have h_coord (s : H) : T (coordSection hN' s) = a • coordSection hN s := by
    simpa [← ha, hU] using h_intertwine s
  exact hT.pull_eq_of_coordSection hN' hN h_coord

/-- Rigidity. Let `N` on `A` and `N'` on `A'` be theta structures over the ring `R` for the same
finite group `H` of odd order and the same subgroup `Lg`. Assume that global functions on `A` are
constant on the fibres over `R` (`h_const`) and that the coordinates of `N` span `H⁰(N)` (`h_span`).
If a homomorphism `f: A ⟶ A'` carries `η` to `η'` and `[N] = f^* [N']` in the Picard group, then
`f^* N' = N` as linear systems: `f` matches the coordinates. -/
lemma IsThetaStructure.pull_eq_of_picClass_eq (h : IsThetaStructure Lg η hN c) [Finite H]
    (h_const : HasConstFunctions A.hom) (h_span : span R (range (coordSection hN)) = ⊤)
    {A' : Over (Spec (CommRingCat.of R))} [AddObj A']
    {η' : H →+ (𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A')}
    {N' : LineBundle A'.left H} {hN' : N'.IsLinearSystem} {c' : H → AddChar H R}
    (h' : IsThetaStructure Lg η' hN' c') (h_odd : Odd (card H)) (f : A ⟶ A') [IsAdditive f]
    (hη : ∀ s : H, η s ≫ f = η' s) (h_cls : N.picClass = N'.picClass.pull f.left) :
    N'.pull f.left = N := by
  -- Take a lift `T` of `f`. It intertwines the lifts `U' m s` and `U m s` up to scalars, which
  -- cancel in the relation `h_rel` between `U 1 (s + s)`, `U 1 s` and `U (-1) 0`. As `card H` is
  -- odd, every element of `H` is some `s + s`, and `pull_eq_of_intertwines` applies.
  obtain ⟨T, hT⟩ := exists_isSectionLift f h_cls
  choose U hU U_coord using h.theta_law
  choose U' hU' U'_coord using h'.theta_law
  -- By `hη`, `T ∘ U' m s` and `U m s ∘ T` lift the same map `A ⟶ A'`, so they are proportional.
  have h_scalar (m : ℤˣ) (s : H) : ∃ b : R, ∀ v, T (U' m s v) = b • U m s (T v) := by
    -- `f` is additive and carries `η s` to `η' s`, so it intertwines `y ↦ m y + η s` on `A` and
    -- `y ↦ m y + η' s` on `A'`
    have h_map : (((m : ℤ) • 𝟙 A) ≫ translation (η s)).left ≫ f.left =
        f.left ≫ (((m : ℤ) • 𝟙 A') ≫ translation (η' s)).left := by
      simp [← comp_left, hη, AddGrpObj.zsmul_comp, comp_add, add_comp]
    have h_lift : IsSectionLift N N' (f.left ≫ (((m : ℤ) • 𝟙 A') ≫ translation (η' s)).left)
        (U m s ∘ T) := by simpa only [h_map] using (hU m s).comp hT
    exact (hT.comp (hU' m s)).exists_eq_smul h_const h_lift
  choose b hb using h_scalar
  -- Both sides send the coordinate `coordSection hN t` to a multiple of `coordSection hN (s - t)`.
  have h_rel (s : H) : U 1 (s + s) * U (-1) 0 * U 1 s = U 1 s * U (-1) 0 := by
    refine LinearMap.ext_on_range h_span ?_
    -- The scalars agree, since each `c s` is a character of `H` and `c s (-t) = c t s`.
    have h_coeff (t : H) :
        c s t * (c 0 (s + t) * c (s + s) (-s + -t)) = c 0 t * c s (-t) := by
      grind only [IsThetaStructure, map_add_eq_mul, add_neg_cancel]
    simp [U_coord, smul_smul, h_coeff]
  -- Moving `T` to the right gives the scalar `b 1 s * b (-1) 0` on both sides.
  have h_transfer (s : H) (v : N'.H0 R) :
      T (U' 1 s (U' (-1) 0 v)) = U 1 (s + s) (T (U' (-1) 0 (U' 1 s v))) := by
    have h_rel_T : (b 1 s * b (-1) 0) • U 1 s (U (-1) 0 (T v)) =
        (b 1 s * b (-1) 0) • U 1 (s + s) (U (-1) 0 (U 1 s (T v))) := by
      rw [← Module.End.mul_apply, ← h_rel s]
      rfl
    simpa only [hb, map_smul, smul_smul, mul_comm] using h_rel_T
  have hU_one (s t : H) : U 1 s (coordSection hN t) = c s t • coordSection hN (s + t) := by
    simpa using U_coord 1 s t
  -- as `card H` is odd, every element of `H` is `s + s` for some `s`
  have h_two : Function.Surjective fun s : H ↦ 2 • s :=
    h_odd.coprime_two_right.nsmul_right_bijective.surjective
  refine h.pull_eq_of_intertwines h_span h' hU_one hT (h_two.forall.mpr fun s ↦ ?_)
  -- At `v = coordSection hN' (-s)` both sides carry the unit `c' s s`.
  simpa [U'_coord, h'.neg_eq_swap, two_smul, ((c' s).val_isUnit s).smul_left_cancel] using
    h_transfer s (coordSection hN' (-s))

/-- Let `N` be a theta structure on `A` over the ring `R`, indexed by the finite group `H`, which is
a projective embedding. Assume that global functions on `A` are constant on the fibres over `R`
(`h_const`), and that the coordinates of `N` span `H⁰(N)` (`h_span`). If the translation by a
section `y` lifts to `N` (when `R` is local, this means `y ∈ K([N])`), then `y` is killed by the
order of `H`. -/
lemma IsThetaStructure.card_nsmul_eq_zero_of_isTranslationLift (h : IsThetaStructure Lg η hN c)
    [Finite H] (h_const : HasConstFunctions A.hom) (h_span : span R (range (coordSection hN)) = ⊤)
    (hE : N.IsProjEmbedding A.hom) {y : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A}
    {Ψ : Module.End R ↥(N.H0 R)} (hΨ : IsTranslationLift N y Ψ) :
    card H • y = 0 := by
  -- Put `n = card H`. The lift `Ψ ^ n` of the translation by `n • y` satisfies the hypothesis of
  -- `pull_eq_of_intertwines`, so this translation keeps the coordinates; and `N` is an embedding.
  -- `U s` lifts the translation by `η s` and acts on coordinates by the theta law.
  have h_law : ∀ s : H, ∃ Φ : Module.End R (N.H0 R), IsTranslationLift N (η s) Φ ∧
      ∀ t : H, Φ (coordSection hN t) = c s t • coordSection hN (s + t) := by
    simpa using h.theta_law 1
  choose U hU U_coord using h_law
  have h_comm (s : H) :
      (Ψ ^ card H) (coordSection hN s) = U s ((Ψ ^ card H) (coordSection hN 0)) := by
    -- `Ψ ^ n` and `(Ψ * U s) ^ n` lift the same translation, because `n • η s = 0`; two lifts of
    -- one map are proportional (`IsSectionLift.exists_eq_smul`).
    have h_lift : IsTranslationLift N (card H • y) ((Ψ * U s) ^ card H) := by
      simpa [← map_nsmul, IsTranslationLift] using (hΨ.mul (hU s)).pow (card H)
    obtain ⟨a, ha⟩ := (hΨ.pow (card H)).exists_eq_smul h_const h_lift
    -- So `Ψ ^ n` commutes with `Ψ * U s`; evaluate at `coordSection hN 0` and cancel `Ψ`.
    have h_commute : Commute (Ψ ^ card H) (Ψ * U s) := by
      rw [show Ψ ^ card H = a • (Ψ * U s) ^ card H from LinearMap.ext ha]
      exact (Commute.pow_self (Ψ * U s) (card H)).smul_left a
    apply hΨ.injective
    simpa [U_coord, pow_mul_comm', ← mul_assoc] using
      LinearMap.congr_fun h_commute.eq (coordSection hN 0)
  have h_pull : N.pull (translation (card H • y)).left = N :=
    h.pull_eq_of_intertwines h_span h U_coord (hΨ.pow (card H)) h_comm
  -- maps into `A` over `R` that pull `N` back to the same linear system are equal (`hE.ext`)
  have h_transl : translation (card H • y) = 𝟙 A := OverMorphism.ext (hE.ext h_pull (w _))
  simpa [comp_add] using y ≫= h_transl

end ThetaStructure

end New.Variety
