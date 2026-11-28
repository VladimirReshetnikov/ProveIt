import Lib.Adelic.Unitary.Defs
import Lib.Cohomology.Etale.Basic
import Lib.General.Geometry.ProjectiveSpace
import Lib.General.NumberTheory.EmbeddingsAndDifferent
import Lib.Shimura.AbelianScheme.Basic

/-!
# Pairings of line bundle classes on abelian schemes and their fpqc descent

This file studies classes of line bundles on commutative group schemes and abelian schemes. Line
bundles are cocycles (`New.LineBundle`), and `New.Pic` is written additively. For a class `c` and
points `x`, `y`, the pairing `New.Pic.pairing c x y` is the class (x + y)^*c − x^*c − y^*c + 0^*c.
The file proves rules for the pairing, a quasi-finiteness criterion, and stability of abelian
schemes under base change. It also treats the descent of identities between pairings along an fpqc
cover.

## Main definitions and results

* `New.Variety.locallyQuasiFinite_of_pull_picClass`: a map that pulls a class back to a nonzero
  multiple of an embedding class is locally quasi-finite.
* `New.Pic.ParallelogramLaw.pairing_nsmul_left`, `New.Variety.pairing_comm`,
  `New.Variety.pairing_comp`: rules for the pairing.
* `New.Variety.pull_nsmul_eq_sq_smul`: over a local ring, multiplication by `m` pulls `c` back to
  `m² c` if `c` satisfies the parallelogram law.

Notions from other files:
* `New.Pic.atPoint`: For c in Pic A and a T-point x of A, the pull-back x^*c in Pic T.
* `New.Pic.ParallelogramLaw`: (x + y)^*c + (x − y)^*c + 2·0^*c = 2(x^*c + y^*c) for all points.
* `New.IsAbelianScheme`: a commutative group scheme A over S is abelian if it is smooth and proper
  over S and multiplication by every m ≠ 0 is surjective.
* `New.LineBundle.IsProjEmbedding L s`: `L` embeds `X` in projective space over `S`: it is a linear
  system, `s` is proper, and points of one chart with the same coordinates and the same image in `S`
  are equal.

## Relation to the literature

Known; see `Lib.Shimura.AbelianScheme.IsogenyFlatness` for sources.
-/

/-! ## Quasi-finiteness, rules for the pairing, and multiplication by m -/

namespace New

open CategoryTheory Over AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory AffineSpace
  LineBundle Pic IsFinite MorphismProperty

variable {S : Scheme} {A B T : Over S}

/-- Let N be a linear system separating the points of A, proper over S, and let B be separated
over S. An S-morphism f : A → B with f^*c = m[N] for some c in Pic B and m ≠ 0 is locally
quasi-finite. -/
lemma Variety.locallyQuasiFinite_of_pull_picClass [IsSeparated B.hom] {ι : Type} {c : Pic B.left}
    {m : ℕ} {N : LineBundle A.left ι} (hN : N.IsProjEmbedding A.hom) {f : A ⟶ B} (hm : m ≠ 0)
    (hf : Pic.pull f.left c = m • N.picClass) :
    LocallyQuasiFinite f.left := by
  -- On a fibre `X` of `f` the embedding system `N.pow m` is a trivial bundle, so its sections are
  -- global functions. They embed `X` as a closed subscheme of affine space, so `X` is affine.
  have hN_pow : (N.pow m).IsProjEmbedding A.hom := hN.pow hm
  have h_lin : (N.pow m).IsLinearSystem := hN_pow.isLinearSystem
  have hA_proper : IsProper A.hom := hN.isProper
  have hf_proper : IsProper f.left := by
    have h_comp : IsProper (f.left ≫ B.hom) := by rwa [f.w]
    exact IsProper.of_comp f.left B.hom
  refine locallyQuasiFinite_iff_isFinite_fiber.mpr fun b ↦ ?_
  suffices h_fibre_finite : ∀ {X : Scheme} {p : X ⟶ A.left} {s : X ⟶ Spec (B.left.residueField b)},
      IsPullback p s f.left (B.left.fromSpecResidueField b) → IsFinite s from
    h_fibre_finite (IsPullback.of_hasPullback f.left (B.left.fromSpecResidueField b))
  intro X p s h_fibre
  have hs_proper : IsProper s := of_isPullback h_fibre hf_proper
  refine iff_isProper_and_isAffineHom.mpr ⟨hs_proper, ?_⟩
  -- The class of `N.pow m` on `X` comes from the spectrum of a field, so it vanishes.
  have h_class : ((N.pow m).pull p).picClass = 0 := by
    simpa [c.pull_comp, ← picClass_pow, eq_zero_of_isLocalRing, hf] using
      congrArg (fun g ↦ Pic.pull g c) h_fibre.w
  obtain ⟨u, hu⟩ : ∃ u : (Fin m → ι) → PointFn X, ((N.pow m).pull p).IsFrame u :=
    exists_isFrame_of_picClass_eq_zero h_class
  -- The `j`-th section of the system is a global function `a j` times the frame `u`.
  have h_coords (j : Fin m → ι) : ∃ a : Γ(X, ⊤), ∀ (i : Fin m → ι) (R : CommRingCat)
      (t : Spec R ⟶ X), LandsIn t (((N.pow m).pull p).opens i) →
        ((N.pow m).pull p).transition i j R t = (PointFn.ofSection a * u i) R t :=
    hu.exists_eq_mul ((h_lin.pull p).isSection j)
  choose a ha using h_coords
  -- `s` factors as `homOfVector s a` followed by the structure map of affine space.
  rw [← homOfVector_over s a] at h_fibre hs_proper ⊢
  -- Two points with the same image pull back the same system, and `N.pow m` separates points.
  have h_mono : Mono (homOfVector s a) := by
    refine ⟨fun {Z} x y hxy ↦ ?_⟩
    have h_val (l : Fin m → ι) (R : CommRingCat) (t : Spec R ⟶ Z) :
        PointFn.ofSection (a l) R (t ≫ x) = PointFn.ofSection (a l) R (t ≫ y) := by
      rw [← homOfVector_appTop_coord s a l, PointFn.ofSection_appTop, PointFn.ofSection_appTop,
        Category.assoc, Category.assoc, hxy]
    have h_base : (x ≫ p) ≫ A.hom = (y ≫ p) ≫ A.hom := by
      simp only [← f.w, Category.assoc, h_fibre.w_assoc, reassoc_of% hxy]
    suffices h_pull : (N.pow m).pull (x ≫ p) = (N.pow m).pull (y ≫ p) from
      h_fibre.hom_ext (hN_pow.ext h_pull h_base) (by rw [reassoc_of% hxy])
    refine (h_lin.pull _).ext_of_transition_eq_mul (h_lin.pull _) fun i j k R t hi hj ↦ ?_
    simp only [pull_opens, landsIn_preimage, pull_transition, PointFn.pull, Pi.mul_apply,
      ← Category.assoc] at ha hi hj ⊢
    have h_one : PointFn.ofSection (a i) R (t ≫ y) * u i R (t ≫ y) = 1 := by
      rw [← ha i i R (t ≫ y) hi, (N.pow m).transition_self i R _ hi]
    show (N.pow m).transition j k R ((t ≫ x) ≫ p) =
      (N.pow m).transition j i R ((t ≫ x) ≫ p) * (N.pow m).transition i k R ((t ≫ y) ≫ p)
    rw [ha k j R (t ≫ x) hj, ha i j R (t ≫ x) hj, ha k i R (t ≫ y) hi, h_val k, h_val i]
    linear_combination -(PointFn.ofSection (a k) R (t ≫ y) * u j R (t ≫ x)) * h_one
  have h_proper : IsProper (homOfVector s a) :=
    IsProper.of_comp _ (𝔸(Fin m → ι; Spec (B.left.residueField b)) ↘ Spec (B.left.residueField b))
  have h_closed_imm : IsClosedImmersion (homOfVector s a) :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨h_proper, h_mono⟩
  -- A closed immersion followed by the structure map of affine space is affine.
  infer_instance

variable [AddObj A]
  {c : Pic A.left} {S' : Scheme} (b : S' ⟶ S)
  {O : Type} [CommRing O] [ModuleObj O A] (x y z : T ⟶ A) (m : ℕ)

/-! ### The pairing of a class that satisfies the parallelogram law -/

/-- If `c` satisfies the parallelogram law, its pairing `⟨·, ·⟩` (`New.Pic.pairing`) satisfies
`⟨x + y, z⟩ + ⟨x - y, z⟩ = 2 ⟨x, z⟩` for `T`-points `x`, `y`, `z` of `A`. -/
lemma Pic.ParallelogramLaw.pairing_add_add_pairing_sub (hc : c.ParallelogramLaw) (x y z : T ⟶ A) :
    c.pairing (x + y) z + c.pairing (x - y) z = 2 • c.pairing x z := by
  grind [pairing, ParallelogramLaw, sub_add_eq_add_sub]

/-- If c in Pic A satisfies the parallelogram law on a commutative group scheme A over S, then ⟨mx,
y⟩ = m⟨x, y⟩ in Pic T for T-points x, y and natural m, where ⟨x,
y⟩ = (x+y)^*c − x^*c − y^*c + 0^*c. -/
lemma Pic.ParallelogramLaw.pairing_nsmul_left (hc : c.ParallelogramLaw) (x y : T ⟶ A) (m : ℕ) :
    c.pairing (m • x) y = m • c.pairing x y := by
  induction m using Nat.twoStepInduction with
  | zero => simp [pairing]
  | one => simp
  | more m ih ih' =>
    have key : c.pairing ((m + 2) • x) y + c.pairing (m • x) y = 2 • c.pairing ((m + 1) • x) y := by
      simpa [succ_nsmul] using hc.pairing_add_add_pairing_sub ((m + 1) • x) x y
    linear_combination (norm := module) key - ih + 2 • ih'

/-- If `c` satisfies the parallelogram law, the pairing of `m • c` at `(x, y)` is the pairing of `c`
at `(m • x, y)`. -/
lemma Pic.ParallelogramLaw.nsmul_pairing_eq_pairing_nsmul (hc : c.ParallelogramLaw) (x y : T ⟶ A)
    (m : ℕ) :
    (m • c).pairing x y = c.pairing (m • x) y := by
  rw [hc.pairing_nsmul_left]
  simp [pairing, atPoint, smul_sub]

namespace Variety

/-! ### Base change and products -/

/-- Let `A` be a commutative group scheme over `S` with an action of the ring `O` (`ModuleObj O A`).
The pull-back of `A` along `b : S' → S`, with the counit as projection, is a base change in the
sense of `New.IsGroupBaseChange`: the square is a pullback, and composing with the counit is
`O`-linear on points. -/
lemma isGroupBaseChange_counit :
    IsGroupBaseChange b (A := A) ((mapPullbackAdj b).counit A) where
  isPullback := IsPullback.of_hasPullback A.hom b
  linear {U} := by
    -- The module structure on the `U`-points of the pullback is transported along the adjunction
    -- bijection `e`, and `e.symm` is composition with the counit.
    let e : ((CategoryTheory.Over.map b).obj U ⟶ A) ≃ (U ⟶ (pullback b).obj A) :=
      (mapPullbackAdj b).homEquiv U A
    have h_add (x y : (CategoryTheory.Over.map b).obj U ⟶ A) : e (x + y) = e x + e y := by
      unfold pullbackAddObj
      simp [e, Adjunction.homEquiv, Functor.map_add', comp_add]
    change IsLinearMap O e.symm
    exact (AddEquiv.linearEquiv O (AddEquiv.mk e h_add).symm).isLinear

/-- The pairing `⟨x, y⟩ = (x + y)^*c − x^*c − y^*c + 0^*c` of a class `c` in `Pic A` is symmetric
in the `T`-points `x`, `y` of `A`. -/
lemma pairing_comm : c.pairing x y = c.pairing y x := by grind [pairing]

/-- Pairing after pulling `c` back along a homomorphism `f : B → A` is pairing at the images under
`f`. -/
lemma pairing_comp [AddObj B] (f : B ⟶ A) [IsAdditive f] (x y : T ⟶ B) :
    (c.pull f.left).pairing x y = c.pairing (x ≫ f) (y ≫ f) := by
  simp [pairing, Pic.atPoint, ← c.pull_comp, ← comp_left, add_comp]

/-- The product over `S` of two proper schemes over `S` is proper over `S`. -/
instance [IsProper A.hom] [IsProper B.hom] : IsProper (A ⊗ B).hom := by
  simpa using (inferInstance : IsProper (Limits.pullback.fst A.hom B.hom ≫ A.hom))

/-- The base change of an abelian scheme along `b : S' → S` is an abelian scheme over `S'`. -/
noncomputable instance [i : IsAbelianScheme B] : IsAbelianScheme (pullback b B) :=
  -- `h`: the pull-back of `B` along `b`, with the counit as projection, is a group base change.
  have h := isGroupBaseChange_counit b
  -- Smoothness and properness pass to the base change, and multiplication by `m` on the
  -- pullback is the base change of multiplication by `m` on `B`.
  IsAbelianScheme.mk (toSmooth := of_isPullback h.isPullback i.toSmooth)
    (toIsProper := of_isPullback h.isPullback i.toIsProper) fun m hm ↦
      of_isPullback (.of_bot (by simp_rw [w, h.isPullback]) (h.nsmul_id_comp m).symm h.isPullback)
        (i.nsmul_surjective m hm)

variable {R : CommRingCat} {A : Over (Spec R)} [IsLocalRing R] [AddObj A] {c : Pic A.left}

/-! ### Group schemes over a local ring -/

omit [AddObj A] in
/-- Over a local ring, a class pulls back to zero along a point that comes from a section. -/
@[simp]
lemma atPoint_toUnit_comp_eq_zero {T : Over (Spec R)} (z : 𝟙_ (Over (Spec R)) ⟶ A) :
    c.atPoint (toUnit T ≫ z) = 0 := by
  simp [Pic.atPoint, c.pull_comp, eq_zero_of_isLocalRing]

@[simp]
lemma atPoint_zero {T : Over (Spec R)} : c.atPoint (T := T) 0 = 0 := atPoint_toUnit_comp_eq_zero _

/-- Let `A` be a commutative group scheme over a local ring and `c` a class in `Pic A` that
satisfies the parallelogram law `New.Pic.ParallelogramLaw`. Then the pull-back of `c` under
multiplication by a natural number `m` is `m² c`. -/
lemma pull_nsmul_eq_sq_smul (hc : c.ParallelogramLaw) (m : ℕ) :
    Pic.pull (m • 𝟙 A).left c = m ^ 2 • c := by
  change c.atPoint (m • 𝟙 A) = m ^ 2 • c
  induction m with
  | zero => simp
  | succ m ih =>
    -- As `0^* c = 0`, `pairing_nsmul_left` at `x = y = 𝟙 A` reads
    -- `(m + 1)^* c - m^* c - c = m • (2^* c - 2 • c)`; the parallelogram law gives `2^* c = 4 • c`.
    have h_id : c.atPoint (𝟙 A) = c := by simp [Pic.atPoint]
    have h_two : c.atPoint (𝟙 A + 𝟙 A) = 4 • c := by
      simpa [h_id, ← two_smul ℕ c, smul_smul] using hc (𝟙 A) (𝟙 A)
    have h_pair : c.atPoint ((m + 1) • 𝟙 A) - c.atPoint (m • 𝟙 A) - c = m • (4 • c - c - c) := by
      simpa [pairing, h_id, h_two, ← succ_nsmul] using hc.pairing_nsmul_left (𝟙 A) (𝟙 A) m
    linear_combination (norm := module) h_pair + ih

end Variety

end New

/-!
## Descent of pairing identities along an fpqc cover

A' is a base change to S of an abelian variety over a field, and f : A → A₁ is flat, surjective and
quasi-compact over S.

* `New.Variety.eq_pull_zero_section`: a class on A₁ × A' that is trivial on A × A' is pulled back
  from A₁ × 0.
* `New.Variety.pairing_eq_of_fpqc_cover`: an identity between two pairings that holds for points
  factoring through f holds for all points.

The idea: global functions on a base change of A' are constant along A'
(`New.Variety.hasConstFunctions_of_isPullback`), so a frame normalised along the zero section
descends.
-/

section PairingDescent

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory Over New LineBundle
  Pic

/-- Let `f : A → A₁` be a morphism over `S`. For `T`-points `x` of `A` and `a` of `A'`, the point
`(x, a)` of `A × A'` maps to `(f x, a)` under `f × 1` (as morphisms of underlying schemes). -/
lemma New.Variety.lift_left_comp_whiskerRight_left {S : Scheme.{0}} {A A₁ T A' : Over S}
    (x : T ⟶ A) (a : T ⟶ A') (f : A ⟶ A₁) :
    (lift x a).left ≫ (f ▷ A').left = (lift (x ≫ f) a).left := by
  rw [← comp_left, lift_whiskerRight]

/-- Let `f : A → A₁` be a morphism over `S`. Two `Y`-points of `A × A'` with the same image under
`f × 1` lie over one point `s` of `S` and have the form `(x, z)` and `(y, z)` with `f x = f y`. -/
lemma New.Variety.exists_eq_lift_of_comp_whiskerRight_eq {S : Scheme.{0}} {A A₁ A' : Over S}
    (f : A ⟶ A₁) {Y : Scheme}
    {t t' : Y ⟶ (A ⊗ A').left} (same_image : t ≫ (f ▷ A').left = t' ≫ (f ▷ A').left) :
    ∃ (s : Y ⟶ S) (x y : Over.mk s ⟶ A) (z : Over.mk s ⟶ A'),
      x ≫ f = y ≫ f ∧ (lift x z).left = t ∧ (lift y z).left = t' := by
  let s : Y ⟶ S := t ≫ (A ⊗ A').hom
  have ht' : t' ≫ (A ⊗ A').hom = s := by
    rw [← Over.w (f ▷ A'), ← reassoc_of% same_image, Over.w]
  -- `t` and `t'` underlie points `u` and `u'` over `s`; take their components
  obtain ⟨u, hu⟩ : ∃ u : Over.mk s ⟶ A ⊗ A', u.left = t := ⟨homMk t, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u' : Over.mk s ⟶ A ⊗ A', u'.left = t' := ⟨homMk t' ht', rfl⟩
  have h_image : u ≫ f ▷ A' = u' ≫ f ▷ A' := by
    apply OverMorphism.ext
    rw [comp_left, comp_left, hu, hu', same_image]
  have h_fst : (u ≫ fst A A') ≫ f = (u' ≫ fst A A') ≫ f := by simpa using h_image =≫ fst A₁ A'
  have h_snd : u ≫ snd A A' = u' ≫ snd A A' := by simpa using h_image =≫ snd A₁ A'
  refine ⟨s, u ≫ fst A A', u' ≫ fst A A', u ≫ snd A A', h_fst, ?_, ?_⟩
  · rw [lift_comp_fst_snd, hu]
  · rw [h_snd, lift_comp_fst_snd, hu']

variable {k : Type} [Field k]
  {A₀ : Over (Spec ⟨k⟩)} [IsAbelianScheme A₀] [IsIntegral A₀.left] {S : Scheme}
  {A A₁ A' B B' : Over S} [AddObj A'] [AddObj B] [AddObj B']
  {p : A'.left ⟶ A₀.left} {q : S ⟶ Spec (CommRingCat.of k)}

/-- Let A' be the base change of an integral abelian variety over a field (`hp`), and let `u` be a
frame of the pull-back of `L` along `f × 1`. For points `x`, `y` of `A` with `f x = f y`, the
values of `u` at `(x, a)` and `(y, a)` differ by a factor that does not depend on `a`. -/
lemma New.Variety.exists_apply_lift_eq_mul_of_isFrame (hp : IsPullback p A'.hom A₀.hom q)
    {f : A ⟶ A₁} {ι : Type} {L : LineBundle (A₁ ⊗ A').left ι} {u : ι → PointFn (A ⊗ A').left}
    (hu : (L.pull (f ▷ A').left).IsFrame u) {R : CommRingCat} {s : Spec R ⟶ S} {x y : Over.mk s ⟶ A}
    (hxy : x ≫ f = y ≫ f) :
    ∃ r : R, ∀ (j : ι) (a : Over.mk s ⟶ A'), LandsIn (lift (y ≫ f) a).left (L.opens j) →
      u j R (lift x a).left = r * u j R (lift y a).left := by
  -- The frames pulled back along `x × 1` and `y × 1` differ by a global function `r` on the base
  -- change of `A'` along `s`, and such a function is constant along `A'`.
  have frame (w : Over.mk s ⟶ A) (hw : w ≫ f = y ≫ f) :
      (L.pull ((y ≫ f) ▷ A').left).IsFrame fun j : ι ↦ (u j).pull (w ▷ A').left := by
    rw [← hw, comp_whiskerRight]
    exact hu.pull (w ▷ A').left
  obtain ⟨h_section_x, -⟩ := frame x hxy
  obtain ⟨r, hr⟩ := (frame y rfl).exists_eq_mul h_section_x
  have const : HasConstFunctions (X := (Over.mk s ⊗ A').left) (Limits.pullback.fst s A'.hom) :=
    hasConstFunctions_of_isPullback (.paste_horiz (.flip (.of_hasPullback ..)) hp)
  have h_over (a : Over.mk s ⟶ A') :
      (lift (𝟙 (Over.mk s)) a).left ≫ (fst (Over.mk s) A').left = 𝟙 (Over.mk s).left := by
    rw [← comp_left, lift_fst, id_left]
  refine ⟨PointFn.ofSection r R (lift (𝟙 (Over.mk s)) 0).left, fun j a ha ↦ ?_⟩
  have h_point {X : Over S} (w : Over.mk s ⟶ X) :
      (lift (𝟙 (Over.mk s)) a).left ≫ (w ▷ A').left = (lift w a).left := by
    rw [lift_left_comp_whiskerRight_left, Category.id_comp]
  have h_value : u j R ((lift (𝟙 (Over.mk s)) a).left ≫ (x ▷ A').left) =
      PointFn.ofSection r R (lift (𝟙 (Over.mk s)) a).left *
        u j R ((lift (𝟙 (Over.mk s)) a).left ≫ (y ▷ A').left) := by
    rw [← h_point (y ≫ f)] at ha
    exact hr j R (lift (𝟙 (Over.mk s)) a).left ha
  rw [h_point x, h_point y] at h_value
  rw [h_value, const r R _ _ ((h_over a).trans (h_over 0).symm)]

/-- Let A' be the base change along q : S → Spec k of an integral abelian variety A₀ over a field k
(`hp`), and let f : A → A₁ be flat, surjective and quasi-compact over S. A class in Pic(A₁ × A')
that is trivial on A × A' equals its pull-back along (x, a) ↦ (x, 0). -/
lemma New.Variety.eq_pull_zero_section (hp : IsPullback p A'.hom A₀.hom q) (f : A ⟶ A₁)
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left]
    (c : Pic (A₁ ⊗ A').left) (hc : Pic.pull (f ▷ A').left c = 0) :
    c = Pic.pull (A₁ ◁ 0).left c := by
  -- Let `L` represent `c`, and `u` be a frame of the pullback of `L` to `A ⊗ A'`; divide it by its
  -- value along the zero section. The quotient descends to `A₁ ⊗ A'`, because two lifts of a point
  -- change `u` by a global function on a base change of `A'`, which is constant along `A'` and
  -- cancels.
  obtain ⟨ι, L⟩ := c
  obtain ⟨u, hu⟩ : ∃ u : ι → PointFn (A ⊗ A').left, (L.pull (f ▷ A').left).IsFrame u :=
    exists_isFrame_of_picClass_eq_zero hc
  have zero_frame : ((L.pull (A₁ ◁ (0 : A' ⟶ A')).left).pull (f ▷ A').left).IsFrame
      fun j : ι ↦ (u j).pull (A ◁ (0 : A' ⟶ A')).left := by
    rw [← LineBundle.pull_comp, ← comp_left, ← whisker_exchange f 0, comp_left,
      LineBundle.pull_comp]
    exact hu.pull _
  -- `u (x, z) / u (x, 0)` is a frame of the pullback of `L ⊗ ((A₁ ◁ 0)^* L)⁻¹`
  have normalised := hu.mul zero_frame.inv
  have h_flat : Flat (f ▷ A').left := MorphismProperty.overPullbackMap A'.hom f inferInstance
  have h_surj : Surjective (f ▷ A').left := MorphismProperty.overPullbackMap A'.hom f inferInstance
  have h_qc : QuasiCompact (f ▷ A').left := MorphismProperty.overPullbackMap A'.hom f inferInstance
  -- by fpqc descent it suffices that its values at `t`, `t'` agree when their images agree
  refine picClass_eq_iff.mpr (exists_isFrame_of_fpqc _ normalised fun i R t t' same_image hi ↦ ?_)
  -- write `t = (x, z)` and `t' = (y, z)` as points over `s` with `x ≫ f = y ≫ f`
  obtain ⟨s, x, y, z, hxy, rfl, rfl⟩ := exists_eq_lift_of_comp_whiskerRight_eq f same_image
  obtain ⟨r, ratio⟩ := exists_apply_lift_eq_mul_of_isFrame hp hu hxy
  have h_zero {X : Over S} (w : Over.mk s ⟶ X) :
      (lift w z).left ≫ (X ◁ (0 : A' ⟶ A')).left = (lift w 0).left := by
    rw [← comp_left, lift_whiskerLeft, comp_zero]
  have h_image : (lift x z).left ≫ (f ▷ A').left = (lift (y ≫ f) z).left := by
    rw [lift_left_comp_whiskerRight_left, hxy]
  obtain ⟨h₁, h₂⟩ : LandsIn ((lift x z).left ≫ (f ▷ A').left) (L.opens i.1) ∧
      LandsIn (((lift x z).left ≫ (f ▷ A').left) ≫ (A₁ ◁ (0 : A' ⟶ A')).left) (L.opens i.2) :=
    landsIn_inf.1 hi
  obtain ⟨-, u_unit⟩ := hu
  have h_unit : IsUnit (u i.1 R (lift x z).left) := u_unit i.1 R (lift x z).left h₁
  rw [h_image] at h₁
  rw [h_image, h_zero] at h₂
  -- the factor `r` is a unit, so it cancels between `a = z` and `a = 0`
  have hr_unit : IsUnit r := by
    rw [ratio i.1 z h₁] at h_unit
    exact isUnit_of_mul_isUnit_left h_unit
  change u i.1 R (lift x z).left * Ring.inverse (u i.2 R ((lift x z).left ≫ (A ◁ 0).left)) =
    u i.1 R (lift y z).left * Ring.inverse (u i.2 R ((lift y z).left ≫ (A ◁ 0).left))
  rw [h_zero, h_zero, ratio i.1 z h₁, ratio i.2 0 h₂, Ring.mul_inverse_rev]
  linear_combination (u i.1 R (lift y z).left * Ring.inverse (u i.2 R (lift y 0).left)) *
    Ring.mul_inverse_cancel r hr_unit

/-- Let A' be the base change of an integral abelian variety over a field (`hp`), let f : A → A₁ be
flat, surjective and quasi-compact, let a, a' be morphisms from A₁, and let b, b' be homomorphisms
on A'. If ⟨a(x), b(y)⟩_c = ⟨a'(x), b'(y)⟩_c' for all points x of A₁
factoring through f and y of A', it holds for all x. -/
lemma New.Variety.pairing_eq_of_fpqc_cover (hp : IsPullback p A'.hom A₀.hom q) (f : A ⟶ A₁)
    [Flat f.left] [Surjective f.left] [QuasiCompact f.left] {c : Pic B.left} {c' : Pic B'.left}
    (a : A₁ ⟶ B) (b : A' ⟶ B) [IsAdditive b] (a' : A₁ ⟶ B') (b' : A' ⟶ B') [IsAdditive b']
    (h_cover : ∀ ⦃T : Over S⦄ (x : T ⟶ A) (y : T ⟶ A'),
      Pic.pairing c (x ≫ f ≫ a) (y ≫ b) = Pic.pairing c' (x ≫ f ≫ a') (y ≫ b'))
    ⦃T : Over S⦄ (x : T ⟶ A₁) (y : T ⟶ A') :
    c.pairing (x ≫ a) (y ≫ b) = c'.pairing (x ≫ a') (y ≫ b') := by
  -- the difference `d` of the two pairings at the universal point is trivial on `A ⊗ A'`
  let d : Pic (A₁ ⊗ A').left :=
    c.pairing (fst A₁ A' ≫ a) (snd A₁ A' ≫ b) - c'.pairing (fst A₁ A' ≫ a') (snd A₁ A' ≫ b')
  have trivial_on_cover : Pic.pull (f ▷ A').left d = 0 := by
    simp_all [d, Pic.pairing, Pic.atPoint, ← Pic.pull_comp, ← comp_left, -lift_left, comp_add]
  -- so its value at `(x, y)` is its value at `(x, 0)`, where both pairings vanish
  have h_zero_section : d = Pic.pull (A₁ ◁ 0).left d := eq_pull_zero_section hp f d trivial_on_cover
  simpa [d, Pic.pairing, Pic.atPoint, ← Pic.pull_comp, ← comp_left, sub_eq_zero, -lift_left,
    comp_add] using congrArg (Pic.pull (lift x y).left) h_zero_section

end PairingDescent
