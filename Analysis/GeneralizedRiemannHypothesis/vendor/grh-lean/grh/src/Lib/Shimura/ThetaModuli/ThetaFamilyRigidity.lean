import Lib.Shimura.AbelianScheme.TangentCoordinates
import Lib.Shimura.ThetaGroup
import Lib.Shimura.ThetaModuli.PELThetaTori

/-!
# Theta objects of PEL moduli problems, their pull-backs, and rigidity over local rings

The moduli problem for a PEL datum `D : New.PEL E` is studied through one family `New.ThetaFamily`.
An object is rigid if it satisfies a constancy and spanning condition over Noetherian local rings.
Over a local Noetherian ring, rigidity yields a criterion for points in the kernel of the
polarisation to vanish. It also yields the identification of objects related by compatible
homomorphisms.

## Main definitions and results

* `New.ThetaFamily`: an abelian scheme with `𝓞 E`-action, theta coordinates and level points.
* `New.ThetaObject`: a point of the base; its abelian scheme, bundle and level points are
  pull-backs.
* `New.ThetaObject.FullLevelStructure`, `New.ThetaObject.FullLevelStructure.exists_pullback`:
  trivialisations of all torsion, and their pull-back along a local homomorphism to `ℂ`.
* `New.ThetaObject.HasSpanningCoords`: constant functions and spanning coordinates on every
  pull-back to a Noetherian local ring; such an object is called rigid.
* `New.ThetaObject.HasSpanningCoords.eq_zero_of_pairing_eq_zero`: a criterion, in characteristic
  `l`, for a point in the kernel of the polarisation to be zero.
* `New.ThetaObject.HasSpanningCoords.eq_and_comp_toFamily_eq_of_hom`: for two objects with the same
  map `𝓞 E → B`, a homomorphism that respects the action, the pairing and the level points
  identifies them.

Notions from other files:
* `New.PEL.levelTorsion`: the level module: the O_E-submodule of (𝔸_f / Ô)^rank of elements killed
  by the level 𝔑.
* `New.Pic.pairing`: for c in Pic A and T-points x, y of A, the class
  ⟨x, y⟩ = (x + y)^*c − x^*c − y^*c + 0^*c in Pic T.
* `New.Variety.IsSectionLift`: a map H⁰(L) → H⁰(L') that is pull-back along f followed by some
  isomorphism f^*L ≅ L'; `New.Variety.IsTranslationLift` is the case of a translation, L' = L.

## Relation to the literature

Known; see `Lib.Shimura.ThetaModuli.UniversalFamily`,
`Lib.Cohomology.ProjectiveLine.ConstantLineFormula` and `Lib.Shimura.IntegralModel.UniversalFamily`
for sources.
-/

noncomputable section

/-! ## Theta objects of a family and their pull-backs along base morphisms -/

namespace New

open CategoryTheory AlgebraicGeometry MonoidalCategory NumberField Variety Over LineBundle
  OverMorphism Matrix Spec Pic

variable {E : Type} [Field E] [CMBase E] (D : PEL E)

/-- A family for the PEL data `D`: an abelian scheme `total` with `𝓞 E`-action over an
`𝓞 E`-scheme `S`, of relative dimension `New.Variety.abelianDim E D.Index`, with a line bundle
`lineBundle` whose coordinates separate points and with level points `levelPoints`. Over local
rings the coordinates are theta coordinates (`theta_law`), and the action on the Lie algebra
satisfies a rank one condition (`signature`). An affine point of `S` over `𝓞 E` is determined by
the coordinates of its level points (`eq_of_level_coords_eq`). No universal property is asked
for. -/
structure ThetaFamily (S : Scheme) (τ : S ⟶ Spec ⟨𝓞 E⟩) where
  /-- The total space `A`, a scheme over `S`. -/
  total : Over S
  /-- `total` is an abelian scheme over `S`. -/
  [isAbelianScheme : IsAbelianScheme total]
  /-- The action of `𝓞 E` on `total` by endomorphisms. -/
  [moduleObj : ModuleObj (𝓞 E) total]
  /-- The line bundle 𝒩 on `total`, with cover and coordinates indexed by `D.dualTorsion`. -/
  lineBundle : LineBundle total.left D.dualTorsion
  /-- `total` is proper over `S`, and `lineBundle` is a linear system whose coordinates separate
  the points of `total` over `S`. -/
  embeds : lineBundle.IsProjEmbedding total.hom
  /-- The level points: an `𝓞 E`-linear map from the 𝔑-torsion to the sections of `total`. -/
  levelPoints : D.levelTorsion →ₗ[𝓞 E] 𝟙_ (Over S) ⟶ total
  /-- The theta law: take any base change to a local ring. Restrict the pulled-back level points to
  `D.dualTorsion`. Then the coordinates of `lineBundle` are theta coordinates for the Lagrangian
  `D.lagrangian` and some bicharacter `c`. -/
  theta_law {B : Type} [CommRing B] [IsLocalRing B] (t : Spec ⟨B⟩ ⟶ S) {T : Over (Spec ⟨B⟩)}
      [AddObj T] [ModuleObj (𝓞 E) T] {q : (Over.map t).obj T ⟶ total}
      (h : IsGroupBaseChange t (B := T) q) : ∃ c : D.dualTorsion → AddChar D.dualTorsion B,
    IsThetaStructure (D.lagrangian.addSubgroupOf D.dualTorsion)
      (AddMonoidHom.comp (h.pullSection ∘ₗ levelPoints)
        (AddSubgroup.inclusion D.dualTorsion_le_levelTorsion))
      (embeds.isLinearSystem.pull q.left) c
  /-- The class of `lineBundle` satisfies the three identities of `PEL.HasClassLaws`. -/
  class_laws : D.HasClassLaws lineBundle.picClass
  /-- The signature condition: over a local ring there are coordinates at `0` in which `c` acts on
  the Lie algebra by a matrix `m c`, and `m (β̄ - b) - (β - b)` has its image on a line on which
  `𝓞 E` acts by scalars, through the structure map. -/
  signature (b : ℤ) {B : CommRingCat} (t : Spec B ⟶ S) [IsLocalRing B] :
      ∃ (V : total.left.Opens) (z : Fin (abelianDim E D.Index) → Γ(total.left, V))
          (m : 𝓞 E → Matrix (Fin (abelianDim E D.Index)) (Fin (abelianDim E D.Index)) B),
        IsLieChart total (ι := Fin (abelianDim E D.Index)) t V z m ∧
        HasSignature (preimage (t ≫ τ)).hom (Star.star D.β - b) (D.β - b) m
  /-- `total` is smooth over `S` of relative dimension `abelianDim E D.Index`. -/
  relative_dim : SmoothOfRelativeDimension (abelianDim E D.Index) total.hom
  /-- A point of `S` over `𝓞 E` with affine source is determined by its list, the coordinates of the
  level points. -/
  eq_of_level_coords_eq {B : CommRingCat} (t t' : Spec B ⟶ S) :
      t ≫ τ = t' ≫ τ →
      (∀ l : D.levelTorsion, lineBundle.pull (t ≫ (levelPoints l).left) = lineBundle.pull
        (t' ≫ (levelPoints l).left)) →
      t = t'

attribute [instance] ThetaFamily.moduleObj ThetaFamily.isAbelianScheme ThetaFamily.relative_dim

variable {D} {S S' Z : Scheme} (b : S' ⟶ S) {τ : Z ⟶ Spec (CommRingCat.of (𝓞 E))}
  {X : ThetaFamily D Z τ} {R : Type} {K : Type} [CommRing R]

/-! ### Objects and their data -/

/-- An object of the family X over a scheme T: a morphism from T to the base of X. -/
abbrev ThetaObject (_ : ThetaFamily D Z τ) (T : Scheme) : Type := T ⟶ Z

variable (x : ThetaObject X S) (y : ThetaObject X (Spec ⟨R⟩))

namespace ThetaObject

/-- The group scheme with O_E-action of an object x over S: the pull-back of the abelian scheme
of the family along x : S → base. -/
def groupScheme : Over S := pullback x X.total
  deriving AddObj, ModuleObj (𝓞 E), IsAbelianScheme

/-- The projection from the abelian scheme of an object x to that of the family X, as a morphism
over the base of X. -/
def toFamily : Over.map x x.groupScheme ⟶ X.total := (mapPullbackAdj x).counit X.total

/-- The projection `x.toFamily` is a base change of the abelian scheme of the family along `x` that
respects the group law and the `𝓞 E`-action. -/
lemma isGroupBaseChange : IsGroupBaseChange x x.toFamily := isGroupBaseChange_counit _

/-- The abelian scheme of an object is smooth of relative dimension
`New.Variety.abelianDim E D.Index`. -/
instance smoothOfRelativeDimension :
    SmoothOfRelativeDimension (abelianDim E D.Index) x.groupScheme.hom := by
  -- `simp` writes the structure map of the pull-back as `pullback.snd`, which has the instance
  simp [groupScheme]
  infer_instance

attribute [irreducible] groupScheme toFamily

/-- The line bundle, with its coordinates, on the abelian scheme of an object: the pull-back of the
bundle `X.lineBundle` of the family along the projection. -/
def lineBundle : LineBundle x.groupScheme.left D.dualTorsion := X.lineBundle.pull x.toFamily.left

/-- The line bundle of an object is a linear system whose coordinates separate points over `S`. -/
lemma isProjEmbedding : x.lineBundle.IsProjEmbedding x.groupScheme.hom :=
  X.embeds.of_isPullback x.isGroupBaseChange.isPullback

/-- The level points of an object: the O_E-linear map from the 𝔑-torsion of (𝔸_f / Ô)ⁿ to
sections of its abelian scheme, pulled back from those of the family. -/
def levelPoints : D.levelTorsion →ₗ[𝓞 E] 𝟙_ (Over S) ⟶ x.groupScheme :=
  x.isGroupBaseChange.pullSection ∘ₗ X.levelPoints

/-- The level points of an object lie over those of the family. -/
lemma levelPoints_comp_toFamily (l : ↥D.levelTorsion) :
    (x.levelPoints l).left ≫ x.toFamily.left = x ≫ (X.levelPoints l).left :=
  x.isGroupBaseChange.pullSection_comp _

/-- The class of the line bundle of an object satisfies the identities of `PEL.HasClassLaws`. -/
lemma hasClassLaws : D.HasClassLaws x.lineBundle.picClass := by
  -- The class of `x.lineBundle` at a point is that of `X.lineBundle` at its image under the linear
  -- map `x.isGroupBaseChange.pointEquiv`.
  refine ⟨fun T u v ↦ ?_, fun T u v ↦ ?_⟩
  · simpa [lineBundle, x.isGroupBaseChange.atPoint_picClass_pull] using
      X.class_laws.left (x.isGroupBaseChange.pointEquiv u) (x.isGroupBaseChange.pointEquiv v)
  · simpa [pairing, lineBundle, x.isGroupBaseChange.atPoint_picClass_pull] using
      X.class_laws.right (x.isGroupBaseChange.pointEquiv u) (x.isGroupBaseChange.pointEquiv v)

/-- For the class of the line bundle of an object, `(β - b) ^ k` is adjoint to `(β̄ - b) ^ k`,
where `β̄ = star β`: `⟨(β - b) ^ k • y, z⟩ = ⟨y, (β̄ - b) ^ k • z⟩` for the pairing of the class. -/
lemma pairing_pow_smul_adjoint (b : ℤ) (k : ℕ) {T : Over S} :
    ∀ y z : T ⟶ x.groupScheme,
      x.lineBundle.picClass.pairing ((D.β - b) ^ k • y) z =
        x.lineBundle.picClass.pairing y ((Star.star D.β - b) ^ k • z) := by
  -- The tool is `⟨u + w, z⟩ + ⟨u - w, z⟩ = 2 ⟨u, z⟩`
  -- (`Pic.ParallelogramLaw.pairing_add_add_pairing_sub`). The case `k = 1` follows for all `b` from
  -- the cases `b = 0` and `b = 1`, and the general case by induction on `k`.
  set c : Pic x.groupScheme.left := x.lineBundle.picClass
  have h_par (u w z : T ⟶ x.groupScheme) :
      c.pairing (u + w) z + c.pairing (u - w) z = 2 • c.pairing u z :=
    x.hasClassLaws.left.pairing_add_add_pairing_sub u w z
  -- With `u = 0` the parallelogram law says that the pairing is odd.
  have h_odd (u z : T ⟶ x.groupScheme) : c.pairing (-u) z = -c.pairing u z :=
    eq_neg_of_add_eq_zero_right (by simpa [pairing.eq_1 _ 0] using h_par 0 u z)
  -- The case `k = 1`.
  have h_adjoint (b : ℤ) (y z : T ⟶ x.groupScheme) :
      c.pairing ((D.β - b) • y) z = c.pairing y ((star D.β - b) • z) := by
    -- The defect `F b` satisfies `F (b - 1) + F (b + 1) = 2 F b` by the parallelogram law in each
    -- argument, and vanishes at `b = 0` and `b = 1`; so it vanishes for all `b`.
    let F (b : ℤ) : Pic T.left := c.pairing ((D.β - b) • y) z - c.pairing y ((star D.β - b) • z)
    have h_rec (b : ℤ) : F (b - 1) + F (b + 1) = 2 • F b := by
      have h_step (a : 𝓞 E) (u w : T ⟶ x.groupScheme) :
          c.pairing ((a - (b - 1 : ℤ)) • u) w + c.pairing ((a - (b + 1 : ℤ)) • u) w =
            2 • c.pairing ((a - b) • u) w := by
        rw [← h_par _ u w, Int.cast_sub, Int.cast_add, Int.cast_one]
        congr 2 <;> module
      simp only [F, pairing_comm y, smul_sub, ← h_step]
      abel
    -- at `b = 0` this is the adjointness of `β` and `β̄ = 1 - β`
    have h_law (u v : T ⟶ x.groupScheme) : c.pairing (D.β • u) v = c.pairing u ((1 - D.β) • v) :=
      (x.hasClassLaws.right u v).left
    have h_F0 : F 0 = 0 := by simp [F, D.star_beta, h_law]
    -- at `b = 1` it is the same law with the points exchanged, as the pairing is symmetric and odd
    have h_F1 : F 1 = 0 := by
      simp only [F, Int.cast_one, D.star_beta, sub_sub_cancel_left, ← neg_sub 1 D.β, neg_smul]
      rw [pairing_comm y, h_odd, h_odd, h_law, pairing_comm z, sub_self]
    have h_all (b : ℤ) : F b = 0 := by
      induction b using Polynomial.Chebyshev.induct with
      | zero => exact h_F0
      | one => exact h_F1
      | add_two n h_succ h_n =>
        simpa [add_assoc, one_add_one_eq_two, h_n, h_succ] using h_rec (n + 1)
      | neg_add_one n h_n h_succ => simpa [h_n, h_succ] using h_rec (-n)
    exact sub_eq_zero.mp (h_all b)
  intro y z
  induction k generalizing y z with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, ih, h_adjoint, pow_succ', mul_smul]

/-! ### Pull-backs of objects -/

/-- The object x' is the pull-back of the object x along b: x' is x∘b. -/
abbrev IsPullbackAlong (x' : ThetaObject X S') (x : ThetaObject X S) : Prop := b ≫ x = x'

namespace IsPullbackAlong

variable {b x} {x' : ThetaObject X S'} (h : IsPullbackAlong b x' x)

/-- For x' the pull-back of x along b, the S-morphism from the abelian scheme of x' to that of x
that commutes with the projections to the family. -/
def schemeMap : Over.map b x'.groupScheme ⟶ x.groupScheme :=
  x.isGroupBaseChange.pointEquiv.symm (homMk x'.toFamily.left (by simp [h]))

lemma comp_toFamily : h.schemeMap.left ≫ x.toFamily.left = x'.toFamily.left :=
  x.isGroupBaseChange.isPullback.lift_fst _ _ _

/-- For x' the pull-back of x along b, the map `New.ThetaObject.IsPullbackAlong.schemeMap` is a base
change along b that respects the group law and the `𝓞 E`-action. -/
lemma isGroupBaseChange : IsGroupBaseChange b h.schemeMap := by
  -- The square of `h.schemeMap` followed by that of `x.toFamily` is the pull-back square of
  -- `x'.toFamily`.
  have h_square :
      IsPullback (h.schemeMap.left ≫ x.toFamily.left) x'.groupScheme.hom X.total.hom x' := by
    simpa only [h.comp_toFamily] using x'.isGroupBaseChange.isPullback
  have hx'_baseChange : IsGroupBaseChange x' x'.toFamily := x'.isGroupBaseChange
  have h_eq : b ≫ x = x' := h
  subst h_eq
  refine ⟨.of_right h_square h.schemeMap.w x.isGroupBaseChange.isPullback, fun {T} ↦ ?_⟩
  -- On points, `h.schemeMap` is the composite of two linear bijections through the points of
  -- `X.total`. (`convert`: the composite is `(· ≫ h.schemeMap)` only by the equation proved next.)
  convert
    (hx'_baseChange.pointEquiv ≪≫ₗ (x.isGroupBaseChange.pointEquiv (T := map b T)).symm).isLinear
  exact x.isGroupBaseChange.pointEquiv.eq_symm_apply.mpr (ext (_ ≫= h.comp_toFamily))

lemma lineBundle_eq_pull : x'.lineBundle = x.lineBundle.pull h.schemeMap.left :=
  congrArg _ h.comp_toFamily.symm

lemma lineBundle_pow_eq_pull (m : ℕ) :
    x'.lineBundle.pow m = (x.lineBundle.pow m).pull h.schemeMap.left :=
  -- `pull_pi` for the bundle of `x`, rewritten by `h.lineBundle_eq_pull`
  h.lineBundle_eq_pull ▸ (pull_pi _).symm

/-- The level points of the pull-back `x'` are the pull-backs of those of `x`. -/
lemma levelPoints_eq_pullSection (l : ↥D.levelTorsion) :
    x'.levelPoints l = h.isGroupBaseChange.pullSection (x.levelPoints l) := by
  -- both lie over the level point of the family, and over `S'`
  refine ext (x'.isGroupBaseChange.isPullback.hom_ext ?_ (by simp))
  simp [↓levelPoints_comp_toFamily, ← h, ← h.comp_toFamily,
    h.isGroupBaseChange.pullSection_comp_assoc]

end IsPullbackAlong

/-- Every object has a pull-back along `b`, namely `b ≫ x`. -/
lemma exists_isPullbackAlong : ∃ x' : ThetaObject X S', IsPullbackAlong b x' x := ⟨b ≫ x, rfl⟩

/-! ### Objects over a ring: full structures and logarithms on infinitesimal points -/

/-- For an object y over Spec R, the ring homomorphism O_E → R induced by y and the structure
morphism of the base of the family to Spec O_E. -/
def baseHom : 𝓞 E →+* R := (preimage (y ≫ τ)).hom

/-- A full structure on an object `y` over `R`: an injective `𝓞 E`-linear map from `(𝔸_f / Ô)ⁿ` to
the sections of `y.groupScheme` that extends the level points. The field `weil_pairing` prescribes
the commutator pairing: for each `ι : R → ℂ` there is a unit `ε` of `Ẑ` such that, for `m`-torsion
points `x`, `z`, lifts of the two translations to `y.lineBundle.pow m` commute on coordinates up to
a scalar `c` with `ι c = ψ_f (ε m ξ zᴴ x)`. -/
structure FullLevelStructure where
  /-- The `𝓞 E`-linear map from all torsion, `(𝔸f E / Ô E)ⁿ`, to the sections of `y.groupScheme`. -/
  torsionPoint : AdelicTorsion E D.Index →ₗ[𝓞 E] 𝟙_ (Over (Spec ⟨R⟩)) ⟶ y.groupScheme
  /-- The map `torsionPoint` is injective. -/
  injective : (⇑torsionPoint).Injective
  /-- The map `torsionPoint` extends the level points of `y`. -/
  levelPoints_eq (l : D.levelTorsion) : y.levelPoints l = torsionPoint l
  /-- For each `ι` there is a unit `ε` of Ẑ with this property: for `m`-torsion points `x`, `z`,
  lifts of the two translations to `y.lineBundle.pow m` commute on coordinate sections up to a
  scalar `c`, where `ι c = ψf (ε * m * xiForm D.ξ x z)`. -/
  weil_pairing (ι : R →+* ℂ) : ∃ ε : (Ô ℚ)ˣ, ∀ (m : ℕ) (x z : D.Index → 𝔸f E),
    m • torsionClass x = 0 → m • torsionClass z = 0 → ∃ c : R,
    ι c = ψf E (finAdeleIncl ℚ E ε * (m * xiForm D.ξ x z)) ∧
    ∀ Φ Ψ : Module.End R ((y.lineBundle.pow m).H0 R),
      IsTranslationLift (y.lineBundle.pow m) (torsionPoint (torsionClass x)) Φ →
      IsTranslationLift (y.lineBundle.pow m) (torsionPoint (torsionClass z)) Ψ →
      ∀ (h : (y.lineBundle.pow m).IsLinearSystem) (i : Fin m → D.dualTorsion),
        Φ (Ψ (coordSection h i)) = c • Ψ (Φ (coordSection h i))

/-- If `y` over `K` is the pull-back of `x` over `R` along `φ : R → K`, then the homomorphism from
`𝓞 E` given by `y` is that given by `x` followed by `φ`. -/
lemma IsPullbackAlong.baseHom_eq_comp [CommRing K] {φ : R →+* K}
    {x : ThetaObject X (Spec (CommRingCat.of R))} {y : ThetaObject X (Spec (CommRingCat.of K))}
    (h_pb : y.IsPullbackAlong (specMap φ) x) :
    y.baseHom = φ.comp x.baseHom := by
  simp [ThetaObject.baseHom, ← h_pb]

/-- The properties of a logarithm at one point. Here `ω` maps the `C`-points of `y.groupScheme` to
`C` for all rings `C`, `x` is a `C`-point, `ψ : C → C'` is a ring map and `b` is an integer.
`New.ThetaObject.IsTangentLog` asks these properties when `ψ` is onto with square-zero kernel and
`x` vanishes modulo that kernel. -/
structure IsTangentLogAt (b : ℤ)
    (ω : ∀ ⦃C : CommRingCat⦄ ⦃t : Spec C ⟶ Spec ⟨R⟩⦄, (Over.mk t ⟶ y.groupScheme) → C)
    {C C' : CommRingCat} (ψ : C ⟶ C') {t : Spec C ⟶ Spec ⟨R⟩} (x : Over.mk t ⟶ y.groupScheme) :
    Prop where
  /-- `ω` turns `c •` into multiplication by `y.baseHom c`. -/
  map_smul (c : 𝓞 E) : ω (c • x) = preimage t (y.baseHom c) * ω x
  /-- A zero of `ω` is killed by `star β - b`. -/
  smul_eq_zero_of_eq_zero : ω x = 0 → (Star.star D.β - b) • x = 0
  /-- `ω` is additive on the points that vanish modulo the kernel of `ψ`. -/
  map_add ⦃x' : Over.mk t ⟶ y.groupScheme⦄ : IsInfinitesimal ψ x' → ω (x + x') = ω x + ω x'
  /-- The value of `ω` lies in the kernel of `ψ`. -/
  infinitesimal : ψ (ω x) = 0
  /-- `ω` commutes with a change of rings `χ : C → C₁`. -/
  naturality ⦃C₁ : CommRingCat⦄ ⦃χ : C ⟶ C₁⦄ ⦃t₁ : Spec C₁ ⟶ Spec ⟨R⟩⦄
    (a : Over.mk t₁ ⟶ Over.mk t) : a.left = Spec.map χ → ω (a ≫ x) = χ (ω x)

/-- `ω` is a logarithm of `y` along the line of the signature for `b`: it satisfies
`New.ThetaObject.IsTangentLogAt` at every point that vanishes modulo a square-zero kernel. -/
def IsTangentLog (b : ℤ)
    (ω : ∀ ⦃C : CommRingCat⦄ ⦃t : Spec C ⟶ Spec ⟨R⟩⦄, (Over.mk t ⟶ y.groupScheme) → C) : Prop :=
  ∀ ⦃C C' : CommRingCat⦄ ⦃ψ : C ⟶ C'⦄ [IsSqZeroExt ψ] ⦃t : Spec C ⟶ Spec ⟨R⟩⦄
    ⦃x : Over.mk t ⟶ y.groupScheme⦄, IsInfinitesimal ψ x → y.IsTangentLogAt b ω ψ x

variable [IsLocalRing R] {y}

/-- Let `y` be an object of the family over a local ring `R` such that the ring map
`y.baseHom : 𝓞 E → R` induced by `y` kills `β - b` for an integer `b`. Then `y` has a logarithm
along the line of the signature for `b` (`New.ThetaObject.IsTangentLog`), the line of the Lie
algebra that contains the image of `star D.β - b` (field `signature` of the family). This is a map
`ω` that sends, for every ring `C` and every `t : Spec C ⟶ Spec R`, each `C`-point over `t` of the
group scheme `y.groupScheme` to an element of `C`, and that satisfies
`New.ThetaObject.IsTangentLogAt` at every point that vanishes modulo a square-zero kernel. -/
lemma exists_isTangentLog {b : ℤ} (hb : y.baseHom (D.β - b) = 0) :
    ∃ ω : ∀ ⦃C : CommRingCat⦄ ⦃t : Spec C ⟶ Spec ⟨R⟩⦄, (Over.mk t ⟶ y.groupScheme) → C,
      y.IsTangentLog b ω := by
  -- In coordinates `z` at `0` the matrix of `star β - b` is `baseHom (β - b) • 1 + Y ξᵀ`, and
  -- `baseHom (β - b) = 0` by `hb`: its image lies on the line of `Y`. So
  -- `tangentCoords z ((star β - b) • x)` is a multiple of `Y`, determined by its coordinate `k`
  -- (`Y k` is a unit): this is `ω x`. Every `m c` acts on `Y` by `baseHom c` (`hY_eigen`).
  obtain ⟨V, z, m, ⟨h_chart, h_jac⟩, Y, ξ, k, hY_unit, hY_eigen, h_rank_one⟩ := X.signature b y
  -- `p t` carries points of `y.groupScheme` to points of `X.total`, where the chart lives.
  let p {C} (t : Spec C ⟶ Spec ⟨R⟩) : (Over.mk t ⟶ y.groupScheme) ≃ₗ[𝓞 E] Over.mk (t ≫ y) ⟶
    X.total :=
    y.isGroupBaseChange.pointEquiv
  refine ⟨fun _ t x ↦ tangentCoords z (p t ((star D.β - b) • x)) k, fun C C' ψ _ t x hx ↦ ?_⟩
  -- `IsInfinitesimal ψ x` unfolds to an equation `… = 0`, which the linear equivalence `p t` keeps.
  have h_tiny_p {x} : IsInfinitesimal ψ x → IsInfinitesimal ψ (p t x) := (p _).map_eq_zero_iff.2
  -- `0` lies in the chart; on infinitesimal points `tangentCoords z` is additive and turns `a • ·`
  -- into the matrix `m a` (`h_linear`).
  obtain ⟨h_zero_mem, h_linear⟩ := h_jac (map_preimage t =≫ _)
  have h_tiny : IsInfinitesimal ψ ((star D.β - b) • p t x) := (h_tiny_p hx).smul _
  obtain ⟨s, h_on_line⟩ :
      ∃ s : C, ∀ i, tangentCoords z ((star D.β - b) • p t x) i = preimage t (Y i) * s := by
    refine ⟨∑ j, preimage t (ξ j) * tangentCoords z (p t x) j, fun i ↦ ?_⟩
    simpa [eq_add_of_sub_eq h_rank_one, mulVec_apply_eq_sum, hb, ← baseHom.eq_1, mul_assoc,
      vecMulVec, ← Finset.mul_sum] using congrFun ((h_linear (h_tiny_p hx)).1 (star D.β - b)) i
  refine
    { map_smul := fun c ↦ ?_
      smul_eq_zero_of_eq_zero := fun h_log_zero ↦ (p t).injective ?_
      map_add := fun x' hx' ↦ by simp [h_linear h_tiny, (h_tiny_p hx').smul]
      infinitesimal := by simp [h_chart.map_tangentCoords_eq_zero h_zero_mem h_tiny]
      naturality := fun C₁ χ t₁ a ha ↦ ?_ }
  · -- `c` acts on the line of `Y` by `baseHom c`
    have h_eigen_k :
        preimage t ((m c *ᵥ Y) k) * s = preimage t (y.baseHom c) * (preimage t (Y k) * s) := by
      simp [hY_eigen c, baseHom, mul_assoc]
    simpa [smul_comm _ c, h_linear h_tiny, h_on_line, mulVec_apply_eq_sum, Finset.sum_mul,
      mul_assoc] using h_eigen_k
  · -- `Y k` is a unit, so all coordinates vanish, and an infinitesimal point is determined by them.
    have h_k : preimage t (Y k) * s = 0 := by simpa [h_on_line] using h_log_zero
    have hs : s = 0 := (hY_unit.map _).mul_right_eq_zero.mp h_k
    simp [h_chart.eq_zero_of_tangentCoords_eq_zero h_zero_mem h_tiny, h_on_line, hs, funext_iff]
  · -- the tangent coordinates commute with the change of rings `χ`
    have h_comp : tangentCoords z ((map y).map a ≫ ((star D.β - b) • p t x)) =
        χ ∘ tangentCoords z ((star D.β - b) • p t x) :=
      IsEtaleChart.tangentCoords_comp h_zero_mem h_tiny ((map y).map a) ha
    -- `using!`: the two sides agree only after unfolding `Over.map` and `pointEquiv`
    simpa using! congrFun h_comp k

/-- The five properties of a logarithm (`New.ThetaObject.exists_isTangentLog`) as one conjunction:
(a) equivariance, (b) kernel, (c) additivity, (d) infinitesimal values, (e) naturality. -/
lemma exists_tangent_log {b : ℤ} (hb : y.baseHom (D.β - b) = 0) :
    ∃ ω : ∀ ⦃C : CommRingCat⦄ ⦃t : Spec C ⟶ Spec ⟨R⟩⦄, (Over.mk t ⟶ y.groupScheme) → C,
      ∀ ⦃C C' : CommRingCat⦄ ⦃ψ : C ⟶ C'⦄ [IsSqZeroExt ψ] ⦃t : Spec C ⟶ Spec (CommRingCat.of R)⦄
          ⦃x : Over.mk t ⟶ y.groupScheme⦄,
      IsInfinitesimal ψ x →
      (∀ c : 𝓞 E, ω (c • x) = preimage t (y.baseHom c) * ω x) ∧
      (ω x = 0 → (Star.star D.β - b) • x = 0) ∧
      (∀ ⦃x' : Over.mk t ⟶ y.groupScheme⦄, IsInfinitesimal ψ x' → ω (x + x') = ω x + ω x') ∧
      ψ (ω x) = 0 ∧
      ∀ ⦃C₁ : CommRingCat⦄ ⦃χ : C ⟶ C₁⦄ ⦃t₁ : Spec C₁ ⟶ Spec (CommRingCat.of R)⦄
          (a : Over.mk (t₁ : Spec C₁ ⟶ Spec ⟨R⟩) ⟶ Over.mk t),
        a.left = Spec.map χ →
        ω (a ≫ x) = χ (ω x) := by
  refine (exists_isTangentLog hb).imp fun ω h_log C C' ψ _ t x hx ↦ ?_
  obtain ⟨h_smul, h_zero, h_add, h_inf, h_nat⟩ := h_log hx
  exact ⟨h_smul, h_zero, h_add, h_inf, h_nat⟩

/-- Let the object be over a local ring. Then the translation by an `m`-torsion point of a full
structure lifts to `y.lineBundle.pow m`, the `m`-th power of the line bundle of `y`. -/
lemma FullLevelStructure.exists_isTranslationLift (e : y.FullLevelStructure) {m : ℕ}
    {l : AdelicTorsion E D.Index} (hl : m • l = 0) :
    ∃ Φ : Module.End R ↥((y.lineBundle.pow m).H0 R),
      IsTranslationLift (y.lineBundle.pow m) (e.torsionPoint l) Φ := by
  -- A lift exists iff `⟨l, ·⟩ = 0` for the class of `y.lineBundle.pow m`, which is
  -- `m • [y.lineBundle]`; this pairing is `⟨m • l, ·⟩` for `[y.lineBundle]`.
  simp [exists_isTranslationLift_iff, y.hasClassLaws.left.nsmul_pairing_eq_pairing_nsmul,
    ← comp_nsmul,
    ← map_nsmul, hl, pairing.eq_1]

/-- Let `y` be an object of the family `X` over a local ring `R`, `φ : R → ℂ` a local homomorphism,
and `y'` the pull-back of `y` along `φ` (`h_pb`). A full structure `e` on `y` is an injective
`𝓞 E`-linear map `torsionPoint` from `(𝔸_f / Ô)ⁿ` to the sections of the group scheme that extends
the level points and has the prescribed commutator pairing (`weil_pairing`). The claim is that there
is a full structure `e'` on `y'` whose map is `e.torsionPoint` followed by pulling sections back
along the base change. -/
lemma FullLevelStructure.exists_pullback {φ : R →+* ℂ}
    {y' : ThetaObject X (Spec (CommRingCat.of ℂ))}
    (h_pb : IsPullbackAlong (specMap φ) y' y) [IsLocalHom φ] (e : y.FullLevelStructure) :
    ∃ e' : y'.FullLevelStructure,
      e'.torsionPoint = h_pb.isGroupBaseChange.pullSection ∘ₗ e.torsionPoint := by
  refine ⟨⟨_, ?injective, ?levelPoints_eq, fun ι ↦ ?_⟩, rfl⟩
  case injective =>
    -- A torsion section with vanishing pull-back along `φ` is zero, as its order is a unit of `R`.
    refine (injective_iff_map_eq_zero _).mpr fun s hs ↦ e.injective ?_
    obtain ⟨m, hm, hms⟩ := exists_nsmul_adelicTorsion_eq_zero s
    have h_unit : IsUnit (m : R) := .of_map φ _ (by simpa using hm)
    simpa using eq_zero_of_nsmul_eq_zero_of_comp_eq_zero y.smoothOfRelativeDimension h_unit
      (by simp [← map_nsmul, hms]) (h_pb.isGroupBaseChange.pointEquiv.symm.map_eq_zero_iff.mp hs)
  case levelPoints_eq => simp [h_pb.levelPoints_eq_pullSection, e.levelPoints_eq]
  -- The Weil pairing: the commutator of two lifts of translations on `y'` is the image under `φ` of
  -- that on `y`.
  refine (e.weil_pairing (ι.comp φ)).imp fun ε hε m x z hx hz ↦ ?_
  obtain ⟨c, hc, h_comm⟩ := hε m x z hx hz
  refine ⟨φ c, hc, fun Φ Ψ hΦ hΨ h_lin i ↦ ?_⟩
  obtain ⟨Φ₀, hΦ₀⟩ := e.exists_isTranslationLift hx
  obtain ⟨Ψ₀, hΨ₀⟩ := e.exists_isTranslationLift hz
  -- `P` is the pull-back of sections of `lineBundle ^ m` from `y.groupScheme` to `y'.groupScheme`.
  let P := pullSections φ h_pb.schemeMap.w (h_pb.lineBundle_pow_eq_pull m)
  have hP : IsSectionLift (y'.lineBundle.pow m) (y.lineBundle.pow m) h_pb.schemeMap.left P :=
    isSectionLift_pullSections ..
  -- `Θ' ∘ P` and `P ∘ Θ` lift the same morphism, so they differ by a constant.
  have h_prop {s : 𝟙_ (Over (Spec ⟨R⟩)) ⟶ y.groupScheme}
      {Θ' : Module.End ℂ ((y'.lineBundle.pow m).H0 ℂ)}
      {Θ : Module.End R ((y.lineBundle.pow m).H0 R)}
      (hΘ' : IsTranslationLift (y'.lineBundle.pow m) (h_pb.isGroupBaseChange.pullSection s) Θ')
      (hΘ : IsTranslationLift (y.lineBundle.pow m) s Θ) : ∃ a : ℂ, ∀ σ, Θ' (P σ) = a • P (Θ σ) := by
    have h_comp := hΘ'.comp hP
    rw [h_pb.isGroupBaseChange.translation_comp s] at h_comp
    exact h_comp.exists_eq_smul (hasConstFunctions_of_isPullback .of_id_fst) (hP.comp hΘ)
  obtain ⟨a, ha⟩ := h_prop hΦ hΦ₀
  obtain ⟨b, hb⟩ := h_prop hΨ hΨ₀
  have h_lin₀ : (y.lineBundle.pow m).IsLinearSystem := .pi fun _ ↦ y.isProjEmbedding.isLinearSystem
  have h_coord : P (coordSection h_lin₀ i) = coordSection h_lin i := pullSections_coordSection ..
  -- Both sides are `a * b * φ c` times `P (Ψ₀ (Φ₀ (coordSection h_lin₀ i)))`.
  simp only [← h_coord, ha, hb, map_smul, h_comm Φ₀ Ψ₀ hΦ₀ hΨ₀, map_smulₛₗ]
  module

end ThetaObject

end New

/-! ## Rigid objects; the theta structure of an object over a local ring -/

namespace New.ThetaObject

open AlgebraicGeometry Variety

variable {E : Type} [Field E] [CMBase E]
  {D : PEL E} {Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {X : ThetaFamily D Z τ} {R : Type} [CommRing R] (x : ThetaObject X (Spec ⟨R⟩))

/-- On every pull-back of x to a noetherian local ring B, global functions on the abelian scheme are
constant and the coordinate sections of `y.lineBundle` span its H⁰ over B. Such an object is called
rigid. -/
def HasSpanningCoords : Prop :=
  ∀ ⦃B : Type⦄ [CommRing B] [IsLocalRing B] [IsNoetherianRing B] ⦃y : ThetaObject X (Spec ⟨B⟩)⦄
    ⦃b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)⦄,
    y.IsPullbackAlong b x →
    HasConstFunctions y.groupScheme.hom ∧
    Submodule.span B (Set.range (coordSection y.isProjEmbedding.isLinearSystem)) = ⊤

/-- The constants of the theta structure of an object `x` over a local ring: the family of
characters `c s` chosen by the field `theta_law` of the family for `x`. -/
noncomputable def thetaConstants [IsLocalRing R] : D.dualTorsion → AddChar D.dualTorsion R :=
  (X.theta_law x x.isGroupBaseChange).choose

/-- Over a local ring, the linear system of an object is a theta structure for the restriction of
the level points to the group `D.dualTorsion` and the Lagrangian `D.lagrangian ∩ D.dualTorsion`,
with the constants `x.thetaConstants`. -/
lemma isThetaStructure [IsLocalRing R] :
    IsThetaStructure (D.lagrangian.addSubgroupOf D.dualTorsion)
      (AddMonoidHom.comp x.levelPoints (AddSubgroup.inclusion D.dualTorsion_le_levelTorsion))
      x.isProjEmbedding.isLinearSystem x.thetaConstants :=
  (X.theta_law x x.isGroupBaseChange).choose_spec

end New.ThetaObject

/-!
## Consequences of rigidity: the polarisation kernel and compatible maps

Two consequences of rigidity for objects of a family `New.ThetaFamily` of abelian schemes embedded
by theta coordinates, over a local noetherian ring.

For a class `c`, `c.atPoint y` is `y^* c`.
-/

namespace New.ThetaObject.HasSpanningCoords

open CategoryTheory AlgebraicGeometry Variety Over Category

variable {E k : Type} {B : Type} [Field E] [CMBase E] {D : PEL E} [Field k]
  {Z : Scheme} {τ : Z ⟶ Spec (CommRingCat.of (NumberField.RingOfIntegers E))}
  {X : ThetaFamily D Z τ} {x : ThetaObject X (Spec ⟨k⟩)}
  [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

/-- Let `x` be a rigid object (`New.ThetaObject.HasSpanningCoords`) over a field `k` of prime
characteristic `l`: on every pull-back of `x` to a noetherian local ring, the global functions on
the abelian scheme are constant and the coordinates span the sections of the line bundle. Let `w` be
a pull-back of `x` to `S`, and `y` a point of `w.groupScheme` with values in a local noetherian ring
`B`. Suppose that (a) `l ^ m` kills the restriction of `y` to some nonempty affine scheme over
`Spec B`, and (b) `y` is in the kernel of the polarisation: it pairs to zero (`New.Pic.pairing`)
with every point, after any base change. Then `y = 0`. -/
lemma eq_zero_of_pairing_eq_zero (hx : x.HasSpanningCoords) {l : ℕ} [hl : Fact l.Prime] [CharP k l]
    {S : Scheme} {b : S ⟶ Spec (CommRingCat.of k)} {w : ThetaObject X S}
    (hb : w.IsPullbackAlong b x) {t : Spec ⟨B⟩ ⟶ S} (y : Over.mk t ⟶ w.groupScheme) (m : ℕ)
    {C : CommRingCat} (a : Spec C ⟶ Spec ⟨B⟩) [Nontrivial C]
    (h_pow_zero : l ^ m • (homMk a : Over.mk (a ≫ t) ⟶ Over.mk t) ≫ y = 0)
    (h_ker : ∀ ⦃T : Over S⦄ (a : T ⟶ .mk t) (z : T ⟶ w.groupScheme),
      w.lineBundle.picClass.pairing (a ≫ y) z = 0) :
    y = 0 := by
  -- Read `y` as a section `z` of the pull-back `x'` to `B`. By the theta structure the order of
  -- `D.dualTorsion`, which is prime to `l`, kills `z`; so `z` vanishes on `Spec C`, hence
  -- everywhere.
  obtain ⟨x', hp⟩ := w.exists_isPullbackAlong t
  obtain ⟨z, rfl⟩ := (hp.isGroupBaseChange.pointEquiv (T := .mk (𝟙 _))).surjective y
  -- `z` pairs to zero with the universal point, so its translation lifts to `x'.lineBundle`.
  have h_pair : x'.lineBundle.picClass.pairing
      (SemiCartesianMonoidalCategory.toUnit x'.groupScheme ≫ z) (𝟙 x'.groupScheme) = 0 := by
    simpa [hp.lineBundle_eq_pull, Pic.pairing, hp.isGroupBaseChange.atPoint_picClass_pull] using!
      h_ker (homMk _ rfl) hp.schemeMap
  obtain ⟨Φ, hΦ⟩ := exists_isTranslationLift_iff.mpr h_pair
  -- For a rigid theta structure such a section is killed by the order of the index group.
  have h_pb : x'.IsPullbackAlong (t ≫ b) x := by rw [IsPullbackAlong, assoc, hb, hp]
  obtain ⟨h_const, h_span⟩ := hx h_pb
  have h_card : Nat.card D.dualTorsion • z = 0 :=
    x'.isThetaStructure.card_nsmul_eq_zero_of_isTranslationLift h_const h_span x'.isProjEmbedding hΦ
  -- The order of `D.dualTorsion` is a unit in `k`, hence prime to the characteristic `l`.
  have h_not_dvd : ¬l ∣ Nat.card D.dualTorsion :=
    (CharP.isUnit_natCast_iff hl.out).mp x.isThetaStructure.isUnit_card
  -- Both `Nat.card D.dualTorsion` and `l ^ m` kill the value `z₀` of `z` on `Spec C`.
  let z₀ : Over.mk a ⟶ x'.groupScheme := SemiCartesianMonoidalCategory.toUnit (Over.mk a) ≫ z
  have h_card_fibre : Nat.card D.dualTorsion • z₀ = 0 := by simp [z₀, ← comp_nsmul, h_card]
  have h_pow_fibre : l ^ m • z₀ = 0 := by
    apply hp.isGroupBaseChange.pointEquiv.injective
    -- closes with `h_pow_zero`, once simp has put the goal in its form
    simpa [z₀]
  have h_fibre : z₀ = 0 :=
    (nsmul_eq_zero_iff_of_coprime (hl.out.coprime_pow_of_not_dvd h_not_dvd)).mp
      ⟨h_card_fibre, h_pow_fibre⟩
  -- A section of invertible order that vanishes on a nonempty affine scheme is zero.
  exact EmbeddingLike.map_eq_zero_iff.mpr <| eq_zero_of_nsmul_eq_zero_of_comp_eq_zero
    x'.smoothOfRelativeDimension x'.isThetaStructure.isUnit_card h_card h_fibre

/-- Rigidity. Let x be a rigid object (`New.ThetaObject.HasSpanningCoords`) over the field k, x₁ its
pull-back along b to a local noetherian ring B, and x₂ another object over B. Let j : x₁ → x₂ be an
O_E-linear homomorphism of the group schemes that respects the maps from O_E (`h_baseHom`), the
pairings of the line bundles (`h_pairing`) and the level points (`h_levelPoints`). Then x₁ = x₂, and
j commutes with the projections to the family. -/
lemma eq_and_comp_toFamily_eq_of_hom (hx : x.HasSpanningCoords) {x₁ x₂ : ThetaObject X (Spec ⟨B⟩)}
    {b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k)} (hb : x₁.IsPullbackAlong b x)
    (h_baseHom : x₁.baseHom = x₂.baseHom) (j : x₁.groupScheme ⟶ x₂.groupScheme)
    [h_linear_j : IsLinear j]
    (h_pairing : ∀ ⦃T : Over (Spec (CommRingCat.of B))⦄ (y z : T ⟶ x₁.groupScheme),
      x₁.lineBundle.picClass.pairing y z = x₂.lineBundle.picClass.pairing (y ≫ j) (z ≫ j))
    (h_levelPoints : ∀ l : ↥D.levelTorsion, x₁.levelPoints l ≫ j = x₂.levelPoints l) :
    x₁ = x₂ ∧ j.left ≫ x₂.toFamily.left = x₁.toFamily.left := by
  -- The pairing determines the class `c` of the line bundle (`y^* c = ⟨β y, y⟩ + 0^* c`), `j`
  -- respects the pairing and `D.β`, and `0^* c = 0` over a local ring.
  have h_cls :
      x₁.lineBundle.picClass.atPoint (𝟙 x₁.groupScheme) = x₂.lineBundle.picClass.atPoint j :=
    calc
      _ = x₁.lineBundle.picClass.pairing (D.β • 𝟙 x₁.groupScheme) (𝟙 x₁.groupScheme) +
          x₁.lineBundle.picClass.atPoint 0 :=
        (x₁.hasClassLaws.right 0 (𝟙 _)).right
      _ = x₂.lineBundle.picClass.pairing (D.β • j) j + x₂.lineBundle.picClass.atPoint 0 := by
        simp [h_pairing]
      _ = _ := (x₂.hasClassLaws.right 0 j).right.symm
  -- So rigidity of theta structures identifies the bundles with their coordinates.
  obtain ⟨h_const, h_span⟩ := hx hb
  have h_pull : x₂.lineBundle.pull j.left = x₁.lineBundle :=
    x₁.isThetaStructure.pull_eq_of_picClass_eq h_const h_span x₂.isThetaStructure
      D.odd_card j (fun _ ↦ h_levelPoints _) h_cls
  -- A point of the base is determined by `baseHom` and the coordinates of the level points.
  have h_base : x₁ = x₂ := by
    have h_base_pt : x₁ ≫ τ = x₂ ≫ τ := by simpa [baseHom, specMap] using congrArg specMap h_baseHom
    refine X.eq_of_level_coords_eq _ _ h_base_pt fun l ↦ ?_
    simp [← levelPoints_comp_toFamily, ← h_levelPoints l, ← lineBundle.eq_1, h_pull]
  exact ⟨h_base, X.embeds.ext h_pull (by aesop)⟩

end New.ThetaObject.HasSpanningCoords

end
