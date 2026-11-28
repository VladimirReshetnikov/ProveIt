import Lib.GLn.SchurModule.Basic
import Lib.General.Geometry.ProjectiveSpace
import Lib.PadicComparison.Descent.TestCategory
import Lib.Shimura.AbelianScheme.TangentCoordinates
import Lib.Shimura.ComplexTheta.AppellHumbertData

/-!
# Holomorphic families of complex points, jets, uniformisations and theta coordinates

Except in `New.Uniformisation.hasSignature_iff`, where `O` is any commutative ring acting on `A`,
`O` is a valuation ring with fraction field `ℂ` (`New.ValuativeArc`), for example `ℂ` itself. This
file develops calculus for families of complex points of schemes over `O` without an
analytification: holomorphic families, jets and a chain rule. These notions are applied to a
uniformisation `V / L ≅ A(O)` of a commutative group scheme `A`, which yields a count of its torsion
points. The file also treats linear systems whose homogeneous coordinates are theta functions, and
their behaviour under operations on line bundles.

## Main definitions and results

* `New.HolomorphicAt.exists_isJet`, `New.IsJet.unique`, `New.isJet_comp_iff`: jets exist and are
  unique, and they obey the chain rule.
* `New.HolomorphicAt.isFirstOrderConst_of_nsmul`: on a smooth commutative group scheme, if `n • φ`
  is constant to first order in a direction, for some `n ≠ 0`, then so is `φ`.
* `New.Uniformisation.hasSignature_iff`: the condition `New.HasSignature` on the matrices of the
  action of `O` in algebraic coordinates holds iff the space `V` of a uniformisation has a common
  eigenvector `Y ≠ 0` of the maps `F a`, with eigenvalues `ρ a`, such that `F b - ρ c` maps `V` into
  the line of `Y`.
* `New.Uniformisation.card_torsion`: A(O) has m^(2 dim V) points killed by m ≠ 0.
* `New.HasThetaCoords.pull`, `New.HasThetaCoords.pow`, `New.HasThetaCoords.pull_translate`,
  `New.HasThetaCoords.mul`: pull-back, power, translation and tensor product.
* `New.HasThetaCoords.riemannForm_eq_of_isFrame`: if `N ⊗ M⁻¹` has a frame, the Riemann forms and
  the multipliers of `N` and `M` agree, and along the family the frame is a constant times
  exp((B − B′)(z, z)/2)·θ′/θ.

Notions from other files:
* `New.PointFn`: a function on the points of a scheme X; it assigns to each point Spec R → X, for
  every ring R, an element of R, with no compatibility required.
* `New.LandsIn`: the point t : Spec R → X lands in the open U when all of Spec R maps into U.
* `New.IsAppellHumbert`: Appell–Humbert data (B, χ) for a lattice L: Re B is symmetric, and on L one
  has |χ| = 1 and χ(l + m) = χ(l)χ(m)·exp(πi E(m, l)), where E(u, v) = Im(B(u, v) − B(v, u))/(2π) is
  the Riemann form of B (`New.RealComplexForm.riemannForm`).
* `New.RealComplexForm.thetaSpace`: the entire functions f on V with f(z + l) = χ(l)·exp(B(l,
  z) + B(l, l)/2)·f(z) for l in L.
* `New.LineBundle.IsHomogeneousCoords`, `New.LineBundle.IsLinearSystem`: v is a vector of
  homogeneous coordinates of the point t for the line bundle N when t lands in the chart U_j exactly
  when v_j is a unit, and then g_jk(t) = v_k/v_j. N is a linear system when each transition function
  g_ij is regular on U_i and zero at the points outside U_i, and the g_ij(t), j varying, are
  homogeneous coordinates of every point t of U_i.

## Relation to the literature

Known; see `Lib.Shimura.Uniformisation.AppellHumbert` and `Lib.Shimura.ArcExtension` for sources.
-/

noncomputable section

namespace New

/-!
## Complex points over a valuation ring, holomorphic families and uniformisations

The analytic vocabulary for schemes over a valuation ring `O` with fraction field `ℂ`
(`New.ValuativeArc`; the case `O = ℂ` is included).
-/

section Uniformisation

open CategoryTheory AlgebraicGeometry MonoidalCategory PointFn

/-! ### Valuation rings of `ℂ` and sections over them -/

/-- A valuation ring O with fraction field ℂ, given with its algebra map O → ℂ, together with the
generic point Spec ℂ → Spec O, which is the morphism induced by O → ℂ. -/
class ValuativeArc (O : Type) [CommRing.{0} O] extends
    Algebra O ℂ, IsDomain O, ValuationRing O, IsFractionRing O ℂ where
  /-- The generic point `Spec ℂ ⟶ Spec O`. -/
  genericPt : Spec ⟨ℂ⟩ ⟶ Spec ⟨O⟩
  /-- The generic point is the morphism induced by the algebra map `O → ℂ`. -/
  genericPt_eq : genericPt = specMap algebraMap := by rfl

-- The projection ranks low, so that other algebra structures on `ℂ` are found first.
attribute [instance 100] ValuativeArc.toAlgebra

instance : ValuativeArc ℂ where
  genericPt := 𝟙 _
  genericPt_eq := by simp [specMap]

instance (V : ValuationSubring ℂ) : ValuativeArc V := ⟨_, rfl⟩

/-- The set of complex points of a scheme A over ℂ, that is sections of its structure morphism. -/
abbrev ComplexPoint (A : Over (Spec ⟨ℂ⟩)) : Type := 𝟙_ (Over (Spec ⟨ℂ⟩)) ⟶ A

open ValuativeArc Over OverMorphism UniversallyClosed CartesianMonoidalCategory

variable {O : Type} [CommRing O] [ValuativeArc O] {A : Over (Spec ⟨O⟩)}

instance : IsSchemeTheoreticallyDominant ‹ValuativeArc O›.genericPt := by
  -- `O → ℂ` is injective, so the generic point has dense range; and `Spec O` is reduced.
  have h_ker : RingHom.ker (algebraMap O ℂ) ≤ nilradical O := by
    simp [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O ℂ)]
  have h_dom : IsDominant (specMap (algebraMap O ℂ)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr h_ker⟩
  rw [ValuativeArc.genericPt_eq]
  exact .of_isDominant _

/-- Valuative criterion of properness: for A proper over a valuation ring O with fraction field ℂ,
restriction to the generic point of Spec O is a bijection from the sections of A over O to the
ℂ-points of A above the generic point. -/
lemma bijective_restrict_genericPt [IsProper A.hom] :
    Function.Bijective fun s : 𝟙_ (Over (Spec (CommRingCat.of O))) ⟶ A ↦
      (toUnit (Over.mk genericPt) ≫ s : Over.mk genericPt ⟶ A) := by
  refine ⟨fun a b h_eq ↦ ?_, fun t ↦ ?_⟩
  · -- `genericPt` is dominant and `A` is separated, so a section is determined by its generic
    -- point.
    have h_over : a.left ≫ A.hom = b.left ≫ A.hom := by simp
    have h_generic : genericPt ≫ a.left = genericPt ≫ b.left := congrArg CommaMorphism.left h_eq
    exact ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of O)) A.hom h_over
      genericPt h_generic)
  · -- Existence half of the valuative criterion for the universally closed morphism `A.hom`.
    have h_closed : (ValuativeCriterion.Existence ⊓ @QuasiCompact) A.hom := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    obtain ⟨h_exists, -⟩ : ValuativeCriterion.Existence A.hom ∧ QuasiCompact A.hom := h_closed
    let sq : ValuativeCommSq A.hom :=
      { R := O, K := ℂ, i₁ := t.left, i₂ := 𝟙 _, commSq := ⟨t.w.trans genericPt_eq⟩ }
    -- `l.l : Spec O ⟶ A.left` is the lift in the square formed by `t` and the identity of `Spec O`.
    obtain ⟨l⟩ : Nonempty sq.commSq.LiftStruct := (h_exists sq).exists_lift
    have h_fac : genericPt ≫ l.l = t.left :=
      calc genericPt ≫ l.l = specMap (algebraMap O ℂ) ≫ l.l := by rw [genericPt_eq]
        _ = t.left := l.fac_left
    exact ⟨homMk l.l l.fac_right, ext h_fac⟩

/-- For a family s of sections of A over Spec O, O a valuation ring of ℂ, the complex point of A
given by s(z) at the generic point. -/
def atGeneric {Z : Sort*} (s : Z → (𝟙_ (Over (Spec ⟨O⟩)) ⟶ A)) (z : Z) : Spec ⟨ℂ⟩ ⟶ A.left :=
  (toUnit (Over.mk genericPt) ≫ s z).left

/-- Over `O = ℂ`, the point `atGeneric s z` is the underlying morphism of the section `s z`. -/
@[simp]
lemma atGeneric_eq {A : Over (Spec (CommRingCat.of ℂ))} {Z : Sort*} (s : Z → ComplexPoint A) :
    atGeneric s = fun z : Z ↦ (s z).left := rfl

variable (A) [AddObj A] {X : Scheme} {ι P : Type} {T M : Type _} [FinComplexSpace.{0} P]
  (V : Type) [FinComplexSpace.{0} V] [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M]
  [IsCentralScalar ℂ M] (L : Submodule ℤ P) (φ : P → (Spec ⟨ℂ⟩ ⟶ X)) (w₀ : P)

/-! ### Holomorphic families of points and their jets -/

/-- For a family φ : T → X(ℂ) of complex points of the scheme X, a point w₀ of the space T and a
property Q of functions T → ℂ: for each open U of X containing φ(w₀) and each function f on the
points of X that is regular on U (at the points landing in U, f is given by a section over U), φ(w)
lies in U for w near w₀, and the function f ∘ φ satisfies Q. -/
def HasGermAt [TopologicalSpace T] (Q : (T → ℂ) → Prop) (φ : T → (Spec ⟨ℂ⟩ ⟶ X)) (w₀ : T) : Prop :=
  ∀ ⦃U : X.Opens⦄ ⦃f : PointFn X⦄, f.IsRegularOn U → LandsIn (φ w₀) U →
    (∀ᶠ w : T in nhds w₀, LandsIn (φ w) U) ∧ Q fun w : T ↦ f ⟨ℂ⟩ (φ w)

/-- The family φ : P → X(ℂ) of complex points of the scheme X, P a finite-dimensional complex
space, is holomorphic at w₀: functions regular near φ(w₀) pull back to functions analytic at w₀. -/
abbrev HolomorphicAt : Prop := HasGermAt (fun g : P → ℂ ↦ AnalyticAt ℂ g w₀) φ w₀

/-- τ is a jet of the family φ at w₀ for ℓ. Here τ : Spec(ℂ ⊕ M) → X is a point of X over the
trivial square-zero extension ℂ ⊕ M of ℂ by the ℂ-module M, and ℓ sends differentials on P to M. The
condition: τ lands in every open U that contains φ(w₀), and s(τ) = s(φ w₀) + ℓ(d(s ∘ φ) at w₀) for
every section s of the structure sheaf over U. -/
def IsJet (ℓ : (P →ₗ[ℂ] ℂ) →ₗ[ℂ] M) (τ : Spec ⟨TrivSqZeroExt ℂ M⟩ ⟶ X) : Prop :=
  ∀ (U : X.Opens) (s : Γ(X, U)), LandsIn (φ w₀) U → LandsIn τ U ∧
    PointFn.ofSection s ⟨TrivSqZeroExt ℂ M⟩ τ = .inl (PointFn.ofSection s ⟨ℂ⟩ (φ w₀)) +
      .inr (ℓ (fderiv ℂ (fun w : P ↦ PointFn.ofSection s ⟨ℂ⟩ (φ w)) w₀))

/-- φ is constant to first order at w₀ in the direction v: the constant point φ(w₀), seen over the
dual numbers, is the jet of φ for evaluation of differentials at v. Equivalently
(`New.isFirstOrderConst_iff`), d(s ∘ φ)(v) = 0 at w₀ for every section s over an open that contains
φ(w₀). -/
abbrev IsFirstOrderConst (v : P) : Prop :=
  IsJet φ w₀ (LinearMap.applyₗ v) (specMap (algebraMap ℂ (TrivSqZeroExt ℂ ℂ)) ≫ φ w₀)

/-- φ is a holomorphic immersion at w₀: it is holomorphic there, and constant to first order
only in the direction 0. -/
def IsHolomorphicImmersionAt : Prop :=
  HolomorphicAt φ w₀ ∧ ∀ v : P, IsFirstOrderConst φ w₀ v → v = 0

/-! ### Uniformisations and theta coordinates -/

/-- A uniformisation of A by V, for a commutative group object A over Spec O (`New.AddObj`), O a
valuation ring of ℂ, and a finite-dimensional complex space V: a surjective homomorphism from V to
the sections of A over O whose kernel is a full-rank lattice, which is a holomorphic immersion on
complex points, and through which every homomorphism holomorphic at 0 factors ℂ-linearly. -/
structure Uniformisation where
  /-- The uniformising map, an additive map from `V` to the sections of `A` over `O`. -/
  expMap : V →+ (𝟙_ (Over (Spec ⟨O⟩)) ⟶ A)
  /-- The period lattice. -/
  lattice : Submodule ℤ V
  /-- The lattice is discrete and spans `V` over `ℝ`. -/
  [isFullRankLattice : IsFullRankLattice lattice]
  /-- Every section of `A` over `O` is a value of the uniformising map. -/
  surjective : Function.Surjective expMap
  /-- The kernel of the uniformising map is the lattice. -/
  eq_zero_iff (z : V) : z ∈ lattice ↔ expMap z = 0
  /-- On complex points the uniformising map is a holomorphic immersion at every point. -/
  immersive (z : V) : IsHolomorphicImmersionAt (atGeneric expMap) z
  /-- Every additive map `γ` to the sections that is holomorphic at `0` factors through the
  uniformising map by a continuous `ℂ`-linear map. -/
  universal {W : Type} [FinComplexSpace W] (γ : W →+ (𝟙_ (Over (Spec ⟨O⟩)) ⟶ A)) :
      HolomorphicAt (atGeneric γ) 0 → ∃ F : W →L[ℂ] V, ∀ z : W, expMap (F z) = γ z

attribute [instance] Uniformisation.isFullRankLattice

attribute [simp, grind =] Uniformisation.eq_zero_iff

/-- Theta coordinates for a family φ : P → X(ℂ) of complex points and a lattice L in P: the line
bundle N is a linear system (`New.LineBundle.IsLinearSystem`), (B, χ) are Appell–Humbert data
for L, with B a form on P, and θ(z) gives homogeneous coordinates of φ(z), each θ_i being a theta
function of type (B, χ). -/
structure HasThetaCoords (N : LineBundle X ι) (B : ThetaTori.LatticeForm L) (χ : P → ℂ)
    (θ : P → ι → ℂ) where
  /-- `N` is a linear system. -/
  isLinearSystem : N.IsLinearSystem
  /-- `(B, χ)` are Appell–Humbert data for the lattice `L`. -/
  isAppellHumbert : IsAppellHumbert (V := P) (L := L) B χ
  /-- Each coordinate of `θ` is a theta function of type `(B, χ)` for `L`. -/
  mem_thetaSpace (i : ι) : (θ · i) ∈ B.thetaSpace χ
  /-- `θ z` is a vector of homogeneous coordinates of the point `φ z`. -/
  hasFieldCoords (z : P) : N.IsHomogeneousCoords (φ z) (θ z)

end Uniformisation

/-!
## Germs, jets and tangent vectors of families of complex points

Families `φ` of complex points of a scheme are treated without an analytification. Sections over an
open set are functions on ring-valued points (`New.PointFn.ofSection`), and they are pulled back
along `φ`. For `New.HolomorphicAt`, `Q` is analyticity at `w₀`.

* `New.HasGermAt.of_isHomogeneousCoords`, `New.HasGermAt.of_jointly_mono`: on a projective scheme,
  `HasGermAt` can be tested on homogeneous coordinates (`New.LineBundle.IsHomogeneousCoords`) or on
  maps that separate points.
* `New.HolomorphicAt.exists_isJet`, `New.IsJet.unique`, `New.isJet_comp_iff`: a holomorphic
  family has exactly one jet for each linear map on differentials, and jets obey the chain rule.
* `New.HolomorphicAt.isFirstOrderConst_of_nsmul`, `New.Uniformisation.hasSignature_iff`: on a
  smooth commutative group scheme, if `n • φ` is constant to first order in a direction for some
  `n ≠ 0`, so is `φ`; and the signature condition on the tangent action can be read on the space
  of a uniformisation.
-/

section HolomorphicFamily

open CategoryTheory AlgebraicGeometry Limits CartesianMonoidalCategory Filter Topology CommRingCat
  TrivSqZeroExt Variety Spec PointFn Over LineBundle ContinuousLinearMap Matrix

attribute [local instance low] Fintype.ofFinite

/-! ### Germs of families of points -/

section Germs

variable {X Y : Scheme} {ι : Type} {T : Type*} {U : X.Opens} {Q : (T → ℂ) → Prop}
  {N : LineBundle X ι} [TopologicalSpace T] {φ : T → (Spec (CommRingCat.of ℂ) ⟶ X)} {w₀ : T}

/-- Every function in `Q` is continuous at `w₀`. `Q` also contains every function that near `w₀` is
an analytic function of finitely many functions in `Q`. -/
class GermClass (Q : (T → ℂ) → Prop) (w₀ : T) where
  /-- A finite family `p` of functions in the class is continuous at `w₀`, and the class contains
  every function that agrees near `w₀` with `g ∘ p` for some `g` analytic at `p w₀`. -/
  comp {ι : Type} [Fintype ι] {p : T → ι → ℂ} : (∀ i : ι, Q (p · i)) →
    ContinuousAt p w₀ ∧
      ∀ {g : (ι → ℂ) → ℂ} {f : T → ℂ}, AnalyticAt ℂ g (p w₀) → g ∘ p =ᶠ[𝓝 w₀] f → Q f

instance : GermClass (ContinuousAt · w₀) w₀ where
  comp h_cont := ⟨continuousAt_pi.mpr h_cont,
    fun hg h_eq ↦ (hg.continuousAt.comp (continuousAt_pi.mpr h_cont)).congr h_eq⟩

namespace HasGermAt

/-- If `φ` has a germ of class `Q` at `w₀`, so has its composite with a morphism `f : X ⟶ Y`. -/
lemma comp_hom (h_germ : HasGermAt Q φ w₀) (f : X ⟶ Y) : HasGermAt Q (φ · ≫ f) w₀ :=
  fun _ _ hg ↦ h_germ (hg.pull f)

/-- If `N` is a linear system, a family of class `Q` has, near `w₀`, homogeneous coordinates for `N`
of class `Q`. -/
lemma exists_isHomogeneousCoords (h_germ : HasGermAt Q φ w₀) (hN : N.IsLinearSystem) :
    ∃ p : T → ι → ℂ, (∀ i : ι, Q (p · i)) ∧
      ∀ᶠ w : T in 𝓝 w₀, N.IsHomogeneousCoords (φ w) (p w) := by
  -- Take the affine coordinates `N.transition i j` of a chart `N.opens i` that contains `φ w₀`.
  obtain ⟨i, hi⟩ : ∃ i : ι, LandsIn (φ w₀) (N.opens i) := N.exists_landsIn (φ w₀)
  have h_near : ∀ᶠ w : T in 𝓝 w₀, LandsIn (φ w) (N.opens i) :=
    (h_germ (hN.isRegularOn_transition i i) hi).left
  have h_coords_Q (j : ι) : Q fun w : T ↦ N.transition i j (CommRingCat.of ℂ) (φ w) :=
    (h_germ (hN.isRegularOn_transition i j) hi).right
  exact ⟨fun w j ↦ N.transition i j _ (φ w), h_coords_Q,
    h_near.mono fun w h_lands ↦ hN.isHomogeneousCoords_transition h_lands⟩

variable [hQ : GermClass Q w₀] [Finite ι] {R : CommRingCat} {p : T → ι → ℂ}

/-- Let `Q` be a germ class at `w₀` and `U` an affine open set. Suppose that near `w₀` the family
stays in `U`, and that every section over `U` pulls back to a function of class `Q`. Then the family
is of class `Q`. -/
lemma of_affine (hU : IsAffineOpen U) (h_near : ∀ᶠ w : T in 𝓝 w₀, LandsIn (φ w) U)
    (h_sec : ∀ s : Γ(X, U), Q fun w : T ↦ PointFn.ofSection s (CommRingCat.of ℂ) (φ w)) :
    HasGermAt Q φ w₀ := by
  -- Near `φ w₀` the function `f` is a quotient `G / H ^ n` of sections over `U`, hence an analytic
  -- function of the values of `G` and `H`, which lie in the class.
  intro W f hf hW
  obtain ⟨H, basic_le, mem_basic⟩ :=
    hU.exists_basicOpen_le ⟨_, landsIn_iff_mem.mp hW⟩ (landsIn_iff_mem.mp h_near.self_of_nhds)
  obtain ⟨a, ha⟩ := (hf.mono basic_le).exists_ofSection
  obtain ⟨n, G, hG⟩ := exists_eq_pow_mul_of_isAffineOpen _ _ hU _ a
  let p (w : T) (i : Fin 2) : ℂ := PointFn.ofSection (![G, H] i) _ (φ w)
  obtain ⟨p_cont, p_comp⟩ := hQ.comp (p := p) fun i ↦ h_sec _
  have H_ne : p w₀ 1 ≠ 0 := by
    simpa [p, h_near.self_of_nhds, landsIn_basicOpen] using landsIn_iff_mem.mpr mem_basic
  have quotient : ∀ᶠ w : T in 𝓝 w₀, LandsIn (φ w) W ∧ p w 0 / p w 1 ^ n = f _ (φ w) := by
    filter_upwards [h_near, (p_cont.apply_nhds 1).eventually_ne H_ne] with w hw H_ne_w
    have in_basic : LandsIn (φ w) (X.basicOpen H) := by simp_all [p, landsIn_basicOpen]
    -- Evaluate `G = H ^ n * a`, an equation on the basic open set of `H`, at the point `φ w`.
    have h_eval := congrArg (evalSection (φ w) in_basic) hG
    rw [map_mul, map_pow] at h_eval
    have ev_G : p w 0 = p w 1 ^ n * f _ (φ w) := by
      simpa [p, ← ofSection_eq in_basic, ofSection_map _ _ in_basic, ha _ _ in_basic,
        TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict] using h_eval
    exact ⟨in_basic.mono basic_le, by rw [ev_G, mul_div_cancel_left₀ _ (pow_ne_zero n H_ne_w)]⟩
  have analytic : AnalyticAt ℂ (fun q : Fin 2 → ℂ ↦ q 0 / q 1 ^ n) (p w₀) :=
    ContDiffAt.analyticAt (by fun_prop (disch := exact pow_ne_zero n H_ne))
  exact (eventually_and.mp quotient).imp_right (p_comp analytic)

/-- Let `N` embed `X` in projective space over `Spec R`, and let all points `φ w` lie over one
complex point `b` of `Spec R`. If near `w₀` the points `φ w` have homogeneous coordinates `p w`
whose components lie in the class `Q`, then `φ` has a germ of class `Q` at `w₀`. -/
lemma of_isHomogeneousCoords {s : X ⟶ Spec R} {φ : T → (Spec (CommRingCat.of ℂ) ⟶ X)}
    {b : Spec (CommRingCat.of ℂ) ⟶ Spec R} (hN : N.IsProjEmbedding s) (hp : ∀ i : ι, Q (p · i))
    (h_coords : ∀ᶠ w : T in 𝓝 w₀, N.IsHomogeneousCoords (φ w) (p w))
    (h_over : ∀ w : T, φ w ≫ s = b) : HasGermAt Q φ w₀ := by
  -- The chart `N.opens i` with `p w₀ i ≠ 0` is affine, its sections are polynomials `π F` in the
  -- affine coordinates, and these are `p w j / p w i` at `φ w`.
  obtain ⟨i, hi⟩ : ∃ i : ι, p w₀ i ≠ 0 := h_coords.self_of_nhds.exists_ne_zero
  obtain ⟨affine, π, π_surj, -, ev_π⟩ := hN.exists_affine_chart i
  obtain ⟨p_cont, p_comp⟩ := hQ.comp hp
  have near : ∀ᶠ w : T in 𝓝 w₀, p w i ≠ 0 := (p_cont.apply_nhds i).eventually_ne hi
  have coord (j : ι) : AnalyticAt ℂ (fun q : ι → ℂ ↦ q j / q i) (p w₀) :=
    ContDiffAt.analyticAt (by fun_prop (disch := exact hi))
  have in_chart : ∀ᶠ w : T in 𝓝 w₀, LandsIn (φ w) (N.opens i) := by
    filter_upwards [near, h_coords] with w p_ne coords_w using (coords_w i).left.mpr p_ne.isUnit
  refine of_affine affine in_chart (π_surj.forall.mpr fun F ↦ ?_)
  have ev_F : ∀ᶠ w : T in 𝓝 w₀,
      MvPolynomial.aeval (fun j ↦ p w j / p w i) (F.map (preimage b).hom) =
        PointFn.ofSection (π F) (CommRingCat.of ℂ) (φ w) := by
    filter_upwards [near, h_coords, in_chart] with w p_ne coords_w in_chart_w
    have affine_coords (j : ι) : N.transition i j (CommRingCat.of ℂ) (φ w) = p w j / p w i := by
      rw [(coords_w i).right j p_ne.isUnit, Ring.inverse_eq_inv', div_eq_mul_inv]
    rw [ev_π in_chart_w, h_over, funext affine_coords]
    simp [MvPolynomial.aeval_eq_eval, MvPolynomial.eval_map]
  exact p_comp (.aeval_mvPolynomial coord (F.map (preimage b).hom)) ev_F

/-- Let `W` be proper over `Spec R`, with finitely many maps `π l` to projectively embedded
schemes that together separate its points. A family `φ` of points of `W` over one complex point
`b` of `Spec R` has a germ of class `Q` at `w₀` as soon as each image `φ · ≫ π l` has one. -/
lemma of_jointly_mono {W : Over (Spec R)} [h_proper : IsProper W.hom] {Z : ι → Over (Spec R)}
    (π : ∀ l : ι, W ⟶ Z l) [h_emb : ∀ l : ι, HasProjEmbedding (Z l).hom]
    (h_sep : ∀ {C : Over (Spec R)} {x y : C ⟶ W}, (∀ l : ι, x ≫ π l = y ≫ π l) → x = y)
    {φ : T → (Spec (CommRingCat.of ℂ) ⟶ W.left)} {b : Spec (CommRingCat.of ℂ) ⟶ Spec R}
    (h_germ : ∀ l : ι, HasGermAt Q (fun w : T ↦ φ w ≫ (π l).left) w₀)
    (h_over : ∀ w : T, φ w ≫ W.hom = b) : HasGermAt Q φ w₀ := by
  -- The Segre product of the embeddings of the `Z l` embeds `W`; its coordinates are products of
  -- coordinates of the points `φ w ≫ π l`.
  have h_bundle (l : ι) : ∃ (ν : Type) (N : LineBundle (Z l).left ν),
      Finite ν ∧ N.IsProjEmbedding (Z l).hom := (hasProjEmbedding_iff _).mp (h_emb l)
  choose ν N ν_finite hN using h_bundle
  have h_coords (l : ι) : ∃ p : T → ν l → ℂ, (∀ i : ν l, Q fun w ↦ p w i) ∧
      ∀ᶠ w in 𝓝 w₀, (N l).IsHomogeneousCoords (φ w ≫ (π l).left) (p w) :=
    (h_germ l).exists_isHomogeneousCoords (hN l).isLinearSystem
  choose p hp lifts using h_coords
  refine of_isHomogeneousCoords (isProjEmbedding_pi π hN h_sep) (p := fun w i ↦ ∏ l, p l w (i l))
    (fun i ↦ ?_) ?_ h_over
  · -- A product is an analytic function of its factors.
    obtain ⟨-, p_comp⟩ := hQ.comp fun l ↦ hp l (i l)
    exact p_comp (g := fun q ↦ ∏ l, q l) (ContDiffAt.analyticAt (by fun_prop)) .rfl
  · -- Both clauses of `IsHomogeneousCoords` for the product follow factor by factor.
    filter_upwards [eventually_all.mpr lifts] with w lifts_w j
    have landsIn_iff (l : ι) :
        LandsIn (φ w ≫ (π l).left) ((N l).opens (j l)) ↔ IsUnit (p l w (j l)) :=
      (lifts_w l (j l)).left
    refine ⟨?_, fun k prod_unit ↦ ?_⟩
    · -- The point lands in the product chart iff it lands in the chart of every factor.
      simp [landsIn_iInf, landsIn_iff, Finset.prod_eq_zero_iff]
    · have transition_eq (l : ι) :
          (N l).transition (j l) (k l) (CommRingCat.of ℂ) (φ w ≫ (π l).left) =
            p l w (k l) * Ring.inverse (p l w (j l)) :=
        (lifts_w l (j l)).right (k l) (IsUnit.prod_univ_iff.mp prod_unit l)
      simp [transition_eq, Finset.prod_mul_distrib]

/-- Two families of class `Q` in a projective scheme `A` give a family of class `Q` in `A × A`. -/
lemma lift {A : Over (Spec ⟨ℂ⟩)} {N : LineBundle A.left ι} (hN : N.IsProjEmbedding A.hom)
    {φ ψ : T → ComplexPoint A} (hφ : HasGermAt Q (fun w : T ↦ (φ w).left) w₀)
    (hψ : HasGermAt Q (fun w : T ↦ (ψ w).left) w₀) :
    HasGermAt Q (fun w : T ↦ (CartesianMonoidalCategory.lift (φ w) (ψ w)).left) w₀ := by
  -- The two projections separate the points of the product, which is proper as `A` is.
  have h_proper : IsProper A.hom := hN.isProper
  refine of_jointly_mono ![fst A A, snd A A] (h_emb := fun _ ↦ ⟨hN⟩)
    (h_proper := inferInstanceAs (IsProper (pullback.fst A.hom A.hom ≫ A.hom)))
    (fun h_proj ↦ CartesianMonoidalCategory.hom_ext _ _ (h_proj 0) (h_proj 1))
    (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) fun w ↦ Over.w (CartesianMonoidalCategory.lift (φ w) (ψ w))
  · simpa only [Matrix.cons_val_zero, ← comp_left, lift_fst] using hφ
  · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, ← comp_left, lift_snd] using hψ

end HasGermAt

end Germs

variable {X Y S : Scheme} {P : Type _} [FinComplexSpace P] {s : X ⟶ S}
  {φ ψ : P → (Spec (CommRingCat.of ℂ) ⟶ X)} {w₀ : P} {V M : Type}
  {A : Over (Spec (CommRingCat.of ℂ))} [FinComplexSpace V] [AddObj A]
  (u : Uniformisation (O := ℂ) A V) [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M]
  [IsCentralScalar ℂ M] {ℓ : (P →ₗ[ℂ] ℂ) →ₗ[ℂ] M}
  {τ τ' : Spec (CommRingCat.of (TrivSqZeroExt ℂ M)) ⟶ X} {v₀ : V}
  {b : Spec (CommRingCat.of ℂ) ⟶ S} {g : V → P}

instance : GermClass (AnalyticAt ℂ · w₀) w₀ where
  comp h_analytic :=
    ⟨(AnalyticAt.pi h_analytic).continuousAt, fun hg ↦ (hg.comp (.pi h_analytic)).congr⟩

namespace IsJet

/-! ### Jets -/

lemma landsIn (hτ : IsJet (M := M) φ w₀ ℓ τ) {U : X.Opens} (hU : LandsIn (φ w₀) U) : LandsIn τ U :=
  (hτ U 0 hU).left

/-- The value of a section `s` at a jet of `φ` is its value at `φ w₀` plus `ℓ` of the
derivative of `s ∘ φ` at `w₀`. -/
lemma ofSection_eq (hτ : IsJet (M := M) φ w₀ ℓ τ) {U : X.Opens} (hU : LandsIn (φ w₀) U)
    (s : Γ(X, U)) :
    PointFn.ofSection s (CommRingCat.of (TrivSqZeroExt ℂ M)) τ =
      inl (PointFn.ofSection s (CommRingCat.of ℂ) (φ w₀)) +
      inr (ℓ (fderiv ℂ (fun w : P ↦ PointFn.ofSection s (CommRingCat.of ℂ) (φ w)) w₀)) :=
  (hτ U s hU).right

/-- A family has at most one jet for a given linear map `ℓ` on differentials. -/
lemma unique (hτ : IsJet (M := M) φ w₀ ℓ τ) (hτ' : IsJet φ w₀ ℓ τ') : τ = τ' := by
  -- Both jets lie in an affine open set around `φ w₀` and give each section the same value.
  obtain ⟨U, hU, mem⟩ := exists_isAffineOpen_landsIn (φ w₀)
  exact point_eq_of_ofSection_eq hU (hτ.landsIn mem) (hτ'.landsIn mem) fun s ↦
    (hτ.ofSection_eq mem s).trans (hτ'.ofSection_eq mem s).symm

/-- The composite of a jet `τ` of `φ` with a morphism `p : X ⟶ Y` is a jet of `w ↦ φ w ≫ p`. -/
lemma comp_hom (hτ : IsJet (M := M) φ w₀ ℓ τ) (p : X ⟶ Y) : IsJet (φ · ≫ p) w₀ ℓ (τ ≫ p) :=
  fun U s ↦ hτ (p ⁻¹ᵁ U) (p.app U s)

/-- A jet of `φ` at `w₀` is also a jet of every family `ψ` that agrees with `φ` near `w₀`. -/
lemma congr (hτ : IsJet (M := M) φ w₀ ℓ τ) (h_eq : φ =ᶠ[𝓝 w₀] ψ) : IsJet ψ w₀ ℓ τ := by
  -- The value and the derivative at `w₀` depend only on the germ.
  intro U s
  have h_deriv : fderiv ℂ (fun w ↦ PointFn.ofSection s _ (φ w)) w₀ =
      fderiv ℂ (fun w ↦ PointFn.ofSection s _ (ψ w)) w₀ :=
    (h_eq.fun_comp (PointFn.ofSection s _)).fderiv_eq
  rw [← h_eq.eq_of_nhds, ← h_deriv]
  exact hτ U s

/-- Reducing a jet `τ` of `φ` at `w₀` modulo the square-zero part `M` gives the point `φ w₀`. -/
lemma fst_comp (hτ : IsJet (M := M) φ w₀ ℓ τ) : specMap (fstHom ℂ ℂ M).toRingHom ≫ τ = φ w₀ := by
  -- Both points lie in an affine open set `U` and give each section the same value.
  obtain ⟨U, hU, mem⟩ := exists_isAffineOpen_landsIn (φ w₀)
  refine point_eq_of_ofSection_eq hU ((hτ.landsIn mem).comp _) mem fun s ↦ ?_
  simp [isRegularOn_ofSection s _ _ (hτ.landsIn mem), hτ.ofSection_eq mem s]

/-- If all points `φ w` lie over one point `b` of `S`, a jet `τ` of `φ` lies over `b`, seen as a
point with values in `ℂ ⊕ M`. -/
lemma comp_base_eq (hτ : IsJet (M := M) φ w₀ ℓ τ) (h_over : ∀ w : P, φ w ≫ s = b) :
    τ ≫ s = specMap (algebraMap ℂ (TrivSqZeroExt ℂ M)) ≫ b := by
  -- `φ · ≫ s` is the constant family `b`, and its jet is the constant point `b`.
  have h_const_jet : IsJet (φ · ≫ s) w₀ ℓ (specMap (algebraMap ℂ (TrivSqZeroExt ℂ M)) ≫ b) := by
    simp +contextual [h_over, isRegularOn_ofSection _ _, IsJet, LandsIn.comp, algebraMap_eq_inl]
  exact (hτ.comp_hom s).unique h_const_jet

end IsJet

/-- A family holomorphic at `g v₀`, precomposed with a map `g` analytic at `v₀`, is holomorphic
at `v₀`. -/
lemma HolomorphicAt.comp (hφ : HolomorphicAt φ (g v₀)) (hg : AnalyticAt ℂ g v₀) :
    HolomorphicAt (fun v : V ↦ φ (g v)) v₀ :=
  fun _ _ hf hU ↦ ⟨hg.continuousAt (hφ hf hU).left, (hφ hf hU).right.comp hg⟩

/-- Let `φ` be a family of complex points of `X`, parametrised by a finite-dimensional complex space
`P` and holomorphic at `w₀`, and let `ℓ` be a linear map from linear functionals on `P` to a
ℂ-module `M`. Then there is a point `τ` of `X` over the trivial square-zero extension `ℂ ⊕ M` that
is a jet of `φ` at `w₀` for `ℓ`. That is, `τ` lands in every open containing `φ w₀`, and every
regular function `s` there satisfies `s(τ) = s(φ w₀) + ℓ(d(s ∘ φ) at w₀)`. -/
lemma HolomorphicAt.exists_isJet (hφ : HolomorphicAt φ w₀) (ℓ : (P →ₗ[ℂ] ℂ) →ₗ[ℂ] M) :
    ∃ τ : Spec (CommRingCat.of (TrivSqZeroExt ℂ M)) ⟶ X, IsJet (M := M) φ w₀ ℓ τ := by
  -- Sending a section `s` near `x = φ w₀` to the value and the derivative of `s ∘ φ` at `w₀` is a
  -- ring map to `ℂ ⊕ M` that is compatible with restriction, so it factors through the stalk at
  -- `x`; the jet is the corresponding point `Spec (ℂ ⊕ M) → Spec 𝒪_x → X`.
  let x : X := φ w₀ (IsLocalRing.closedPoint ℂ)
  have near {U : X.Opens} (hU : x ∈ U) : ∀ᶠ w : P in 𝓝 w₀, LandsIn (φ w) U :=
    (hφ (isRegularOn_ofSection 0) (landsIn_iff_mem.mpr hU)).left
  have diff {U : X.Opens} (hU : x ∈ U) (s : Γ(X, U)) :
      DifferentiableAt ℂ (fun w ↦ PointFn.ofSection s _ (φ w)) w₀ :=
    (hφ (isRegularOn_ofSection s) (landsIn_iff_mem.mpr hU)).right.differentiableAt
  let jet (f : P → ℂ) : TrivSqZeroExt ℂ M := inl (f w₀) + inr (ℓ (fderiv ℂ f w₀))
  have jet_congr {f g : P → ℂ} (h_eq : f =ᶠ[𝓝 w₀] g) : jet f = jet g := by
    simp only [jet, h_eq.eq_of_nhds, h_eq.fderiv_eq]
  let jetHom {U : X.Opens} (hU : x ∈ U) : Γ(X, U) →+* TrivSqZeroExt ℂ M :=
    { toFun s := jet fun w ↦ PointFn.ofSection s _ (φ w)
      map_one' := by
        have h_one_near : (fun w : P ↦ PointFn.ofSection (1 : Γ(X, U)) _ (φ w)) =ᶠ[𝓝 w₀] 1 :=
          (near hU).mono fun w hw ↦ by simp [ofSection_eq hw]
        simp [jet_congr h_one_near, jet]
      map_mul' s t := by simp [jet, diff hU, fderiv_fun_mul, TrivSqZeroExt.ext_iff]
      map_zero' := by simp [jet]
      map_add' s t := by simp [jet, diff hU, fderiv_fun_add, TrivSqZeroExt.ext_iff] }
  let cocone : Cocone ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf) :=
    { pt := of (TrivSqZeroExt ℂ M)
      ι.app U := ofHom (jetHom U.unop.property)
      ι.naturality _ V _ := hom_ext <| RingHom.ext fun _ ↦
        jet_congr ((near V.unop.property).mono fun _ ↦ ofSection_map _ _) }
  let stalkHom : X.presheaf.stalk x ⟶ of (TrivSqZeroExt ℂ M) := colimit.desc _ cocone
  refine ⟨map stalkHom ≫ X.fromSpecStalk x, fun U s hU ↦ ?_⟩
  have hx : x ∈ U := landsIn_iff_mem.mp hU
  refine ⟨(landsIn_fromSpecStalk hx).comp _, ?_⟩
  calc PointFn.ofSection s _ (map stalkHom ≫ X.fromSpecStalk x)
    _ = stalkHom (X.presheaf.germ U x hx s) := by
      rw [isRegularOn_ofSection s _ _ (landsIn_fromSpecStalk hx), ofSection_fromSpecStalk]
    _ = jet fun w ↦ PointFn.ofSection s _ (φ w) := colimit.ι_desc_apply cocone ..

/-- The chain rule: if `g : V → P` has derivative `g'` at `v₀`, the jet of `φ ∘ g` at `v₀` in the
direction `v : V` is the jet of `φ` at `g v₀` in the direction `g' v`. -/
lemma isJet_comp_iff {τ : Spec (CommRingCat.of (TrivSqZeroExt ℂ ℂ)) ⟶ X} {v₀ v : V}
    {g' : V →L[ℂ] P} {g : V → P} (hg : HasFDerivAt (𝕜 := ℂ) g g' v₀) (hφ : HolomorphicAt φ (g v₀)) :
    IsJet (fun u : V ↦ φ (g u)) v₀ (LinearMap.applyₗ v) τ ↔
      IsJet φ (g v₀) (LinearMap.applyₗ (g' v)) τ := by
  -- The chain rule for each section `s` near `φ (g v₀)`.
  refine forall₃_congr fun U s hU ↦ ?_
  have chain : fderiv ℂ (fun w ↦ PointFn.ofSection s _ (φ (g w))) v₀ =
      fderiv ℂ (fun w ↦ PointFn.ofSection s _ (φ w)) (g v₀) ∘L g' :=
    ((hφ (isRegularOn_ofSection s) hU).right.differentiableAt.hasFDerivAt.comp v₀ hg).fderiv
  simp [chain]

/-- `φ` is constant to first order in the direction `v` iff the following holds for every open `U`
containing `φ w₀` and every section `s` over `U`: the derivative of `s ∘ φ` at `w₀` vanishes in the
direction `v`. -/
lemma isFirstOrderConst_iff {v : P} :
    IsFirstOrderConst φ w₀ v ↔ ∀ (U : X.Opens) (s : Γ(X, U)), LandsIn (φ w₀) U →
      fderiv ℂ (fun w : P ↦ PointFn.ofSection s (CommRingCat.of ℂ) (φ w)) w₀ v = 0 := by
  simp_all [isRegularOn_ofSection _ _, IsJet, LandsIn.comp, algebraMap_eq_inl,
    TrivSqZeroExt.ext_iff]

/-! ### Immersions and tangent vectors of group schemes -/

/-- Let `A` be the fibre of `s : X ⟶ S` at the complex point `c` of `S`, with `p : A ⟶ X` the map
of the fibre square `h_pb`. Then the uniformisation of `A` followed by `p` is still a holomorphic
immersion at every `z : V`. -/
lemma Uniformisation.isHolomorphicImmersionAt_of_isPullback {p : A.left ⟶ X}
    {c : Spec (CommRingCat.of ℂ) ⟶ S} (h_pb : IsPullback p A.hom s c) (z : V) :
    IsHolomorphicImmersionAt (atGeneric u.expMap · ≫ p) z := by
  obtain ⟨h_hol, h_imm⟩ := u.immersive z
  refine ⟨h_hol.comp_hom p, fun v h_still ↦ h_imm v ?_⟩
  -- The jet `τ` of `u.expMap` in the direction `v` and the constant jet have the same images under
  -- both projections of the fibre product, so they agree.
  obtain ⟨τ, hτ⟩ := h_hol.exists_isJet (M := ℂ) (.applyₗ v)
  obtain rfl : τ = specMap (algebraMap ℂ (TrivSqZeroExt ℂ ℂ)) ≫ atGeneric u.expMap z :=
    h_pb.hom_ext ((hτ.comp_hom p).unique h_still) (by simp [hτ.comp_base_eq])
  exact hτ

/-- Let 𝒜 be a commutative group scheme over X, smooth of relative dimension d, φ a family of
complex points of 𝒜 holomorphic at w₀, and n ≠ 0. If the family w ↦ n • φ(w) is constant to first
order in the direction v, so is φ. -/
lemma HolomorphicAt.isFirstOrderConst_of_nsmul {v : P} {𝒜 : Over X} [AddObj 𝒜]
    {φ : P → (Spec (CommRingCat.of ℂ) ⟶ 𝒜.left)} {d n : ℕ} (h : HolomorphicAt φ w₀)
    (hd : SmoothOfRelativeDimension d 𝒜.hom) (hn : n ≠ 0)
    (h_still : IsFirstOrderConst (φ · ≫ (n • 𝟙 𝒜).left) w₀ v) : IsFirstOrderConst φ w₀ v := by
  -- Compare the jet `y` of `φ` in the direction `v` with the constant jet `y₀`, as points of `𝒜`
  -- over the dual numbers: `y - y₀` reduces to `0` and is killed by `n`, a unit of the dual
  -- numbers; on a smooth group scheme this forces `y - y₀ = 0`.
  obtain ⟨τ, hτ⟩ := h.exists_isJet (M := ℂ) (.applyₗ v)
  let τ₀ : Spec (CommRingCat.of (TrivSqZeroExt ℂ ℂ)) ⟶ 𝒜.left :=
    specMap (algebraMap ℂ (TrivSqZeroExt ℂ ℂ)) ≫ φ w₀
  have h_still_base : IsJet (M := ℂ) (φ · ≫ 𝒜.hom) w₀ (.applyₗ v) (τ₀ ≫ 𝒜.hom) := by
    simpa [τ₀] using h_still.comp_hom 𝒜.hom
  let y : mk (τ₀ ≫ 𝒜.hom) ⟶ 𝒜 := homMk τ ((hτ.comp_hom 𝒜.hom).unique h_still_base)
  let y₀ : mk (τ₀ ≫ 𝒜.hom) ⟶ 𝒜 := homMk τ₀
  -- `y` and `y₀` both reduce to `φ w₀`, so `y - y₀` reduces to `0`.
  have tiny : IsInfinitesimal (ofHom (fstHom ℂ ℂ ℂ).toRingHom) (y - y₀) := by
    rw [IsInfinitesimal, AddGrpObj.comp_sub, sub_eq_zero]
    exact OverMorphism.ext (hτ.fst_comp.trans (by simp [y₀, τ₀, ← map_comp_assoc, ← ofHom_comp]))
  have h_comp_eq : y ≫ (n • 𝟙 𝒜) = y₀ ≫ (n • 𝟙 𝒜) :=
    OverMorphism.ext ((hτ.comp_hom _).unique h_still)
  have h_nsmul_sub : n • (y - y₀) = 0 := by
    simpa [comp_nsmul, smul_sub, sub_eq_zero] using h_comp_eq
  obtain ⟨h_inj, -⟩ := tiny.eq_zero_of_isUnit_and_nsmul_eq_zero_of_cast_eq_zero hd (𝟙 _) n
  have y_eq : y = y₀ := sub_eq_zero.mp (h_inj (by simpa [isUnit_iff_isUnit_fst]) h_nsmul_sub)
  rwa [show τ = τ₀ from congrArg CommaMorphism.left y_eq] at hτ

/-- The signature condition read on a uniformisation. Let `u` uniformise `A`, a group scheme over
`ℂ` on which `O` acts, by a space `V` of dimension `d`, and let `A` be the fibre at the complex
point `s` of the group scheme `𝒜`, with `p` the map of the fibre square, compatible with the action
of `O` (`h_bc`). Let `a : O` act on `V` by `F a`, compatibly with `u.expMap` (`hF`), and let `z` be
a Lie chart of `𝒜` over `s` (`h_lieChart`): étale coordinates on an open set `U` around the zero
section, in which `a` acts on tangent vectors by the matrix `m a`. Then `HasSignature ρ b c m` (the
`m a` have a common eigenvector with eigenvalues `ρ a` and a unit coordinate, and `m b - ρ c` maps
into its line) holds iff some `Y ≠ 0` in `V` has `F a Y = ρ a • Y` for all `a`, and `F b - ρ c` maps
`V` into the line of `Y`. -/
lemma Uniformisation.hasSignature_iff {O : Type} {d : ℕ} [CommRing O] [ModuleObj O A]
    {F : O → V →L[ℂ] V} (hF : ∀ (a : O) (w : V), u.expMap (F a w) = a • u.expMap w) {𝒜 : Over S}
    [AddObj 𝒜] [ModuleObj O 𝒜] {s : Spec (CommRingCat.of ℂ) ⟶ S} {U : 𝒜.left.Opens}
    {z : Fin d → Γ(𝒜.left, U)} {m : O → Matrix (Fin d) (Fin d) ℂ}
    {p : (Over.map s).obj A ⟶ 𝒜} (h_lieChart : IsLieChart (ι := Fin d) 𝒜 s U z m)
    (h_bc : IsGroupBaseChange (R := O) s p) (hd : Module.finrank ℂ V = d) {ρ : O →+* ℂ} {b c : O} :
    HasSignature ρ b c m ↔
      ∃ Y ≠ (0 : V), (∀ a : O, F a Y = ρ a • Y) ∧
        ∃ ξ : V →ₗ[ℂ] ℂ, ∀ w : V, F b w - ρ c • w = ξ w • Y := by
  -- The derivative `D` at `0` of the coordinates `z` along the uniformisation is an isomorphism
  -- `V ≃ ℂ ^ d` that carries `F a` to the matrix `m a`; both sides then say the same.
  -- `τ v` is the tangent vector at `0` in the direction `v`, a point over the dual numbers.
  obtain ⟨h_hol₀, -⟩ := u.immersive 0
  obtain ⟨h_etale, h_chart⟩ := h_lieChart
  have h_jets : ∀ v : V, ∃ τ : Spec (CommRingCat.of (TrivSqZeroExt ℂ ℂ)) ⟶ A.left,
      IsJet (M := ℂ) (atGeneric u.expMap) 0 (.applyₗ v) τ :=
    fun v ↦ h_hol₀.exists_isJet (M := ℂ) (.applyₗ v)
  choose τ₀ jet using h_jets
  have τ₀_over (v : V) : τ₀ v ≫ A.hom = (specOver ℂ (TrivSqZeroExt ℂ ℂ)).hom := by
    simpa using (jet v).comp_base_eq fun w ↦ (u.expMap w).w
  let τ (v : V) : specOver ℂ (TrivSqZeroExt ℂ ℂ) ⟶ A := homMk (τ₀ v) (τ₀_over v)
  have zero_p : (AddMonObj.zero (X := A)).left ≫ p.left = s ≫ (AddMonObj.zero (X := 𝒜)).left := by
    have h_comp_zero := h_bc.pullSection_comp 0
    rw [map_zero] at h_comp_zero
    simpa [Hom.zero_def] using h_comp_zero
  have zero_mem : LandsIn (s ≫ (AddMonObj.zero (X := 𝒜)).left) U := by
    simpa [Hom.zero_def] using (h_chart (map_id _ =≫ s)).left
  have h_infinitesimal (v : V) :
      IsInfinitesimal (ofHom (fstHom ℂ ℂ ℂ).toRingHom) (h_bc.pointEquiv (τ v)) := by
    refine OverMorphism.ext (((jet v).fst_comp =≫ _).trans ?_)
    simp [zero_p, Hom.zero_def, ← map_comp_assoc, ← ofHom_comp]
  let D₀ : V →ₗ[ℂ] Fin d → ℂ := LinearMap.pi fun j ↦
    (fderiv ℂ (fun w ↦ PointFn.ofSection (z j) _ (atGeneric u.expMap w ≫ p.left)) 0).toLinearMap
  -- The coordinates of `τ v` differ from those of `0` by `ε • D₀ v`, by the definition of a jet.
  have dv_eq (v : V) : tangentCoords z (h_bc.pointEquiv (τ v)) = inr ∘ D₀ v := by
    simp [isRegularOn_ofSection _ _, tangentCoords, τ, zero_p, D₀, (jet v).comp_hom _ U,
      IsGroupBaseChange.pointEquiv, zero_mem, funext_iff, Hom.zero_def, algebraMap_eq_inl]
  -- If `D₀ v = 0`, the image of `τ v` in `𝒜` is `0` as `z` is a chart; and `u` is an immersion.
  have D₀_inj : Function.Injective D₀ := by
    obtain ⟨-, h_imm_p⟩ := u.isHolomorphicImmersionAt_of_isPullback h_bc.isPullback 0
    refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ h_imm_p v ?_
    have h_coords_zero : tangentCoords z (h_bc.pointEquiv (τ v)) = 0 := by simp [dv_eq, hv]
    have τ_zero : h_bc.pointEquiv (τ v) = 0 :=
      h_etale.eq_zero_of_tangentCoords_eq_zero (h_chart rfl).left (h_infinitesimal v) h_coords_zero
    have const : τ₀ v ≫ p.left =
        specMap (algebraMap ℂ (TrivSqZeroExt ℂ ℂ)) ≫ atGeneric u.expMap 0 ≫ p.left := by
      refine (congrArg CommaMorphism.left τ_zero).trans ?_
      simp [zero_p, Hom.zero_def]
    have h_jet_p : IsJet (M := ℂ) (atGeneric u.expMap · ≫ p.left) 0 (.applyₗ v) (τ₀ v ≫ p.left) :=
      (jet v).comp_hom p.left
    rwa [const] at h_jet_p
  let D : V ≃ₗ[ℂ] Fin d → ℂ := D₀.linearEquivOfInjective D₀_inj (by simpa using hd)
  -- Both sides are the jet at `0` of `w ↦ u.expMap (F a w) = a • u.expMap w` in the direction `v`.
  have τ_F (a : O) (v : V) : τ (F a v) = a • τ v := by
    have h_jet_F :
        IsJet (M := ℂ) (atGeneric u.expMap) (F a 0) (.applyₗ (F a v)) (τ₀ (F a v)) := by
      simpa using jet (F a v)
    have chain : IsJet (fun w ↦ atGeneric u.expMap (F a w)) 0 (.applyₗ v) (τ₀ (F a v)) :=
      (isJet_comp_iff (F a).hasFDerivAt (u.immersive (F a 0)).1).mpr h_jet_F
    refine OverMorphism.ext (chain.unique ?_)
    simpa [hF, ← comp_left] using (jet v).comp_hom (τ := (τ v).left) (a • 𝟙 A).left
  -- Take the `ε`-part of the equation `tangentCoords z (a • y) = m a *ᵥ tangentCoords z y` of the
  -- chart, for the image `y` of `τ v` in `𝒜`.
  have D_F (a : O) (v : V) : D (F a v) = m a *ᵥ D v := by
    obtain ⟨h_act, -⟩ := (h_chart rfl).right (h_infinitesimal v)
    have hD_apply (w : V) : D w = D₀ w := rfl
    simpa [dv_eq, mulVec_eq_sum, snd_sum, ← map_smul, ← τ_F, funext_iff, hD_apply,
      algebraMap_eq_inl] using congrArg (fun c ↦ snd ∘ c) (h_act a)
  -- Transport vectors along `D` and linear forms along its dual.
  simp [HasSignature, ↓reindex_equiv D.symm, ← D.apply_eq_iff_eq, D_F, ext_iff_mulVec,
    reindex_equiv (D.symm.dualMap ≪≫ₗ (dotProductEquiv ..).symm).symm, vecMulVec_mulVec, funext_iff,
    sub_mulVec, smul_mulVec]

end HolomorphicFamily

end New

/-!
## Linear lifts, lattice indices and counting torsion points

A uniformisation (`New.Uniformisation`) identifies the sections of A with V modulo its period
lattice `lattice`, the kernel of `expMap`.

* `New.Uniformisation.linear_ext`: a continuous ℂ-linear map into V is determined by its composite
  with the uniformising map.
* `New.relIndex_comap_eq_det_mul_conj_det`: for an injective ℂ-linear F preserving a lattice L, the
  index of L in F⁻¹(L) is |det F|².
* `New.Uniformisation.card_torsion`: A(O) has m^(2 dim V) points killed by m ≠ 0.
-/

section TorsionOfTorus

open Int Complex AddSubgroup LinearMap ComplexConjugate CategoryTheory MonoidalCategory Module

namespace New

variable {O : Type} [CommRing O] [ValuativeArc O]
  {A : Over (AlgebraicGeometry.Spec (CommRingCat.of O))} [AddObj A] {V : Type} {V' : Type*}
  [FinComplexSpace V] [FinComplexSpace V'] (u : Uniformisation (O := O) A V)

/-- Two continuous ℂ-linear maps into the uniformising space are equal if they agree after the
uniformisation `u.expMap`. -/
lemma Uniformisation.linear_ext {F G : V' →L[ℂ] V} (h : ∀ z : V', u.expMap (F z) = u.expMap (G z)) :
    F = G := by
  -- `F - G` is a continuous map from the connected space `V'` to the discrete lattice `u.lattice`,
  -- so it is constant, with value `(F - G) 0 = 0`.
  have h_mem (z : V') : (F - G) z ∈ u.lattice := by simp [h]
  ext z
  have h_const : (⟨(F - G) z, h_mem z⟩ : u.lattice) = ⟨(F - G) 0, h_mem 0⟩ :=
    TotallyDisconnectedSpace.eq_of_continuous _ ((F - G).continuous.subtype_mk h_mem) z 0
  simpa [sub_eq_zero] using h_const

/-- Let L be a lattice in a finite-dimensional complex space V and F an injective ℂ-linear
endomorphism of V with F(L) ⊂ L. Then the index of L in F⁻¹(L) equals det F times its
complex conjugate, that is |det F|². -/
lemma relIndex_comap_eq_det_mul_conj_det {L : Submodule ℤ V} [IsFullRankLattice L] {F : V →ₗ[ℂ] V}
    (hF_mem : ∀ z ∈ L, F z ∈ L) (hF_inj : Function.Injective F) :
    relIndex L.toAddSubgroup (L.toAddSubgroup.comap F) = F.det * conj F.det := by
  -- Take a `ℤ`-basis `b` of `L`. Its preimage `b'` under `F` is a basis of `F⁻¹ L`, and the matrix
  -- of `b` in `b'` is the matrix of `F` in `b`. So the index is the absolute value of the real
  -- determinant of `F`, which is `|det F|²`.
  let b : Basis (Fin (finrank ℤ L)) ℤ L := finBasis ℤ L
  let Φ : V ≃ₗ[ℤ] V := (LinearEquiv.ofInjectiveEndo F hF_inj).restrictScalars ℤ
  let b' : Basis (Fin (finrank ℤ L)) ℤ (L.comap Φ.toLinearMap) := b.map (Φ.ofSubmodule' L).symm
  let M : Matrix (Fin (finrank ℤ L)) (Fin (finrank ℤ L)) ℤ :=
    b'.toMatrix fun i ↦ ⟨b i, hF_mem (b i) (b i).prop⟩
  -- `b` is read as a basis of `L.toAddSubgroup.toIntSubmodule`.
  have h_index : relIndex L.toAddSubgroup (L.toAddSubgroup.comap F) = M.det.natAbs := by
    erw [relIndex_eq_natAbs_det _ _ hF_mem b b']
    rfl
  let bℝ : Basis (Fin (finrank ℤ L)) ℝ V := b.ofZLatticeBasis ℝ
  have h_matrix : M.map (↑) = toMatrix bℝ bℝ (F.restrictScalars ℝ) := by
    ext i j
    have h_image : Φ.ofSubmodule' L ⟨(b j : V), hF_mem (b j) (b j).prop⟩ =
        ⟨F (b j), hF_mem (b j) (b j).prop⟩ := rfl
    simpa [bℝ, M, b', Basis.toMatrix_apply, toMatrix_apply, h_image] using
      (b.ofZLatticeBasis_repr_apply ℝ L ⟨F (b j), hF_mem (b j) (b j).prop⟩ i).symm
  have h_det : (M.det : ℝ) = normSq F.det := by
    rw [cast_det, h_matrix, det_toMatrix, det_restrictScalars, Algebra.norm_complex_apply]
  rw [h_index, mul_conj, ← abs_of_nonneg (normSq_nonneg _), ← h_det]
  simp [← cast_abs]

/-- Let O be a valuation ring with fraction field ℂ, A a commutative group scheme over O, and u a
uniformisation, with V / u.lattice ≅ A(O) and dim V = d. For m ≠ 0, exactly m^{2d} points of A(O)
are killed by m. -/
lemma Uniformisation.card_torsion (u : Uniformisation A V) {m : ℕ} (hm : m ≠ 0) :
    Nat.card {y : 𝟙_ (Over (AlgebraicGeometry.Spec (CommRingCat.of O))) ⟶ A // m • y = 0} =
      m ^ (finrank ℂ V * 2) := by
  -- The `m`-torsion is the image under `u.expMap` of `F⁻¹ L`, for `F` the multiplication by `m` on
  -- `V` and `L = u.lattice` the kernel of `u.expMap`. So its order is the index of `L` in `F⁻¹ L`,
  -- `|det F|²`.
  let F : V →ₗ[ℂ] V := (m : ℂ) • 1
  have hF (z : V) : F z = m • z := Nat.cast_smul_eq_nsmul ℂ m z
  have h_ker : u.expMap.ker = u.lattice.toAddSubgroup := (AddSubgroup.ext u.eq_zero_iff).symm
  have h_comap : (nsmulAddMonoidHom m).ker.comap u.expMap = u.lattice.toAddSubgroup.comap F :=
    AddSubgroup.ext fun z ↦ by simp [hF]
  have h_card : Nat.card {y : 𝟙_ _ ⟶ A // m • y = 0} =
      relIndex u.lattice.toAddSubgroup (u.lattice.toAddSubgroup.comap F) := by
    rw [← h_comap, ← h_ker, relIndex_ker, map_comap_eq_self_of_surjective u.surjective]
    rfl
  have h_index : relIndex u.lattice.toAddSubgroup (u.lattice.toAddSubgroup.comap F) = F.det * conj
    F.det :=
    relIndex_comap_eq_det_mul_conj_det (fun z hz ↦ by simpa only [hF] using nsmul_mem hz m)
      (lsmul_injective (Nat.cast_ne_zero.mpr hm))
  have h_det : F.det = (m : ℂ) ^ finrank ℂ V := by simp [F]
  rw [h_card, ← Nat.cast_inj (R := ℂ), h_index, h_det]
  simp [pow_mul, sq]

end New

end TorsionOfTorus

/-!
## Theta coordinates under operations on line bundles

Line bundles `New.LineBundle` are given by a cover and a cocycle; a section `w` is a family of
functions on points, one for each chart, and a frame is a section that vanishes nowhere.

* `New.Uniformisation.atGeneric_add`, `New.Uniformisation.atGeneric_add_of_mem`: on complex
  points the uniformising map turns addition into translation and is periodic for its lattice.
* `New.HasThetaCoords.pull`, `New.HasThetaCoords.pow`, `New.HasThetaCoords.pull_translate`,
  `New.HasThetaCoords.mul`: theta coordinates under pull-back, powers, translation and tensor
  product.
* `New.HasThetaCoords.exists_theta_of_isSection`: a section of `N ⊗ M⁻¹` is given by a theta
  function of the quotient type.
-/

namespace New

open CategoryTheory Complex Finset LineBundle Submodule

variable {O : Type} [CommRing O] [ValuativeArc O]
  {X : Over (AlgebraicGeometry.Spec (CommRingCat.of O))} {ι κ V : Type} {V' : Type}
  [FinComplexSpace V] [FinComplexSpace V'] {L : Submodule ℤ V}
  {B B' : ThetaTori.LatticeForm L} {χ χ' : V → ℂ} {θ : V → ι → ℂ} {θ' : V → κ → ℂ}
  {S : AlgebraicGeometry.Scheme} {e : V → (AlgebraicGeometry.Spec (CommRingCat.of ℂ) ⟶ S)}
  {N : LineBundle S ι} {M : LineBundle S κ} [AddObj X] (u : Uniformisation (O := O) X V)

/-- On complex points, the uniformising map at `z + a` is its value at `z` followed by the
translation by the section `u.expMap a`. -/
lemma Uniformisation.atGeneric_add (a z : V) :
    atGeneric u.expMap (z + a) = atGeneric u.expMap z ≫ (translation (u.expMap a)).1 := by
  simp [← Over.comp_left, atGeneric, comp_add]

open MonoidalCategory in
/-- If the additive map `s` from `V` to the sections of `X` kills `l`, then on complex points
`s` takes the same value at `z + l` and at `z`. -/
lemma atGeneric_add_of_map_eq_zero
    (s : V →+ (𝟙_ (Over (AlgebraicGeometry.Spec (CommRingCat.of O))) ⟶ X)) {l : V} (hl : s l = 0)
    (z : V) : atGeneric s (z + l) = atGeneric s z := by simp [hl, atGeneric]

/-- On complex points the uniformising map is periodic for its lattice `u.lattice`. -/
lemma Uniformisation.atGeneric_add_of_mem (l : V) (hl : l ∈ u.lattice) (z : V) :
    atGeneric u.expMap (z + l) = atGeneric u.expMap z :=
  atGeneric_add_of_map_eq_zero u.expMap ((u.eq_zero_iff l).mp hl) z

lemma Uniformisation.holomorphicAt (z : V) : HolomorphicAt (atGeneric u.expMap) z :=
  (u.immersive z).1

namespace HasThetaCoords

/-- Let `N` have theta coordinates `θ` along `e`, let `F` be a complex linear map that sends `L'`
into `L`, and let `f` send the point `e' z` to `e (F z)`. Then the pull-back of `N` along `f` has
theta coordinates `θ ∘ F` along `e'`, of the type pulled back along `F`. -/
lemma pull (h : HasThetaCoords L e N B χ θ) {S' : AlgebraicGeometry.Scheme} {L' : Submodule ℤ V'}
    {e' : V' → (AlgebraicGeometry.Spec (CommRingCat.of ℂ) ⟶ S')} {f : S' ⟶ S} (F : V' →L[ℂ] V)
    (he : ∀ z : V', e (F z) = e' z ≫ f) (hF : ∀ l ∈ L', F l ∈ L) :
    HasThetaCoords L' e' (N.pull f) (B.pullForm F) (χ ∘ F) (θ ∘ F) where
  isLinearSystem := h.isLinearSystem.pull f
  isAppellHumbert :=
    { re_symm v w := by simpa using h.isAppellHumbert.re_symm (F v) (F w)
      norm_eq_one l hl := h.isAppellHumbert.norm_eq_one (F l) (hF l hl)
      semicharacter l hl m hm := by
        simpa [riemannForm_def] using h.isAppellHumbert.semicharacter _ (hF l hl) _ (hF m hm) }
  mem_thetaSpace i :=
    ⟨(h.mem_thetaSpace i).1.comp F.differentiable,
      fun l hl z ↦ by simpa using (h.mem_thetaSpace i).2 _ (hF l hl) (F z)⟩
  hasFieldCoords z := show N.IsHomogeneousCoords (e' z ≫ f) (θ (F z)) by
    simpa only [he z] using h.hasFieldCoords (F z)

/-- If θ gives theta coordinates of type (B, χ) for N along e, then the monomials of degree m in
θ give theta coordinates of type (mB, χ^m) for the m-th power of N. -/
lemma pow (h : HasThetaCoords L e N B χ θ) (m : ℕ) :
    HasThetaCoords L e (N.pow m) (m • B) (χ ^ m) fun (z : V) (i : Fin m → ι) ↦
      ∏ a : Fin m, θ z (i a) := by
  have θ_diff (i : ι) : Differentiable ℂ fun z : V ↦ θ z i := (h.mem_thetaSpace i).1
  have θ_add (i : ι) (l : V) (hl : l ∈ L) (z : V) :
      θ (z + l) i = χ l * exp (B l z + B l l / 2) * θ z i := (h.mem_thetaSpace i).2 l hl z
  refine
    { isLinearSystem := by simp [IsLinearSystem.pi, LineBundle.pow, h.isLinearSystem]
      isAppellHumbert := h.isAppellHumbert.nsmul m
      mem_thetaSpace := fun i ↦ ⟨by fun_prop, ?_⟩
      hasFieldCoords := ?_ }
  · -- The rule under `L` of a product of `m` coordinates is the `m`-th power of the rule.
    simp +contextual [θ_add, prod_mul_distrib, ← exp_nsmul, mul_div, mul_pow]
  · -- The monomials are homogeneous coordinates of the point in the power of `N`.
    simp +contextual [landsIn_iInf, LineBundle.pow, prod_eq_zero_iff, h.hasFieldCoords ..,
      IsHomogeneousCoords, prod_mul_distrib]

/-- Let `f : S ⟶ S` act along `e` as translation by `a`. Then the twisted translates
`thetaShift B a` of the coordinates `θ`, z ↦ exp(−(B(a, z) + B(a, a)/2))·θ(z + a), are theta
coordinates for the pull-back of `N` along `f`; the form `B` stays, and `χ l` is multiplied by
`exp (2 π i E(l, a))`, with `E` the Riemann form of `B`. -/
lemma pull_translate (h : HasThetaCoords L e N B χ θ) {f : S ⟶ S} {a : V}
    (he : ∀ z : V, e (z + a) = e z ≫ f) :
    HasThetaCoords L e (N.pull f) B (fun l : V ↦ χ l * B.riemannPhase l a)
      fun (z : V) (i : ι) ↦ B.thetaShift a (fun x : V ↦ θ x i) z where
  isLinearSystem := h.isLinearSystem.pull f
  isAppellHumbert := h.isAppellHumbert.mul_riemannPhase a
  mem_thetaSpace i := h.isAppellHumbert.thetaShift_mem (h.mem_thetaSpace i) a
  hasFieldCoords z := by
    -- The new coordinates at `z` are those at `z + a` times a nonzero exponential.
    show N.IsHomogeneousCoords (e z ≫ f) (exp (-(B a z + B a a / 2)) • θ (z + a))
    rw [← he z]
    exact (h.hasFieldCoords (z + a)).smul (exp_ne_zero _).isUnit

/-- Let θ and θ' give theta coordinates of types (B, χ) for N and (B', χ') for M along e. Then the
products θ_i·θ'_a give theta coordinates for the tensor product N ⊗ M, of type (B + B', χχ'). -/
lemma mul (h : HasThetaCoords L e N B χ θ) (h' : HasThetaCoords L e M B' χ' θ') :
    HasThetaCoords L e (N.mul M) (B + B') (χ * χ') fun (z : V) (p : ι × κ) ↦ θ z p.1 * θ' z p.2
    where
  isLinearSystem := h.isLinearSystem.mul h'.isLinearSystem
  isAppellHumbert := h.isAppellHumbert.add h'.isAppellHumbert
  mem_thetaSpace p := thetaSpace.mul (h.mem_thetaSpace p.1) (h'.mem_thetaSpace p.2)
  hasFieldCoords z := (h.hasFieldCoords z).mul (h'.hasFieldCoords z)

/-- Let `N` and `M` have theta coordinates `θ` and `θ'` along a family `e` of complex points,
holomorphic everywhere, for the lattice `L`, with Appell–Humbert data `(B, χ)` and `(B', χ')`
respectively. Let `w` be a section of `N ⊗ M⁻¹` whose values along `e` are unchanged by translation
by `L`. Then there is a theta function `G` of type `(B - B', χ * χ'⁻¹)` such that `w (i, a)` at
`e z` equals `G z * θ' z a / θ z i` whenever `θ z i` and `θ' z a` are both nonzero. -/
lemma exists_theta_of_isSection (h : HasThetaCoords L e N B χ θ)
    (h' : HasThetaCoords L e M B' χ' θ') {w : ι × κ → PointFn S}
    (hw : (N.mul M.inv).IsSection w) (he : ∀ z : V, HolomorphicAt e z)
    (hL : ∀ l ∈ L, ∀ (z : V) (q : ι × κ),
      w q (CommRingCat.of ℂ) (e (z + l)) = w q (CommRingCat.of ℂ) (e z)) :
    ∃ G ∈ (B + -B').thetaSpace (χ * χ'⁻¹), ∀ (i : ι) (a : κ) (z : V), θ z i ≠ 0 → θ' z a ≠ 0 →
      w (i, a) (CommRingCat.of ℂ) (e z) = G z * θ' z a / θ z i := by
  -- Put `G z = w q (e z) * θ z q.1 / θ' z q.2` for a chart `q` that contains `e z`. The cocycle
  -- rule for `w` makes this independent of `q`, so `G` is holomorphic; its transformation rule
  -- under `L` is the quotient of the rules for `θ` and `θ'`.
  have h_landsIn_iff (q : ι × κ) (z : V) :
      LandsIn (e z) ((N.mul M.inv).opens q) ↔ θ z q.1 ≠ 0 ∧ θ' z q.2 ≠ 0 := by
    simp [(h.hasFieldCoords z q.1).left, (h'.hasFieldCoords z q.2).left]
  obtain ⟨hw_regular, hw_cocycle⟩ := hw
  choose p hp using fun z : V ↦ (N.mul M.inv).exists_landsIn (e z)
  let G (z : V) : ℂ := w (p z) (CommRingCat.of ℂ) (e z) * θ z (p z).1 / θ' z (p z).2
  have G_eq (q : ι × κ) (z : V) (hq : LandsIn (e z) ((N.mul M.inv).opens q)) :
      G z = w q (CommRingCat.of ℂ) (e z) * θ z q.1 / θ' z q.2 := by
    obtain ⟨θp_ne, θ'p_ne⟩ := (h_landsIn_iff (p z) z).mp (hp z)
    obtain ⟨-, θ'q_ne⟩ := (h_landsIn_iff q z).mp hq
    -- The transition function is `θ z q.1 / θ z (p z).1 * (θ' z (p z).2 / θ' z q.2)`.
    simp [G, hw_cocycle (p z) q _ (e z) (hp z) hq,
      (h.hasFieldCoords z (p z).1).right q.1 θp_ne.isUnit,
      (h'.hasFieldCoords z q.2).right (p z).2 θ'q_ne.isUnit, field]
  have θ_add (i : ι) (l : V) (hl : l ∈ L) (z : V) :
      θ (z + l) i = χ l * exp (B l z + B l l / 2) * θ z i := (h.mem_thetaSpace i).2 l hl z
  have θ'_add (a : κ) (l : V) (hl : l ∈ L) (z : V) :
      θ' (z + l) a = χ' l * exp (B' l z + B' l l / 2) * θ' z a := (h'.mem_thetaSpace a).2 l hl z
  refine ⟨G, ⟨fun z ↦ ?_, fun l hl z ↦ ?_⟩, fun i a z hi ha ↦ ?_⟩
  · -- Near `z` the chart `p z` serves for all points.
    obtain ⟨h_near, h_analytic⟩ := he z (hw_regular (p z)) (hp z)
    obtain ⟨-, θ'p_ne⟩ := (h_landsIn_iff (p z) z).mp (hp z)
    have h_diff : DifferentiableAt ℂ
        (fun x : V ↦ w (p z) (CommRingCat.of ℂ) (e x) * θ x (p z).1 / θ' x (p z).2) z :=
      (h_analytic.differentiableAt.mul ((h.mem_thetaSpace (p z).1).1 z)).mul
        (((h'.mem_thetaSpace (p z).2).1 z).inv θ'p_ne)
    exact h_diff.congr_of_eventuallyEq (h_near.mono (G_eq (p z)))
  · -- The chart `p (z + l)` also contains `e z`, as `θ (z + l)` is a multiple of `θ z`.
    have h_chart : LandsIn (e z) ((N.mul M.inv).opens (p (z + l))) := by
      have h_ne : θ (z + l) (p (z + l)).1 ≠ 0 ∧ θ' (z + l) (p (z + l)).2 ≠ 0 :=
        (h_landsIn_iff _ _).mp (hp (z + l))
      rw [θ_add _ l hl, θ'_add _ l hl] at h_ne
      exact (h_landsIn_iff _ z).mpr (h_ne.imp right_ne_zero_of_mul right_ne_zero_of_mul)
    have h_factor : exp ((B + -B') l z + (B + -B') l l / 2) =
        exp (B l z + B l l / 2) / exp (B' l z + B' l l / 2) := by
      simp only [← exp_sub, _root_.add_apply, _root_.neg_apply]
      ring_nf
    rw [G_eq _ _ (hp (z + l)), G_eq _ z h_chart, hL l hl, θ_add _ l hl, θ'_add _ l hl, h_factor,
      Pi.mul_apply, Pi.inv_apply]
    ring
  · simp [G_eq (i, a) z ((h_landsIn_iff (i, a) z).mpr ⟨hi, ha⟩), hi, ha]

/-- Let `N` and `M` have theta coordinates `θ` and `θ'` along a holomorphic family of points `e`
that is periodic for `L`, and let `w` be a frame of `N ⊗ M⁻¹`. Then the two Riemann forms agree,
the two multipliers agree on `L`, and along `e` the frame is `c * exp ((B - B') z z / 2) * θ' / θ`
for a constant `c`. -/
lemma riemannForm_eq_of_isFrame (h : HasThetaCoords L e N B χ θ)
    (h' : HasThetaCoords L e M B' χ' θ') [IsFullRankLattice L] {w : ι × κ → PointFn S}
    (hw : (N.mul M.inv).IsFrame w) (he : ∀ z : V, HolomorphicAt e z)
    (hL : ∀ l ∈ L, ∀ z : V, e (z + l) = e z) :
    B.riemannForm = B'.riemannForm ∧ (∀ l ∈ L, χ l = χ' l) ∧
    ∃ c : ℂ, ∀ (i : ι) (a : κ) (z : V), θ z i ≠ 0 → θ' z a ≠ 0 →
      w (i, a) (CommRingCat.of ℂ) (e z) = c * exp ((B z z - B' z z) / 2) * θ' z a / θ z i := by
  -- `w` is `G * θ' / θ` for a theta function `G` of type `(B - B', χ / χ')`. As `w` is a frame,
  -- `G` has no zero, so by `IsAppellHumbert.eq_exp_of_ne_zero` its Riemann form vanishes,
  -- `χ / χ' = 1` on `L`, and `G z = G 0 * exp ((B - B') z z / 2)`.
  obtain ⟨hw_section, hw_unit⟩ := hw
  obtain ⟨G, hG, hwG⟩ :=
    h.exists_theta_of_isSection h' hw_section he fun l hl z q ↦ by rw [hL l hl z]
  have hG_ne (z : V) : G z ≠ 0 := by
    -- In a chart containing `e z` both coordinates are nonzero, so the unit `w` would vanish.
    intro hz
    obtain ⟨⟨i, a⟩, hp⟩ := exists_landsIn (N.mul M.inv) (e z)
    obtain ⟨hi, ha⟩ : θ z i ≠ 0 ∧ θ' z a ≠ 0 := by
      simpa [(h.hasFieldCoords z i).left, (h'.hasFieldCoords z a).left] using hp
    exact (hw_unit (i, a) (CommRingCat.of ℂ) (e z) hp).ne_zero (by simp [hwG i a z hi ha, hz])
  obtain ⟨h_riem, h_χ, h_exp⟩ :=
    (h.isAppellHumbert.add h'.isAppellHumbert.neg).eq_exp_of_ne_zero hG hG_ne
  refine ⟨?_, fun l hl ↦ eq_of_div_eq_one ?_, G 0, fun i a z hi ha ↦ ?_⟩
  · simpa [add_neg_eq_zero] using h_riem
  · simpa [div_eq_mul_inv] using h_χ l hl
  · simp [hwG i a z hi ha, h_exp z, sub_eq_add_neg, mul_comm (G 0)]

end HasThetaCoords

end New

end
