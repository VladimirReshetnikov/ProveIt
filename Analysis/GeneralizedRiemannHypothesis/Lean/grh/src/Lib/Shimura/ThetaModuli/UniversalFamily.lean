import Lib.General.Geometry.SmoothnessCriterion
import Lib.Shimura.Deformation.TangentBound
import Lib.Shimura.GoodReduction.MultiplicativeNorm
import Lib.Shimura.IntegralModel.BallImmersion
import Lib.Shimura.ThetaModuli.FamilyFromPoints

/-!
# Existence of the universal theta family over a smooth projective base

`New.Variety.ThetaNull.nonempty_universalFamily` shows, when `R` is a localization of `𝓞 E` at a
submonoid of non-zero-divisors and every maximal ideal of `R` lies over a good prime for `D`
(`IsGoodOver D R`), that the type `New.Variety.UniversalFamily D R` of universal objects is
nonempty. A universal object is a family of theta-embedded abelian schemes for the PEL data `D`
(`New.ThetaFamily`) over a projective `R`-scheme that is smooth of relative dimension
`card D.Index - 1`. Its fibres at a dense set of complex points are the theta tori
(`New.ThetaTori.ThetaTorus`) of all analytic families (`New.Variety.AnalyticFamily`). Its
uniformisations are holomorphic in the parameter and in the fibre.

The base is the reduced closure of the theta coordinates of the level points in a product of
projective spaces. `New.Variety.exists_thetaFamily_of_points` puts a family on it, using good
reduction at the level points. Smoothness comes from the immersion of the balls and the tangent
bound.

Notions from other files:
* `New.ThetaObject.TorusModel`: a model of a fibre of the family on the complex torus of a polarised
  period map, with its uniformisation and its theta functions `θ`.
* `LineBundle.IsHomogeneousCoords L t v`: `v` are homogeneous coordinates of the point `t` for `L`:
  `t` lies in the chart `j` of `L` exactly when `v j` is a unit, and there the transition function
  to the chart `k` is `v k / v j`. For a linear system (`IsLinearSystem`), the transition functions
  are regular on the charts and give homogeneous coordinates.
* `ReducedClosure`: the reduced Zariski closure `W` of a family of tuples of complex points in a
  product of schemes, with its complex points `point a`, which are dense.
* `PEL.IsGoodAt D w`: the prime `w` of `𝓞 E` is good for the data `D`: it contains neither
  `D.paddedNorm` nor the order of `D.dualTorsion`, and it contains a prime number `p` and `D.β - b`
  for an integer `b` with `D.β - b` coprime to `star D.β - b`, and two further conditions hold
  (see its definition).

## Relation to the literature

Known result: Moduli of abelian varieties by theta values via theta-null embedding and universal
family. Here the base is the closure of the theta values at the level points of PEL tori, not a
locus cut out by quartic relations; the family on it comes from
`New.Variety.exists_thetaFamily_of_points`. Source: D. Mumford, On the equations defining abelian
varieties II, Invent. Math. 3 (1967) 75-135; theta groups in part I, Invent. Math. 1 (1966) 287-354.
-/

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing RingHom New ThetaObject Obj
  LineBundle ThetaTori Over ProjSpace FaithfulSMul Ideal IsPrime PeriodMap And

noncomputable section

namespace New.Variety.ThetaNull

/-- The datum `D` is good at every closed point of `Spec R`: for each maximal ideal `m` of the
`𝓞 E`-subalgebra `R` of `E`, the datum `D` is good at the contraction of `m` to `𝓞 E`. -/
def IsGoodOver {E : Type} [Field E] [CMBase E] (D : PEL E) (R : Subalgebra (𝓞 E) E) : Prop :=
  ∀ m : Ideal R, m.IsMaximal → D.IsGoodAt (m.comap (algebraMap (𝓞 E) R))

/-- If the maximal ideals of the `𝓞 E`-subalgebra `R` of `E` lie over good primes, then `β̄ - β`
and the order of `D.dualTorsion` are units of `R`. -/
lemma isUnit_star_sub_and_card_of_isGoodOver {E : Type} [Field E] [CMBase E] {D : PEL E}
    {R : Subalgebra (𝓞 E) E} (hR_good : IsGoodOver D R) :
    IsUnit (algebraMap (𝓞 E) R (star D.β - D.β)) ∧ IsUnit (Nat.card D.dualTorsion : R) := by
  -- Otherwise the product lies in a maximal ideal `m`, whose contraction `w` to `𝓞 E` is good.
  refine IsUnit.mul_iff.mp (by_contra fun h_nonunit ↦ ?_)
  obtain ⟨m, hm, h_mem⟩ := exists_max_ideal_of_mem_nonunits h_nonunit
  obtain ⟨⟨-, hT⟩, p, b, -, -, hβ, h_coprime, -⟩ := hR_good m hm
  -- As `#T ∉ w`, the factor `β̄ - β` is in `m`; adding `β - b` puts `β̄ - b` in `w`, against
  -- coprimality.
  have h_diff : algebraMap (𝓞 E) R (star D.β - D.β) ∈ m :=
    (hm.isPrime.mem_or_mem h_mem).resolve_right (by simpa using hT)
  have h_conj : star D.β - b ∈ m.comap (algebraMap (𝓞 E) R) := by
    simpa using add_mem h_diff hβ
  exact notMem_of_isCoprime_of_mem h_coprime hβ h_conj

/-- The charts of the bundles `c l`, for `l` in `D.dualTorsion` seen inside the larger
`D.levelTorsion` that indexes the level points, cover the point `t` in the pattern of the largest
theta constants: for each `s` there is `o` such that `t` lands in the chart `k` of `c l` whenever
`l + k` is `o`, `-o` or `s - o`. -/
def HasPeakCharts {E : Type} [Field E] [CMBase E] {D : PEL E} {S : Scheme} {A : CommRingCat}
    (c : D.levelTorsion → LineBundle S D.dualTorsion) (t : Spec A ⟶ S) : Prop :=
  ∀ s : D.dualTorsion, ∃ o : D.dualTorsion, ∀ l k : D.dualTorsion,
    l + k ∈ [o, -o, s - o] → LandsIn t ((c ⟨l, D.dualTorsion_le_levelTorsion l.property⟩).opens k)

/-- The peak pattern at the closed point of an arc. Let `x` have good reduction for `v`, with
`v (#T) = 1`. Let `p ω` be the theta coordinates of the level point `ω` of `x`, taken at its lift
`x.torsionLift ω` to `V`, divided by the nonzero coordinate `i ω`, and let their residues be
homogeneous coordinates, for `c ω`, of the closed point of `α`. Then the charts of the `c ω` cover
that point in the pattern of the largest theta constants (`New.Variety.ThetaNull.HasPeakCharts`). -/
private lemma hasPeakCharts_of_hasGoodReduction {E V : Type} [Field E] [CMBase E]
    [FinComplexSpace V] {D : PEL E} {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ}
    (x : ThetaTorus D g ℓ V) {v : Valuation ℂ NNReal}
    (h_good : HasGoodReduction x.automorphyForm x.multiplier v D.paddedNorm)
      (hvT : v (Nat.card D.dualTorsion) = 1) {S : Scheme}
    {α : Spec (.of v.valuationSubring) ⟶ S} {c : D.levelTorsion → LineBundle S D.dualTorsion}
    (i : D.levelTorsion → D.dualTorsion) (p : D.levelTorsion → D.dualTorsion → v.valuationSubring)
    (h_ne : ∀ ω : D.levelTorsion, x.thetaCoord (i ω) (x.torsionLift ω) ≠ 0)
    (hp : ∀ (ω : D.levelTorsion) (j : D.dualTorsion),
      (p ω j : ℂ) = x.thetaCoord j (x.torsionLift ω) / x.thetaCoord (i ω) (x.torsionLift ω))
    (h_red : ∀ ω : D.levelTorsion,
      (c ω).IsHomogeneousCoords (specMap (residue v.valuationSubring) ≫ α)
        fun j : D.dualTorsion ↦ residue v.valuationSubring (p ω j)) :
    HasPeakCharts c (specMap (residue v.valuationSubring) ≫ α) := by
  intro s
  -- The theta constants at `o`, `-o` and `s - o` have the largest valuation.
  obtain ⟨o, ho⟩ := x.exists_forall_valuation_thetaCoord_zero_le h_good hvT s
  refine ⟨o, fun l k hk ↦ ?_⟩
  set ω : D.levelTorsion := ⟨l, D.dualTorsion_le_levelTorsion l.property⟩
  -- Up to a factor `e` that does not depend on `j`, the coordinate `j` of the level point `ω = l`
  -- has the size of the theta constant at `l + j`: the shift formula, evaluated at `0`, under `v`.
  let e : ℂ := Complex.exp (-(x.automorphyForm (x.torsionLift ω) (x.torsionLift ω) / 2))
  have h_law (j : D.dualTorsion) :
      v e * v (x.thetaCoord j (x.torsionLift ω)) = v (x.thetaCoord (l + j) 0) := by
    simpa [e, ω, thetaShift, valuation_multiplier_mul_bicharacter_eq_one, PeriodMap.torsionLift]
      using
      congrArg (fun f ↦ v (f 0)) (x.thetaShift_thetaCoord (frameTorsionClass_ratLift l.val) j)
  -- Hence the coordinate `k` is at least as large as the coordinate `i ω`, so that their quotient
  -- `p ω k` is a unit of the valuation ring.
  have h_le :
      v (x.thetaCoord (i ω) (x.torsionLift ω)) ≤ v (x.thetaCoord k (x.torsionLift ω)) := by
    rw [← mul_le_mul_iff_right₀ (a := v e) (by simp [e, pos_iff_ne_zero]), h_law, h_law]
    exact ho (l + k) hk (l + i ω)
  refine (h_red ω k).left.mpr ?_
  simpa [v.mem_maximalIdeal_iff, hp, one_le_div₀, h_ne, pos_iff_ne_zero] using h_le

/-- Good reduction along an arc. Let `α` be a map to `S` from the spectrum of the valuation ring of
`v`, where `ρ : 𝓞 E → v.valuationSubring` agrees with the complex embedding `Φ v₀` of `E` and the
prime of `𝓞 E` below the maximal ideal is good for `D`. Let each bundle `c ω` be a linear system,
and let the theta coordinates of the level point `ω` of `x` be homogeneous coordinates of the
generic point of `α` for `c ω`. Then at the closed point of `α` the bundles `c` cut out some set `Z`
(`New.Variety.ThetaNull.IsCutOutAt`): in each chart, the ideal of `Z` is cut out by the affine
coordinates there, with ranks `thetaRanks`. Also, their charts cover that point in the pattern of
the largest theta constants (`New.Variety.ThetaNull.HasPeakCharts`): for each `s` some `o` puts it
in chart `k` of `c l` whenever `l + k` is `o`, `-o` or `s - o`. -/
lemma exists_isCutOutAt_and_hasPeakCharts {E V : Type} [Field E] [CMBase E] [FinComplexSpace V]
    {D : PEL E} {g : GL D.Index (𝔸f E)} {ℓ : Matrix D.Index D.Index ℂ} (x : ThetaTorus D g ℓ V)
    {v : Valuation ℂ NNReal} {ρ : 𝓞 E →+* v.valuationSubring} (hρ : ∀ c : 𝓞 E, ρ c = Φ v₀ c.val)
    (h_goodAt : D.IsGoodAt (comap ρ (maximalIdeal v.valuationSubring))) {S : Scheme}
    {α : Spec (.of v.valuationSubring) ⟶ S} {c : D.levelTorsion → LineBundle S D.dualTorsion}
    (hc : ∀ ω : D.levelTorsion, (c ω).IsLinearSystem)
    (hx : ∀ ω : D.levelTorsion, (c ω).IsHomogeneousCoords (specMap v.valuationSubring.subtype ≫ α)
      fun j : D.dualTorsion ↦ x.thetaCoord j (x.torsionLift ω)) :
    (∃ Z : Set (D.dualTorsion → ResidueField v.valuationSubring),
      IsCutOutAt D.paddedNorm D.exponentBound (thetaRanks D.dualTorsion D.paddedNorm) c
        (specMap (residue v.valuationSubring) ≫ α) Z) ∧
    HasPeakCharts c (specMap (residue v.valuationSubring) ≫ α) := by
  -- Over the local ring each level point lies in one chart `i ω`. Its transition functions `p ω`
  -- are integral coordinates of the theta vector and reduce to coordinates of the closed point.
  obtain ⟨h_good, hvT⟩ := x.hasGoodReduction_and_val_card_eq_one hρ h_goodAt
  choose i hi using fun ω : D.levelTorsion ↦ (c ω).exists_landsIn α
  let p (ω : D.levelTorsion) (j : D.dualTorsion) : v.valuationSubring :=
    (c ω).transition (i ω) j (.of _) α
  -- the complex point of the arc lands in the chart `i ω`, so its coordinate `i ω` is a unit
  have h_ne (ω : D.levelTorsion) : x.thetaCoord (i ω) (x.torsionLift ω) ≠ 0 :=
    ((hx ω (i ω)).left.mp ((hi ω).comp _)).ne_zero
  have hp (ω : D.levelTorsion) (j : D.dualTorsion) :
      (p ω j : ℂ) = x.thetaCoord j (x.torsionLift ω) / x.thetaCoord (i ω) (x.torsionLift ω) := by
    -- `p ω j`, seen in `ℂ`, is the transition function at the complex point of the arc
    have h_value :
        (c ω).transition (i ω) j (.of ℂ) (specMap v.valuationSubring.subtype ≫ α) = (p ω j : ℂ) :=
      (hc ω).isRegularOn_transition (i ω) j (CommRingCat.ofHom v.valuationSubring.subtype) α (hi ω)
    simp [← h_value, (hx ω (i ω)).right j (h_ne ω).isUnit, div_eq_mul_inv]
  have h_red (ω : D.levelTorsion) :
      (c ω).IsHomogeneousCoords (specMap (residue v.valuationSubring) ≫ α)
        fun j ↦ residue v.valuationSubring (p ω j) := by
    -- at the closed point the transition functions are the residues of `p ω`
    have h_value (j : D.dualTorsion) : residue v.valuationSubring (p ω j) =
        (c ω).transition (i ω) j (.of _) (specMap (residue v.valuationSubring) ≫ α) :=
      ((hc ω).isRegularOn_transition (i ω) j (CommRingCat.ofHom (residue _)) α (hi ω)).symm
    rw [funext h_value]
    exact (hc ω).isHomogeneousCoords_transition ((hi ω).comp _)
  -- Any theta vector is made integral by dividing by a coordinate `m z` of largest valuation.
  have h_max (z : V) : ∃ m : D.dualTorsion, ∀ t : D.dualTorsion,
    v (x.thetaCoord t z) ≤ v (x.thetaCoord m z) :=
    Finite.exists_max _
  choose m hm using h_max
  -- otherwise every coordinate has valuation at most `v 0 = 0`, so the theta vector is zero
  have hm_ne (z : V) : x.thetaCoord (m z) z ≠ 0 := fun h_zero ↦
    x.thetaCoord_vector_ne_zero z (by simpa [h_zero, funext_iff] using hm z)
  let q (z : V) (j : D.dualTorsion) : v.valuationSubring :=
    ⟨x.thetaCoord j z / x.thetaCoord (m z) z, by simp [div_le_one_of_le₀, hm]⟩
  have hq (z : V) : IsIntegralCoords (fun t : D.dualTorsion ↦ x.thetaCoord t z) (q z) :=
    ⟨x.thetaCoord (m z) z, fun j ↦ rfl, m z, by simp [q, hm_ne]⟩
  have hp_integral (ω : D.levelTorsion) :
      IsIntegralCoords (fun t : D.dualTorsion ↦ x.thetaCoord t (x.torsionLift ω)) (p ω) :=
    ⟨x.thetaCoord (i ω) (x.torsionLift ω), hp ω, i ω, by simp [hp, h_ne]⟩
  exact ⟨⟨_, x.isCutOutAt_reduction residue_surjective h_good hq hp_integral h_red⟩,
    hasPeakCharts_of_hasGoodReduction x h_good hvT i p h_ne hp h_red⟩
variable {E : Type} [Field E] [CMBase E] {D : PEL E} {R : Subalgebra (𝓞 E) E}

/-- A parameter is an analytic family together with a point of the space containing its domain. -/
abbrev FamilyParameter (D : PEL E) : Type := AnalyticFamily D × BallBase D.Index

/-- The theta torus of the family `a.1` at the point `a.2`. -/
abbrev FamilyParameter.torus (a : FamilyParameter D) :
    ThetaTorus D a.1.frame (a.1.reflection a.2) (BallFibre E D.Index) :=
  a.1.torus a.2

/-- The theta coordinates of the level point `ω` of the theta torus at the parameter `a`. -/
abbrev FamilyParameter.levelCoords (a : FamilyParameter D) (ω : D.levelTorsion)
    (j : D.dualTorsion) : ℂ :=
  a.torus.thetaCoord j (a.torus.torsionLift ω)

/-- For a parameter `a` and a level point `ω`, some complex point `t` of projective space over `R`
lies over the complex point `specOver R ℂ` of `Spec R` and has the theta coordinates of `ω` at `a`
as homogeneous coordinates for the hyperplane bundle. -/
lemma exists_isHomogeneousCoords_levelCoords (R : Subalgebra (𝓞 E) E) (ω : D.levelTorsion)
    (a : FamilyParameter D) :
    ∃ t : Spec (.of ℂ) ⟶ ProjSpace D.dualTorsion ⨯ Spec (.of R), t ≫ prod.snd = (specOver R ℂ).hom ∧
      ((hyperplaneBundle D.dualTorsion).pull prod.fst).IsHomogeneousCoords t (a.levelCoords ω) := by
  obtain ⟨j, hj⟩ : ∃ j : D.dualTorsion, a.levelCoords ω j ≠ 0 :=
    Function.ne_iff.mp (a.torus.thetaCoord_vector_ne_zero _)
  exact exists_isHomogeneousCoords (specOver R ℂ).hom hj.isUnit

/-- The complex point of projective space over `R` whose homogeneous coordinates are the theta
coordinates of the level point `ω` at the parameter `a`. -/
def levelPoint (R : Subalgebra (𝓞 E) E) (ω : D.levelTorsion) (a : FamilyParameter D) :
    specOver R ℂ ⟶ Over.mk (prod.snd : ProjSpace D.dualTorsion ⨯ Spec (.of R) ⟶ Spec (.of R)) :=
  homMk (exists_isHomogeneousCoords_levelCoords R ω a).choose
    (exists_isHomogeneousCoords_levelCoords R ω a).choose_spec.1

/-- The theta coordinates of the level point `ω` at `a` are homogeneous coordinates of
`levelPoint R ω a`. -/
lemma isHomogeneousCoords_levelPoint (ω : D.levelTorsion) (a : FamilyParameter D) :
    ((hyperplaneBundle D.dualTorsion).pull prod.fst).IsHomogeneousCoords (levelPoint R ω a).left
      (a.levelCoords ω) :=
  (exists_isHomogeneousCoords_levelCoords R ω a).choose_spec.2

/-- The reduced closure, in a product of projective spaces over `R` indexed by the level torsion,
of the theta coordinates of the level points at the parameters `y b`. -/
abbrev ThetaClosure [Fintype D.levelTorsion] (R : Subalgebra (𝓞 E) E) {B : Type}
    (y : B → FamilyParameter D) : Type 1 :=
  ReducedClosure fun (ω : D.levelTorsion) (b : B) ↦ levelPoint R ω (y b)

namespace ThetaClosure

section AnyParameters

variable [Fintype D.levelTorsion] {B : Type} {y : B → FamilyParameter D} (C : ThetaClosure R y)

/-- The hyperplane bundle of the factor `ω`, pulled back to the closure. -/
abbrev coordBundle (ω : D.levelTorsion) : LineBundle C.scheme.left D.dualTorsion :=
  ((hyperplaneBundle D.dualTorsion).pull prod.fst).pull (C.proj ω).left

/-- The complex point of the closure at the parameter `y b`. -/
abbrev complexPoint (b : B) : Spec (.of ℂ) ⟶ C.scheme.left := (C.point b).left

/-- The structure map of the closure to `Spec (𝓞 E)`. -/
abbrev toIntegers : C.scheme.left ⟶ Spec (.of (𝓞 E)) := C.scheme.hom ≫ specMap (algebraMap (𝓞 E) R)

lemma isLinearSystem_coordBundle (ω : D.levelTorsion) : (C.coordBundle ω).IsLinearSystem :=
  (isLinearSystem_hyperplaneBundle.pull _).pull _

/-- The theta coordinates of the level point `ω` at the parameter `y b` are homogeneous
coordinates of the complex point at `b` for the bundle of the factor `ω`. -/
lemma isHomogeneousCoords_complexPoint (b : B) (ω : D.levelTorsion) :
    (C.coordBundle ω).IsHomogeneousCoords (C.complexPoint b) ((y b).levelCoords ω) := by
  -- The bundle is pulled back along the projection to the factor `ω`, which sends the point at `b`
  -- to `levelPoint R ω (y b)`.
  rw [IsHomogeneousCoords.pull_iff, ← comp_left, C.point_comp_proj]
  exact isHomogeneousCoords_levelPoint ω (y b)

/-- The morphism `C.scheme.hom` has a projective embedding, obtained via `C.incl` into a product of
projective spaces. -/
instance hasProjEmbedding : HasProjEmbedding C.scheme.hom :=
  HasProjEmbedding.of_isClosedImmersion_pi C.incl (h := fun _ ↦ ⟨isProjEmbedding_projSpace⟩)

/-- The product of the bundles `C.coordBundle ω` over all `ω` embeds the closure in projective
space over `R`. -/
lemma isProjEmbedding_pi_coordBundle : (pi C.coordBundle).IsProjEmbedding C.scheme.hom :=
  isProjEmbedding_pi C.proj (fun _ ↦ isProjEmbedding_projSpace) C.hom_ext

variable [IsNoetherianRing R] {κ : Type} [Finite κ] {j : κ → B}

/-- Let `R` be a noetherian `𝓞 E`-subalgebra of the CM field `E`, with the PEL data `D` good at its
maximal ideals. If finitely many points `j i` are dense in the closure `C`, then every point `z`
specialises to the centre of an arc through one of them, and the arc lies over a good prime. -/
lemma exists_arc_isGoodAt (hR_good : IsGoodOver D R)
    (h_dense : IsDenseFamily fun i : κ ↦ C.complexPoint (j i)) (z : C.scheme.left) :
    ∃ (i : κ) (v : Valuation ℂ NNReal) (α : Spec (.of v.valuationSubring) ⟶ C.scheme.left),
      specMap v.valuationSubring.subtype ≫ α = C.complexPoint (j i) ∧
      z ⤳ α (closedPoint v.valuationSubring) ∧
      D.IsGoodAt
        ((maximalIdeal v.valuationSubring).comap (Spec.preimage (α ≫ C.toIntegers)).hom) := by
  -- By properness `z` specialises to a point `w` over a maximal ideal `m` of `R`.
  have h_noeth : IsLocallyNoetherian C.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian C.scheme.hom
  obtain ⟨m, hm, hzm⟩ := (C.scheme.hom z).asIdeal.exists_le_maximal (C.scheme.hom z).isPrime.ne_top
  obtain ⟨w, hzw, hw⟩ : ∃ w : C.scheme.left, z ⤳ w ∧ C.scheme.hom w = ⟨m, hm.isPrime⟩ :=
    C.scheme.hom.isClosedMap.specializingMap
      ((PrimeSpectrum.le_iff_specializes _ ⟨m, hm.isPrime⟩).mp hzm)
  -- An arc from one of the dense complex points `j i` has `w` as its closed point.
  obtain ⟨i, v, α, hα, rfl⟩ := exists_valuative_arc_of_isDenseFamily _ h_dense w
  refine ⟨i, v, α, hα, hzw, ?_⟩
  -- The ideal in question is the prime of `𝓞 E` below `m`.
  have h_ideal :
      (maximalIdeal v.valuationSubring).comap (Spec.preimage (α ≫ C.toIntegers)).hom =
        (C.scheme.hom (α (closedPoint v.valuationSubring))).asIdeal.comap (algebraMap (𝓞 E) R) :=
    congrArg (fun f ↦ (f (closedPoint _)).asIdeal) (Spec.map_preimage (α ≫ C.toIntegers))
  rw [h_ideal, hw]
  exact hR_good m hm

/-- The family `X` over the closure has the theta tori as fibres: at each point `b` there is a model
of the fibre on the torus at `y b` whose theta coordinates are those of the torus. -/
def HasThetaFibres (X : ThetaFamily D C.scheme.left C.toIntegers) : Prop :=
  ∀ b : B, X.IsModelledOn (C.complexPoint b) (y b).torus

/-- Let `R` be a noetherian `𝓞 E`-subalgebra of the CM field `E`, the localisation of `𝓞 E` at `M`,
with the PEL data `D` good at its maximal ideals. Let `C` be the reduced closure, in a product over
the level torsion of projective spaces over `R`, of the theta coordinates of the level points at the
parameters `y b`. If the complex points of `C` at finitely many parameters `y (j i)` are dense, then
there is a theta family `X` over `C` (via its structure map to `Spec 𝓞 E`) such that for every `b`
the fibre at the complex point `b` has a model on the theta torus at `y b` with the same theta
coordinates. -/
lemma exists_hasThetaFibres (M : Submonoid (𝓞 E)) [IsLocalization M R] (hR_good : IsGoodOver D R)
    (h_dense : IsDenseFamily fun i : κ ↦ C.complexPoint (j i)) :
    ∃ X : ThetaFamily D C.scheme.left C.toIntegers, C.HasThetaFibres X := by
  -- Apply `exists_thetaFamily_of_points`, using good reduction along the arcs `α z`, whose closed
  -- points are `t z`.
  have h_noeth : IsLocallyNoetherian C.scheme.left :=
    LocallyOfFiniteType.isLocallyNoetherian C.scheme.hom
  have h_base (b : B) (c : 𝓞 E) :
      (Spec.preimage (C.complexPoint b ≫ C.toIntegers)).hom c = Φ v₀ c.val := by
    -- after unfolding, both sides are the embedding of `𝓞 E` in `ℂ` through `R`
    simp [complexPoint, toIntegers]
    rfl
  choose i v α hα h_spec h_good using C.exists_arc_isGoodAt hR_good h_dense
  let t (z : C.scheme.left) : Spec (.of (ResidueField (v z).valuationSubring)) ⟶ C.scheme.left :=
    specMap (residue (v z).valuationSubring) ≫ α z
  have h_red (z : C.scheme.left) :
      (∃ Z, IsCutOutAt D.paddedNorm D.exponentBound (thetaRanks D.dualTorsion D.paddedNorm)
        C.coordBundle (t z) Z) ∧
        HasPeakCharts C.coordBundle (t z) := by
    refine exists_isCutOutAt_and_hasPeakCharts (y (j (i z))).torus ?_ (h_good z)
      C.isLinearSystem_coordBundle ?_
    · simpa [← hα z] using h_base (j (i z))
    · simpa only [hα z] using C.isHomogeneousCoords_complexPoint (j (i z))
  have h_closed (z : C.scheme.left) :
      z ⤳ t z (closedPoint (ResidueField (v z).valuationSubring)) := by
    have h_spec_z : z ⤳ α z (closedPoint (v z).valuationSubring) := h_spec z
    rwa [← comap_closedPoint (residue _)] at h_spec_z
  obtain ⟨hβ_unit, hT_unit⟩ := isUnit_star_sub_and_card_of_isGoodOver hR_good
  refine exists_thetaFamily_of_points j h_dense
    (IsPreimmersion.of_isLocalization M).instMonoScheme h_base C.isLinearSystem_coordBundle
    C.isProjEmbedding_pi_coordBundle C.isHomogeneousCoords_complexPoint hβ_unit hT_unit
    (fun z ↦ ⟨_, inferInstance, inferInstance, t z, h_closed z, (h_red z).left⟩) fun z s ↦ ?_
  -- A chart is open, so it holds `z` once it holds the closed point of the arc.
  obtain ⟨o, ho⟩ : ∃ o : D.dualTorsion, ∀ l k : D.dualTorsion, l + k ∈ [o, -o, s - o] →
      LandsIn (t z) ((C.coordBundle ⟨l, D.dualTorsion_le_levelTorsion l.property⟩).opens k) :=
    (h_red z).right s
  have h_index (a : D.dualTorsion) (ha : a ∈ [o, -o, s - o]) :
    IsNonvanishingIndex C.coordBundle z a :=
    fun l k hk ↦ (h_closed z).mem_open (LineBundle.opens ..).isOpen
      (landsIn_iff_mem.mp (ho l k (by rwa [hk])))
  exact ⟨o, h_index o (by simp), h_index (-o) (by simp), h_index (s - o) (by simp)⟩

end AnyParameters

variable [Fintype D.levelTorsion] (C : ThetaClosure R (id : FamilyParameter D → FamilyParameter D))

/-- In an analytic family `F` the point of the closure depends holomorphically on the parameter. -/
lemma holomorphicAt_complexPoint {F : AnalyticFamily D} ⦃b : BallBase D.Index⦄ (hb : b ∈ F.domain) :
    HolomorphicAt (fun b' : BallBase D.Index ↦ C.complexPoint (F, b')) b := by
  -- After scaling by `u b' ≠ 0` the theta coordinates are analytic in `b'`.
  obtain ⟨u, hu, hu_ne⟩ := F.exists_analytic_thetaCoord hb
  -- The coordinates of the point at `b'` in the product of the bundles are the products over `ω`
  -- of the scaled theta coordinates of the level points `ω`.
  let coords (b' : BallBase D.Index) (k : D.levelTorsion → D.dualTorsion) : ℂ :=
    ∏ ω : D.levelTorsion, (u b' • FamilyParameter.levelCoords (F, b') ω) (k ω)
  have h_analytic (k : D.levelTorsion → D.dualTorsion) : AnalyticAt ℂ (fun b' ↦ coords b' k) b :=
    Finset.analyticAt_fun_prod _ fun ω _ ↦
      (hu ..).comp₂ analyticAt_id (F.analyticAt _ hb (toRealVectors (ratLift F.frame ω.1)))
  refine .of_isHomogeneousCoords C.isProjEmbedding_pi_coordBundle h_analytic
    (hu_ne.mono fun b' h_unit ↦ ?_) fun _ ↦ Over.w _
  exact .pi (w := (·)) fun ω ↦ (C.isHomogeneousCoords_complexPoint (F, b') ω).smul h_unit

/-- Let `m a` be a model of the fibre of `X` at the parameter `a` on the theta torus at `a`, whose
theta functions `(m a).θ` are those of the torus (`hθ`). Then for a point `b` of the domain of an
analytic family `F`, the uniformisations `(m (F, b')).uniformisation` of the fibres, followed by the
maps to the total space, are holomorphic in the parameter `b'` and the fibre variable together. -/
lemma holomorphicAt_uniformisation {X : ThetaFamily D C.scheme.left C.toIntegers}
    (m : ∀ a : FamilyParameter D, TorusModel (X := X) (C.complexPoint a) a.torus.toPeriodMap)
    (hθ : ∀ a : FamilyParameter D,
      (m a).θ = fun (z : BallFibre E D.Index) (μ : D.dualTorsion) ↦ a.torus.thetaCoord μ z)
    (F : AnalyticFamily D) (b : BallBase D.Index) (hb : b ∈ F.domain) (z : BallFibre E D.Index) :
    HolomorphicAt (fun q : BallBase D.Index × BallFibre E D.Index ↦
      atGeneric (m (F, q.1)).uniformisation.expMap q.2 ≫
        (ThetaObject.toFamily (X := X) (C.complexPoint (F, q.1))).left) (b, z) := by
  -- Both the theta coordinates on the fibre and the coordinates of the base point are holomorphic.
  obtain ⟨u, hu, hu_ne⟩ := F.exists_analytic_thetaCoord hb
  obtain ⟨q, hq, hq_lifts⟩ := (C.holomorphicAt_complexPoint hb).exists_isHomogeneousCoords
    C.isProjEmbedding_pi_coordBundle.isLinearSystem
  refine .of_isHomogeneousCoords (b := (specOver R ℂ).hom)
    (X.embeds.mul C.isProjEmbedding_pi_coordBundle)
    (fun _ ↦ (hu ..).mul ((hq _).comp analyticAt_fst))
    (((hq_lifts.and hu_ne).prod_inl_nhds _).mono fun w ⟨h_base, h_unit⟩ ↦ .mul ?_ ?_)
    fun _ ↦ by simp [complexPoint]
  · -- the bundle of a fibre is `X.lineBundle` pulled back along the map of the fibre to the total
    -- space
    simpa [hθ, lineBundle, IsHomogeneousCoords.pull_iff] using
      ((m _).hasThetaCoords.hasFieldCoords _).smul h_unit
  · simpa [IsHomogeneousCoords.pull_iff] using h_base

variable [IsDedekindDomain R] (M : Submonoid (𝓞 E)) [IsLocalization M R]

include M in
/-- Let `R` be a Dedekind domain, the localisation of `𝓞 E` at `M`, with `D` good at its maximal
ideals. Parameters `x = (F, b)` and `x'` whose moduli points `F.ballPoint 0 (b, 0)` are isomorphic
at level `D.level` (by `z`, which lies in the level group `levelGU D.Index D.level` and matches
their reflections) have the same point in the closure. -/
lemma point_eq_of_isLevelIso (hR_good : IsGoodOver D R) {x x' : FamilyParameter D}
    {z : GL D.Index E}
    (h_iso : (x.fst.ballPoint 0 (x.snd, 0) : ModuliPoint E D.Index 0).IsLevelIso
      (levelGU D.Index D.level) z (x'.fst.ballPoint 0 (x'.snd, 0))) :
    C.point x = C.point x' := by
  -- Compare the models of the two fibres in the family over the closure of these two parameters.
  obtain ⟨C'⟩ : Nonempty (ThetaClosure R ![x, x']) := inferInstance
  obtain ⟨X, hX⟩ := C'.exists_hasThetaFibres (j := id) M hR_good C'.isSeparatingFamily.right
  choose m _ using hX
  have h_eq : C'.point 0 = C'.point 1 := by
    -- `h_pt`: by the level isomorphism, the models `m 0` and `m 1` give the same point of the
    -- fibre power.
    have h_pt : pointOf _ _ = pointOf _ _ :=
      (ThetaFamily.IsPointOf.eq_iff (𝔪 := 1) ⟨m 0, rfl⟩ ⟨m 1, rfl⟩).mpr
        ⟨z, levelGU_inf_one.ge h_iso.mem_level, h_iso.reflection_eq, h_iso.sub_mem_lattice⟩
    -- The two points are the images in the base of one point of the fibre power.
    have h_base : C'.complexPoint 0 = C'.complexPoint 1 := by
      simpa only [pointOf_hom] using h_pt =≫ Over.hom _
    exact OverMorphism.ext h_base
  -- `C` and `C'` have the same factors, and the points of `C` are determined by their projections
  have h_proj (ω : D.levelTorsion) : C.point x ≫ C.proj ω = C.point x' ≫ C.proj ω := by
    simpa using h_eq =≫ C'.proj ω
  exact C.hom_ext h_proj

/-- The point `b` of the domain of `F` is generic: the point of the closure at `b` specialises to
the points at all parameters in the domain of `F`. -/
def IsGenericParameter (F : AnalyticFamily D) (b : BallBase D.Index) : Prop :=
  b ∈ F.domain ∧
    ∀ b' ∈ F.domain, C.complexPoint (F, b) (closedPoint ℂ) ⤳ C.complexPoint (F, b') (closedPoint ℂ)

include M in
/-- The generic points of finitely many analytic families are dense in the closure. -/
lemma exists_finite_isDenseFamily (hR_good : IsGoodOver D R) :
    ∃ (ι : Type) (_ : Finite ι) (a : ι → FamilyParameter D),
      (∀ i : ι, C.IsGenericParameter (a i).fst (a i).snd) ∧
      IsDenseFamily fun i : ι ↦ C.complexPoint (a i) := by
  -- Every moduli point is isomorphic at level `D.level` to a point of one of finitely many
  -- families.
  obtain ⟨ι, f, hι, h_rep⟩ := ModuliPoint.exists_finite_analyticFamily_isLevelIso D 0
    D.level_ne_zero
  choose b hb h_generic using fun i : ι ↦ exists_generic_member C.scheme.hom (f i).domain.isOpen
    (f i).isConnected C.holomorphicAt_complexPoint
  refine ⟨ι, hι, fun i ↦ (f i, b i), fun i ↦ ⟨hb i, h_generic i⟩, fun p ↦ ?_⟩
  refine C.isSeparatingFamily.right.induction_on p isClosed_closure fun x ↦ ?_
  obtain ⟨i, a, ha, z, h_iso⟩ := h_rep (x.fst.ballPoint 0 (x.snd, 0))
  have h_pt : C.point x = C.point (f i, a.1) :=
    C.point_eq_of_isLevelIso M hR_good (z := z) ⟨h_iso.mem_level, h_iso.reflection_eq, nofun⟩
  simpa [h_pt] using closure_mono (by simp) (h_generic i _ ha.1).mem_closure

/-- Let `X` have the theta tori as fibres and `a` be a generic parameter. Let `α` be an arc whose
generic point is the complex point at `a` and whose closed point lies over a prime good for `D`.
Then some open `U` through which `α` factors is smooth of relative dimension `card D.Index - 1`
over `Spec R`. -/
lemma exists_smooth_near_arc {X : ThetaFamily D C.scheme.left C.toIntegers}
    (hX : C.HasThetaFibres X)
    {a : FamilyParameter D} (ha : C.IsGenericParameter a.fst a.snd) {v : Valuation ℂ NNReal}
    {α : Spec (.of v.valuationSubring) ⟶ C.scheme.left}
    (hα : specMap v.valuationSubring.subtype ≫ α = C.complexPoint a)
    (h_good : D.IsGoodAt
      ((maximalIdeal v.valuationSubring).comap (Spec.preimage (α ≫ C.toIntegers)).hom)) :
    ∃ U : C.scheme.left.Opens, LandsIn α U ∧
      SmoothOfRelativeDimension (Fintype.card D.Index - 1) (U.ι ≫ C.scheme.hom) := by
  -- The family is an immersion at the generic point, and `card D.Index - 1` bounds the dimension
  -- of the tangent space at the closed point.
  obtain ⟨F, b⟩ := a
  obtain ⟨hb, h_generic⟩ := ha
  choose m hθ using hX
  have h_imm : IsHolomorphicImmersionAt (fun b' : BallBase D.Index ↦ C.complexPoint (F, b')) b :=
    F.isHolomorphicImmersionAt_of_holomorphicAt (fun b' ↦ m (F, b')) hb
      (C.holomorphicAt_uniformisation m hθ F b hb)
  -- near `b`, the points along `F` are specialisations of the point at `b` (`h_generic`)
  refine exists_landsIn_smoothOfRelativeDimension (ϑ := residue _) C.scheme.hom h_imm hα
    (fun _ ↦ Over.w _)
    (algebraMap_injective ..) ((F.domain.isOpen.eventually_mem hb).mono h_generic)
    fun _ τ h_reduction h_over ↦ ?_
  -- The model of the generic fibre extends along the arc, so
  -- `finrank_tangent_le_card_index_sub_one` applies.
  obtain ⟨m', -⟩ := (m (F, b)).exists_torusModel_of_isPullbackAlong hα
  refine finrank_tangent_le_card_index_sub_one h_reduction ?_ m'.fullStructure
    (m'.hasSpanningCoords_of_specMap_comp_eq (residue _) rfl) rfl ?_
  · simpa [← comap_ker, ker_residue, ThetaObject.baseHom] using h_good
  · simp [ThetaObject.baseHom, toIntegers, reassoc_of% h_over, comp_assoc]

end ThetaClosure

/-- Existence of the universal family. Let `R` be the localisation of `𝓞 E` at a submonoid of
non-zero-divisors, and let `D` be good (`New.PEL.IsGoodAt`) at the contraction to `𝓞 E` of every
maximal ideal of `R`. Then there is a theta family (an abelian scheme with `𝓞 E`-action, a line
bundle with point-separating coordinates and level points) over an `R`-scheme `S`, projective and
smooth of relative dimension `card D.Index - 1`. It comes with a dense set of complex points indexed
by pairs of an analytic family of tori `f` and a parameter `b`, at which the fibres are uniformised
by the tori, holomorphically in `b` on the domain of `f`. -/
theorem nonempty_universalFamily {M : Submonoid (𝓞 E)} [IsLocalization M R]
    (hM_le : M ≤ nonZeroDivisors (𝓞 E)) (hR_good : IsGoodOver D R) :
    Nonempty (UniversalFamily D R) := by
  -- The base is the closure `C` of the theta coordinates of the level points at all parameters.
  -- Finitely many generic points are dense in it, so it carries a family `X`. It is smooth near
  -- each of the arcs `α z`, and these neighbourhoods cover it.
  have h_finite : Finite D.levelTorsion := finite_torsionBy ⟨_, by simp [D.level_ne_zero]⟩
  have h_fintype := Fintype.ofFinite D.levelTorsion
  have h_dedekind : IsDedekindDomain R := IsLocalization.isDedekindDomain (𝓞 E) hM_le R
  obtain ⟨C⟩ : Nonempty (ThetaClosure (D := D) R id) := inferInstance
  obtain ⟨ι, hι, a, h_generic, h_dense⟩ := C.exists_finite_isDenseFamily M hR_good
  obtain ⟨X, hX⟩ := C.exists_hasThetaFibres M hR_good h_dense
  choose i v α hα h_spec h_good using C.exists_arc_isGoodAt hR_good h_dense
  choose U hU hU_smooth using fun z : C.scheme.left ↦
    C.exists_smooth_near_arc hX (h_generic (i z)) (hα z) (h_good z)
  have h_cover : ⨆ z, U z = ⊤ :=
    top_unique fun z _ ↦ le_iSup U z ((h_spec z).mem_open (U z).isOpen (hU z ⟨⟩))
  have h_smooth : SmoothOfRelativeDimension (Fintype.card D.Index - 1) C.scheme.hom :=
    HasRingHomProperty.instIsZariskiLocalAtSource.of_iSup_eq_top U h_cover hU_smooth
  choose m hθ using hX
  exact ⟨{ isDedekindDomain := h_dedekind
           base := C.scheme
           family := X
           hasProjEmbedding := C.hasProjEmbedding
           smooth := h_smooth
           obj := C.point
           model := m
           holomorphic := C.holomorphicAt_uniformisation m hθ
           dense := C.isSeparatingFamily.right }⟩

end New.Variety.ThetaNull

end
