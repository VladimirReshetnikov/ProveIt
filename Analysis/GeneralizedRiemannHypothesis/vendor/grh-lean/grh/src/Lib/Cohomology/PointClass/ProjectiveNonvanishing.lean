import Lib.Cohomology.Hodge.FixedPointFormula
import Lib.Cohomology.PointClass.ProjectiveSpace
import Lib.Cohomology.ProjectiveLine.TiltedLineFormula
import Lib.PadicComparison.HodgeTate.Map

/-!
# The Hodge–Tate map does not kill point classes of the projective line and space

Let `k` be a field with an embedding in `ℚ̄_p`, and let `λ_h = New.Variety.hodgeTateMap h` be the
Hodge–Tate map of weight `h`, from Hodge cohomology to `p`-adic cohomology. We compute `λ₁` of the
symbol `[dT / T]` of the pair `(𝔸¹, 𝔸¹ ∖ 0)` through the extension `0 → T → Bˣ → Tˣ → 0`.

## Main definitions and results

* `New.Variety.thickeningOver.oneSubMu`, `New.Variety.thickeningOver.shortExact_oneSubMu`: the short
  exact sequence `0 → T → Bˣ → Tˣ → 0` whose first map is `t ↦ 1 - μ t`.
* `New.Variety.hodgeTateMap_symbolClass`: the image of `[dT / T]` comes from the product of the
  boundary class of the pair with the class of this extension.
* `New.Variety.projSpace.exists_hodgeTateMap_pointClass_line`: `λ₁` of the class of `[1 : 0]` in
  `ℙ¹` comes from a degree-two class `η` on `p`-adic tests such that `x ↦ x × η` is injective on
  functors with flat values.
* `New.Variety.projSpace.hodgeTateMap_pointClass_ne_zero`: the class of a point of `ℙ^d` has a
  nonzero image under the Hodge–Tate map of weight `d`.

Notions from other files:
* `New.Variety.PadicTest`: a `p`-adic test, a non-empty family of cells (`New.Variety.IsCell`) with
  a ring map from `O_C` to their product; `R` denotes its ring.
* `New.Variety.thickeningOver`: the functor sending a `p`-adic test with ring `R` to the `k`-algebra
  `B = W(R♭)[1/p] / (ker θ)²`. `New.Variety.genericOver` sends it to `T = R[1/p]`, and
  `New.Variety.thickeningOver.proj : B → T` is the projection; its kernel is `μ T`, `μ = [ε] - 1`.
* `New.Variety.hodgeTateMap`: `λ_h` sends a Hodge class to a class on Hodge–Tate pairs (a `p`-adic
  test with a finite free module `M` over `T`). It restricts along `B ×_T (T ⊕ M) → T ⊕ M`, applies
  the `h`-th power of the contraction class, and projects `⋀M` to degree zero.
  `New.Variety.restrictToPairs` maps cohomology on `p`-adic tests to the same target.
* `New.Variety.symbolClass`: the class `[dT / T]` in the Hodge cohomology of the pair
  `(𝔸^d, 𝔸^d ∖ 0)`.
* `New.Variety.pointClass`: the class of a `k`-point `z` in Hodge cohomology of degree `d`, the
  image of a chosen class with support `z` and multiplicity `1` at `z`. Projective space
  `New.Variety.projSpace k d` sends `A` to the unimodular vectors in `A ^ (d + 1)` modulo units.

## Relation to the literature

Known; see `Lib.Cohomology.PointClass.LinearIndependence` for sources.
-/

noncomputable section

/-!
## The Hodge–Tate map of the symbol [dT/T]

For a `p`-adic test with ring `R`, `T = R[1/p]` is `New.Variety.genericOver`, with additive group
`New.Variety.genericCoeff`.
-/

section KummerSymbol

set_option backward.isDefEq.respectTransparency false

namespace New.Variety

open CategoryTheory AddCommGrpCat TotalH thickeningOver

variable {p : ℕ} {k : Type} [Field k] [EmbeddedInQpBar p k]

/-- A unimodular vector `v` of length one over a `k`-algebra `A` (an `A`-point of `𝔸¹ ∖ 0`) has a
unit as its only coordinate `v 0`. -/
lemma isUnit_of_unimodular_one {A : CommAlg k} (v : (unimodular (d := 1)).toFunctor.obj A) :
    IsUnit (v.val.down 0) := by
  simpa [unimodular, Set.range_unique] using v.prop

/-- The coordinate of `𝔸¹ ∖ 0` as a map to the multiplicative group: the morphism from `ℤ[𝔸¹ ∖ 0]`,
the free abelian group on the unimodular vectors of length one, to `A ↦ Aˣ` (written additively)
on `k`-algebras. It sends a generator `[v]` to the coordinate `v 0`, a unit by
`New.Variety.isUnit_of_unimodular_one`. -/
def Gm.ofCoord :
    freeAb (unimodular (k := k) (d := 1)).toFunctor ⟶ forget₂ (CommAlg k) CommRingCat ⋙ Gm :=
  freeAb.desc (fun _ v ↦ ⟨(isUnit_of_unimodular_one v).unit⟩) fun _ _ _ _ ↦ ext.2 rfl

/-- On `p`-adic tests with ring `R`, the morphism `t ↦ 1 - μ t` from the additive group of
`T = R[1/p]` (`New.Variety.genericCoeff`) to the units of `B = W(R♭)[1/p] / (ker θ)²`. Here `μ t` is
`New.Variety.thickeningOver.mulMu`, the product with `μ = [ε] - 1`. As `(μ s) * (μ t) = 0`, the
map sends sums to products, so its values are units. -/
def thickeningOver.oneSubMu :
    genericCoeff ⟶ thickeningOver ⋙ forget₂ (CommAlg k) CommRingCat ⋙ Gm where
  app c :=
    uliftFunctor.map <| ofHom <| MonoidHom.toAdditiveRight <| MonoidHom.toHomUnits
      { toFun t := 1 - mulMu c t.toAdd
        map_one' := by simp
        -- `(1 - mulMu s) * (1 - mulMu t) = 1 - mulMu (s + t)`, as
        -- `mulMu s * mulMu t = mulMu (proj (mulMu s) * t) = 0`.
        map_mul' := by simp [mul_sub, ← mulMu_proj_mul, proj_mulMu, sub_sub] }
  naturality c d f := by
    refine ext fun t ↦ Gm.ext.2 (.symm ?_)
    change thickeningOver.map f (1 - mulMu c t.1) = 1 - mulMu d (genericOver.map f t.1)
    rw [map_sub, map_one, map_mulMu]

/-- On `p`-adic tests the sequence `0 → T → Bˣ → Tˣ → 0` is short exact: its first map is
`t ↦ 1 - μ t` (`New.Variety.thickeningOver.oneSubMu`), its second is induced on units by the
projection `New.Variety.thickeningOver.proj : B → T`, and `w` says that their composite is zero. -/
lemma thickeningOver.shortExact_oneSubMu :
    ∃ w : oneSubMu ≫ Functor.whiskerRight proj (forget₂ (CommAlg k) CommRingCat ⋙ Gm) = 0,
      ShortComplex.ShortExact
        ⟨oneSubMu, Functor.whiskerRight proj (forget₂ (CommAlg k) CommRingCat ⋙ Gm), w⟩ := by
  -- At each test `c` the additive sequence `0 → T → B → T → 0` of `mulMu` and `proj` is exact.
  choose h_surj h_inj h_exact using exact_mulMu_proj (k := k)
  refine shortExact_of_app (fun c ⟨s⟩ ⟨t⟩ h_eq ↦ ?_) (fun c ⟨u⟩ ↦ ?_) fun c ⟨u⟩ ↦ ?_
  · -- `1 - μ s = 1 - μ t` forces `s = t`.
    exact congrArg ULift.up (h_inj c (sub_right_injective (Gm.ext.mp h_eq)))
  · -- Exactness applied to `1 - u`: the units with image `1` are those of the form `1 - mulMu t`.
    have : Nonempty (genericOver (k := k) |>.obj c) := ⟨0⟩
    have : Nonempty (PadicTest.genericAlg.obj c) := ⟨0⟩
    have h_one : proj c u.val = 1 ↔ ∃ t, 1 - mulMu c t = u.val := by
      simpa [sub_eq_zero.trans eq_comm, eq_comm.trans sub_eq_iff_comm] using h_exact c (1 - u.val)
    refine .trans ?_ ULift.exists.symm
    -- `using!`: `Gm.map` of `proj` and `oneSubMu` agree with `h_one` only after unfolding.
    simpa [Gm.ext] using! h_one
  · -- A lift `b` of the unit `u` is a unit, as the kernel has square zero.
    obtain ⟨b, hb⟩ : ∃ b : thickeningOver.obj c, proj c b = u.val := h_surj c u.val
    have h_unit : IsUnit b := (IsNilpotent.isUnit_quotient_mk_iff ⟨2, c.ker_thickeningProj_sq⟩).mp
      (.of_map (RingHom.quotientKerEquivOfSurjective (h_surj c)) _ ⟨u, hb.symm⟩)
    exact ⟨⟨h_unit.unit⟩, Gm.ext.mpr hb⟩

/-- Let `ω` be a form on `𝔸¹ ∖ 0` over Hodge tests that sends a point `a + m` to a one-form `w`
with `a • w = m`, so that `ω = dT / T` (such an `ω` is given by `New.Variety.symbolClass_one`). On
Hodge–Tate pairs, the pull-back of `ω` followed by one contraction
(`New.Variety.HodgeTatePair.contractionPow 1`) is the pull-back of the class of the extension
`0 → T → Bˣ → Tˣ → 0` (`New.Variety.thickeningOver.shortExact_oneSubMu`) along the coordinate
`New.Variety.Gm.ofCoord`. -/
private lemma pull_mk₀_comp_contractionPow_one_eq_pull_extClass_oneSubMu
    (ω : HodgeTest.sqZeroExt ⋙ freeAb.obj (unimodular (k := k) (d := 1)).toFunctor ⟶ hodgeCoeff)
    (hω : ∀ (c : HodgeTest k)
        (v : (unimodular (k := k) (d := 1)).toFunctor.obj (HodgeTest.sqZeroExt.obj c)),
      ∃ w : c.Index → c.baseAlg, (v.val.down 0).fst • w = (v.val.down 0).snd ∧
        ω.app c (FreeAbelianGroup.of v) = ⟨ExteriorAlgebra.ι c.baseAlg w⟩) :
    comp
        ((Comparison.restrict HodgeTatePair.toHodgeTest hodgeCoeff).pull
          (Functor.whiskerRight HodgeTatePair.toSqZero
            (freeAb.obj (unimodular (k := k) (d := 1)).toFunctor)) 0 (.mk₀ ω)).toTotalH
        (HodgeTatePair.contractionPow 1) =
      ((Comparison.restrict HodgeTatePair.toTest genericCoeff).pull
        (Functor.whiskerRight HodgeTatePair.toGeneric
          (freeAb.obj (unimodular (k := k) (d := 1)).toFunctor)) 1
        (H.map genericCoeff (genericOver.whiskerLeft Gm.ofCoord) 1
          shortExact_oneSubMu.2.extClass)).toTotalH := by
  -- Both sides are computed by explicit cocycles on pairs.
  let N : CommAlg k ⥤ AddCommGrpCat := freeAb.obj (unimodular (k := k) (d := 1)).toFunctor
  let α : HodgeTatePair.pairAlg ⋙ N ⟶ HodgeTatePair.toHodgeTest ⋙ hodgeCoeff :=
    Functor.whiskerRight HodgeTatePair.toSqZero N ≫ HodgeTatePair.toHodgeTest.whiskerLeft ω
  simp [Comparison.pull, H.map, H.push, Abelian.Ext.toTotalH, Functor.mapExtAddHom,
    Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_extClass]
  -- The left side is `α` (the form `ω` on pairs), then one contraction, then the projection
  -- `HodgeTatePair.contractionPow 0` of `⋀ M` to degree zero; with `D` below it is the class of the
  -- cocycle `D` (the form `ω`, then contraction along `f`), followed by that projection.
  show TotalH.comp (TotalH.homClass α)
      (TotalH.comp HodgeTatePair.contractionCocycle.cohomClass (HodgeTatePair.contractionPow 0)) = _
  let D : Cocycle (HodgeTatePair.pairAlg ⋙ N) HodgeTatePair.formCoeff :=
    ⟨fun {c d} f ↦ α.app c ≫ HodgeTatePair.contractionCocycle.component f,
      -- `↓`: without it, simp leaves the naturality square of `α` open.
      by simp [Cocycle.cocycle_comp, ↓NatTrans.naturality_assoc]⟩
  -- `α` carries `D` to the contraction cocycle (`New.Variety.Cocycle.cohomClass_naturality`).
  have h_nat : D.cohomClass.comp (TotalH.homClass (𝟙 _)) =
      pullbackAlong α HodgeTatePair.contractionCocycle.cohomClass :=
    D.cohomClass_naturality _ α (𝟙 _) fun c d f ↦ (Category.comp_id _).symm
  rw [comp_assoc_of_eq h_nat.symm, comp_id]
  -- `erw`: the right side is type-correct only up to unfolding `ShortComplex.map`, so `rw` fails.
  erw [← pullbackAlong_of]
  -- A unit of `B ×_T (T ⊕ M)` has a first component in `Bˣ`, which lifts its image in `Tˣ`. By
  -- `Cocycle.cohomClass_comp_eq_extClass` it remains to check that this is a lift, and that its
  -- failure to be natural in the pair is the cocycle `D`, carried into `Bˣ`.
  refine Cocycle.cohomClass_comp_eq_extClass _
    (shortExact_oneSubMu.2.map_of_exact (restrictAlong _)) _ _
    (fun _ ↦ Gm.ofCoord _ ≫ Gm.map (CommRingCat.ofHom (.pullbackFst ..))) (fun X ↦ ?_)
    fun X Y f ↦ hom_ext (FreeAbelianGroup.lift_ext _ _ fun ⟨⟨v⟩, hv⟩ ↦ ?_)
  · -- On a point `(b, t)` of `B ×_T (T ⊕ M)`, `proj b` is the first component of `t`.
    simp [← Functor.map_comp]
    congr with ⟨⟨b, t⟩, h_pullback⟩
    exact h_pullback
  · -- On the unit `v 0 = a + m`, `ω` takes the value `w` with `a • w = m`. The lift at `Y` is
    -- the image under `f` of the lift at `X`, times `1 + mulMu t` for the contraction `t` of `w`.
    obtain ⟨w, hw_smul, hω_app⟩ :=
      hω (HodgeTatePair.toHodgeTest.obj X) ⟨_, unimodular.map (HodgeTatePair.toSqZero X) hv⟩
    simp [D, α, ← Functor.map_comp]
    -- `erw`: the terms match `hω_app` and `Gm.ext` only up to unfolding `ShortComplex.map`.
    erw [hω_app, ← sub_eq_iff_eq_add', freeAb.desc_of, Gm.ext]
    change _ *
      (1 - mulMu (HodgeTatePair.toTest.obj Y)
        (-ExteriorAlgebra.algebraMapInv (contraction f.2 (.ι _ w)))) = _ + _
    -- `mulMu` is linear over `B` (`mulMu_proj_mul`); `v 0 = (b, a + m)` with `proj b = a` (the
    -- fibre product condition) and `m = a • w` (`hw_smul`).
    -- `erw`: `rw` finds no instance of `proj.naturality_apply`, which matches only up to unfolding.
    erw [mul_one_sub, ← mulMu_proj_mul, proj.naturality_apply, (v 0).2, ← hw_smul, map_smulₛₗ]
    -- After unfolding `contraction`, both sides read `f b + mulMu (f a * f w)`, through maps of
    -- pairs that agree by definition.
    simp [contraction]
    rfl

/-- The Hodge–Tate map on `[dT / T]` in dimension one: `λ₁ [dT / T]` is the image under
`New.Variety.restrictToPairs` of a degree-two class on `p`-adic tests. This class is the Yoneda
product of the boundary class of the pair `(𝔸¹, 𝔸¹ ∖ 0)` (the extension class of
`0 → ℤ[𝔸¹ ∖ 0] → ℤ[𝔸¹] → ℤ[𝔸¹] / ℤ[𝔸¹ ∖ 0] → 0`, restricted to tests) with the class of the
extension `0 → T → Bˣ → Tˣ → 0` of `New.Variety.thickeningOver.shortExact_oneSubMu`, pulled back
along the coordinate `New.Variety.Gm.ofCoord`. -/
lemma hodgeTateMap_symbolClass :
    hodgeTateMap 1 symbolClass =
      restrictToPairs
        (relFreeAb.shortExact unimodular
          |>.2
          |>.map_of_exact (restrictAlong genericOver)
          |>.extClass.comp
            (H.map genericCoeff (genericOver.whiskerLeft Gm.ofCoord) 1
              shortExact_oneSubMu.2.extClass)
            rfl) := by
  -- Both sides are boundaries for the pair `(𝔸¹, 𝔸¹ ∖ 0)`, so it suffices to compare two degree-one
  -- classes on `𝔸¹ ∖ 0`: the contraction of `ω = dT / T` and the class of the extension of units
  -- pulled back along `Gm.ofCoord`. `hθ` says that the symbol is the boundary of `ω`.
  obtain ⟨ω, hω, hθ⟩ := symbolClass_one k
  -- Compose the comparison on `𝔸¹ ∖ 0` with the boundary class of the pair, which commutes with
  -- restriction (`New.Variety.Comparison.pull_comp_restrictAlong`), on the Hodge side and on the
  -- side of tests. Up to `hθ`, `h_chain` is the goal with `hodgeTateMap` and `restrictToPairs`
  -- unfolded.
  have h_chain := (comp_assoc_of_eq
      (Comparison.pull_comp_restrictAlong (relFreeAb.shortExact unimodular).2.extClass (.mk₀ ω)
        (rfl : 1 + 0 = 1)) _).symm.trans
    ((congrArg _ (pull_mk₀_comp_contractionPow_one_eq_pull_extClass_oneSubMu ω hω)).trans
      (Comparison.pull_comp_restrictAlong (relFreeAb.shortExact unimodular).2.extClass _
        (rfl : 1 + 1 = 2)))
  simpa [hθ, Abelian.Ext.mapExactFunctor_extClass, hodgeTateMap, restrictToPairs] using h_chain

end New.Variety

end KummerSymbol

/-!
## The point class of the projective line

`New.Variety.hodgeTateMap h` is the Hodge–Tate map `λ_h` on Hodge cohomology.
`New.Variety.pointClass d z` is the class of a `k`-point `z`, and `New.Variety.cup` is the external
product of classes.
-/

section LinePointClass

set_option backward.isDefEq.respectTransparency false

namespace New.Variety

open CategoryTheory MvPolynomial TotalH PadicTest Period PerfectLine thickeningOver CommAlgCat
  WittVector Functor freeAb NNRat

variable {p : ℕ} {k : Type} [Field k] [EmbeddedInQpBar p k]

/-- For a `p`-adic test `c` with ring `R`, in `B = W(R♭)[1/p] / (ker θ)²` the Teichmüller lift of
`ε` (`Period.epsTilt`, mapped to the tilt `R♭`) is `1 + μ`, where `μ = mulMu c 1` is the image of
`[ε] - 1`. -/
lemma thickeningOver.teichmullerLift_epsTilt (c : PadicTest) :
    teichmullerLift c (algebraMap OFlat (tilt.obj c) Period.epsTilt) = 1 + mulMu c 1 := by
  -- `mulMu c 1` is the image of `mu = [ε] - 1`, so it remains to compare the two lifts of `ε`.
  -- The lift `[·]` commutes with the map `O♭ → R♭`, and `W(O♭) → B` is `W(O♭) → W(R♭) → B`.
  have h_lift : teichmullerLift (k := k) c (algebraMap OFlat (tilt.obj c) epsTilt) =
      algebraMap (WittVector p OFlat) c.Thickening (teichmuller p epsTilt) :=
    congrArg (algebraMap (WittVector p c.TiltRing) c.Thickening) (map_teichmuller ..).symm
  rw [h_lift, ← map_one c.thickeningProj, mulMu_thickeningProj]
  simp [mu]

/-- Let `V` be covered by charts of dimension one (`New.Variety.IsChartCovered 1 V`) and `U` an
open subfunctor of `V`. Then restriction from `p`-adic tests to Hodge–Tate pairs is bijective
(`New.Variety.PairRestrictBijective`) on the cohomology of `relFreeAb U = ℤ[V] / ℤ[U]`. -/
lemma pairRestrictBijective_relFreeAb_of_isOpenSubfunctor {V : CommAlg k ⥤ Type 1}
    {U : Subfunctor V} [hV : IsChartCovered 1 V] (hU : IsOpenSubfunctor U) :
    PairRestrictBijective (relFreeAb U) := by
  -- Two out of three in the sequence `0 → ℤ[U] → ℤ[V] → relFreeAb U → 0`: the property holds for
  -- `ℤ[V]`, and for `ℤ[U]` since `U` is again covered by charts.
  have hU_charts : IsChartCovered 1 U.toFunctor := hV.comap U.ι (by simpa using hU)
  have h_closed : IsClosedClass fun N : CommAlg k ⥤ AddCommGrpCat ↦ PairRestrictBijective N :=
    (Comparison.restrict HodgeTatePair.toTest genericCoeff).isClosedClass HodgeTatePair.toGeneric
  exact (h_closed.right _ (relFreeAb.shortExact U).2 hU_charts.pairRestrictBijective).mp
    hV.pairRestrictBijective

/-- On the chart `0` of the projective line (the points `[1 : x]`), the coordinate `X` cuts out the
point `affinePoint 0 0 = [1 : 0]`: a map `α` from the chart's ring to a `k`-algebra `C` kills `X`
exactly when it sends the chart's point to `[1 : 0]` (`New.Variety.CutsOutLocus`). -/
lemma projSpace.cutsOutLocus_stdChart_zero_X :
    CutsOutLocus (projSpace k 1) (ComesFromPoints {affinePoint 0 0}) (stdChart k 1 0).point X := by
  -- The image of the chart's point under `α` is `[1 : α X]`, which is `[1 : 0]` iff `α X = 0`.
  intro C α
  simp [ComesFromPoints]
  -- Both sides of the equation are points `[v]`; compare them by cross products.
  change _ ↔ projSpace.mk _ _ = projSpace.mk _ _
  rw [mk_eq_mk_iff_cross_mul]
  simp +contextual [Set.range_unique]

/-- The points of the chart `1` of the projective line (the points `[x : 1]`) avoid
`affinePoint 0 0 = [1 : 0]`: for every map `ψ` from the chart's ring to `A`, the image of the
chart's point is zero in `ℤ[ℙ¹] / ℤ[ℙ¹ ∖ [1 : 0]]` (`New.Variety.relFreeAb` of
`New.Variety.offPoints`). -/
lemma projSpace.relFreeAb_mk_stdChart_one_eq_zero (A : CommAlg k)
    (ψ : (stdChart k 1 1).coordRing ⟶ A) :
    relFreeAb.mk (offPoints {affinePoint 0 0})
      ((projSpace k 1).map ψ (stdChart k 1 1).point) = 0 := by
  -- At a field `K`, a point of the chart `1` has a unit as its coordinate `1`, and `[1 : 0]` has
  -- `0` there.
  refine relFreeAb.mk_eq_zero ((offPoints _).map ψ ?_)
  rintro K φ hK ⟨z, rfl, h_eq⟩
  have : Nontrivial K := hK.nontrivial
  simpa using (mk_mem_stdChart_iff ..).mp ⟨_, h_eq⟩

/-- There is a degree-two class `ξT` in the cohomology on `p`-adic tests with coefficients
`genericCoeff` (a test with ring R ↦ R[1/p]) of ℤ[ℙ¹]/ℤ[`offPoints {affinePoint 0 0}`] composed with
`genericOver`. It satisfies two conditions. First, `hodgeTateMap 1` of the class of the point
`affinePoint 0 0 = [1 : 0]` of `ℙ¹` is `restrictToPairs` of the image of `ξT` in the cohomology of
ℤ[ℙ¹]. Second, the pull-back of `ξT` to the chart `stdChart k 1 0` equals the pull-back, along the
identification of that chart with the pair `(𝔸¹, 𝔸¹ ∖ 0)`, of the product of the boundary class of
`0 → ℤ[𝔸¹ ∖ 0] → ℤ[𝔸¹] → ℤ[𝔸¹]/ℤ[𝔸¹ ∖ 0] → 0` with the pull-back along `Gm.ofCoord` of the
degree-one class of the extension of units `thickeningOver.shortExact_oneSubMu`. -/
lemma projSpace.exists_relative_point_class :
    ∃ ξT : H (genericOver ⋙ relFreeAb (offPoints {affinePoint 0 0})) genericCoeff 2,
      hodgeTateMap 1 (pointClass 1 (affinePoint (k := k) (d := 1) 0 0)) =
        restrictToPairs
          (H.map genericCoeff (genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0})))
            2 ξT) ∧
      H.map genericCoeff
          (genericOver.whiskerLeft (relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl)) 2 ξT =
        H.map genericCoeff
          (genericOver.whiskerLeft
            (relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le))
          2
          (relFreeAb.shortExact (unimodular (k := k) (d := 1))
            |>.2
            |>.map_of_exact (restrictAlong genericOver)
            |>.extClass.comp
              (H.map genericCoeff (genericOver.whiskerLeft Gm.ofCoord) 1
                shortExact_oneSubMu.2.extClass)
              rfl) := by
  -- The class of the point comes from a relative class `ξ` that equals `[dX / X]` on the chart.
  obtain ⟨ξ, ⟨h_cut, h_chart, hξ_local⟩, hξ_point⟩ :
      ∃ ξ : HodgeH (relFreeAb (offPoints {affinePoint 0 0})) 1,
        IsLocalSymbol ξ (stdChart k 1 0).point (ComesFromPoints {affinePoint 0 0}) X 1 ∧
        IsPointSum {affinePoint 0 0} 1 ξ :=
    (stdChart k 1 0).exists_isLocalSymbol cutsOutLocus_stdChart_zero_X
      ((mk_mem_stdChart_iff _).mpr isUnit_one)
  obtain ⟨ξT, hξ⟩ : ∃ ξT, hodgeTateMap 1 ξ = restrictToPairs (n := 1 + 1) ξT :=
    (pairRestrictBijective_relFreeAb_of_isOpenSubfunctor
      isOpenSubfunctor_offPoints).exists_hodgeTateMap_eq 1 ξ
  refine ⟨ξT, ?_, ?_⟩
  · -- `ξ` has multiplicity `1` at the point, so it maps to the point class.
    have h_point : HodgeH.map (relFreeAb.π _) ξ = pointClass 1 (affinePoint 0 0) :=
      hξ_point.map_eq_smul_pointClass.trans (one_smul k _)
    rw [← h_point, hodgeTateMap_map, hξ, restrictToPairs_map]
  · -- `restrictToPairs` is injective on the chart. By `hξ` and `hodgeTateMap_symbolClass`, it sends
    -- the two sides of the goal to `λ₁` of the two sides of `hξ_local`.
    apply (pairRestrictBijective_relFreeAb_of_isOpenSubfunctor
      (hV := .comap _ (EtaleChart.isOpenSubfunctor _))
      (isOpenSubfunctor_offPoints.preimage _)).injective_restrictToPairs
    apply_fun hodgeTateMap 1 at hξ_local
    rw [one_smul, hodgeTateMap_map, hodgeTateMap_map, hξ, hodgeTateMap_symbolClass] at hξ_local
    rw [restrictToPairs_map]
    exact hξ_local.trans (restrictToPairs_map _ _).symm

/-- The Teichmüller lift is natural in the test: for a map `f : c ⟶ d` of `p`-adic tests,
`thickeningOver.map f` sends `[x]` to `[tilt.map f x]`. -/
private lemma thickeningOver.teichmullerLift_map {c d : PadicTest} (f : c ⟶ d) (x : tilt.obj c) :
    teichmullerLift d (tilt.map f x) = thickeningOver.map f (teichmullerLift c x) := by
  -- `with_unfolding_all`: only then is `thickeningOver.map f` seen as a map of localizations,
  -- which sends `[x]` to `[tilt.map f x]` by `WittVector.map_teichmuller`.
  with_unfolding_all
    exact congr(.mk _ $(.symm ((IsLocalization.map_eq (powers_le_comap_powers ..) _).trans
      (congrArg _ (map_teichmuller ..)))))

/-- The Teichmüller coordinate. For a `p`-adic test with ring `R`, a point `t` of the perfect disc
over the tilt is an `O♭`-algebra map `O♭[ℚ≥0] → R♭` with coordinate `u = t (T ^ 1)`; it goes to the
Teichmüller lift `[u]`, a point of the affine line over `B = W(R♭)[1/p] / (ker θ)²`. -/
def teichmullerCoordinate : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ thickeningOver ⋙ affineSpace k 1 :=
  ⟨fun c ↦ ↾fun t ↦ ⟨fun _ ↦ teichmullerLift c (t.down.hom (.single 1 1))⟩, fun c d f ↦ by
    ext t
    exact congrArg (fun b ↦ ULift.up fun (_ : Fin 1) ↦ b) (teichmullerLift_map f _)⟩

/-- On a point of the torus `O♭[ℚ] → R♭`, the Teichmüller coordinates at `u` and at `u⁻¹` multiply
to `1`. -/
lemma teichmullerCoordinate_mul_inv (c : PadicTest) (t : monoidAlg ℚ ⟶ tilt c) :
    (teichmullerCoordinate (k := k) c ⟨discToTorus coeHom ≫ t⟩).down 0 *
      (teichmullerCoordinate (k := k) c ⟨discToTorus (-coeHom) ≫ t⟩).down 0 = 1 := by
  simp [teichmullerCoordinate, ← map_mul, ← AddMonoidAlgebra.one_def]

/-- Followed by the projection `B → T = R[1/p]`, the Teichmüller coordinate does not change when the
point is twisted by `charTwist`, which multiplies `u` by `ε` or by `ε⁻¹`. -/
lemma teichmullerCoordinate_comp_proj_charTwist (c : PadicTest) (i : Bool)
    (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c) :
    (teichmullerCoordinate ≫ whiskerRight proj (affineSpace k 1)) c
        ⟨charTwist epsPow (cond i coeHom (-coeHom)) ≫ t.down⟩ =
      (teichmullerCoordinate ≫ whiskerRight proj (affineSpace k 1)) c t := by
  -- The twist multiplies `[u]` by `[ε ^ (±1)]`, and `[ε] = 1 + mulMu c 1` maps to `1` under `proj`.
  let θ : Multiplicative ℚ →* genericOver.obj c :=
    (proj (k := k) c).hom.toRingHom.toMonoidHom.comp
      ((teichmullerLift c).comp ((algebraMap OFlat _).toMonoidHom.comp epsPow))
  let sign : Multiplicative ℚ := .ofAdd ((cond i coeHom (-coeHom) : ℚ≥0 →+ ℚ) 1)
  have h_eps : sign ∈ θ.ker := by
    cases i <;> simp [θ, sign, teichmullerLift_epsTilt, proj_mulMu]
  -- After unfolding, the goal reads `proj [ε ^ (±1)] * proj [u] = proj [u]`.
  -- The first two exclusions keep `algebraMap` on the monoid algebra and `cond` as they stand;
  -- `mul_eq_right₀` and `mul_eq_mul_right_iff` would cancel `b` in `a * b = b`.
  simp [teichmullerCoordinate, affineSpace, charTwist, _root_.funext_iff,
    -AddMonoidAlgebra.coe_algebraMap, -Bool.cond_eq_ite, -mul_eq_right₀, -mul_eq_mul_right_iff]
  change θ sign * proj c (teichmullerLift c (t.down.hom (.single 1 1))) =
    proj c (teichmullerLift c (t.down.hom (.single 1 1)))
  rw [θ.mem_ker.mp h_eps, one_mul]

/-- The Teichmüller coordinate `A = New.Variety.teichmullerCoordinate` with its three properties:
(a) its formula, (b) `[u] [u⁻¹] = 1` on the torus, (c) invariance under `charTwist` after the
projection to `R[1/p]`. -/
lemma exists_teichmuller_coordinate :
    ∃ A : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ thickeningOver ⋙ affineSpace k 1,
      -- (a)
      (∀ (c : PadicTest) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c),
        A c t = ⟨fun (_ : Fin 1) ↦ teichmullerLift c (t.down.hom (AddMonoidAlgebra.single 1 1))⟩) ∧
      -- (b)
      (∀ (c : PadicTest) (t : monoidAlg ℚ ⟶ tilt c),
        (A c ⟨discToTorus coeHom ≫ t⟩).down 0 * (A c ⟨discToTorus (-coeHom) ≫ t⟩).down 0 = 1) ∧
      -- (c)
      ∀ (c : PadicTest) (i : Bool) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c),
        (A ≫ whiskerRight proj (affineSpace k 1)) c
            ⟨charTwist epsPow (cond i coeHom (-coeHom)) ≫ t.down⟩ =
          (A ≫ whiskerRight proj (affineSpace k 1)) c t :=
  ⟨teichmullerCoordinate, fun _ _ ↦ rfl, teichmullerCoordinate_mul_inv,
    teichmullerCoordinate_comp_proj_charTwist⟩

/-- If `one` is a unit for `mult`, that is, `x ↦ x ⊗ one` followed by `mult` is the identity of `F`,
then pulling the class `x ⊗ F` followed by `mult` back along `S ↦ S ⊗ one` recovers `x`. -/
lemma pullbackAlong_tensorPoint_comp_eq_self {N F : AbFunctor PadicTest} [HasFlatValues F]
    (x : TotalH N F) {one : freeAb (onePointFunctor PadicTest) ⟶ F} {mult : abTensor F F ⟶ F}
    (h_unit : tensorPoint one F ≫ mult = 𝟙 F) :
    pullbackAlong (tensorPoint one N)
      (TotalH.comp (TotalH.map (abTensor.flip F) x) (TotalH.homClass mult)) = x := by
  -- `S ↦ S ⊗ one` is natural in `S`, so the pull-back moves past `x`; then `h_unit` applies.
  calc
    _ = TotalH.comp (TotalH.map (𝟭 _) x) (pullbackAlong (tensorPoint one F) (.homClass mult)) :=
      (TotalH.comp_assoc_of_sq (naturality ..) _).symm
    _ = x := by
      rw [TotalH.map_id, ← homClass_comp, h_unit]
      exact comp_id

/-- The class on `p`-adic tests that `λ₁` gives on the symbol `[dT/T]`
(`New.Variety.hodgeTateMap_symbolClass`): the boundary class of the pair `(𝔸¹, 𝔸¹ ∖ 0)` times the
class of the extension `0 → T → Bˣ → Tˣ → 0` of `New.Variety.thickeningOver.shortExact_oneSubMu`,
pulled back along `New.Variety.Gm.ofCoord`. -/
private def unitsExtClass :
    H (genericOver ⋙ relFreeAb (unimodular (k := k) (d := 1))) genericCoeff 2 :=
  ((relFreeAb.shortExact (unimodular (k := k) (d := 1))).2.map_of_exact
      (restrictAlong genericOver)).extClass.comp
    (H.map _ (genericOver.whiskerLeft Gm.ofCoord) 1 shortExact_oneSubMu.2.extClass) rfl

/-- Let `s` be a section of the map of pairs induced by the coordinate of the chart `0` of `ℙ¹`
(`h_section`), and let `ξT` restrict on the chart `0` to the pull-back of
`New.Variety.unitsExtClass` along that coordinate (`h_compare`). If `j'` lifts `j` followed by `s`
and the inclusion of the chart (`hj'`), then the pull-back of `unitsExtClass` along `j` is the
pull-back along `j'` of the image of `ξT` in `ℤ[ℙ¹]`. -/
private lemma projSpace.map_unitsExtClass_eq_map_of_comp_eq {B : AbFunctor PadicTest}
    {s : relFreeAb (unimodular (k := k) (d := 1)) ⟶
      relFreeAb ((offPoints {affinePoint 0 0}).preimage (pointMap (stdChart k 1 0).point))}
    (h_section : s ≫ relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le =
      𝟙 (relFreeAb (unimodular (d := 1))))
    {ξT : H (genericOver ⋙ relFreeAb (offPoints {affinePoint 0 0})) genericCoeff 2}
    (h_compare :
      H.map genericCoeff
          (genericOver.whiskerLeft (relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl)) 2 ξT =
        H.map genericCoeff
          (genericOver.whiskerLeft
            (relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le))
          2 unitsExtClass)
    {j : B ⟶ genericOver ⋙ relFreeAb (unimodular (k := k) (d := 1))}
    {j' : B ⟶ genericOver ⋙ freeAb.obj (projSpace k 1)}
    (hj' : j' ≫ genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0})) =
      j ≫ genericOver.whiskerLeft (s ≫ relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl)) :
    H.map genericCoeff j 2 unitsExtClass =
      H.map genericCoeff j' 2
        (H.map genericCoeff (genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0})))
          2 ξT) := by
  -- `r` is the inclusion of the chart; `s` is a section of the coordinate map, so `ξT` pulls back
  -- to `unitsExtClass` along `s ≫ r`.
  let r : relFreeAb _ ⟶ relFreeAb (offPoints {affinePoint 0 0}) :=
    relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl
  have h_local : H.map genericCoeff (genericOver.whiskerLeft (s ≫ r)) 2 ξT = unitsExtClass :=
    calc
      _ = H.map genericCoeff
          (genericOver.whiskerLeft
            (s ≫ relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le))
          2 unitsExtClass := by
        rw [whiskerLeft_comp, H.map_comp, h_compare]
        exact (H.map_comp ..).symm
      _ = unitsExtClass := by rw [h_section, whiskerLeft_id', H.map_id]
  calc
    _ = H.map genericCoeff (j ≫ genericOver.whiskerLeft (s ≫ r)) 2 ξT := by
      rw [H.map_comp, h_local]
    _ = H.map genericCoeff
          (j' ≫ genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0}))) 2 ξT := by
      rw [hj']
    _ = _ := H.map_comp ..

/-- The map `j` of a Toda cancellation lifts through the projective line. Let `A` be a natural map
from the perfect disc to the affine line over `B` whose values at `u` and `u⁻¹` multiply to `1` on
the torus (`hA_inv`), and let its image `a` in `R[1/p]` be invariant under the twists of the two
discs (`hA_twist`). Let `(j, y, ω)` cancel `New.Variety.unitsExtClass` in the sense of
`New.Variety.IsTodaCancellation`, for the gluing of the two discs and the map induced by `a`. Let
`ξT` be a class on tests relative to the complement of `[1 : 0]` whose restriction to the chart `0`
is the pull-back of `unitsExtClass` along the coordinate (`h_compare`). Then the pull-back of
`unitsExtClass` along `j` is the pull-back along some `j'` of the image of `ξT` in `ℤ[ℙ¹]`. -/
private lemma projSpace.exists_map_eq_map_of_isTodaCancellation
    (A : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ thickeningOver ⋙ affineSpace k 1)
    (hA_inv : ∀ (c : PadicTest) (t : monoidAlg ℚ ⟶ tilt c),
      (A c ⟨discToTorus coeHom ≫ t⟩).down 0 * (A c ⟨discToTorus (-coeHom) ≫ t⟩).down 0 = 1)
    (hA_twist :
      ∀ (c : PadicTest) (i : ULift.{1} Bool) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c),
        (A ≫ whiskerRight proj (affineSpace k 1)) c ⟨discTwist epsPow i ≫ t.down⟩ =
          (A ≫ whiskerRight proj (affineSpace k 1)) c t)
    {B K Z₀ : AbFunctor PadicTest} {ε : Z₀ ⟶ genericCoeff} {y : Z₀ ⟶ K} {ω : TotalH B K}
    {j : B ⟶ genericOver ⋙ relFreeAb (unimodular (k := k) (d := 1))}
    (h_toda : IsTodaCancellation gluing (oneSub (discTwist epsPow))
      ((projFirst ≫ freeAb.map (A ≫ whiskerRight proj (affineSpace k 1))) ≫
        genericOver.whiskerLeft (relFreeAb.π unimodular))
      unitsExtClass ε j y ω)
    (ξT : H (genericOver ⋙ relFreeAb (offPoints {affinePoint 0 0})) genericCoeff 2)
    (h_compare :
      H.map genericCoeff
          (genericOver.whiskerLeft (relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl)) 2 ξT =
        H.map genericCoeff
          (genericOver.whiskerLeft
            (relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le))
          2 unitsExtClass) :
    ∃ j' : B ⟶ genericOver ⋙ freeAb.obj (projSpace k 1),
      H.map genericCoeff j 2 unitsExtClass =
        H.map genericCoeff j' 2
          (H.map genericCoeff (genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0})))
            2 ξT) := by
  let a : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ genericOver ⋙ affineSpace k 1 := A ≫ whiskerRight proj _
  -- `hA_twist` stated for the let `a`, the form in which `simp` meets it below.
  have ha_twist (c : PadicTest) (i : ULift.{1} Bool) (t) :
      a c ⟨discTwist epsPow i ≫ t.down⟩ = a c t :=
    hA_twist c i t
  -- `φ` maps the disc `true` to the chart `0` and the disc `false` to the chart `1`.
  let T : affineSpace k 1 ⟶ reprBy (stdChart k 1 0).coordRing :=
    ⟨fun _ ↦ ↾fun v ↦ ⟨ofHom (aeval v.1)⟩,
      fun _ _ _ ↦ by ext; congrm ⟨ofHom $((comp_aeval ..).symm)⟩⟩
  let φ : twoDiscs ⟶ genericOver ⋙ projSpace k 1 :=
    sigma.desc fun i ↦ a ≫ whiskerLeft _ (T ≫ pointMap (stdChart k 1 (cond i.down 0 1)).point)
  -- A unit `v` gives a point `[1 : v]` other than `[1 : 0]`; `r` is the inclusion of the chart `0`.
  let s :
      relFreeAb unimodular ⟶
        relFreeAb ((offPoints {affinePoint 0 0}).preimage (pointMap (stdChart k 1 0).point)) :=
    relFreeAb.map T fun _ v hv ↦ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.ge _
      (.trans (congrArg _ (congrArg _ (funext (aeval_X _)))) hv)
  let r :
      relFreeAb ((offPoints {affinePoint 0 0}).preimage (pointMap (stdChart k 1 0).point)) ⟶
        relFreeAb (offPoints {affinePoint 0 0}) :=
    relFreeAb.map (pointMap (stdChart k 1 0).point) le_rfl
  -- The map `x ↦ [φ x] - [∞]` on the discs, `∞` the image of the origin of the disc `false`, lifts
  -- `j` to `j'` with values in `freeAb (projSpace k 1)`.
  obtain ⟨j', hj'⟩ :
      ∃ j',
        j' ≫ genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0})) =
          j ≫ genericOver.whiskerLeft (s ≫ r) := by
    refine h_toda.exists_lift (freeAb.map φ - origin ⟨false⟩ _ ≫ freeAb.map φ) _ _
      (hom_ext ?_) (hom_ext fun c t ↦ ?_) (hom_ext ?_)
    · -- The two charts are glued along `u ↦ u⁻¹`.
      rintro c ⟨⟨_ | _⟩, t⟩
      · simp
      simp [sub_eq_zero]
      refine congrArg FreeAbelianGroup.of (mk_eq_mk_iff_cross_mul.2 ?_)
      simp
      -- The coordinates are `aeval` of `X` only after unfolding `T`, hence `erw`.
      erw [aeval_X, aeval_X, mul_comm, ← map_mul (proj c).1, hA_inv]
      simp
    · -- `φ` is invariant under the twist, by `ha_twist`.
      simp [sub_eq_zero]
      simp [freeAb, φ, sigma.desc, ha_twist]
    · -- Modulo the complement of the point, `∞` and the whole disc `false` vanish.
      rintro c ⟨⟨_ | _⟩, t⟩
      · simp [sub_eq_zero]
        exact (relFreeAb_mk_stdChart_one_eq_zero ..).trans
          (relFreeAb_mk_stdChart_one_eq_zero ..).symm
      · simp
        exact sub_eq_self.2 (relFreeAb_mk_stdChart_one_eq_zero ..)
  -- `T` is a section of the coordinate map.
  have h_section : s ≫ relFreeAb.map _ cutsOutLocus_stdChart_zero_X.preimage_fieldLocus_not.le = 𝟙
    _ :=
    relFreeAb.hom_ext fun _ _ ↦ congrArg (relFreeAb.mk unimodular ⟨·⟩) (funext (aeval_X _))
  exact ⟨j', map_unitsExtClass_eq_map_of_comp_eq h_section h_compare hj'⟩

/-- Let `(j, y, ω)` cancel `New.Variety.unitsExtClass` in the sense of
`New.Variety.IsTodaCancellation`, for the gluing of the two perfect discs, where `ε` sends the point
to a unit for the multiplication of `R[1/p]` (`h_unit`). If the pull-back of `unitsExtClass` along
`j` is the pull-back of `η` along `j'` (`h_pull`), then for `N` with flat values and `x` in
`H^n(N, R[1/p])`, the product `x × η` vanishes only if `x = 0`. -/
private lemma eq_zero_of_cup_eq_zero_of_isTodaCancellation {B K : AbFunctor PadicTest}
    {q : freeAb twoDiscs ⟶ genericOver ⋙ relFreeAb (unimodular (k := k) (d := 1))}
    {ε : freeAb (onePointFunctor PadicTest) ⟶ genericCoeff}
    {j : B ⟶ genericOver ⋙ relFreeAb (unimodular (k := k) (d := 1))}
    {y : freeAb (onePointFunctor PadicTest) ⟶ K} {ω : TotalH B K}
    (h_toda : IsTodaCancellation gluing (oneSub (discTwist epsPow)) q unitsExtClass ε j y ω)
    (h_unit :
      tensorPoint ε genericCoeff ≫
          (genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing =
        𝟙 genericCoeff)
    {η : H (genericOver ⋙ freeAb.obj (projSpace k 1)) genericCoeff 2}
    {j' : B ⟶ genericOver ⋙ freeAb.obj (projSpace k 1)}
    (h_pull : H.map genericCoeff j 2 unitsExtClass = H.map genericCoeff j' 2 η)
    {N : AbFunctor PadicTest} [HasFlatValues N] {n : ℕ} (x : H N genericCoeff n)
    (hx : cup (genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing x η (add_comm 2 n) =
      0) :
    x = 0 := by
  -- Apply `h_toda` to `Φ = N ⊗ -` and `m`, the class `x ⊗ genericCoeff` followed by multiplication:
  -- its product with `j^* unitsExtClass` is the pull-back along `j'` of `x × η = 0`.
  let Φ : AbFunctor PadicTest ⥤ AbFunctor PadicTest := abTensor N
  let mult : abTensor genericCoeff genericCoeff ⟶ genericCoeff :=
    (genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing
  let m : TotalH (Φ genericCoeff) genericCoeff :=
    TotalH.comp (TotalH.map (abTensor.flip genericCoeff) x.toTotalH) (.homClass mult)
  have h_zero :
      pullbackAlong (Φ.map j) (TotalH.comp (TotalH.map Φ unitsExtClass.toTotalH) m) = 0 :=
    calc
      _ = TotalH.comp (TotalH.map Φ (pullbackAlong j unitsExtClass.toTotalH)) m := by
        rw [TotalH.map_comp_assoc, map_homClass]
      _ = TotalH.comp (TotalH.map Φ (pullbackAlong j' η.toTotalH)) m := by
        rw [Abelian.Ext.toTotalH, Abelian.Ext.toTotalH, pullbackAlong_of, pullbackAlong_of, h_pull]
      _ = pullbackAlong (Φ.map j') (TotalH.comp (TotalH.map Φ η.toTotalH) m) := by
        rw [TotalH.map_comp_assoc, map_homClass]
      _ = pullbackAlong (Φ.map j') (cup mult x η (add_comm 2 n)).toTotalH :=
        congrArg _ ((comp_assoc_of_eq rfl _).trans (cup_of ..))
      _ = 0 := by
        rw [hx]
        exact (congrArg _ (map_zero _)).trans (map_zero _)
  -- Pulling `m` back along `S ↦ S ⊗ ε` recovers `x`, and by `h_toda` this pull-back is zero;
  -- `subsingleton_H_cokernel_gluing` gives the acyclicity of the cokernel of the gluing that it
  -- needs.
  have h_vanish : pullbackAlong (tensorPoint ε N) m = 0 :=
    (h_toda.pullbackAlong_comp_map_eq Φ (subsingleton_H_cokernel_gluing isCohomEquiv_gluing_generic
      N)
      (tensorPoint (𝟙 _) _) m 0 (h_zero.trans (map_zero _).symm)).trans (map_zero _)
  rw [pullbackAlong_tensorPoint_comp_eq_self x.toTotalH h_unit] at h_vanish
  exact DirectSum.of_injective n (h_vanish.trans (map_zero _).symm)

/-- Let `k` be a field of characteristic `0` with an embedding in `ℚ̄_p`. There is a degree-two
cohomology class `η` of the functor `S ↦ ℤ[ℙ¹(S[1/p])]` on `p`-adic tests `S` (with ring `R`,
written `S[1/p] = R[1/p]`), with coefficients `S ↦ R[1/p]` (`genericCoeff`), such that the following
hold. (a) The Hodge–Tate map `hodgeTateMap 1` sends the class of the point `[1 : 0]` to
`restrictToPairs η`. (b) For every functor `N` from `p`-adic tests to abelian groups with flat
values and every `x` in the degree-`n` cohomology of `N` with coefficients `R[1/p]`, the cup product
of `x` and `η` (paired by multiplication in `R[1/p]`) vanishes only if `x = 0`. -/
lemma projSpace.exists_hodgeTateMap_pointClass_line :
    ∃ η : H (genericOver ⋙ freeAb.obj (projSpace k 1)) genericCoeff 2,
    -- (a)
    hodgeTateMap 1 (pointClass 1 (affinePoint (k := k) (d := 1) 0 0)) = restrictToPairs η ∧
    -- (b)
    ∀ {N : AbFunctor PadicTest} {n : ℕ} [HasFlatValues N] (x : H N genericCoeff n),
      cup (genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing x η (add_comm 2 n) = 0 →
        x = 0 := by
  -- `hodgeTateMap 1` of the point comes from `unitsExtClass`; `exists_isTodaCancellation`, for two
  -- perfect discs mapping to the charts of `ℙ¹`, gives a map `j` along which `unitsExtClass` comes
  -- from `η`, and `x × η = 0` then forces `x = 0`.
  obtain ⟨ξT, h_point, h_compare⟩ := exists_relative_point_class (k := k)
  let η : H (genericOver ⋙ freeAb.obj (projSpace k 1)) genericCoeff 2 :=
    H.map _ (genericOver.whiskerLeft (relFreeAb.π (offPoints {affinePoint 0 0}))) 2 ξT
  refine ⟨η, h_point, fun {N n} _ x hx ↦ ?_⟩
  -- `A` sends `u` to `[u]`; its image `a` in `R[1/p]` is invariant under the twist `charTwist`.
  obtain ⟨A, hA, hA_inv, hA_twist⟩ := exists_teichmuller_coordinate (k := k)
  let a : tilt ⋙ reprBy (monoidAlg ℚ≥0) ⟶ genericOver ⋙ affineSpace k 1 := A ≫ whiskerRight proj _
  have ha_twist (c : PadicTest) (i : ULift.{1} Bool) (t : (tilt ⋙ reprBy (monoidAlg ℚ≥0)).obj c) :
      a c ⟨discTwist epsPow i ≫ t.down⟩ = a c t := by
    obtain ⟨_ | _⟩ := i
    exacts [hA_twist c false t, hA_twist c true t]
  -- On the torus `[u]` is a unit, so a point of `unimodular` over `thickeningOver`; `W` kills the
  -- extra point of `pointOrTorus`.
  let W :
      freeAb (tiltPointsSum pointOrTorus) ⟶
        thickeningOver ⋙ freeAb (unimodular (k := k) (d := 1)).toFunctor :=
    projFirst ≫ desc
        (fun c t ↦
          .of ⟨A c ⟨discToTorus _ ≫ t.1⟩, span_eq_top_of_isUnit 0 (.of_mul_eq_one _ (hA_inv ..))⟩)
      fun _ _ f _ ↦ .symm congr(.of $(Subtype.ext (A.naturality_apply ..).symm))
  -- `one` sends every point to the unit of `genericAlg`.
  let one {X : PadicTest ⥤ Type 1} : freeAb X ⟶ genericCoeff :=
    desc (fun c _ ↦ ⟨(1 : genericAlg c)⟩) fun _ _ _ _ ↦
      congrArg _ (map_one (genericAlg.map _).1).symm
  -- `exists_isTodaCancellation` for the gluing, with `δ`, `δ'` one minus the twist and `origin`
  -- that of the disc `true`; `h_toda` says that `j^* (unitsExtClass m) = 0` kills the pull-back of
  -- `m` along `one`.
  obtain ⟨B, K, j, y, ω, h_toda⟩ := by
    refine exists_isTodaCancellation (oneSub_comp_gluing epsPow) (origin ⟨true⟩)
      (hom_ext (by simp -dsimp [discTwist_comp_evalZero]))
      ((relFreeAb.shortExact unimodular).2.map_of_exact (restrictAlong _)) shortExact_oneSubMu.2
        (f := projFirst ≫ freeAb.map a)
      (α := -W ≫ whiskerLeft _ Gm.ofCoord) (κ := projFirst ≫ one) (n := whiskerLeft _ Gm.ofCoord)
      (α₁ := -W ≫ whiskerRight proj _) (freeAb.hom_ext ?_) (freeAb.hom_ext ?_) (freeAb.hom_ext ?_)
        (freeAb.hom_ext ?_)
    · -- Both sides send a point `u` of the torus to `-[a u]`.
      rintro c ⟨⟨_ | _⟩, t⟩
      · simp [W]
      · simp [W]
        rfl
    · -- `a` is invariant under the twist.
      rintro c ⟨⟨_ | _⟩, t⟩
      · simp
      · simp [sub_eq_zero, -Bool.cond_eq_ite]
        exact congrArg FreeAbelianGroup.of (ha_twist _ ⟨true⟩ _).symm
    · -- With `μ = mulMu c 1`, which has square zero:
      -- `(1 - μ) * [ε * u] = (1 - μ) * (1 + μ) * [u] = [u]`.
      rintro c ⟨⟨_ | _⟩, t⟩
      · simp [W]
      simp [W]
      refine sub_eq_of_eq_add (Gm.ext.2 (.symm ?_))
      change (1 - mulMu c _) * _ = _
      -- The values of `W` and `one` on generators are `desc_of` only up to unfolding, hence `erw`.
      erw [desc_of, desc_of, desc_of, IsUnit.unit_spec]
      simp [hA, pointOrTorusTwist, charTwist, pointOrTorus, teichmullerLift_epsTilt, AddEquiv.ulift,
        -AddMonoidAlgebra.coe_algebraMap, -Bool.cond_eq_ite]
    · -- `Gm.ofCoord` commutes with `proj`.
      rintro c ⟨⟨_ | _⟩, t⟩ <;> simp [W]
  obtain ⟨j', h_pull⟩ :=
    exists_map_eq_map_of_isTodaCancellation A hA_inv ha_twist h_toda ξT h_compare
  -- The point goes to `1`, a unit for the multiplication of `R[1/p]`.
  have h_unit :
      tensorPoint (origin ⟨true⟩ ≫ projFirst ≫ one) genericCoeff ≫
          (genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing =
        𝟙 genericCoeff := by
    ext _ ⟨⟩
    exact congrArg _ ((mul_one_add ..).trans (by simp))
  exact eq_zero_of_cup_eq_zero_of_isTodaCancellation h_toda h_unit h_pull x hx

end New.Variety

end LinePointClass

/-! ## Point classes of projective space -/

section ProjectivePointClass

open CategoryTheory Finset CartesianMonoidalCategory CommAlgCat Fin Polynomial

set_option backward.isDefEq.respectTransparency false

/-- All `k`-points of projective space have the same class: a global function takes the same value
at all of them. -/
lemma New.Variety.projSpace.pointClass_eq_pointClass_affinePoint {k : Type} [Field k] [CharZero k]
    {d : ℕ} (z : (projSpace k d).obj (of k k)) :
    pointClass d z = pointClass d (affinePoint 0 0 : (projSpace k d).obj (of k k)) := by
  obtain ⟨⟨u⟩, hu⟩ := z
  refine pointClass_eq_of_functions_eq fun g ↦ ?_
  -- `val x` is the value of `g` at a point `x`; it commutes with algebra maps.
  let val {A : CommAlg k} (x : (projSpace k d).obj A) : A := (g.app A x).down 0
  have val_map {A B : CommAlg k} (ψ : A ⟶ B) (x : (projSpace k d).obj A) (y : (projSpace k d).obj B)
      (hy : y = (projSpace k d).map ψ x) : val y = ψ (val x) := by
    subst hy
    exact congrArg (fun a ↦ a.down 0) (g.naturality_apply ψ x)
  by_cases h : ∃ j, u (succ j) ≠ 0
  swap
  · -- If all coordinates but the first vanish, the point is `affinePoint 0 0`.
    simp only [not_exists, not_not] at h
    refine val_map (𝟙 _) _ _ (mk_eq_mk_iff_cross_mul.mpr ?_)
    simp [forall_fin_succ, h]
  -- The line through the two points is covered by the `k[X]`-points `x = [X : u₁ : ⋯]` and
  -- `x' = [1 : u₁ X : ⋯]`, which agree over `k[X, X⁻¹]` after `X ↦ X⁻¹`.
  obtain ⟨j, hj⟩ := h
  have h_unit : IsUnit ((cons X (C ∘ u ∘ succ) : Fin (d + 1) → k[X]) j.succ) := by simpa using hj
  let x : (projSpace k d).obj (of k k[X]) :=
    mk (cons X (C ∘ u ∘ succ)) (span_eq_top_of_isUnit j.succ h_unit)
  let x' : (projSpace k d).obj (of k k[X]) := affinePoint 0 (monomial 1 ∘ u ∘ succ)
  have glue : toLaurent (val x) = LaurentPolynomial.invert (toLaurent (val x')) := by
    refine (val_map (ofHom toLaurentAlg) x _ (mk_eq_mk_iff_cross_mul.mpr ?_)).symm.trans
      (val_map (ofHom (LaurentPolynomial.invert.toAlgHom.comp toLaurentAlg)) x' _ rfl)
    simp [forall_fin_succ]
    grind
  -- `P(T) = Q(T⁻¹)` forces `P` and `Q` to be one constant.
  obtain ⟨c, val_x, val_x'⟩ : ∃ c : k, val x = C c ∧ val x' = C c :=
    eq_C_of_toLaurent_eq _ _ glue
  -- The first point is `x` at `X = u 0`, the second is `x'` at `X = 0`.
  have hx_eval : mk u hu = (projSpace k d).map (ofHom (aeval (u 0))) x :=
    mk_eq_mk_iff_cross_mul.mpr (by simp [forall_fin_succ])
  have hx'_eval : affinePoint 0 0 = (projSpace k d).map (ofHom (aeval (0 : k))) x' :=
    mk_eq_mk_iff_cross_mul.mpr (by simp [forall_fin_succ])
  calc
    val (mk u hu) = aeval (u 0) (val x) := val_map (ofHom (aeval (u 0))) x _ hx_eval
    _ = aeval 0 (val x') := by simp [val_x, val_x']
    _ = val (affinePoint 0 0) := (val_map (ofHom (aeval 0)) x' _ hx'_eval).symm

/-- Let `k` be a field of characteristic zero with an embedding in `ℚ̄_p`, and let `X` be a functor
on `k`-algebras with an atlas of dimension `d` (separated, with finitely many charts, each having
`d` étale coordinates, that together contain every field-valued point). For a `k`-point `z` of `X`,
the class `pointClass d z` of `z` in degree-`d` Hodge cohomology is killed by `hodgeTateMap l` for
every `l ≠ d`. -/
lemma New.Variety.hodgeTateMap_pointClass_eq_zero_of_ne {p : ℕ} {k : Type} [Field k]
    [EmbeddedInQpBar p k] {d l : ℕ}
    {X : CommAlg k ⥤ Type 1} [hX : HasAtlas d X] (z : X.obj (of k k)) (hl : l ≠ d) :
    hodgeTateMap l (pointClass (X := X) d z) = 0 := by
  -- By the fixed point formula for the identity and the constant map `z`, one class `x` has
  -- `HodgeH.scale t x = t ^ d • pointClass d z` for all `t`. Compare `t = 1` and `t = 2` under
  -- `hodgeTateMap l`, which turns `HodgeH.scale t` into `t ^ l` (`hodgeTateMap_scale`).
  obtain ⟨δ, hδ⟩ := exists_diagonal_map_scaledGraph_eq_sum_pointClass hX
  have h_coincidence : IsCoincidenceSet (𝟙 X) (constMap z) {z} := by
    simp [IsCoincidenceSet, ConstIfCoincident, constMap, map_map_structureMap (k := k)]
  have h_jacobian (t : k) (w : X.obj (of k k)) :
      HasJacobianRatio (E := k) (𝟙 X) (constMap z) d t (Matrix.scalar (Fin d) t).det w := by
    refine fun A _ ↦ ⟨.scalar _ t, rfl, fun _ _ γ _ _ hγ ↦ ?_⟩
    rw [A.eq_comp_of_map_point_eq _ (h_coincidence.1 _ hγ.symm)]
    simp
    -- The tangent vector `γ` of the constant map is zero; it is seen as `0` only up to unfolding.
    repeat erw [sub_zero]
  let x : HodgeH (freeAb.obj X) d := HodgeH.map (freeAb.map (lift (𝟙 X) (constMap z))) δ.baseChange
  have h_scale_eq (t : k) : HodgeH.scale t x = t ^ d • pointClass d z :=
    calc
      _ = H.map _ (freeAb.map (scaledGraph t (𝟙 X) (constMap z))) d δ.baseChange :=
        -- `scale t` and pull-back along the graph compose to pull-back along the scaled graph.
        (H.map_comp ..).symm.trans
          (congrArg (fun f ↦ H.map _ f d δ.baseChange) freeAb.hom_ext)
      _ = ∑ w ∈ {z}, (Matrix.scalar (Fin d) t).det • pointClass d w :=
        hδ _ _ _ t _ h_coincidence fun w _ ↦ h_jacobian t w
      _ = t ^ d • pointClass d z := by simp
  have h_one : hodgeTateMap l x = hodgeTateMap l (pointClass d z) := by
    simpa [hodgeTateMap_scale] using congrArg (hodgeTateMap l) (h_scale_eq 1)
  have h_two : (2 : k) ^ l • hodgeTateMap l (pointClass d z) =
      (2 : k) ^ d • hodgeTateMap l (pointClass d z) := by
    simpa [hodgeTateMap_scale, h_one] using congrArg (hodgeTateMap l) (h_scale_eq 2)
  by_contra h_ne
  have h_pow_cast : ((2 ^ l : ℕ) : k) = (2 ^ d : ℕ) := by simpa [smul_left_inj h_ne] using h_two
  exact hl (Nat.pow_right_injective le_rfl (Nat.cast_injective h_pow_cast))

/-- In characteristic zero, let `z` be a `k`-point of `ℙ^d` and
`lineProductMap k d : ℙ^d × ℙ¹ → ℙ^(d+1)` the map sending `([v], [w 0 : w 1])` to the point with
coordinates `w 0 * ∑ i, v i` and `(w 1 - i * w 0) * v i`. Then the pull-back along this map of the
Hodge class of the point `affinePoint 0 0 = [1 : 0 : … : 0]` of `ℙ^(d+1)` is a positive multiple `n`
of the image in the Hodge cohomology of `ℤ[ℙ^d × ℙ¹]` of the cup product (exterior-algebra
multiplication) of the classes of `z` and of `[1 : 0]` in `ℙ¹`. -/
lemma New.Variety.projSpace.exists_map_pointClass_eq_nsmul_map_cup {k : Type} [Field k] [CharZero k]
    {d : ℕ} (z : (projSpace k d).obj (of k k)) :
    ∃ n ≠ (0 : ℕ),
      HodgeH.map (freeAb.map (lineProductMap k d)) (pointClass (d + 1) (affinePoint 0 0)) =
        n •
          HodgeH.map (freeAb.prod (projSpace k d) (projSpace k 1))
            (cup (exteriorAlg (k := k)).mulPairing (pointClass d z) (pointClass 1 (affinePoint 0 0))
              (add_comm 1 d)) := by
  classical
  let W : CommAlg k ⥤ Type 1 := MonoidalCategory.tensorObj (projSpace k d) (projSpace k 1)
  let y (j : Fin (d + 1)) : W.obj (of k k) := (affinePoint j 0, affinePoint 0 ![j])
  -- Over a local ring, a point of the fibre is one of the `y j`.
  have fibre {B : CommAlg k} {v : (projSpace k d).obj B} {u : (projSpace k 1).obj B}
      (e :
        (lineProductMap k d).app B (v, u) = (projSpace k d.succ).map structureMap (affinePoint 0 0))
      [IsLocalRing B] : ∃ j : Fin (d + 1), (v, u) = W.map structureMap (y j) := by
    induction v, u using Quot.induction_on₂
    refine exists_eq_map_affinePoint_of_mul_eq_zero _ _ fun i ↦ ?_
    simpa using mk_eq_mk_iff_cross_mul.mp e i.succ 0
  have coin :
      IsCoincidenceSet (constMap (affinePoint 0 0)) (lineProductMap k d) (univ.image y) := by
    refine ⟨fun (v, u) e ↦ ?_, forall_mem_image.mpr fun j _ ↦ ?_, fun B field (v, u) e ↦ ?_⟩
    · obtain ⟨j, hj⟩ := fibre e
      rw [hj, map_map_structureMap]
    · exact mk_eq_mk_iff_cross_mul.mpr (by simp [forall_fin_succ, Pi.single_apply])
    · let : Field B := field.toField
      exact exists_mem_image.mpr ((fibre e).imp fun j hj ↦ ⟨mem_univ j, hj⟩)
  refine ⟨#(univ.image y), by simp [Finset.ext_iff], ?_⟩
  -- The class pulls back to the sum of the classes of the points of the reduced fibre.
  rw [map_pointClass_eq_sum_of_isCoincidenceSet _ _ coin]
  -- The class of a point `(v, w)` is the product of the classes, which do not depend on the points.
  refine sum_eq_card_nsmul fun ⟨v, w⟩ _ ↦ ?_
  rw [← IsPointSum.cup_pointClass, pointClass_eq_pointClass_affinePoint v,
    pointClass_eq_pointClass_affinePoint w, pointClass_eq_pointClass_affinePoint z]

-- Keeps definitional checks from unfolding the Ext groups.
seal CategoryTheory.Abelian.Ext in
/-- Let `k` be a field of characteristic zero with an embedding in `ℚ̄_p`, and let `z` be a
`k`-point of projective `d`-space. The Hodge–Tate map `hodgeTateMap d` does not kill the class
`pointClass d z` of `z` in the degree-`d` Hodge cohomology of projective `d`-space. -/
lemma New.Variety.projSpace.hodgeTateMap_pointClass_ne_zero {p : ℕ} {k : Type} [Field k]
    [EmbeddedInQpBar p k] {d : ℕ} (z : (projSpace k d).obj (of k k)) :
    hodgeTateMap d (pointClass d z) ≠ 0 := by
  -- Induct on `d`, pulling the class of `affinePoint 0 0` back along `lineProductMap k d`; `η`
  -- lifts `hodgeTateMap 1` of the class of `[1 : 0]` (`hη`), and `x × η = 0` forces `x = 0`.
  obtain ⟨η, hη, η_reg⟩ := exists_hodgeTateMap_pointClass_line (k := k)
  -- The pull-back of the class of `affinePoint 0 0` is killed by `hodgeTateMap (d + 1)` exactly if
  -- the class of `z` is killed by `hodgeTateMap d`.
  have key_iff {d} (z : (projSpace k d).obj (of k k)) :
      hodgeTateMap (d + 1)
          (.map (freeAb.map (lineProductMap k d)) (pointClass (d + 1) (affinePoint 0 0))) = 0 ↔
        hodgeTateMap d (pointClass d z) = 0 := by
    obtain ⟨ξ, hξ⟩ : ∃ ξ, hodgeTateMap d (pointClass d z) = restrictToPairs (n := d + d) ξ :=
      IsChartCovered.pairRestrictBijective.exists_hodgeTateMap_eq d (pointClass d z)
    obtain ⟨n, n_ne, hn⟩ := exists_map_pointClass_eq_nsmul_map_cup z
    -- Only the term `h = d` of the product formula survives; its coefficient is `± n * (d + 1)`.
    trans PairH.map (freeAb.prod (projSpace k d) (projSpace k 1))
      (HodgeTatePair.cross (restrictToPairs η) (restrictToPairs ξ)) = 0
    · rw [hn, map_nsmul, hodgeTateMap_map, hodgeTateMap_cup, sum_eq_single d _ (by simp)]
      · simp [n_ne, hξ, hη, ← Nat.cast_smul_eq_nsmul k, Nat.cast_add_one_ne_zero]
      · intro h _ h_ne
        simp [hodgeTateMap_pointClass_eq_zero_of_ne z h_ne]
    rw [hξ]
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    -- The product comes from the product `x` of `ξ` and `η` on tests, and `η` is regular.
    let x :=
      cup (PadicTest.genericAlg ⋙ forget₂ _ (AlgCat ℂ_[p])).mulPairing ξ η (add_comm 2 (d + d))
    have restrictToPairs_x :
        restrictToPairs
            (N := (abTensor.obj (freeAb.obj (projSpace k d))).obj (freeAb.obj (projSpace k 1))) x =
        HodgeTatePair.cross (restrictToPairs η) (restrictToPairs ξ) := by
      let c := Comparison.restrict HodgeTatePair.toTest genericCoeff
      let F := HodgeTatePair.toTest ⋙ genericCoeff
      let μ : (abTensor.obj F).obj F ⟶ F := HodgeTatePair.toTest.whiskerLeft
        (PadicTest.genericAlg ⋙ forget₂ _ (AlgCat ℂ_[p])).mulPairing
      -- `abTensor_hom_ext` is given explicitly: `simp` is slow here.
      have pull_x := c.pull_cup (μ' := μ) (η := HodgeTatePair.toGeneric)
        (abTensor_hom_ext fun _ _ _ ↦ rfl) ξ η (add_comm 2 (d + d))
      exact (congrArg Abelian.Ext.toTotalH pull_x).trans (TotalH.cup_of μ ..).symm
    have x_zero : x = 0 := by
      refine IsChartCovered.pairRestrictBijective.injective_restrictToPairs.comp
        (IsCohomEquiv.of_isIso ..).1
        ((restrictToPairs_map (freeAb.prod (projSpace k d) (projSpace k 1)) x).trans ?_)
      simpa [restrictToPairs_x] using h
    rw [η_reg (N := _ ⋙ freeAb.obj (projSpace k d)) ξ x_zero, map_zero]
  induction d with
  | succ d ih =>
    rw [pointClass_eq_pointClass_affinePoint z]
    intro h_zero
    have h_pullback_zero :
        hodgeTateMap (d + 1)
          (.map (freeAb.map (lineProductMap k d)) (pointClass (d + 1) (affinePoint 0 0))) = 0 := by
      rw [hodgeTateMap_map, h_zero, map_zero]
    exact ih (affinePoint 0 0) ((key_iff _).1 h_pullback_zero)
  | zero =>
    -- Here `lineProductMap k 0` has a section `σ`, so `key_iff` would give `η = 0`.
    intro h
    let σ : projSpace k 1 ⟶ MonoidalCategory.tensorObj (projSpace k 0) (projSpace k 1) :=
      lift (constMap (affinePoint 0 0)) (𝟙 _)
    have σ_mul : σ ≫ lineProductMap k 0 = 𝟙 _ := by
      ext _ ⟨⟩
      exact mk_eq_mk_iff_cross_mul.2 (by simp)
    have η_zero : η = 0 := by
      have h_pullback := congrArg (PairH.map (freeAb.map σ)) ((key_iff z).2 h)
      -- Since `σ` is a section, the left side is `hodgeTateMap 1` of the class of `[1 : 0]`, the
      -- restriction of `η`.
      erw [← hodgeTateMap_map, ← HodgeH.map_comp, ← freeAb.map_comp, σ_mul, freeAb.map_id, H.map_id,
        hη, map_zero,
        map_eq_zero_iff _ IsChartCovered.pairRestrictBijective.injective_restrictToPairs]
        at h_pullback
      exact h_pullback
    -- Then every class on tests vanishes, so the coefficients `genericCoeff` are zero; but `1 ≠ 0`
    -- at the test `T`.
    have id_zero : 𝟙 genericCoeff = 0 := by simpa [cup, η_zero] using η_reg (.mk₀ (𝟙 genericCoeff))
    let T : PadicTest := ⟨Unit, _, Pi.constRingHom ..⟩
    have h_one_eq_zero : algebraMap T.ProdRing T.GenericRing 1 = 0 :=
      congr(($(id_zero).1 T ⟨algebraMap T.ProdRing T.GenericRing 1⟩).1)
    simpa using T.eq_zero_of_algebraMap_genericRing 1 h_one_eq_zero

end ProjectivePointClass

end
