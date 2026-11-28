import Lib.Cohomology.SmoothBaseChange

/-!
# The primitive comparison theorem and finiteness of p-adic cohomology

This file concerns a proper scheme `Y` over `R` that is charted over an algebraic closure `Ω` of `ℚ`
(`New.Variety.IsCharted`). A p-adic test is a product of valuation rings over `O_C`, the integers of
`ℂ_p`, and `O^♭` is the tilt of `O_C`. The primitive comparison theorem compares the mod `p`
cohomology of `Y`, tensored with `O^♭`, with the cohomology of its points in p-adic tests with
tilted coefficients.

## Main definitions and results

* `New.Variety.finite_and_primitive_comparison`: let `Y` be proper over `R` and charted over `Ω`,
  and assume `IsAcyclicOnPerfect (moduleCoeff (tensorCoeff M))`. Then `Y_Ω` has flat base change and
  finite mod `p` cohomology, and the comparison map is bijective.
* `New.Variety.finite_padic_cohomology`: the cohomology with coefficients `ℤ_p` is finitely
  generated; hence `New.Variety.ellAdicCohom R Ω n`, which is `ℚ_p ⊗` this module, is
  finite-dimensional at `Y`.
* `New.Variety.ellAdicCohom.continuous_galoisAction`: the Galois action
  `New.Variety.ellAdicCohom.galoisAction` is continuous, tested on a vector and a linear map to
  `Q̄_p ^ N`. Modulo `p ^ k` a class is defined over finitely many elements of `Ω`, so it is fixed
  by an open subgroup.

Notions from other files:
* `New.Variety.genericTestOver`: The functor sending a p-adic test with ring R to R[1/p], a test
  over Ω with algebra structure through Ω → ℂ_p.
* `New.Variety.primitiveMap`: The natural map O^♭ ⊗ LC(Spec S[1/p], 𝔽_p) → S^♭ on p-adic tests S,
  with LC the locally constant functions; its source is `New.Variety.oFlatLocConst`.
* `New.Variety.HasFlatBaseChange` N: M ⊗ Hⁿ(N, Φ) → Hⁿ(N, M ⊗ Φ) is bijective for flat M.
* `New.Variety.testPoints`: For R → O_C, the functor sending an R-scheme X to the functor S ↦ X(S)
  of its points over R in p-adic tests.
* `New.Variety.H`: `H N F n` is Extⁿ(N, F) among functors to abelian groups; for
  `N = freeAb X = ℤ[X]` it is the cohomology Hⁿ(X, F). `testIncl ⋙ X` restricts `X` to test rings.

## Relation to the literature

Known result: Finiteness and Galois continuity of p-adic étale cohomology. The result is stated for
cohomology on test rings, not identified with étale cohomology, of proper schemes charted over an
algebraic closure of Q, with constant coefficients, where integral coefficients are the Witt vectors
of the mod p functions. Finiteness is lifted from finiteness modulo p, which comes from the
primitive comparison. Source: SGA 4, Exp. XIV (Artin), finiteness for proper morphisms; Scholze 2013
Thm 1.1; by duality, Zavyalov arXiv 2301.03821 Appl. 1.3.4.

See also `Lib.PadicComparison.HodgeTate.PeriodMap`.
-/

/-! ## The primitive comparison theorem and flat base change -/

namespace New.Variety

open CategoryTheory TensorProduct Functor Period AlgebraTensorModule AlgebraicGeometry TotalH
  Function PadicTest Abelian.Ext ConcreteCategory Comparison DirectSum ULift CommRingCat Over

variable {p : ℕ} [ThePrime p]
  {M : ModuleCat OFlat} {R : CommRingCat}
  (Ω : Type) [Field.{0} Ω] [Algebra R Ω] [Algebra Ω ℂ_[p]]

/-- The valuative criterion in a p-adic test `c`. Its ring `c.ProdRing` is the product of a
non-empty family of valuation rings (cells) with a ring map from O_C, and
`c.GenericRing = c.ProdRing[1/p]`. Let `Y` be proper over `R`, and make `Spec c.ProdRing` and
`Spec c.GenericRing` schemes over `R` by `a : Spec c.ProdRing ⟶ Spec R` and
`b : Spec c.GenericRing ⟶ Spec R`. The map `Spec c.GenericRing → Spec c.ProdRing` is a map over `R`:
`w` says that `b` is the restriction of `a`, and `r` is the trivial map of the one-point base of
`Over`, so `w` is `Spec.map (algebraMap c.ProdRing c.GenericRing) ≫ a = b ≫ 𝟙 _`. Then restriction
`Y(c.ProdRing) → Y(c.GenericRing)` of points over `R` is bijective. -/
lemma PadicTest.bijective_generic_points {Y : Over (Spec R)} [IsProper Y.hom] (c : PadicTest)
    {a b r w} :
    Bijective
      ((uliftYoneda.{1} Y).map
        (.op (X := .mk b) (Y := .mk a)
          ⟨Spec.map (ofHom (algebraMap c.ProdRing c.GenericRing)), r, w⟩)) := by
  have hY_compact : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  -- `Y` is separated: two points agree if they do after a jointly injective family of ring maps.
  have h_sep {C : CommRingCat} {J : Type} {K : J → CommRingCat} (f : ∀ j, C ⟶ K j)
      (hf : ∀ t : C, (∀ j, f j t = 0) → t = 0) {x y : Spec C ⟶ Y.left}
      (h : ∀ j, Spec.map (f j) ≫ x = Spec.map (f j) ≫ y) : x = y :=
    up.inj ((isProperOver_pointsToBase Y.hom).ext_of_jointly_injective f hf fun j ↦
      congrArg up (h j))
  refine ⟨fun x y h ↦ ?_, fun z ↦ ?_⟩
  · -- Injectivity: `c.ProdRing → c.GenericRing` is itself injective.
    have h_left : x.down.left = y.down.left :=
      h_sep (fun _ : Unit ↦ ofHom (algebraMap c.ProdRing c.GenericRing))
        (fun t ht ↦ c.eq_zero_of_algebraMap_genericRing t (ht ())) fun _ ↦ congrArg (·.down.left) h
    exact down_injective (OverMorphism.ext h_left)
  -- Surjectivity. As `p ≠ 0` in the cell `c.Cell i`, the projection extends to a map `φ i` from
  -- `c.GenericRing` to the fraction field of the cell.
  let π (i : c.Index) : of c.ProdRing ⟶ of (c.Cell i) := CommRingCat.ofHom (Pi.evalRingHom c.Cell i)
  let j (i : c.Index) : of (c.Cell i) ⟶ of (FractionRing (c.Cell i)) :=
    CommRingCat.ofHom (algebraMap _ _)
  have hp (i : c.Index) : IsUnit ((π i ≫ j i).hom p) := by
    simp [π, j, -map_natCast, IsCell.p_ne_zero]
  let φ (i : c.Index) : c.GenericRing →+* FractionRing (c.Cell i) :=
    IsLocalization.Away.lift (p : c.ProdRing) (hp i)
  have sq (i : c.Index) : CommSq (Spec.map (ofHom (φ i))) (Spec.map (j i))
      (Spec.map (ofHom (algebraMap c.ProdRing c.GenericRing))) (Spec.map (π i)) :=
    ⟨by simp [← Spec.map_comp, ← ofHom_comp, φ, π, j]⟩
  -- The valuative criterion extends the point `z` over `Frac (c.Cell i)` to the cell `c.Cell i`.
  have lift (i : c.Index) : ∃ l : Spec (of (c.Cell i)) ⟶ Y.left,
      Spec.map (j i) ≫ l = Spec.map (ofHom (φ i)) ≫ z.down.left ∧
        l ≫ Y.hom = Spec.map (π i) ≫ a := by
    have h_val : ValuativeCriterion.Existence Y.hom :=
      (UniversallyClosed.eq_valuativeCriterion.le _ _ _ inferInstance).1
    -- the valuative square: the cell, its fraction field, `z` after `φ i` on top, `a` on the cell
    let S : ValuativeCommSq Y.hom :=
      { R := c.Cell i, K := FractionRing (c.Cell i)
        i₁ := Spec.map (ofHom (φ i)) ≫ z.down.left, i₂ := Spec.map (π i) ≫ a
        commSq := (sq i).horiz_comp ⟨z.down.w.trans w.symm⟩ }
    obtain ⟨⟨l⟩⟩ : S.commSq.HasLift := h_val S
    exact ⟨l.l, l.fac_left, l.fac_right⟩
  choose l hl_left hl_right using lift
  -- `Y` is quasi-compact, so the points `l i` come from a point `x` in the product `c.ProdRing`.
  -- The first argument of `pointsPi_surjective` is explicit: with `_` the search for `IsLocalRing`
  -- times out.
  obtain ⟨x, hx⟩ := pointsPi_surjective (of <| c.Cell ·) Y.left l
  have hx_eq (i : c.Index) : Spec.map (π i) ≫ x = l i := congrFun hx i
  have hx_over : x ≫ Y.hom = a := by
    -- both sides are determined by their restrictions to the cells, where `hl_right` holds
    refine pointsPi_injective _ _ (funext fun i ↦ ?_)
    show Spec.map (π i) ≫ x ≫ Y.hom = Spec.map (π i) ≫ a
    rw [← Category.assoc, hx_eq, hl_right]
  -- The restriction of `x` to `c.GenericRing` and `z` agree after each `φ i`.
  refine ⟨⟨homMk x hx_over⟩,
    down_injective (OverMorphism.ext (h_sep (fun i ↦ ofHom (φ i)) (fun t ht ↦ ?_) fun i ↦ ?_))⟩
  · -- The `φ i` are jointly injective: up to a unit, `t` comes from some `r : c.ProdRing`.
    obtain ⟨r, u, rfl⟩ := exists_associated_localization t
    have hr : r = 0 := by simp_all [φ, π, j, funext_iff, (u.isUnit.map _).ne_zero]
    simp [hr]
  · -- after `Spec (φ i)`, the restriction of `x` to `c.GenericRing` is `x` on the cell, that is
    -- `l i`, which extends `z`
    show Spec.map (ofHom (φ i)) ≫ Spec.map (ofHom (algebraMap c.ProdRing c.GenericRing)) ≫ x =
      Spec.map (ofHom (φ i)) ≫ z.down.left
    rw [(sq i).w_assoc, hx_eq, hl_left]

/-- For a scheme Y over R, the map Y(S) → Y(S[1/p]), natural in the p-adic test S; `he` says that
R → Ω → ℂ_p agrees with R → O_C → ℂ_p. -/
noncomputable def toGenericPoints [Algebra R OC]
    (he : ∀ r : R, algebraMap Ω ℂ_[p] (algebraMap R Ω r) = algebraMap R OC r) (Y : Over (Spec R)) :
    testPoints Y ⟶ genericTestOver Ω ⋙ ObjectProperty.ι _ ⋙ algPointsOf Ω R Y :=
  whiskerRight (H := genericAlg ⋙ restrictAlg Ω (ℂ_[p]) ⋙ restrictAlg R Ω)
    { app c :=
        CommAlg.homOfRingHom (algebraMap c.ProdRing c.GenericRing) fun r ↦
          (he r ▸ c.genericStructureMap_coe ((algebraMap R OC) r)).symm
      naturality := by
        intros
        ext
        exact (mapGeneric_algebraMap ..).symm }
    (algPointsOf R R Y)

set_option backward.isDefEq.respectTransparency false

/-- Let `Ω` be a field in which `ℓ` is invertible and `D` a compared theory on tests over `Ω`
(`New.Variety.ComparedTheory`). Then `D.IsFiniteLerayHirsch` (the classes `D.comparison` form a
Leray–Hirsch basis and the total cohomology is finite) holds for `ℤ[X] = freeAb X` iff it holds for
`ℤ[X] / ℤ[U]` (`relFreeAb`), where `U = offClosedFibre X` is the part of `X` away from the special
fibre. Over a field `U` does not count: the maximal ideal of `Ω` is zero, so `U` has points only
over the zero ring. -/
lemma ComparedTheory.isFiniteLerayHirsch_freeAb_iff_relFreeAb {ℓ : ℕ} {Ω : Type} {C : Type 1}
    [Field Ω] [InvertsPrime Ω ℓ]
    [Category.{0, 1} C] {g : C ⥤ TestOver Ω} (D : ComparedTheory g) {X : TestOver Ω ⥤ Type 1} :
    D.IsFiniteLerayHirsch (freeAb X) ↔ D.IsFiniteLerayHirsch (relFreeAb (offClosedFibre X)) := by
  -- `D.IsFiniteLerayHirsch` is a closed class: it holds at zero objects, and along a short exact
  -- sequence it passes between the middle and the quotient when it holds for the subobject
  obtain ⟨h_zero, h_ses⟩ := D.isClosedClass_isFiniteLerayHirsch
  -- The maximal ideal of `Ω` is zero, so `offClosedFibre X` has points only over the zero ring and
  -- does not count.
  have h_sub : D.IsFiniteLerayHirsch (freeAb (offClosedFibre X).toFunctor) := by
    -- The empty subfunctor is locally everything: a ring with a point `y` has no maximal ideal.
    refine (D.isFiniteLerayHirsch_iff_of_isCohomEquiv (freeAb.map (Subfunctor.ι ⊥))
      fun _ zar ↦ ?_).mp (h_zero _ (freeAb.hom_ext nofun))
    refine (zar (U := .whisker (Y := (offClosedFibre X).toFunctor) ⊥ _)
      fun _ y _ hm ↦ ?_).isCohomEquiv
    refine (hm.ne_top (eq_top_mono ?_ y.prop)).elim
    simp only [IdealFamily.ofMaximalIdeal, IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot, bot_le]
  obtain ⟨w, h_exact⟩ := relFreeAb.shortExact (offClosedFibre X)
  exact h_ses ⟨_, _, w⟩ h_exact h_sub

omit [ThePrime p] [Algebra Ω ℂ_[p]] in
/-- The points of a proper `Y` over `R` on tests over `Ω` have flat base change: the functor is
covered by affine pieces (`isAffinelyCovered_algPointsOf`). -/
lemma hasFlatBaseChange_algPointsOf [InvertsPrime Ω p] (Y : Over (Spec R)) [IsProper Y.hom] :
    HasFlatBaseChange
      (freeAb (ObjectProperty.ι _ ⋙ algPointsOf Ω R Y) : AbFunctor (TestOver Ω)) :=
  (isAffinelyCovered_algPointsOf (·.2.2) Y).hasFlatBaseChange

omit [ThePrime p] [Algebra Ω ℂ_[p]] in
/-- Flat base change for the points of `Y_Ω` on test rings, for `Y` proper over `R`. Restriction
from all test rings to tests over `Ω` is bijective on cohomology (`isBijective_algToBaseChange`)
and commutes with base change (`baseChangeMap_pull`), and on tests over `Ω` flat base change holds
by `hasFlatBaseChange_algPointsOf`. -/
lemma hasFlatBaseChange_geomPoints [InvertsPrime Ω p] (Y : Over (Spec R)) [IsProper Y.hom] :
    HasFlatBaseChange (freeAb (testIncl ⋙ geomPoints R Ω Y)) := by
  -- the eight instance arguments of `HasFlatBaseChange` stay anonymous
  intro S T L _ _ _ _ _ _ _ _ Φ n
  exact (bijective_iff_of_comm_sq (baseChangeMap_pull (𝟙 _) _)
      (map_bijective bijective_id (isBijective_algToBaseChange Ω Y (moduleCoeff Φ) n))
      (by simpa using! isBijective_algToBaseChange ..)).2
    (hasFlatBaseChange_algPointsOf Ω Y ..)

/-- The functors `S ↦ Hom(O^♭, S^♭)` (maps of `O^♭`-algebras) and `S ↦ Hom(Ω, S[1/p])` (maps of
tests over `Ω`) on `p`-adic tests are isomorphic: each value is a single point, since `O^♭` and
`Ω` are initial. -/
noncomputable def tiltReprIsoGenericRepr [IsAbsIntegrallyClosedLocal Ω] :
    tilt ⋙ reprBy (.of OFlat OFlat) ≅ genericTestOver Ω ⋙ reprBy (.ofSelf Ω) :=
  -- at each test there is exactly one map of `O^♭`-algebras out of `O^♭`
  have h_init (A : PadicTest) : Bijective ((toUnit (tilt ⋙ reprBy (.of OFlat OFlat))).app A) :=
    ⟨fun _ _ _ ↦ congrArg ULift.up (CommAlgCat.hom_ext (by ext)), fun _ ↦ ⟨⟨structureMap⟩, rfl⟩⟩
  isoOfAppBijective _ h_init ≪≫ isoWhiskerLeft _
    (isoOfAppBijective _ pointMap_ofSelf_bijective).symm

/-- The locally constant functions on `Spec Ω`, tensored with `O^♭` (`oFlatLocConst` at the test
`Ω`), are `O^♭` itself: on the spectrum of a field the locally constant functions are
constant. -/
noncomputable def oFlatLocConstOfSelfIso [IsAbsIntegrallyClosedLocal Ω] :
    CommAlgCat.of OFlat OFlat ≅ (TestOver.toTest Ω ⋙ oFlatLocConst).obj (.ofSelf Ω) :=
  CommAlgCat.isoMk (.ofBijective _ (Algebra.TensorProduct.includeLeft_bijective
    ((bijective_const_of_isDomain (B := .of Ω)).of_comp_left up_injective)))

/-- Primitive comparison. Let `Ω` be algebraically closed with a map to `ℂ_p`, `Y` proper over `R`
and charted over `Ω` (`IsCharted`), and `M` an `O^♭`-module. Assume `ac`: for each perfect
`O^♭`-algebra `b`, the functor `S ↦ Hom(b, S^♭)` on p-adic tests, with coefficients `S ↦ S^♭ ⊗ M`,
has cohomology `b ⊗ M` in degree 0. Write `X` for the points of `Y_Ω` on test rings. Then (a) the
cohomology of `Y_Ω` commutes with flat extension of coefficients; (b) each `Hⁿ(Y_Ω, 𝔽_p)` is finite;
(c) if moreover `R` maps to `O_C` compatibly (`he`), then `primitiveMap ⊗ M` induces a bijection in
every degree, along `toGenericPoints` followed by `algToBaseChange` (points of `Y` over tests over
`Ω` taken as points of `Y_Ω`). Here `primitiveMap` is the natural map `O^♭ ⊗ LC(Spec S[1/p]) → S^♭`,
with `LC` the locally constant `𝔽_p`-valued functions. The bijection goes from the cohomology of
`Y_Ω` with coefficients `A ↦ O^♭ ⊗ LC(Spec A) ⊗ M` to that of `S ↦ Y(S)` on p-adic tests with
coefficients `S^♭ ⊗ M`. Only (c) uses the map `R → O_C`. -/
lemma finite_and_primitive_comparison [IsAlgClosed Ω]
    (ac : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff M))) (Y : Over (Spec R)) [IsCharted Y Ω]
    [IsProper Y.hom] :
    let X := testIncl ⋙ geomPoints R Ω Y
    -- (a)
    HasFlatBaseChange (freeAb X) ∧
    -- (b)
    (∀ n : ℕ, Finite (H (freeAb X) (locConstCoeff ⟨ZMod p⟩) n)) ∧
    -- (c)
    ∀ [Algebra R OC] (he : ∀ r : R, algebraMap Ω ℂ_[p] (algebraMap R Ω r) = algebraMap R OC r),
      CoeffCompBijective primitiveMap
        (freeAbMap (Y := X)
          (toGenericPoints Ω he Y ≫
            whiskerLeft (genericTestOver Ω) (whiskerLeft _ (algToBaseChange Ω Y))))
        (tensorCoeff M) := by
  -- The comparison `c` induced by `primitiveMap` is bijective iff a basis of `M` over `ZMod p`
  -- gives a bijective Leray–Hirsch map. This holds at the point `Ω`, so at `Y` by
  -- `ComparedTheory.mem_of_isClosedClass_of_isCharting`.
  have h_inverts : InvertsPrime Ω p :=
    InvertsPrime.mk (NeZero.nat_of_neZero (algebraMap Ω ℂ_[p])).out.isUnit
  let module_ZMod : Module (ZMod p) M := Module.restrictScalars (ZMod p) OFlat M
  -- `M ⊗[ZMod p] L ≅ (OFlat ⊗[ZMod p] L) ⊗[OFlat] M` for `L` the locally constant functions.
  let γ₀ : asModules (TestOver.toTest Ω ⋙ testIncl ⋙ locConstAlg) ⋙ tensorWith OFlat M ≅
      (TestOver.toTest Ω ⋙ oFlatLocConst) ⋙ tensorCoeff M :=
    NatIso.ofComponents
      (fun _ ↦ ((cancelBaseChange ..).symm ≪≫ₗ TensorProduct.comm ..).toModuleIso)
      fun _ ↦ ModuleCat.hom_ext (tmul_ext fun _ _ ↦ rfl)
  let γ := isoWhiskerRight γ₀ (moduleCoeff (𝟭 _))
  let b := Module.Free.chooseBasis (ZMod p) M
  let c : Comparison (TestOver.toTest Ω ⋙ oFlatLocConst ⋙ moduleCoeff (tensorCoeff M))
      (tilt ⋙ moduleCoeff (tensorCoeff M)) :=
    ⟨genericTestOver Ω, whiskerRight primitiveMap (moduleCoeff _)⟩
  -- The tilted theory, with the classes `x ↦ b i ⊗ x` of degree zero. It and the locally
  -- constant theory satisfy the projective line formula.
  let θ (i : Module.Free.ChooseBasisIndex (ZMod p) M) :=
    mk₀ (whiskerLeft _ (tensorWith.mk _ (b i) _ ≫ γ.hom) ≫ c.coeffHom)
  let D : ComparedTheory (genericTestOver Ω) :=
    ⟨tiltTheory Ω M ac, _, θ, hasLineFormula_tiltTheory _ ac, hasLineFormula_locallyConstant Ω⟩
  have lh_iff {X : TestOver Ω ⥤ Type 1} {X' : PadicTest ⥤ Type 1}
      (hX : HasFlatBaseChange (freeAb X)) (u : X' ≅ c.functor ⋙ X) :
      IsLerayHirschBasis D.comparison (freeAb X) ↔ c.IsBijective (freeAbMap u.hom) := by
    -- By the basis `b`, flat base change and `γ`, the cohomology of `M ⊗ L` is a sum of copies
    -- of that of `L`.
    let E : (_ →₀ TotalH (freeAb X) _) ≃+ TotalH (freeAb X) _ :=
      ((equivFinsuppOfBasisLeft b).symm ≪≫ₗ directSumRight ..).toAddEquiv.trans
        (congrAddEquiv fun n ↦
          .trans (.ofBijective _ (hX ..))
            (.ofBijective _ (H.push_bijective_of_isIso γ.isIso_hom n)))
    -- The `i`-th copy is mapped by pushing along `x ↦ b i ⊗ x` and `γ`.
    have hE (i : Module.Free.ChooseBasisIndex (ZMod p) M) (n : ℕ)
        (x : H (freeAb X)
          (moduleCoeff (asModules (TestOver.toTest Ω ⋙ testIncl ⋙ locConstAlg))) n) :
        E (.single i (.of _ n x)) =
          TotalH.comp (.comp (.of _ n x) (.homClass (tensorWith.mk _ (b i) _)))
            (.homClass γ.hom) := by
      simp [E, ← lof_eq_of (ZMod p)]
      -- on the summand `n`: base change sends `b i ⊗ x` to the push of `x` along `x ↦ b i ⊗ x`,
      -- and pushing along a map is composing with its class (`of_comp_homClass`)
      simp only [lof_eq_of, of_comp_homClass, ← AddEquiv.coe_toAddMonoidHom, coe_congrAddEquiv,
        DirectSum.map_of]
      rfl
    -- Under `E` the Leray–Hirsch map is restriction along `genericTestOver Ω` followed by
    -- `c.coeffHom`.
    have key : (lerayHirsch D.comparison (freeAb X)).toAddMonoidHom =
        (mapThenComp (restrictAlong (genericTestOver Ω)) (.homClass c.coeffHom)).comp
          E.toAddMonoidHom := by
      ext i n x : 3
      refine (lerayHirsch_single ..).trans (.trans ?_ congr(mapThenComp _ _ $(hE i n x)).symm)
      -- unfold `mapThenComp`: restrict the composite along `genericTestOver Ω`, then compose
      simp only [mapThenComp, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.flip_apply]
      rw [TotalH.map_comp_assoc, TotalH.map_comp_assoc]
      simp_rw [map_homClass, ← homClass_comp]
      rfl
    -- Pull-back along the isomorphism `u` is bijective, and so is `E`.
    erw [← bijective_totalH_iff_isBijective,
      (IsCohomEquiv.of_isIso _).bijective_pullbackAlong.of_comp_iff',
      ← E.bijective.of_comp_iff]
    exact .of_eq (congrArg (fun f : _ →+ _ ↦ Bijective f) key)
  -- The point satisfies `D.IsFiniteLerayHirsch` (Leray–Hirsch and finiteness): `OFlat` and `Ω` are
  -- both initial, `ac` holds at `OFlat`, and the values of the two coefficients agree because the
  -- locally constant functions on `Spec Ω` are constant.
  have h_point : D.IsFiniteLerayHirsch (freeAb (reprBy (.ofSelf Ω))) := by
    let u : tilt ⋙ reprBy (.of OFlat OFlat) ≅ c.functor ⋙ reprBy (.ofSelf Ω) :=
      tiltReprIsoGenericRepr Ω
    have h_bij : c.IsBijective (freeAbMap u.hom) := by
      refine .transfer (ac _)
        (bijective_of_isIso ((moduleCoeff _).map (oFlatLocConstOfSelfIso Ω).hom)) fun _ _ _ ↦ ?_
      -- Both sides are induced by a map of algebras out of the initial `OFlat`.
      erw [← (moduleCoeff _).map_comp_apply, ← map_comp_apply,
        CommAlgCat.isInitialSelf.hom_ext (_ ≫ _)]
      rfl
    -- The cohomology of the point with coefficients `L` consists of the constants `ZMod p`.
    exact ⟨(lh_iff (hasFlatBaseChange_freeAb_reprBy _) u).2 h_bij,
      .of_surjective _ ((sectionEquiv ..).surjective.comp
        (bijective_const_of_isDomain (B := .of Ω)).2)⟩
  -- So on the charted `Y` the Leray–Hirsch map is bijective and the mod `p` cohomology is finite.
  obtain ⟨h_lh, h_fin⟩ :=
    D.mem_of_isClosedClass_of_isCharting D.isClosedClass_isFiniteLerayHirsch
      D.isFiniteLerayHirsch_freeAb_iff_relFreeAb
      (IsCharted.exists_isCharting (Y := Y) (k := Ω)) h_point
  -- So far `Y` lives on tests over `Ω`, where it has flat base change. Restriction from all
  -- tests to these is bijective on cohomology (`isBijective_algToBaseChange`), which carries over
  -- each claim.
  refine ⟨hasFlatBaseChange_geomPoints Ω Y, fun n ↦ ?_, fun he ↦ ?_⟩
  · -- Degree `n` embeds in the total cohomology, which is finite.
    exact (isBijective_algToBaseChange ..).finite_iff.2 (h_fin.of_injective _ (of_injective n))
  · -- `toGenericPoints` is bijective by the valuative criterion.
    exact (isBijective_algToBaseChange Ω Y _).trans
      ((lh_iff (hasFlatBaseChange_algPointsOf Ω Y)
        (isoOfAppBijective (toGenericPoints Ω he Y) (·.bijective_generic_points))).1 h_lh)
      (freeAb.hom_ext fun _ _ ↦ rfl)

end New.Variety

/-! ## Finite generation of p-adic cohomology and continuity of the Galois action -/

section FiniteCohomology

open CategoryTheory ModuleCat.Algebra

namespace New.Variety

variable {p : ℕ} [ThePrime p]
  {R : CommRingCat} [Algebra R Ω]
  {Y : Over (AlgebraicGeometry.Spec R)} [IsCharted (R := R) Y Ω] [AlgebraicGeometry.IsProper Y.hom]

/-- For `Y` proper over `R` and charted over `Ω`, the cohomology `Hⁿ(Y_Ω, ℤ_p)`, computed on test
rings, is a finitely generated `ℤ_p`-module. -/
lemma finite_padic_cohomology (n : ℕ) :
    Module.Finite ℤ_[p] (H (freeAb (testIncl ⋙ geomPoints R Ω Y)) ellAdicCoeff n) := by
  -- The primitive comparison, after a choice of embedding of `Ω` in `ℂ_p`, gives the finiteness of
  -- `Hⁿ(Y_Ω, 𝔽_p)` (its acyclicity hypothesis is supplied for the zero module); finiteness
  -- modulo `p` lifts to `ℤ_p` by `finite_H_ellAdicCoeff`.
  let alg_Ω : Algebra Ω ℂ_[p] := (IsAlgClosed.lift : Ω →ₐ[ℚ] ℂ_[p]).toAlgebra
  obtain ⟨-, h_finite_mod_p, -⟩ :=
    finite_and_primitive_comparison Ω (isAcyclicOnPerfect_almostCoeff (N := Unit) (by simp)) Y
  exact finite_H_ellAdicCoeff (h_finite_mod_p n)

/-- For `Y` proper over `R` and charted over `Ω`, the `p`-adic cohomology `ℚ_p ⊗ Hⁿ(Y_Ω, ℤ_p)` is
finite-dimensional over `ℚ_p`. -/
instance {n : ℕ} : Module.Finite ℚ_[p] (ellAdicCohom R Ω n ⟨Y⟩) :=
  (finite_padic_cohomology n).base_change ℤ_[p] ℚ_[p] _

/-- Let `Y` be proper over `R` and charted over `Ω`, and `Gal(Ω/K)` the profinite Galois group of
`Ω` over a field `K`, acting `R`-linearly. For a class `x` in `Vⁿ(Y) = ℚ_p ⊗ Hⁿ(Y_Ω, ℤ_p)` and a
`ℚ_p`-linear map `l : Vⁿ(Y) → Q̄_p ^ N`, the map `g ↦ l (g x)` is continuous. -/
lemma ellAdicCohom.continuous_galoisAction (n : ℕ) (K : Type*) [Field K] [Algebra K Ω] [Algebra R K]
    [IsScalarTower R K Ω] [G : IsProGalois Gal(Ω/K) K Ω]
    (x : (ellAdicCohom R Ω n).obj (Opposite.op Y)) {N : ℕ}
    (l : ellAdicCohom R Ω n ⟨Y⟩ →ₗ[ℚ_[p]] Fin N → PadicAlgCl p) :
    Continuous fun g : Gal(Ω/K) ↦ l (galoisAction R Ω Gal(Ω/K) Y n g x) := by
  -- Reduce to a pure tensor `a ⊗ t` and to continuity at `g₀`: given a neighbourhood `U` of `0`,
  -- find an open subgroup of `g` with `L (g t - t) ∈ U`, where `L y = l (g₀ (a ⊗ y))`. The image of
  -- `L` is compact, so `p ^ k` maps it into `U`; and `g t - t` is divisible by `p ^ k` as soon as
  -- `g` fixes the finitely many elements of `Ω` over which `t` modulo `p ^ k` is defined.
  let M := H (freeAb (testIncl ⋙ geomPoints R Ω Y)) ellAdicCoeff n
  obtain ⟨S, rfl⟩ : ∃ S : Finset (ℚ_[p] × M), x = ∑ i ∈ S, i.1 ⊗ₜ[ℤ_[p]] i.2 := x.exists_finset
  -- `l` after the action of `g` is additive, so the map is a sum of maps `g ↦ l (g (a ⊗ t))`.
  -- `erw`: the sum lives in the tensor product, which is the cohomology only up to unfolding.
  erw [funext fun _ ↦ map_sum (l ∘ₗ _) ..]
  refine continuous_finsetSum S fun ⟨a, t⟩ _ ↦ continuous_iff_continuousAt.2 fun g₀ ↦ ?_
  refine tendsto_sub_nhds_zero_iff.1 fun U hU ↦ (map_mul_left_nhds_one _).ge (Filter.mem_map.2 ?_)
  let L : M →ₗ[ℤ_[p]] Fin N → PadicAlgCl p :=
    (l ∘ₗ galoisAction R Ω Gal(Ω/K) Y n g₀).restrictScalars ℤ_[p] ∘ₗ TensorProduct.mk _ _ _ a
  -- `M` is finitely generated, so `L M` is compact, hence bounded.
  have h_bounded : Bornology.IsVonNBounded ℚ_[p] (Submodule.map L ⊤ : Set (Fin N → PadicAlgCl p)) :=
    (Submodule.isCompact_of_fg (.map L (finite_padic_cohomology n).fg_top)).isVonNBounded ℚ_[p]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Set.MapsTo ((p : ℚ_[p]) ^ k • ·) (Submodule.map L ⊤ : Set _) U :=
    ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one).eventually
      ((h_bounded hU).eventually_nhds_zero (mem_of_mem_nhds hU))).exists
  -- `q` is reduction modulo `p ^ k`: the sequence `0 → ℤ_p → ℤ_p → W_k(𝔽_p) → 0` is exact.
  obtain ⟨q, hq⟩ := exists_ellAdicCoeff_modShortExact_pow (ℓ := p) k
  -- The cohomology of `Y_Ω` with these coefficients is the colimit over the subalgebras generated
  -- by finite subsets `s` of `Ω`, so `t` modulo `p ^ k` is the pullback of a class `z` at some
  -- stage `s`. Take `g` in the intersection of the stabilisers of the elements of `s`.
  obtain ⟨s, z, hz⟩ :=
    ((isProperOver_pointsToBase Y.hom).isCohomContinuous.isFilteredColimit_adjoin _ Ω (𝟙 _) n).2
      (t.push _ q n)
  filter_upwards [s.eventually_all.mpr fun b _ ↦ (G.isOpen_stabilizer b).mem_nhds rfl] with g hg
  simp only [Set.mem_preimage, map_mul]
  -- `gt` is the integral class `g t`: the pullback of `t` along the automorphism `g` of `Y_Ω`.
  let gt : M := H.map _ (freeAb.map (mapOnTests (baseChangeTransition (pointsToBase Y.hom)
    (CommRingCat.ofHom (MulSemiringAction.toAlgAut Gal(Ω/K) R Ω g : Ω →+* Ω)) (by aesop)))) n t
  change L gt - L t ∈ U
  -- Pullback commutes with reduction, and `g` is the identity on the subalgebra generated by `s`.
  have h_red : H.push _ q n (gt - t) = 0 := by
    erw [map_sub, sub_eq_zero, ← H.map_push, ← hz, ← TestCohomology.map_comp, ← Functor.map_comp,
      ← op_comp]
    congr with b
    exact (g.toAlgHom.restrictScalars R).adjoin_le_equalizer 1 hg b.2
  obtain ⟨y, hy⟩ : ∃ y : M, ((p ^ k : ℕ) : ℤ_[p]) • y = gt - t :=
    hq.exists_smul_eq_of_push_eq_zero _ h_red
  -- apply `L` to `hy`; the scalar `p ^ k` of `ℤ_p` and that of `ℚ_p` both act as `p ^ k • ·`
  have h_eq : L gt - L t = (p : ℚ_[p]) ^ k • L y := by
    rw [← map_sub, ← hy, map_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [h_eq]
  exact hk (Submodule.mem_map_of_mem Submodule.mem_top)

end New.Variety

end FiniteCohomology
