import Lib.Cohomology.ProjectiveLine.ConstantLineFormula
import Lib.PadicComparison.Duality.GoodPairs

/-!
# Charted varieties, and smooth base change from a valuation ring to its fraction field

From local charts to whole varieties, for cohomology computed on test rings.

* `New.Variety.algToBaseChange`, `New.Variety.isBijective_algToBaseChange`: the cohomology of the
  base change `Y_A` on all test rings agrees with that of `Y` on tests over `A`
  (`New.Variety.TestOver`).
* `New.Variety.ComparedTheory.mem_of_isClosedClass_of_isCharting`: a class of functors governed by
  `New.Variety.ComparedTheory.IsFiniteLerayHirsch` that contains the point contains every functor
  charted by pieces étale over tori (`New.Variety.IsCharting`).
* `New.Variety.isTestCohomEquiv_baseChangeTransition`: let `A` be a valuation ring of an algebraic
  closure `Ω` of `ℚ`, of residue characteristic `p ≠ ℓ`, and let `Y` be charted; then the mod `ℓ`
  cohomology of `Y_A` and of `Y_Ω` agree.

`D.IsFiniteLerayHirsch N` says that the cohomology of `N` with locally constant `ZMod ℓ`
coefficients is finite and computes that of the theory `D`. The functor
`relFreeAb (offClosedFibre X)` is `ℤ[X] / ℤ[U]`, where `U` consists of the points over the tests in
which the maximal ideal of `A` generates the unit ideal.

Notions from other files:
* `New.Variety.freeAb`: The functor sending a set-valued functor Y to Z[Y], whose value at A is the
  free abelian group on Y(A).
* `New.Variety.IsClosedClass`: A closed class P of functors D → Ab: (a) P contains every zero
  functor N (written `𝟙 N = 0`); (b) for a short exact sequence 0 → X₁ → X₂ → X₃ → 0 with X₁ in P,
  the middle term X₂ is in P exactly when the quotient X₃ is.
* `New.Variety.geomPoints`: The functor of points of the base change `X ×_R Ω` of a scheme `X` over
  `R`.

## Relation to the literature

Known result: Smooth base change, with restriction to the generic fibre bijective on cohomology.
Here it is proved for schemes that are covered by finitely many pieces étale over tori and are not
assumed proper. The base is the valuation ring of a place above p of an algebraic closure of Q, the
coefficients are the constant F_ℓ with ℓ invertible, and the result is deduced from proper base
change and duality on products of projective lines. Source: Artin, SGA 4 Exp. XV 2.1, XVI 1.2
(1973); Stacks Project Tag 0EYQ; for the route through the class of the diagonal, Zavyalov, Poincaré
duality in abstract 6-functor formalisms (arXiv 2301.03821) and Li-Reinecke-Zavyalov (arXiv
2410.08200).
-/

namespace New.Variety

open CategoryTheory AlgebraicGeometry ObjectProperty Function Ideal nonZeroDivisors Algebra
  PrimeSpectrum CommRingCat Set Localization TensorProduct IsSmoothAt Comparison

-- Several proofs below (the universal point of `isBijective_algToBaseChange`, the units in
-- `isBijective_restrict_restrictScalars_iff`) fail without this option.
set_option backward.isDefEq.respectTransparency false

section BaseChange

variable {R : CommRingCat} (A : Type) [CommRing A] [Algebra R A] (Y : Over (Spec R))

/-- For Y over R, the map sending a point of Y over R in an A-algebra c to the point of the base
change Y_A given by it and the structure map A → c. -/
noncomputable def algToBaseChange :
    algPointsOf A R Y ⟶ forget₂ (CommAlg A) CommRingCat ⋙ geomPoints R A Y where
  -- the point `y` together with the structure map `A → c`; the two are compatible over `R`
  app c :=
    ↾fun y ↦ ⟨(⟨y.1.1⟩, ⟨ofHom (algebraMap A c)⟩), congr(⟨$(Spec.homEquiv.eq_symm_apply.1 y.1.w)⟩)⟩
  naturality _ _ f := by
    ext
    exact baseChangeOf.ext rfl fun a ↦ (f.hom.commutes a).symm

/-- Let `Y` be over `Spec R` and `A` an `R`-algebra. For any coefficient `F` on test rings, the map
induced by `algToBaseChange`, from the cohomology of the base change `Y_A` to the cohomology of the
points of `Y` on tests over `A` (`New.Variety.TestOver`: test rings with an `A`-algebra structure),
is bijective in every degree. -/
lemma isBijective_algToBaseChange (F : AbFunctor TestRing) :
    (Comparison.restrict (TestOver.toTest A) F).IsBijective
      (freeAbMap (Y := testIncl ⋙ (geomPoints R A).obj Y)
        ((ι _).whiskerLeft (algToBaseChange A Y))) := by
  -- A point `y` of the base change over a test ring `c` includes a ring map `A → c`. The ring `c`
  -- with this algebra structure, with the point of `Y` given by `y`, is universal over `y`.
  refine Comparison.HasUniversalPoints.isBijective fun c y ↦ ?_
  -- The second component of `y`, a ring map `A → c`, makes `c` a test `B` over `A`.
  let algebra_c : Algebra A c.obj := y.val.2.down.hom'.toAlgebra
  let B : TestOver A := ⟨.of A c.obj, c.property⟩
  let x : (ι _ ⋙ algPointsOf A R Y).obj B :=
    ⟨Over.homMk _ (Spec.homEquiv.eq_symm_apply.2 congr($(y.property).down))⟩
  refine ⟨B, x, 𝟙 c, ?_, fun d z f hzf ↦ ?_, ?_⟩
  · -- The point `x` lies over `y`.
    aesop
  · -- The ring map of `f` is a map of `A`-algebras, by the second component of `hzf`.
    have h_commutes (a : A) : f.hom.hom (algebraMap A c.obj a) = algebraMap A d.obj a :=
      congr($(hzf).val.2.down.hom' a).symm
    let g : B ⟶ d := ⟨CommAlg.homOfRingHom _ h_commutes⟩
    -- It carries `x` to `z`, by the first component of `hzf`; it is unique, its ring map being
    -- `f`.
    refine ⟨g, ⟨congrArg _ (Over.OverMorphism.ext congr($(hzf).val.1.down).symm), rfl⟩, ?_⟩
    bound
  · -- On coefficients the comparison is the identity of `F c`.
    change Bijective (F.map (𝟙 c))
    rw [F.map_id]
    exact bijective_id

end BaseChange

variable {C : Type _} [Category C] {ℓ : ℕ} {R : CommRingCat} {A : Type} [CommRing A]
  [Algebra R A] [InvertsPrime A ℓ] {g : C ⥤ TestOver A} (D : ComparedTheory g)

/-- Let `A` be a valuation ring (`PreValuationRing`) and a `k`-algebra in which `ℓ` is a unit, `D` a
compared theory along `g`, and `P` a closed class of functors on tests over `A` that contains
`ℤ[Hom(A, -)]` and holds at `ℤ[Y]`, for each functor `Y` on tests over `A`, exactly when
`D.IsFiniteLerayHirsch` holds for `ℤ[Y] / ℤ[offClosedFibre Y]`. If the functor `X` on `k`-algebras
is charted by some `V` (`New.Variety.IsCharting`: `V` is Zariski locally all of `X`, and `ℤ[V]` lies
in every closed class containing `ℤ[Spec R]` for each chart `R` of `X` étale over a torus), then `P`
holds at `ℤ[X]`, restricted to tests over `A`. -/
lemma ComparedTheory.mem_of_isClosedClass_of_isCharting [PreValuationRing A]
    {P : TestOver A ⥤ Ab → Prop} (hP : IsClosedClass P)
    (h_iff : ∀ {X : TestOver A ⥤ Type 1},
      P (freeAb X) ↔ D.IsFiniteLerayHirsch (relFreeAb (offClosedFibre X)))
    {k : Type} [CommRing k] [Algebra k A] {X : CommAlg k ⥤ Type 1}
    (hV : ∃ V : Subfunctor X, IsCharting (k := k) V)
    (h_pt : P (freeAb (reprBy (TestOver.ofSelf A)))) :
    P (freeAb ((ι _ ⋙ restrictAlg k A) ⋙ X)) := by
  -- Reduce from `X` to `V`, from `V` to affine charts, from a chart to a finite cover by standard
  -- étale pieces; for these `ComparedTheory.isFiniteLerayHirsch_standard_etale` applies. `P` is
  -- local: by excision (`ComparedTheory.isFiniteLerayHirsch_iff_of_locally_bijective`) it passes
  -- from `U` to `Y` if `U` is locally all of `Y`.
  have of_cover {Y : TestOver A ⥤ Type 1} (U : Subfunctor Y)
      (hU : IsZariskiLocallyTop (ringOf (𝟭 _)) U)
      (h_mem : P (freeAb U.toFunctor)) : P (freeAb Y) := by
    -- A point of `U` lies in the range of `U.ι`.
    have h_cover : IsZariskiLocallyTop (ringOf (𝟭 _)) (.range U.ι ⊔ offClosedFibre Y) := by
      intro t y m hm
      refine (hU t y m hm).imp fun _ ↦ .imp_right fun h_in_U B f hf ↦ ?_
      simp [show Y.map f y ∈ U.obj B from h_in_U B f hf]
    have h_inj : IsZariskiLocallyTop (ringOf (𝟭 _)) (sameClassLocus U.ι (offClosedFibre Y)) :=
      isZariskiLocallyTop_sameClassLocus_of_injective _ _ fun _ ↦ Subtype.val_injective
    exact h_iff.2 ((D.isFiniteLerayHirsch_iff_of_locally_bijective U.ι h_cover h_inj).1
      (h_iff.1 h_mem))
  -- `V` is locally all of `X`, and `ℤ[V]` lies in every closed class that contains its charts.
  obtain ⟨V, hV_local, hV_charts⟩ := hV
  refine of_cover (V.whisker _) (hV_local.whisker _)
    (hV_charts _ (hP.comap (restrictAlong _)) fun chart _ ↦ ?_)
  -- On tests over `A` the chart is represented by its base change `B`, a smooth `A`-algebra.
  let B := CommAlgCat.of A (A ⊗[k] chart.coordRing)
  suffices hB : P (freeAb (testSpec A B)) from
    (hP.comap (restrictAlong (ι _))).freeAb_of_bijective
      (Y := restrictAlg k A ⋙ reprBy chart.coordRing) _
      (pointMap_algBaseChange_unit_bijective _) hB
  -- For each prime `x` there is `a x ∉ x` with `B[1/(a x)]` standard étale over the polynomial ring
  -- `S = MvPolynomial (Fin (d x)) A`; finitely many of the unit loci of the `a x` cover `Spec B`.
  -- `ha x : a x ∉ x`; `algebra_x`, `tower_x` make `Away (a x)` an algebra over the polynomial ring
  -- `MvPolynomial (Fin (d x)) A`, standard étale by `h_etale x`.
  choose a ha d algebra_x tower_x h_etale using fun x : PrimeSpectrum B ↦
    exists_isStandardEtale_mvPolynomial (R := A) (p := x.asIdeal)
  obtain ⟨s, hs⟩ :
      ∃ s : Finset (PrimeSpectrum B), ⋃ x ∈ s, (basicOpen (a x) : Set (PrimeSpectrum B)) = ⊤ :=
    CompactSpace.elim_nhds_subcover _ fun x ↦ isOpen_basicOpen.mem_nhds (ha x)
  -- Every `B[1/(a x * f)]` is again standard étale over `S`, so it is `(S[X]/E.f)[1/E.g]` for a
  -- standard étale pair `E`, and `S[X]` is again a polynomial ring over `A`.
  have h_piece (x : PrimeSpectrum B) (f : B) : P (freeAb (testUnitLocus (a x * f)).toFunctor) := by
    have h_etale_x : IsStandardEtale (MvPolynomial (Fin (d x)) A) (Away (a x)) := h_etale x
    obtain ⟨⟨E⟩⟩ :
        IsStandardEtale (MvPolynomial (Fin (d x)) A) (Away (algebraMap B (Away (a x)) f)) :=
      .of_isLocalizationAway (algebraMap B (Away (a x)) f)
    have h_std : P (freeAb (testUnitLocus (AdjoinRoot.mk E.f E.g)).toFunctor) :=
      h_iff.2 (D.isFiniteLerayHirsch_standard_etale
        (h_iff.1 (hP.freeAb_of_bijective _ pointMap_ofSelf_bijective h_pt)) _
        (MvPolynomial.finSuccEquiv A (d x)))
    -- Both unit loci are represented by localisations, and these are isomorphic over `A`.
    let iso := CommAlgCat.isoMk ((E.equivRing.trans E.equivAwayAdjoinRoot).restrictScalars A)
    let e : (testUnitLocus (AdjoinRoot.mk E.f E.g)).toFunctor ⟶
        (testUnitLocus (a x * f)).toFunctor :=
      (testUnitLocus.nonempty_iso_away _).some.inv ≫ (ι _).whiskerLeft (reprMap iso.hom) ≫
        (testUnitLocus.nonempty_iso_away _ _).some.hom
    exact (hP.iff_of_isIso (freeAb.map e)).1 h_std
  refine of_cover (⨆ x : s, testUnitLocus (a x)) (fun t φ m hm ↦ ?_) ?_
  · -- The prime of `B` below `m` misses `a x` for some `x ∈ s`.
    obtain ⟨x, hx, h_unit⟩ := iUnion₂_eq_univ_iff.1 hs (comap φ.down.hom'.toRingHom ⟨m, hm.isPrime⟩)
    refine ⟨_, h_unit, fun B' f hf ↦ ?_⟩
    -- After `f` the point lies in the unit locus of `a x`, one of the pieces of the union.
    aesop
  · -- Mayer–Vietoris (`IsClosedClass.freeAb_iSup`): the unit loci of the `a x * f` form a family
    -- that is closed under intersection, so `P` passes to finite unions.
    refine hP.freeAb_iSup (range fun y : PrimeSpectrum B × B ↦ testUnitLocus (a y.1 * y.2)) ?_ ?_
      fun x ↦ ⟨(x, 1), by simp⟩
    · exact Set.forall_mem_range.2 fun y ↦ h_piece y.1 y.2
    · rintro _ ⟨⟨x, f⟩, rfl⟩ _ ⟨⟨y, f'⟩, rfl⟩
      -- The unit locus of a product is the intersection of the unit loci.
      have h_inf : (testUnitLocus (a x * (f * a y * f')) : Subfunctor (testSpec A B)) =
          testUnitLocus (a x * f) ⊓ testUnitLocus (a y * f') := by
        simp [Subfunctor.ext_iff, funext_iff, Set.ext_iff, testUnitLocus, and_assoc]
      exact ⟨(x, f * a y * f'), h_inf⟩

/-- Let `A` be a valuation ring of `Ω` (a `ClosurePlace`) with the prime `p` in its maximal ideal.
Then `A` has rank one: for every nonzero `a ∈ A`, the maximal ideal lies in the radical of `(a)`. -/
private lemma maximalIdeal_le_radical_span {A : ClosurePlace} {p : ℕ} [Fact p.Prime]
    (hp : A.valuation p < 1) (a : A⁰) : IsLocalRing.maximalIdeal A ≤ radical (span {(a : A)}) := by
  -- `A` comes from `PadicAlgCl p`, whose valuation has rank one: a nonzero `a` divides a power of
  -- any nonunit.
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* PadicAlgCl p, (New.intQpBar p).comap j = A :=
    exists_comap_intQpBar_eq hp
  subst hj
  have h_int : (Valued.v.comap j).Integers ((New.intQpBar p).comap j) :=
    Valuation.integer.integers _
  -- A power of a value below one drops below any positive value. So a nonunit `b` (valuation
  -- below one) has a power `b ^ n` of valuation at most that of `a` (positive): `a ∣ b ^ n`.
  have h_pow_le {r s : NNReal} (hr : 0 < r) (hs : s < 1) : ∃ n : ℕ, s ^ n ≤ r :=
    (exists_pow_lt_of_lt_one hr hs).imp fun _ ↦ le_of_lt
  intro b
  simp +contextual [radical, mem_span_singleton, h_int.dvd_iff_le, isUnit_iff_dvd_one, h_pow_le]

/-- Let `A` be a valuation ring of `Ω` (a `ClosurePlace`) with the prime `p` in its maximal ideal,
and `ℓ` a unit in `A`. For a functor `X` on tests over `A`, restriction of the mod `ℓ` cohomology
from tests over `A` to tests over `Ω` (`New.Variety.TestOver.restrictScalars`) is bijective on
`ℤ[X]` exactly when `ℤ[X] / ℤ[offClosedFibre X]` has no cohomology. -/
private lemma isBijective_restrict_restrictScalars_iff {A : ClosurePlace} {p : ℕ} [Fact p.Prime]
    (hp : A.valuation p < 1) [InvertsPrime A ℓ] {X : TestOver A ⥤ Type 1} :
    (Comparison.restrict (TestOver.restrictScalars A Ω)
      (locConstAlong (𝟭 (TestOver A)))).IsBijective
        (𝟙 (TestOver.restrictScalars A Ω ⋙ freeAb X)) ↔
      ∀ n : ℕ,
        Subsingleton (H (relFreeAb (offClosedFibre X)) (locConstAlong (𝟭 (TestOver A))) n) := by
  let κ := Comparison.restrict (TestOver.restrictScalars A Ω) (locConstAlong (𝟭 (TestOver A)))
  -- In an `Ω`-algebra `p` is a unit, so every point of `X` over it lies in `offClosedFibre X`.
  let u : TestOver.restrictScalars A Ω ⋙ X ⟶ κ.functor ⋙ (offClosedFibre X).toFunctor :=
    { app c := ↾fun x ↦
        ⟨x, eq_top_of_isUnit_mem _ (mem_map_of_mem _ ((A.valuation_lt_one_iff p).2 hp))
          ((NeZero.ne (p : Ω)).isUnit.map (algebraMap Ω c.1))⟩ }
  -- Conversely, if a test `c` carries a point of `offClosedFibre X`, nonzero elements of `A` are
  -- units in `c` (rank one), so `A → c` extends to `Ω` in exactly one way;
  -- `hasUniversalPoints_structurePt` gives the test `B` over `Ω` that is universal under `c`.
  have h_univ : κ.HasUniversalPoints u := fun c y ↦ by
    have h_unit (a : A⁰) : IsUnit (algebraMap A c.1 a) := by
      -- (`using!`: the ring of `c` appears once as `c` and once as `(TestOver.toTest A).obj c`)
      simpa [map_span] using! eq_top_mono
        ((map_mono (maximalIdeal_le_radical_span hp a)).trans (map_radical_le _)) y.2
    obtain ⟨B, x, s, -, h_uniq, h_bij⟩ :=
      hasUniversalPoints_structurePt A Ω c
        ⟨⟨CommAlg.homOfRingHom _ (IsLocalization.lift_eq h_unit)⟩⟩
    refine ⟨B, _, s, rfl, fun d z f h_zf ↦ ?_, h_bij⟩
    -- Two `A`-algebra maps out of the fraction field `Ω` agree, so the lift followed by `f` is the
    -- structure map of `d`; `g` is the factorisation that this gives.
    obtain ⟨g, ⟨-, hg_comp⟩, hg_uniq⟩ :=
      h_uniq d ⟨⟩ f congr(⟨⟨CommAlgCat.ofHom $(IsLocalization.algHom_ext A⁰ (by ext))⟩⟩)
    -- `h_zf` says that `z` is the image of `y` under `f`.
    obtain rfl : z = X.map f y.val := congrArg Subtype.val h_zf
    refine ⟨g, ⟨?_, hg_comp⟩, fun g' ⟨_, hg'_comp⟩ ↦ hg_uniq g' ⟨rfl, hg'_comp⟩⟩
    -- `X.map g (X.map s y) = X.map (s ≫ g) y = X.map f y = z`. What is left holds by definition:
    -- `(TestOver.restrictScalars A Ω ⋙ X).map g` is `X.map` of
    -- `(Comparison.restrict _ _).functor.map g`.
    rw [← hg_comp, X.map_comp_apply]
    rfl
  -- So `κ` is bijective on `X` iff `offClosedFibre X ⊆ X` is an equivalence iff the quotient is
  -- acyclic.
  calc κ.IsBijective (𝟙 (κ.functor ⋙ freeAb X))
    _ ↔ IsCohomEquiv (locConstAlong (𝟭 _)) (freeAb.map (offClosedFibre X).ι) := by
      refine (h_univ.isBijective.trans_iff (c := .id _) ?_).trans isCohomEquiv_iff_isBijective.symm
      -- `u` followed by the inclusion of `offClosedFibre X` is the identity
      exact freeAb.hom_ext fun _ _ ↦ rfl
    _ ↔ ∀ n, Subsingleton (H (relFreeAb (offClosedFibre X)) (locConstAlong (𝟭 _)) n) :=
      relFreeAb.isCohomEquiv_iff_subsingleton_rel _

/-- Let `ℓ` be prime and `A` a valuation ring of the algebraic closure `Ω` of `ℚ` (a `ClosurePlace`)
and an `R`-algebra, with a prime `p` in its maximal ideal and `ℓ` a unit. Suppose `Y` is charted
over `R` (`IsCharted`: its functor of points on `R`-algebras has a subfunctor `V` with
`IsCharting V`). Then pull-back `Hⁿ(Y_A, ℤ/ℓ) → Hⁿ(Y_Ω, ℤ/ℓ)` along `Y_Ω → Y_A` is bijective for all
`n`, where cohomology is computed on test rings with locally constant coefficients. -/
lemma isTestCohomEquiv_baseChangeTransition [ThePrime ℓ]
    {A : ClosurePlace} {p : ℕ} [Fact p.Prime] (hp : A.valuation p < 1)
    (hℓ : IsUnit (ℓ : A)) [Algebra R A] (Y : Over (Spec R)) [IsCharted Y R] :
    IsTestCohomEquiv ⟨ZMod ℓ⟩ (Y := geomPoints R A Y)
      (baseChangeTransition (pointsToBase Y.hom) (ofHom A.subtype) rfl) := by
  -- Compare the cohomology of tests over `A` with that of tests over `Ω` (the comparison `κ`). The
  -- functors on which `κ` is bijective form a class to which
  -- `ComparedTheory.mem_of_isClosedClass_of_isCharting` applies; it contains the point, hence `Y`.
  -- Then `isBijective_algToBaseChange` translates back to the base changes of `Y`.
  -- `h_inverts`, `algebra_Ω` and `h_faithful` serve as instances (for the theory of locally
  -- constant functions and for the line formula).
  have h_inverts : InvertsPrime A ℓ := .mk hℓ
  -- The line formula holds because `A ⊆ Ω` embeds in `ℂ_[ℓ]`.
  have algebra_Ω : Algebra Ω ℂ_[ℓ] :=
    ((algebraMap (PadicAlgCl ℓ) ℂ_[ℓ]).comp Classical.ofNonempty).toAlgebra
  have h_faithful : FaithfulSMul A ℂ_[ℓ] := A.faithfulSMul
  have h_line : (Theory.locallyConstant (A := A)).HasLineFormula := hasLineFormula_locallyConstant A
  -- With no comparison maps, `D.IsFiniteLerayHirsch N` says that `N` has no cohomology: the map
  -- from the empty direct sum to the cohomology is bijective.
  let D : ComparedTheory (𝟭 (TestOver A)) := ⟨Theory.locallyConstant, Empty, nofun, h_line, h_line⟩
  have h_acyclic (N : AbFunctor (TestOver A)) :
      (∀ n, Subsingleton (H N (locConstAlong (𝟭 _)) n)) ↔ D.IsFiniteLerayHirsch N := by
    constructor
    · -- The total cohomology is then trivial, so the empty direct sum maps bijectively onto it.
      intro h_sub
      exact ⟨Unique.bijective (B := TotalH N (locConstAlong _)), .of_subsingleton⟩
    · -- The empty direct sum maps onto the total cohomology, so it and each degree are trivial.
      rintro ⟨h_bij, -⟩ n
      have h_total : Subsingleton (TotalH N (locConstAlong (𝟭 _))) := h_bij.surjective.subsingleton
      exact (DirectSum.of_injective n).subsingleton
  let κ := Comparison.restrict (TestOver.restrictScalars A Ω) (locConstAlong (𝟭 _))
  have h_iff {X : TestOver A ⥤ Type 1} :
      κ.IsBijective (𝟙 (κ.functor ⋙ freeAb X)) ↔ D.IsFiniteLerayHirsch
        (relFreeAb (offClosedFibre X)) :=
    (isBijective_restrict_restrictScalars_iff hp).trans (h_acyclic _)
  -- The point: both `A` and `Ω` are domains, so both sides are the constants `ZMod ℓ`.
  have h_pt : κ.IsBijective (freeAbMap (𝟙 (κ.functor ⋙ reprBy (TestOver.ofSelf A)))) := by
    refine κ.isBijective_of_repr ⟨⟨structureMap⟩⟩
      (fun c ↦ ((pointMap_ofSelf_bijective _).of_comp_iff' _).1 (pointMap_ofSelf_bijective c)) ?_
    exact ((bijective_const_of_isDomain (B := .of A)).of_comp_iff _).1
      (bijective_const_of_isDomain (B := .of Ω))
  have h_cl : IsClosedClass fun N ↦ κ.IsBijective (𝟙 (κ.functor ⋙ N)) :=
    (κ.devissage (𝟭 _) (𝟙 _)).isClosedClass
  have h_Y : κ.IsBijective (𝟙 (κ.functor ⋙ freeAb
    ((ι _ ⋙ restrictAlg R A) ⋙ algPointsOf R R Y))) := by
    refine D.mem_of_isClosedClass_of_isCharting h_cl h_iff IsCharted.exists_isCharting ?_
    -- `freeAb` maps the identity to the identity.
    rwa [freeAbMap, freeAb.map_id] at h_pt
  -- Both `H(Y_A) → H(Y on tests over A) → H(Y on tests over Ω)` and `H(Y_Ω) → H(Y on tests over Ω)`
  -- are bijective, hence so is `H(Y_A) → H(Y_Ω)`.
  have h_A := isBijective_algToBaseChange A Y (locConstCoeff ⟨ZMod ℓ⟩)
  let algebra_R_Ω : Algebra R Ω := .compHom Ω (algebraMap R A)
  have h_Ω := isBijective_algToBaseChange Ω Y (locConstCoeff ⟨ZMod ℓ⟩)
  -- (`(… :)` elaborates the composite `H(Y_A) → H(Y on tests over Ω)` on its own.)
  refine IsBijective.eqv ((h_Ω.trans_iff ?_).1 (h_A.trans h_Y rfl :))
  exact freeAb.hom_ext fun _ _ ↦ rfl

end New.Variety
