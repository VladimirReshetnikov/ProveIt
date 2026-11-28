import Lib.Cohomology.ProjectiveLine.TiltedLineFormula
import Lib.PadicComparison.Duality.LineIntegration

/-!
# The projective line formula for locally constant ℤ/ℓ coefficients

The projective line formula H(ℙ¹ × S) = H(S) ⊕ η H(S) (`New.Variety.TorsionCoeff.HasLineFormula`) is
proved for the theory `New.Variety.Theory.locallyConstant` of locally constant ℤ/ℓ-valued functions
on tests over an absolutely integrally closed valuation ring A, with ℓ invertible, that embeds into
ℂ_ℓ. Here H is total Ext of functors to abelian groups, η is the degree two class
`New.Variety.TorsionCoeff.cupClass`, and `New.Variety.lerayHirsch θ S` is the Leray–Hirsch map w ↦ Σ
θ_i · w_i of a family θ of classes; θ is a Leray–Hirsch basis at S
(`New.Variety.IsLerayHirschBasis`) when this map is bijective.

* `New.Variety.isLerayHirschBasis_lineBasis_of_basis`: the formula over a flat S follows from any
  family θ that contains η and is a Leray–Hirsch basis over S and over S ⊗ ℤ[ℙ¹].
* `New.Variety.hasLineFormula_of_lerayHirsch_ne_zero`: over a valuation ring A the formula holds as
  soon as η acts non-trivially on the point for one coefficient whose tests lie over the generic
  point of A.
* `New.Variety.hasLineFormula_locallyConstant`: the formula for a valuation ring A with an injective
  ring map to ℂ_ℓ.

The formula is reduced to algebraically closed fields k over A
(`New.Variety.hasUniversalPoints_structurePt`), where a Künneth basis contains η unless η · 1 = 0.
That vanishing would spread to the generic point of A; the tilted theory of
`New.Variety.hasLineFormula_tiltTheory` shows that it does not occur for A in ℂ_ℓ.

Notions from other files:
* `New.Variety.TestOver`: The category of tests over A: the commutative A-algebras that are reduced,
  absolutely integrally closed, and in which any a, b admit an idempotent e with a ∣ eb and
  b ∣ (1 − e)a.
* `New.Variety.TorsionCoeff`: A coefficient along g: a functor to abelian groups, killed by ℓ, with
  Zariski descent; a `New.Variety.Theory` is one that also behaves well on closed loci.
* `New.Variety.projLine`: The projective line as a functor on rings; `New.Variety.onePointFunctor`
  is the constant one-point functor and `New.Variety.reprBy A` the functor Hom(A, −).

## Relation to the literature

Known result: the projective line formula for ℤ/ℓ coefficients, where the degree two class is the
Chern class of O(1) given by the Kummer sequence. Here the formula H(ℙ¹ × S) = H(S) ⊕ η H(S) is
stated in Leray–Hirsch form for locally constant ℤ/ℓ coefficients on test rings; the tilted
coefficients serve only to show that η acts non-trivially. Source: SGA 4½ [Cycle]; SGA 5
(Jouanolou); Milne, Étale Cohomology; Scholze, p-adic Hodge theory for rigid-analytic varieties.
-/

noncomputable section

namespace New.Variety

open CategoryTheory MonoidalCategory ObjectProperty CommAlgCat TotalH Period Ideal Finsupp

set_option backward.isDefEq.respectTransparency false

variable {C : Type _} [Category C] {ℓ : ℕ} {A : Type} [CommRing A] {g : C ⥤ TestOver A}

section

variable [InvertsPrime A ℓ]

/-- The projective line formula over a coefficient `S` with flat values, from a family that contains
η. Let Θ be a theory along g and θ a family of classes on the points of ℙ¹ over g, of degrees `d`,
whose member `θ i` is η (`hθ_eta`). If θ is a Leray–Hirsch basis over `S` (`h_base`) and over
`S ⊗ ℤ[ℙ¹]` (`h_line`), then so is the family (1, η) = `New.Variety.TorsionCoeff.lineBasis`, that
is, the projective line formula holds over `S`. -/
lemma isLerayHirschBasis_lineBasis_of_basis (Θ : Theory g) {I : Type*} {S : AbFunctor C}
  [HasFlatValues S]
    {d : I → ℕ} (θ : ∀ i : I,
      H (restrictAlong (elementsProj (projLineAlong g)) Θ.functor)
        Θ.toTorsionCoeff.onElements.functor (d i))
    (i : I) (hθ_eta : (θ i).toTotalH = Θ.cupClass.toTotalH)
    (h_base : IsLerayHirschBasis θ S)
    (h_line : IsLerayHirschBasis θ ((abTensor.obj S).obj (freeAb (projLineAlong g)))) :
    IsLerayHirschBasis Θ.lineBasis S := by
  classical
  -- By `isLerayHirschBasis_lineBasis_of_injective` it suffices that the product with η is injective
  -- on `S`, and that `x` is such a product as soon as `hx` holds over the points of ℙ¹.
  refine isLerayHirschBasis_lineBasis_of_injective Θ (fun v w hvw ↦ ?_) fun x hx ↦ ?_
  · -- As `θ i` is η, the product `v · η` is the Leray–Hirsch image of the family with `v` at `i`.
    have h_single : lerayHirsch θ S (single i v) = lerayHirsch θ S (single i w) := by
      rw [lerayHirsch_single, lerayHirsch_single, hθ_eta, ← Θ.sliceEquiv_mulClass,
        ← Θ.sliceEquiv_mulClass, hvw]
    exact single_injective i (h_base.injective h_single)
  -- Expand `sliceEquiv x` in the basis θ; the coefficient at `i` is the preimage of `x`.
  obtain ⟨w, hw⟩ := h_base.surjective (sliceEquiv x)
  -- On ℙ¹ × ℙ¹ the product with η in the second factor commutes with each `θ j`, and `hx` turns
  -- the result into the image of the family with `x` at `i`.
  have h_prod :
      lerayHirsch θ _ (w.mapRange (Θ.mulClass (etaClass g).toTotalH) (map_zero _)) =
        lerayHirsch θ _ (single i x) := by
    refine (lerayHirsch_naturality θ _ (fun _ _ ↦ Θ.mulClass_naturality ..) w).trans ?_
    rwa [lerayHirsch_single, map_restrictAlong_etaClass, hw, hθ_eta]
  -- By `h_line` the two families agree; their coefficients at `i` give the preimage `w i` of `x`.
  have h_coeff : w.mapRange (Θ.mulClass (etaClass g).toTotalH) (map_zero _) = single i x :=
    h_line.injective h_prod
  have h_coeff_i : Θ.mulClass (etaClass g).toTotalH (w i) = x := by
    simpa using DFunLike.congr_fun h_coeff i
  exact ⟨w i, h_coeff_i⟩

/-- For a test c over A, the class η · 1 with locally constant ℤ/ℓ coefficients L: η of
`New.Variety.Theory.locallyConstant` on the points of ℙ¹, pulled back along
`New.Variety.oneLocConst` (ℤ → L, 1 ↦ the constant 1) and then to the functor
(B, x ∈ ℙ¹(B)) ↦ Hom(c, B). It lies in H²(ℤ[Hom(c, −)], L) on the points of ℙ¹ over tests over A. -/
def etaOneClass (c : TestOver A) :=
  H.map _ (freeAb.map (toUnit (testOfPoint A projLine ⋙ reprBy c))) 2
    (H.map _ oneLocConst 2 Theory.locallyConstant.cupClass)

/-- Pull-back along a map of tests c → d over A sends `New.Variety.etaOneClass` c to
`New.Variety.etaOneClass` d. -/
lemma map_etaOneClass {c d : TestOver A} (φ : c ⟶ d) :
    H.map (locConstAlong (testOfPoint A projLine))
        (freeAb.map ((testOfPoint A projLine).whiskerLeft (reprMap φ))) 2 (etaOneClass c) =
      etaOneClass d :=
  H.map_map ..

/-- Pull a class x back along f, restrict it along φ, pull it back along α and compose with T. The
result is the restriction of x composed with T, pulled back along α followed by the restriction
of f. -/
lemma comp_restrict_pull_map {D D' : Type 1} [Category D] [Category D'] (φ : D' ⥤ D)
    {N N₁ F : AbFunctor D} {N' K : AbFunctor D'} (α : N' ⟶ (restrictAlong φ).obj N) (f : N ⟶ N₁)
    {n : ℕ} (x : H N₁ F n) (T : TotalH ((restrictAlong φ).obj F) K) :
    comp ((Comparison.restrict φ F).pull α n (H.map F f n x)).toTotalH T =
      pullbackAlong (α ≫ (restrictAlong φ).map f)
        (mapThenComp (restrictAlong φ) T x.toTotalH) := by
  -- Restriction along `φ` commutes with pull-back, and the coefficient map of the comparison is
  -- the identity.
  have h_map : (H.map F f n x).mapExactFunctor (restrictAlong φ) =
      H.map ((restrictAlong φ).obj F) ((restrictAlong φ).map f) n
        (x.mapExactFunctor (restrictAlong φ)) := by
    simp only [H.map, Abelian.Ext.precomp, Abelian.Ext.bilinearComp_apply_apply,
      Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  have h_pull : (Comparison.restrict φ F).pull α n (H.map F f n x) =
      H.map ((restrictAlong φ).obj F) (α ≫ (restrictAlong φ).map f) n
        (x.mapExactFunctor (restrictAlong φ)) := by
    rw [H.map_comp, ← h_map]
    exact congrArg (H.map ((restrictAlong φ).obj F) α n) (Abelian.Ext.comp_mk₀_id _)
  have h_total :
      (H.map ((restrictAlong φ).obj F) (α ≫ (restrictAlong φ).map f) n
        (x.mapExactFunctor (restrictAlong φ))).toTotalH =
      pullbackAlong (α ≫ (restrictAlong φ).map f) (TotalH.map (restrictAlong φ) x.toTotalH) := by
    rw [map_of, pullbackAlong_of]
  calc comp ((Comparison.restrict φ F).pull α n (H.map F f n x)).toTotalH T
      = comp (pullbackAlong (α ≫ (restrictAlong φ).map f)
          (TotalH.map (restrictAlong φ) x.toTotalH)) T := by
        rw [← h_total]
        exact congrArg (fun y : H N' ((restrictAlong φ).obj F) n ↦ comp y.toTotalH T) h_pull
    _ = pullbackAlong (α ≫ (restrictAlong φ).map f)
          (mapThenComp (restrictAlong φ) T x.toTotalH) := comp_assoc ..

-- Keeps definitional checks from unfolding the Ext groups and their group structure.
seal CategoryTheory.Abelian.Ext addCommGroupH in
/-- Let c be a test over A and u a map from the point to the functor d ↦ Hom(c, g(d)), that is, maps
c → g(d) natural in the object d of C. Let T be a class in total Ext from the locally constant
ℤ/ℓ coefficient to M, both restricted to the points of ℙ¹ over g. Pull `New.Variety.etaOneClass` c
back along u to the points of ℙ¹ over g and compose it with T. The result is T composed with
η = `New.Variety.TorsionCoeff.cupClass` of M, pulled back along `New.Variety.oneLocConst`. -/
lemma comp_pull_etaOneClass_eq_pullbackAlong_oneLocConst {M : TorsionCoeff g}
    {T : TotalH
      (Functor.Elements.precomp g (ringOf (𝟭 (TestOver A)) ⋙ projLine) ⋙
        (Theory.locallyConstant.toTorsionCoeff.onElements
          (X := projLineAlong (𝟭 (TestOver A)))).functor)
      M.onElements.functor}
    {c : TestOver A} (u : onePointFunctor C ⟶ g ⋙ reprBy c) :
    comp
        ((Comparison.restrict (Functor.Elements.precomp g (ringOf (𝟭 (TestOver A)) ⋙ projLine))
            _).pull
          (freeAbMap ((elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine)).whiskerLeft u)) 2
          (etaOneClass c)).toTotalH
        T =
      pullbackAlong (oneLocConst (g := elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine) ⋙ g))
        (comp T M.cupClass.toTotalH) := by
  -- `etaOneClass c` is η pulled back along a map `f`. By `comp_restrict_pull_map` the left side is
  -- `T` after the restriction of η, pulled back along a map from the point to `ℤ/ℓ`.
  let X : TestOver A ⥤ Type 1 := ringOf (𝟭 (TestOver A)) ⋙ projLine
  let f : freeAb (testOfPoint A projLine ⋙ reprBy c) ⟶ locConstAlong (testOfPoint A projLine) :=
    freeAb.map (toUnit (testOfPoint A projLine ⋙ reprBy c)) ≫ oneLocConst
  have h_eta : etaOneClass c = H.map _ f 2 Theory.locallyConstant.cupClass := (H.map_comp ..).symm
  -- The map from the point sends the generator to the constant 1, so it is `oneLocConst`.
  have h_one :
      freeAbMap ((elementsProj (g ⋙ X)).whiskerLeft u) ≫
          (restrictAlong (Functor.Elements.precomp g X)).map f =
        oneLocConst (g := elementsProj (g ⋙ X) ⋙ g) :=
    freeAb.hom_ext fun _ _ ↦ rfl
  -- `T` commutes with the product with η.
  have h_nat :
      mapThenComp (restrictAlong (Functor.Elements.precomp g X)) T
          (Theory.locallyConstant (A := A)).cupClass.toTotalH =
        comp T M.cupClass.toTotalH :=
    Theory.locallyConstant.onElements.etaAt_naturality (Functor.Elements.precomp g X)
      M.onElements T _
  rw [h_eta]
  refine (comp_restrict_pull_map (Functor.Elements.precomp g X) _ f _ T).trans ?_
  exact (congrArg _ h_nat).trans
    (congrArg (fun f ↦ pullbackAlong f (comp T M.cupClass.toTotalH)) h_one)

/-- Let c be a test over A and u a map from the point to the functor d ↦ Hom(c, g(d)) that has
universal points for the restriction along g of the locally constant ℤ/ℓ coefficient. Suppose that
this restriction is a coefficient along g (`h_torsion`, `h_descent`) and that its class η, pulled
back along `New.Variety.oneLocConst`, is zero. Then `New.Variety.etaOneClass` c is zero. -/
lemma etaOneClass_eq_zero_of_hasUniversalPoints {c : TestOver A}
    {u : onePointFunctor C ⟶ g ⋙ reprBy c}
    (hu : (Comparison.restrict g Theory.locallyConstant.functor).HasUniversalPoints u)
    (h_torsion : ∀ (d : C) (x : (locConstAlong g).obj d), ℓ • x = 0)
    (h_descent : HasZariskiDescent (ringOf g) (locConstAlong g))
    (h_zero :
      pullbackAlong (oneLocConst (g := elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine) ⋙ g))
        (TorsionCoeff.mk (locConstAlong g) h_torsion h_descent).cupClass.toTotalH = 0) :
    etaOneClass c = 0 := by
  -- By `comp_pull_etaOneClass_eq_pullbackAlong_oneLocConst` for the identity class, the pull-back
  -- `P` along `u` sends `etaOneClass c` to η · 1, which is zero; and `P` is injective.
  let P := (Comparison.restrict (Functor.Elements.precomp g (ringOf (𝟭 (TestOver A)) ⋙ projLine))
      Theory.locallyConstant.onElements.functor).pull
    (freeAbMap (Y := testOfPoint A projLine ⋙ reprBy c)
      ((elementsProj (g ⋙ ringOf (𝟭 (TestOver A)) ⋙ projLine)).whiskerLeft u)) 2
  let M : TorsionCoeff g := ⟨locConstAlong g, h_torsion, h_descent⟩
  let one : freeAb (onePointFunctor (projLineAlong g).Elements) ⟶
      locConstAlong (elementsProj (projLineAlong g) ⋙ g) := oneLocConst
  have h_pull : (P (etaOneClass c)).toTotalH = 0 :=
    calc (P (etaOneClass c)).toTotalH
        = comp (P (etaOneClass c)).toTotalH (homClass (𝟙 _)) := comp_id.symm
      _ = pullbackAlong one (comp (homClass (𝟙 M.onElements.functor)) M.cupClass.toTotalH) :=
          comp_pull_etaOneClass_eq_pullbackAlong_oneLocConst (M := M) u
      _ = pullbackAlong one M.cupClass.toTotalH := congrArg _ pullbackAlong_id
      _ = 0 := h_zero
  have h_pull_two : P (etaOneClass c) = 0 :=
    DirectSum.of_injective 2 (h_pull.trans (map_zero _).symm)
  have h_injective : Function.Injective P := (hu.on_elements.isBijective 2).injective
  exact (map_eq_zero_iff P h_injective).mp h_pull_two

variable (A) (k : Type _) [Field k] [IsAlgClosed k] [Algebra A k]

/-! ### Tests over an algebraically closed field -/

/-- For an A-algebra k that is a field, the restriction of scalars functor from test k-algebras to
test A-algebras. -/
def TestOver.restrictScalars : TestOver k ⥤ TestOver A := lift _ (ι _ ⋙ restrictAlg ..) (·.property)

/-- On test k-algebras B, the map from the point to the functor B ↦ Hom_A(k, B) that picks the
structure map k → B. -/
def TestOver.structurePt :
    onePointFunctor (TestOver k) ⟶ restrictScalars A k ⋙ reprBy
      ⟨of A k, isTest_of_preValuationRing⟩ :=
  sectionMap
    { val B := ⟨⟨CommAlg.homOfRingHom _ (by tauto)⟩⟩
      property f := congr(⟨⟨$(by ext; apply f.1.hom.2)⟩⟩) }

/-- For an algebraically closed field k over A, restriction of scalars from tests over k to tests
over A compares the point with the functor Hom_A(k, −) in the sense of
`New.Variety.Comparison.HasUniversalPoints`, for locally constant ℤ/ℓ-valued functions: an A-map y :
k → B makes B a test over k, universal for y, and the identity of B is bijective on coefficients. -/
lemma hasUniversalPoints_structurePt :
    (Comparison.restrict (TestOver.restrictScalars A k)
      Theory.locallyConstant.functor).HasUniversalPoints
      (TestOver.structurePt A k) := by
  -- A point `y` over `B` is an `A`-algebra map k → B; it makes `B` itself a `k`-algebra, and this
  -- algebra `B'`, with the identity of `B`, is the universal member.
  intro B y
  let φ : k →ₐ[A] B.obj := y.down.hom.hom
  let algebra_k_B : Algebra k B.obj := φ.toRingHom.toAlgebra
  let B' : TestOver k := ⟨of k B.obj, B.property⟩
  let s : B ⟶ (TestOver.restrictScalars A k).obj B' :=
    ⟨CommAlg.homOfRingHom (RingHom.id B.obj) fun x ↦ (φ.commutes x).symm⟩
  refine ⟨B', ⟨⟩, s, rfl, fun D z f e ↦ ?_, ?_⟩
  · -- By `e`, the ring map under `f` is `k`-linear; it is the only possible factorisation.
    have h_linear (x : k) : f.hom.hom (algebraMap k B.obj x) = algebraMap k D.obj x :=
      (congrArg (fun a ↦ a.down.hom.hom x) e).symm
    refine ⟨⟨CommAlg.homOfRingHom f.hom.hom.toRingHom h_linear⟩, ⟨rfl, rfl⟩, ?_⟩
    -- As `s` is the identity of `B`, another factorisation has the map of `f` underneath.
    rintro f'' ⟨-, h_comp⟩
    ext x
    exact congrArg (fun a ↦ a.hom.hom x) h_comp
  · -- On coefficients `s` acts as the identity of `B`.
    exact ConcreteCategory.bijective_of_isIso ((locConstCoeff _).map (𝟙 _))

end

/-! ### A valuation ring as a test over itself -/

section

variable (A) [IsAbsIntegrallyClosedLocal A] [PreValuationRing A]

/-- An absolutely integrally closed valuation ring as a test over itself. -/
abbrev TestOver.ofSelf : TestOver A where
  obj := of A A
  property := isTest_of_preValuationRing

variable {A} in
/-- A, seen as a test over itself, is initial among tests over A: for every test D over A, the point
map from Hom(A, D) to the one-point set is bijective. -/
lemma pointMap_ofSelf_bijective :
    AllBijective fun D : TestOver A ↦
      pointMap (Y := onePointFunctor (TestOver A)) (A := TestOver.ofSelf A) ⟨⟩ D := by
  -- As `A` is the initial `A`-algebra, its one map to `D` is the structure map of `D`.
  intro D
  refine ⟨fun f f' _ ↦ ULift.down_injective (InducedCategory.hom_ext ?_),
    fun _ ↦ ⟨ULift.up ⟨structureMap⟩, rfl⟩⟩
  ext

end

/-! ### The projective line formula over a valuation ring -/
-- Without the seal, unification unfolds these two functors and runs out of heartbeats.
seal locConstCoeff projLine in
/-- If every non-zero element of A is a unit in every test g(d) (so every g(d) lies over the generic
point of A) and `New.Variety.etaOneClass` vanishes at the residue field of A at its generic point
(`residueTest (TestOver.ofSelf A) ⊥`, with A seen as a test over itself), then y · η = 0 over the
points of ℙ¹ for every class y of M on the point; here y · η is the Leray–Hirsch map of (1,
η) = `New.Variety.TorsionCoeff.lineBasis` at (y at `false`, 0). -/
lemma lerayHirsch_lineBasis_single_false_eq_zero_of_etaOneClass_eq_zero {C : Type _} [Category C]
    {ℓ : ℕ} (A : Type) [CommRing A] {g : C ⥤ TestOver A} [InvertsPrime A ℓ] [PreValuationRing A]
    (hg : ∀ d : C, ∀ a ≠ (0 : A), IsUnit (algebraMap A (g d).obj a)) (M : TorsionCoeff g)
    (h_generic : etaOneClass (ℓ := ℓ) (residueTest (TestOver.ofSelf A) ⊥).right = 0)
    (y : TotalH (freeAb.obj (onePointFunctor C)) M.functor) :
    lerayHirsch M.lineBasis (freeAb (onePointFunctor C)) (Finsupp.single false y) = 0 := by
  -- The residue field at the generic point maps to every `g d`, naturally in `d`.
  let toTest (d : C) : (residueTest (TestOver.ofSelf A) ⊥).right ⟶ g.obj d :=
    ⟨ofHom (ResidueField.liftₐ _ structureMap.hom bot_le (hg d))⟩
  have h_natural {d d' : C} (f : d ⟶ d') : toTest d ≫ g.map f = toTest d' := by
    -- Both are `A`-algebra maps out of the residue field; such maps agree on the image of `A`.
    ext1
    refine congrArg ofHom (ResidueField.algHom_ext ?_)
    ext
  let u : onePointFunctor C ⟶ g ⋙ reprBy (residueTest (TestOver.ofSelf A) ⊥).right :=
    sectionMap ⟨fun d ↦ ULift.up (toTest d), fun f ↦ congrArg ULift.up (h_natural f)⟩
  -- Every class on the point is the value at 1 of some `T`
  -- (`pullbackAlong_oneLocConst_surjective`); then y · η is `etaOneClass` at the generic point,
  -- pulled back along `u`, composed with `T`.
  obtain ⟨T, rfl⟩ := M.pullbackAlong_oneLocConst_surjective y
  rw [lerayHirsch_single, map_comp_assoc, map_homClass]
  -- `erw`: the goal has `pullbackAlong oneLocConst` only after unfolding the restriction of
  -- `oneLocConst` to the points of ℙ¹.
  erw [← comp_pull_etaOneClass_eq_pullbackAlong_oneLocConst u, h_generic]
  simp

/-- If `New.Variety.etaOneClass` vanishes at a test k over A that is a field, then it vanishes at
the residue field of A at its generic point. -/
lemma etaOneClass_residueTest_bot_eq_zero {ℓ : ℕ} {A : Type} [CommRing A] [InvertsPrime A ℓ]
    [PreValuationRing A] {k : TestOver A} (k_field : IsField k.obj)
    (h_eta_k : etaOneClass (ℓ := ℓ) k = 0) :
    etaOneClass (ℓ := ℓ) (residueTest (TestOver.ofSelf A) ⊥).right = 0 := by
  let k_field_inst : Field k.obj := k_field.toField
  -- The map from `A` to `k` factors over the residue field at the prime `Q` under the zero ideal.
  let Q : PrimeSpectrum A := .comap (algebraMap A k.obj) ⊥
  let toK : (residueTest (TestOver.ofSelf A) Q).right ⟶ k :=
    ⟨ofHom (ResidueField.liftₐ _ structureMap.hom le_rfl
      fun a ha ↦ IsUnit.mk0 (algebraMap A k.obj a) ha)⟩
  -- Vanishing passes from `k` to `Q`, as pull-back between fields is injective.
  have h_eta_under : etaOneClass (ℓ := ℓ) (residueTest (TestOver.ofSelf A) Q).right = 0 :=
    (isDetectedAtPoints_projLine.isCohomEquiv_of_isField _ k toK
      (Field.toIsField (ResidueField _)) k_field 2).injective
      ((map_etaOneClass toK).trans (h_eta_k.trans (map_zero _).symm))
  -- Vanishing then passes to the generic point, as the vanishing locus is open.
  have h_open : IsOpen {P : PrimeSpectrum A |
      etaOneClass (ℓ := ℓ) (residueTest (TestOver.ofSelf A) P).right = 0} := by
    simpa only [map_etaOneClass] using isDetectedAtPoints_projLine.isOpen_setOf_map_eq_zero
      (TestOver.ofSelf A) 2 (etaOneClass (TestOver.ofSelf A))
  have h_specializes : (⊥ : PrimeSpectrum A) ⤳ Q := (PrimeSpectrum.le_iff_specializes ..).mp bot_le
  exact h_specializes.mem_open h_open h_eta_under

-- Keeps unification from unfolding these two functors and the group structure of the Ext groups.
seal locConstCoeff projLine addCommGroupH in
/-- Let A be a valuation ring that is an absolutely integrally closed local domain (not a separate
hypothesis: it is derived from the stated instances `PreValuationRing A` and `InvertsPrime A ℓ`)
with ℓ invertible, g a functor to tests over A, and M a coefficient along g. Suppose that (a) every
non-zero element of A is a unit in every test g(d), and (b) some y in total Ext(ℤ[pt], M) has
y · η ≠ 0 over the points of ℙ¹, where η is the degree-2 class of
`New.Variety.TorsionCoeff.lineBasis`. The product y · η is written as the Leray–Hirsch map of the
family (1, η) = `lineBasis` at the family with y at the index `false` and 0 at the other index. Then
the projective line formula holds for locally constant ℤ/ℓ-valued functions on tests over A: 1 and η
form a basis of H(ℙ¹ × S) over H(S) for every S. -/
lemma hasLineFormula_of_lerayHirsch_ne_zero {C : Type _} [Category C]
    {ℓ : ℕ} (A : Type) [CommRing A] {g : C ⥤ TestOver A} [InvertsPrime A ℓ] [PreValuationRing A]
    (hg : ∀ d : C, ∀ a ≠ (0 : A), IsUnit (algebraMap A (g d).obj a)) (M : TorsionCoeff g)
    (h_ne :
      ¬∀ y : TotalH (freeAb.obj (onePointFunctor C)) M.functor,
        lerayHirsch M.lineBasis (freeAb (onePointFunctor C)) (Finsupp.single false y) = 0) :
    (Theory.locallyConstant (A := A)).HasLineFormula := by
  classical
  -- Reduce to a test `k` over `A` that is a field, and then to the theory `Θ` on tests over `k`.
  -- There a Künneth basis contains η unless η · 1 = 0 over `k`; that vanishing would spread to the
  -- generic point of `A` and kill y · η for every class y of `M`, against `h_ne`.
  suffices h_field : ∀ k : TestOver A, IsField k.obj →
      IsLerayHirschBasis (Theory.locallyConstant (A := A)).lineBasis (freeAb (reprBy k)) from
    isLerayHirschBasis_of_reprBy fun c ↦
      isLerayHirschBasis_of_forall_isField isDetectedAtPoints_projLine fun k _ ↦ h_field k
  rintro ⟨k, k_test⟩ k_field
  let k_field_inst : Field k := k_field.toField
  have k_alg_closed : IsAlgClosed k := k_test.isAlgClosed
  have k_inverts : InvertsPrime k ℓ :=
    ⟨by simpa using (InvertsPrime.isUnit_prime (A := A) (ℓ := ℓ)).map (algebraMap A k)⟩
  let Θ : Theory (TestOver.restrictScalars A k ⋙ 𝟭 (TestOver A)) := {Theory.locallyConstant with}
  suffices h_point : IsLerayHirschBasis Θ.lineBasis (freeAb (onePointFunctor (TestOver k))) from
    (TorsionCoeff.HasLineFormula.bijective_iff_of_hasUniversalPoints (M' := Θ.toTorsionCoeff) _
      (hasUniversalPoints_structurePt A k)).mpr h_point
  have h_max_bot (c : TestOver k) : (IdealFamily.ofMaximalIdeal (A := k)).ideal c = ⊥ :=
    (congrArg (Ideal.map _) IsLocalRing.maximalIdeal_eq_bot).trans Ideal.map_bot
  -- Over `k` there is a Künneth basis `b`, valid at all tests as the maximal ideal of `k` is zero;
  -- it contains η if η · 1 ≠ 0.
  obtain ⟨b, h_eta_mem, hb⟩ :
      ∃ b : Set (Σ n : ℕ, H
          (restrictAlong (testOfPoint k projLine) (locConstAlong (𝟭 (TestOver k))))
          Theory.locallyConstant.onElements.functor n),
        (pullbackAlong oneLocConst Θ.cupClass.toTotalH ≠ 0 → ⟨2, Θ.cupClass⟩ ∈ b) ∧
        ∀ c : TestOver k, ⟨⟩ ∈ IdealFamily.ofMaximalIdeal.botLocus c →
          IsLerayHirschBasis (fun i : b ↦ i.val.snd) (freeAb (reprBy c)) :=
    exists_isLerayHirschBasis_of_isCohomDense
      Theory.locallyConstant.toTorsionCoeff.onElements isDetectedAtPoints_projLine
      (.of_top_le fun _d _x _hx ↦ h_max_bot _) ⟨2, Θ.cupClass⟩
  have h_basis_repr (c : TestOver k) :
      IsLerayHirschBasis (fun i : b ↦ i.val.snd) (freeAb (reprBy c)) := hb c (h_max_bot c)
  -- It is a basis on the point, which `k` represents (as a test over itself).
  have h_basis_point :
      IsLerayHirschBasis (fun i : b ↦ i.val.snd) (freeAb (onePointFunctor (TestOver k))) :=
    isClosedClass_isLerayHirschBasis.freeAb_of_bijective _ pointMap_ofSelf_bijective
      (h_basis_repr _)
  -- It is a basis on `projLinePow Unit` by dévissage from its affine cover.
  have h_basis_pow :
      IsLerayHirschBasis (fun i : b ↦ i.val.snd)
        (freeAb (ringOf (𝟭 (TestOver k)) ⋙ projLinePow Unit)) :=
    -- `(… :)`: unifying with the expected type first runs out of heartbeats.
    isLerayHirschBasis_iff_allBijective_truncMap.mpr
      (isAffinelyCovered_projLinePow.devissage_bijective lerayHirsch.devissage fun c ↦
        isLerayHirschBasis_iff_allBijective_truncMap.mp (h_basis_repr c) :)
  -- This is moved along `projLinePow Unit` ≅ ℙ¹ and then along ℤ[ℙ¹] ≅ ℤ[pt] ⊗ ℤ[ℙ¹].
  let X : TestOver k ⥤ Type 1 := projLineAlong (TestOver.restrictScalars A k ⋙ 𝟭 (TestOver A))
  let ev : ringOf (𝟭 (TestOver k)) ⋙ projLinePow Unit ⟶ X := { app _ := ↾fun f ↦ f () }
  have h_ev : AllBijective fun c : TestOver k ↦ ev.app c := fun _ ↦ (Equiv.funUnique ..).bijective
  have h_basis_X : IsLerayHirschBasis (fun i : b ↦ i.val.snd) (freeAb X) :=
    isClosedClass_isLerayHirschBasis.freeAb_of_bijective ev h_ev h_basis_pow
  have h_basis_line :
      IsLerayHirschBasis (fun i : b ↦ i.val.snd)
        ((abTensor.obj (freeAb (onePointFunctor (TestOver k)))).obj (freeAb X)) :=
    (isClosedClass_isLerayHirschBasis.iff_of_isIso
      (freeAb.map (λ_ X).inv ≫ freeAb.prod (onePointFunctor (TestOver k)) X)).mp h_basis_X
  -- If η · 1 = 0 over `k`, then `etaOneClass` vanishes at `k`, hence at the generic point of `A`.
  -- All `g d` lie over that point, so η kills every class of `M`, against `h_ne`.
  have h_eta_ne : pullbackAlong oneLocConst Θ.cupClass.toTotalH ≠ 0 := by
    intro h_eta_zero
    have h_eta_k : etaOneClass (ℓ := ℓ) ⟨k, k_test⟩ = 0 :=
      etaOneClass_eq_zero_of_hasUniversalPoints (hasUniversalPoints_structurePt A k)
        Θ.prime_smul_eq_zero Θ.zariski_descent h_eta_zero
    exact h_ne (lerayHirsch_lineBasis_single_false_eq_zero_of_etaOneClass_eq_zero A hg M
      (etaOneClass_residueTest_bot_eq_zero k_field h_eta_k))
  -- So η is a member of `b`.
  exact isLerayHirschBasis_lineBasis_of_basis Θ (fun i : b ↦ i.val.snd)
    ⟨⟨2, Θ.cupClass⟩, h_eta_mem h_eta_ne⟩ rfl h_basis_point h_basis_line

/-- Let `A` be a valuation ring (`PreValuationRing A`) that is local and absolutely integrally
closed, with ℓ invertible in it (`InvertsPrime A ℓ`), and that has an injective ring map to ℂ_ℓ. A
test over `A` is a commutative `A`-algebra whose underlying ring is a test ring. Then the theory
`Theory.locallyConstant`, which sends a test B over `A` to the locally constant functions Spec
B → ℤ/ℓ, satisfies the projective line formula: `1` and `η` form a basis of H(ℙ¹ × S) over H(S) for
every S. -/
lemma hasLineFormula_locallyConstant {ℓ : ℕ} (A : Type) [CommRing A] [InvertsPrime A ℓ]
    [PreValuationRing A] [Algebra A ℂ_[ℓ]] [FaithfulSMul A ℂ_[ℓ]] :
    (Theory.locallyConstant (A := A)).HasLineFormula := by
  -- Apply `hasLineFormula_of_lerayHirsch_ne_zero` to the tilted theory Θ with coefficients
  -- S ↦ S^♭ ⊗ N ⊗ 𝔪 (S^♭ the tilt of the test S), where N = O^♭/π and π = `pFlat`. If η killed
  -- all classes on the point, the line formula for Θ would make the cohomology of the point
  -- trivial; but it is N ⊗ 𝔪 = 𝔪/π𝔪, where π is not zero.
  let N : Type := OFlat ⧸ span {pFlat}
  have h_killed (x : N) : pFlat • x = 0 := by simp [N, Algebra.smul_def]
  have h_acyclic : IsAcyclicOnPerfect (moduleCoeff (almostCoeff N)) :=
    isAcyclicOnPerfect_almostCoeff h_killed
  let Θ : Theory (genericTestOver A) := tiltTheory A _ h_acyclic
  -- Non-zero elements of A are units in ℂ_ℓ, hence in the rings R[1/ℓ] of the ℓ-adic tests.
  have h_unit (a : A) (ha : a ≠ 0) : IsUnit (algebraMap A ℂ_[ℓ] a) := by simpa using ha
  refine hasLineFormula_of_lerayHirsch_ne_zero A
    (fun d a ha ↦ (h_unit a ha).map d.genericStructureMap)
    Θ.toTorsionCoeff fun h_eta ↦ ?_
  -- So all classes on the point are equal: their products with η agree, and the line formula for
  -- Θ makes the product with η injective.
  have h_line : IsLerayHirschBasis Θ.lineBasis (freeAb (onePointFunctor PadicTest)) :=
    hasLineFormula_tiltTheory ..
  have h_pt (v w : TotalH (freeAb (onePointFunctor PadicTest)) Θ.functor) : v = w :=
    single_injective false (h_line.injective ((h_eta v).trans (h_eta w).symm))
  -- The point is the functor Hom(O^♭, S^♭), as O^♭ is the initial O^♭-algebra.
  let O : CommAlg OFlat := of OFlat OFlat
  have h_point : IsCohomEquiv Θ.functor (freeAb.map (toUnit (PadicTest.tilt ⋙ reprBy O))) :=
    .of_bijective fun _ ↦ ⟨fun f f' _ ↦ ULift.down_injective (isInitialSelf.hom_ext f.down f'.down),
      fun _ ↦ ⟨ULift.up structureMap, rfl⟩⟩
  -- By acyclicity the cohomology of this functor is the value O^♭ ⊗ N ⊗ 𝔪 of the coefficient at
  -- O^♭; all its elements are equal.
  have h_classes : ∀ v w : TotalH (freeAb (PadicTest.tilt ⋙ reprBy O)) Θ.functor, v = w :=
    h_point.bijective_pullbackAlong.surjective.forall₂.mpr fun v w ↦ congrArg _ (h_pt v w)
  have h_sec (v w : moduleCoeff (almostCoeff N) O) : v = w :=
    (sectionEquiv _ O).injective ((h_acyclic O).bijective_totalH.injective (h_classes _ _))
  let π : MaxIdealFlat := ⟨pFlat, not_isUnit_pFlat⟩
  have h_zero : (1 : N) ⊗ₜ[OFlat] π = 0 :=
    (TensorProduct.lid OFlat _).symm.injective (ULift.up_injective (h_sec _ _))
  -- So π = π a with a in 𝔪; as π ≠ 0 this gives a = 1, which is not in 𝔪.
  have h_mem : π ∈ span {pFlat} • (⊤ : Submodule OFlat _) :=
    (LinearMap.ker_tensorProductMk _).le h_zero
  obtain ⟨a, ha_mem, ha_eq⟩ : ∃ a ∈ IsLocalRing.maximalIdeal OFlat, pFlat * a = pFlat := by
    simpa [π, Submodule.mem_smul_top_iff, mem_span_singleton_mul] using h_mem
  obtain rfl : a = 1 := mul_left_cancel₀ pFlat_ne_zero (ha_eq.trans (mul_one pFlat).symm)
  exact (IsLocalRing.mem_maximalIdeal 1).mp ha_mem isUnit_one

end New.Variety

end
