import Lib.PadicComparison.Primitive.PeriodCoefficients

/-!
# The Hodge–Tate maps λ_h on pairs (S, M): construction, properties and restriction

The field `k` is embedded in `ℚ̄_p`, so it has characteristic zero. For a `p`-adic test `S`, put
`T = S[1/p]`, and let `B_S = W(S^♭)[1/p] / (ker θ)²` be the square-zero extension
`New.Variety.thickeningOver` of `T` by `T`.
Put `B_{S,M} = B_S ×_T (T ⊕ M)`. All groups are `Ext` groups of functors to abelian groups
(`New.Variety.H`). On pairs `(S, M)` with `M = T ^ n`, the Hodge–Tate map `λ_h` restricts a Hodge
class to the pairs. It then composes it with the `h`-th Yoneda power of the class of a contraction
cocycle, followed by the projection to degree zero. So `λ_h` lands in the cohomology of `N(B_{S,M})`
on pairs. This map is natural, turns scaling by `t` into multiplication by `t ^ h`, and satisfies a
binomial product rule.

## Main definitions and results

* `New.Variety.HodgeTatePair`: pairs `(S, M)` with `M = T ^ n`; a map has a semilinear part
  `M → T' × M'`.
* `New.Variety.HodgeTatePair.contractionPow`: the `h`-th Yoneda power of the class of the
  contraction cocycle `New.Variety.HodgeTatePair.contractionCocycle`, followed by the projection to
  degree zero. It is `k`-linear (`New.Variety.HodgeTatePair.act_comp_contractionPow`)
  and has weight `h` (`New.Variety.HodgeTatePair.scaleModule_comp_contractionPow`).
* `New.Variety.hodgeTateMap`: restrict a class of `New.Variety.HodgeH` to these pairs and compose
  with `contractionPow h`. `New.Variety.restrictToPairs` maps the degree-`n` cohomology of `N(T)` on
  `p`-adic tests to the same target `New.Variety.PairH`.
* `New.Variety.PairRestrictBijective`: restriction along `B_{S,M} → T` is bijective on cohomology in
  all degrees.
* `New.Variety.PairRestrictBijective.exists_hodgeTateMap_eq`: under this hypothesis,
  `hodgeTateMap h x` for `x` of degree `q` comes from a class of degree `q + h`.
* `New.Variety.IsChartCovered.pairRestrictBijective`: `PairRestrictBijective` holds for `ℤ[X]` if
  `X` is covered by étale charts. The map `B_{S,M} → T` is a square-zero extension
  (`New.Variety.HodgeTatePair.isSquareZero_toGeneric`), so the lifts of a point of a chart of
  dimension `n` are represented by one pair `(S, T ^ n)`.

Notions from other files:
* `New.Variety.PadicTest`: a p-adic test, a non-empty family of cells (`New.Variety.IsCell`) with a
  ring map from O_C to their product.
* `New.Variety.Cocycle`: a 1-cocycle from F to G, homomorphisms D(f): F(c) → G(d) for f: c → d, with
  D(gf) = G(g)D(f) + D(g)F(f); `D.cohomClass` is its class in Ext¹(F, G).
* `New.Variety.contraction`: for semilinear φ = (φ₀, φ₁): M → T' × M', the map ⋀M → ⋀M' that
  contracts with φ₀ and applies φ₁.
* `New.Variety.TotalH`: the total Ext group, the direct sum of the Ext^n(N,F) over all n ≥ 0;
  `comp x y` is the Yoneda product, `x` followed by `y`.
* `New.Variety.HodgeH`: Hodge cohomology of a functor N on k-algebras, Ext^q from (A, M) ↦ N(A ⊕ M)
  to (A, M) ↦ ⋀_A M on pairs of a k-algebra A and a free module M = A^ι.

## Relation to the literature

Known; see `Lib.PadicComparison.HodgeTate.PeriodMap` for sources.
-/

noncomputable section

namespace New.Variety

/-!
## The site of Hodge–Tate pairs and powers of the contraction class

* `New.Variety.HodgeTatePair.pairAlg`: the ring `B_{S,M} = B_S ×_T (T ⊕ M)`, with its projections
  `New.Variety.HodgeTatePair.toSqZero` to `T ⊕ M` and `New.Variety.HodgeTatePair.toGeneric` to `T`.
* `New.Variety.HodgeTatePair.contractionCocycle`: contraction with the component `M → T'` is a
  1-cocycle from `Λ = ⋀_T M` to `Λ`.
-/

section HodgeTatePairs

open CategoryTheory HodgeTest TrivSqZeroExt ExteriorAlgebra AddCommGrpCat TotalH thickeningOver
  CommAlgCat CliffordAlgebra

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} {k : Type} [Field k] [EmbeddedInQpBar p k]

/-! ### The category of pairs -/

/-- A pair (S, M) of a p-adic test S and the free module M = T^n over T = S[1/p], given by S and
the rank n. -/
structure HodgeTatePair where
  /-- The `p`-adic test `S`. -/
  test : PadicTest
  /-- The rank `n` of the free module `M = T ^ n` over `T = S[1/p]`. -/
  rank : ℕ

variable (X : HodgeTatePair)

namespace HodgeTatePair

/-- For a pair (S, M), the k-algebra T = S[1/p]: `New.Variety.genericOver` of the test S, its ring
with p inverted. -/
abbrev GenericRing : CommAlg k := genericOver X.test

-- Here and below, `seal … in` keeps `PadicTest.genericAlg` folded; unfolded, it makes comparisons
-- of ring instances slow.
seal PadicTest.genericAlg in
/-- Morphisms of pairs. A morphism (S, M) ⟶ (S', M') is a pair (f, φ) of a map of tests
f : S ⟶ S' and a map φ = (φ₀, φ₁) : M → T' × M' that is semilinear over the ring map T → T'
induced by f. The identity is (𝟙, m ↦ (0, m)), and (f, φ) followed by (g, ψ) is
(f ≫ g, m ↦ (g(φ₀ m), 0) + ψ(φ₁ m)). -/
@[simps] instance : Category HodgeTatePair := by
  refine' @Category.mk _ {
    Hom X Y := Σ f : X.test ⟶ Y.test, (Fin X.rank → X.GenericRing)
      →ₛₗ[((genericOver.map f).hom : X.GenericRing →+* Y.GenericRing)] Y.GenericRing ×
      (Fin Y.rank → Y.GenericRing),
    id _ := ⟨𝟙 _, ⟨(0, ·), by simp⟩, by simp⟩
    comp f g := ⟨f.1 ≫ g.1, ⟨fun m ↦ (genericOver.map g.1 (f.2 m).1, 0) + g.2 (f.2 m).2, by
      simp [add_add_add_comm]⟩, by simp⟩} ..
  all_goals
    intros
    exact congr(⟨_, $(by ext <;> simp [add_assoc])⟩)

/-- The map of tests `S ⟶ S'` of a morphism of pairs `(S, M) ⟶ (S', M')`. -/
abbrev testMap {X Y : HodgeTatePair} (f : X ⟶ Y) : X.test ⟶ Y.test := f.1

/-- The map `φ = (φ₀, φ₁) : M → T' × M'` of a morphism of pairs, semilinear over `T → T'`. -/
abbrev moduleMap {X Y : HodgeTatePair} (f : X ⟶ Y) :
    (Fin X.rank → X.GenericRing) →ₛₗ[((genericOver.map (testMap f)).hom :
      X.GenericRing →+* Y.GenericRing)] Y.GenericRing × (Fin Y.rank → Y.GenericRing) :=
  f.2

/-- The forgetful functor from pairs (S,M) to p-adic tests, sending (f,φ) to f. -/
def toTest : HodgeTatePair ⥤ PadicTest := CategoryTheory.Functor.mk test (·.1)

/-- The functor (S,M) ↦ (T,M) to the tests of Hodge cohomology, sending (f,φ) to the ring map
induced by f and the second component of φ. -/
def toHodgeTest : HodgeTatePair ⥤ HodgeTest k := by
  refine ⟨(⟨·.GenericRing, _⟩), (⟨_, .snd .. ∘ₛₗ ·.2⟩), ?_, ?_⟩
  all_goals
    intros
    apply HodgeTest.hom_ext <;> aesop

/-! ### The rings `B_{S,M}` -/

/-- For a pair (S,M), the k-algebra B_S ×_T (T ⊕ M), with B_S as in `New.Variety.thickeningOver`
and T ⊕ M the trivial square-zero extension. -/
abbrev PairRing :
    Subalgebra k (thickeningOver.obj X.test ×
      TrivSqZeroExt (genericOver.obj X.test) (Fin X.rank → X.GenericRing)) :=
  (thickeningOver.proj X.test).hom'.pullback
    (fstHom k (genericOver.obj X.test) (Fin X.rank → X.GenericRing))

/-- The `B_S` component `b` of a point `x = (b, (s, m))` of `B_S ×_T (T ⊕ M)`. -/
abbrev PairRing.base {X : HodgeTatePair} (x : X.PairRing) : thickeningOver.obj X.test := x.val.1

/-- The `T ⊕ M` component `(s, m)` of a point `x = (b, (s, m))` of `B_S ×_T (T ⊕ M)`. -/
abbrev PairRing.sqZero {X : HodgeTatePair} (x : X.PairRing) :
    TrivSqZeroExt (genericOver.obj X.test) (Fin X.rank → X.GenericRing) :=
  x.val.2

/-- Let `f : X ⟶ Y` be a morphism of pairs and `x = (b, (s, m))` a point of `B_S ×_T (T ⊕ M)`, so
that `b` projects to `s` in `T`. Then the image of `b` under the map of tests `testMap f`
projects to the image of `s` in `T'`. -/
lemma proj_map_fst {X Y : HodgeTatePair} (f : X ⟶ Y) (x : X.PairRing) :
    thickeningOver.proj Y.test (thickeningOver.map (testMap f) (PairRing.base x)) =
      genericOver.map (testMap f) (PairRing.sqZero x).fst :=
  (thickeningOver.proj.naturality_apply (testMap f) (PairRing.base x)).trans (congrArg _ x.property)

seal PadicTest.genericAlg in
/-- Let `f : X ⟶ Y` be a morphism of pairs with `moduleMap f = (φ₀, φ₁)`. The map from
`B_S ×_T (T ⊕ M)` to `B_{S'}` sending `x = (b, (s, m))` to `f₀(b) + μ·φ₀(m)` is multiplicative,
where `f₀ = testMap f` and `μ·_` is `thickeningOver.mulMu`, induced by multiplication by
`μ = [ε] − 1`. -/
lemma map_base_add_mulMu_mul {X Y : HodgeTatePair} (f : X ⟶ Y) (x y : X.PairRing) :
    thickeningOver.map (testMap f) (PairRing.base (x * y)) +
        thickeningOver.mulMu Y.test (moduleMap f (PairRing.sqZero (x * y)).snd).fst =
      (thickeningOver.map (testMap f) (PairRing.base x) +
          thickeningOver.mulMu Y.test (moduleMap f (PairRing.sqZero x).snd).fst) *
        (thickeningOver.map (testMap f) (PairRing.base y) +
          thickeningOver.mulMu Y.test (moduleMap f (PairRing.sqZero y).snd).fst) := by
  -- Write x = (b, (s, m)) and y = (b', (s', m')). As b projects to s and b' to s', the term
  -- μ·φ₀(s m' + s' m) is f₀(b) · μ·φ₀(m') + f₀(b') · μ·φ₀(m); the product of two μ-terms vanishes.
  have h_cross : mulMu Y.test (moduleMap f (PairRing.sqZero (x * y)).snd).fst =
      thickeningOver.map (testMap f) (PairRing.base x) *
          mulMu Y.test (moduleMap f (PairRing.sqZero y).snd).fst +
        thickeningOver.map (testMap f) (PairRing.base y) *
          mulMu Y.test (moduleMap f (PairRing.sqZero x).snd).fst := by
    rw [← mulMu_proj_mul, ← mulMu_proj_mul, proj_map_fst, proj_map_fst]
    simp [PairRing.sqZero]
  have h_mulMu_mul_mulMu (u v : genericOver.obj Y.test) : mulMu Y.test u * mulMu Y.test v = 0 := by
    rw [← mulMu_proj_mul, proj_mulMu, zero_mul, map_zero]
  rw [h_cross, PairRing.base, MulMemClass.coe_mul, Prod.fst_mul, map_mul, add_mul, mul_add, mul_add,
    h_mulMu_mul_mulMu]
  ring

seal PadicTest.genericAlg in
/-- Let `f : X ⟶ Y` be a morphism of pairs with `moduleMap f = (φ₀, φ₁)`. The map from
`B_S ×_T (T ⊕ M)` to `B_{S'}` sending `x = (b, (s, m))` to `f₀(b) + μ·φ₀(m)`, `f₀ = testMap f`, is
additive; `map_base_add_mulMu_mul` says that it is multiplicative. -/
lemma map_fst_add_mulMu_add {X Y : HodgeTatePair} (f : X ⟶ Y) (x y : X.PairRing) :
    thickeningOver.map (testMap f) (PairRing.base (x + y)) +
        thickeningOver.mulMu Y.test (moduleMap f (PairRing.sqZero (x + y)).snd).fst =
      (thickeningOver.map (testMap f) (PairRing.base x) +
          thickeningOver.mulMu Y.test (moduleMap f (PairRing.sqZero x).snd).fst) +
        (thickeningOver.map (testMap f) (PairRing.base y) +
          thickeningOver.mulMu Y.test (moduleMap f (PairRing.sqZero y).snd).fst) := by
  have h_base : PairRing.base (x + y) = PairRing.base x + PairRing.base y := rfl
  have h_snd : (PairRing.sqZero (x + y)).snd =
      (PairRing.sqZero x).snd + (PairRing.sqZero y).snd := rfl
  rw [h_base, h_snd, map_add, map_add, Prod.fst_add, map_add, add_add_add_comm]

seal PadicTest.genericAlg in
/-- The functor (S, M) ↦ B_{S,M} = B_S ×_T (T ⊕ M) to k-algebras. A morphism (f, (φ₀, φ₁)) acts by
(b, (s, m)) ↦ (f(b) + μ·φ₀(m), (f(s), φ₁(m))), where μ·_ is `thickeningOver.mulMu`; the first
component is additive and multiplicative by `map_fst_add_mulMu_add` and `map_base_add_mulMu_mul`. -/
def pairAlg : HodgeTatePair ⥤ CommAlg k where
  obj X := CommAlgCat.of k X.PairRing
  map {X Y} f := CommAlgCat.ofHom <| AlgHom.codRestrict
    (AlgHom.prod
      { toFun (x : X.PairRing) :=
          thickeningOver.map f.1 x.1.1 + thickeningOver.mulMu Y.test (f.2 x.1.2.snd).fst
        map_one' := by simp
        map_mul' := map_base_add_mulMu_mul f
        map_zero' := by simp
        map_add' := map_fst_add_mulMu_add f
        commutes' r := by simp [algebraMap_eq_inl'] }
      (((toHodgeTest ⋙ HodgeTest.sqZeroExt).map f).1.comp (AlgHom.pullbackSnd ..)))
    Y.PairRing
    fun x ↦ (map_add ..).trans ((add_eq_left.2 (proj_mulMu ..)).trans (proj_map_fst f x))
  map_id X := by ext : 4 <;> simp <;> rfl
  map_comp f g := by
    ext : 4
    · -- in the first component, `thickeningOver.mulMu` is additive and natural
      change _ = thickeningOver.map _ (_ + _) + _
      simp [← map_mulMu, add_assoc]
      rfl
    · simp
      rfl

/-- The natural projection of k-algebras B_S ×_T (T ⊕ M) → T ⊕ M. -/
def toSqZero : pairAlg ⟶ toHodgeTest ⋙ HodgeTest.sqZeroExt where
  app _ := CommAlgCat.ofHom (AlgHom.pullbackSnd ..)

/-- The natural map of k-algebras B_S ×_T (T ⊕ M) → T: `toSqZero` followed by the projection
T ⊕ M → T, (s, m) ↦ s. -/
def toGeneric : pairAlg ⟶ toTest ⋙ genericOver := toSqZero ≫ {app _ := baseProj _}

/-! ### Coefficients, the contraction cocycle and its powers -/

/-- The functor sending a pair (S,M) to the abelian group ⋀_T M, the restriction of the
coefficients of Hodge cohomology. -/
abbrev formCoeff : HodgeTatePair ⥤ AddCommGrpCat := toHodgeTest ⋙ hodgeCoeff

/-- The coefficient functor `New.Variety.genericCoeff` (S ↦ T = S[1/p]) on p-adic tests, restricted
to pairs along (S,M) ↦ S. -/
abbrev scalarCoeff : HodgeTatePair ⥤ AddCommGrpCat := toTest ⋙ genericCoeff

/-- The field k acts on F = `scalarCoeff`, (S, M) ↦ T, by natural endomorphisms `CoeffAction.act t`,
here multiplication by t on T, through its action on `New.Variety.genericCoeff`. -/
instance : CoeffAction k scalarCoeff :=
  ⟨.comp ⟨(restrictAlong _).mapEnd _, rfl, by tauto⟩ CoeffAction.act⟩

seal PadicTest.genericAlg in
/-- The cocycle from Λ = ⋀_T M (`formCoeff`) to itself that assigns to a morphism (f, φ) with
φ = (φ₀, φ₁) the map `New.Variety.contraction φ` : ⋀M → ⋀M', which contracts with φ₀ and applies
φ₁ to the remaining factors. -/
def contractionCocycle : Cocycle formCoeff formCoeff where
  component f := uliftFunctor.map (AddCommGrpCat.ofHom (contraction f.2).toAddMonoidHom)
  cocycle_comp f g := by
    -- The cocycle identity is the chain rule for contractions. It is proved by induction on the
    -- form, together with the functoriality of `exteriorMapSnd`.
    have h_chain x :
        contraction (f ≫ g).2 x =
          exteriorMapSnd g.2 (contraction f.2 x) + contraction g.2 (exteriorMapSnd f.2 x) ∧
        exteriorMapSnd (f ≫ g).2 x = exteriorMapSnd g.2 (exteriorMapSnd f.2 x) := by
      induction x using left_induction <;> simp_all [Algebra.algebraMap_eq_smul_one,
        mul_add] <;> module
    exact ext fun x ↦ congrArg ULift.up (h_chain x.1).1

/-- For h : ℕ, the class in total Ext(Λ, F) given by the h-th Yoneda power of the class of
`contractionCocycle` in Ext¹(Λ, Λ), followed by the projection of ⋀M onto its degree-zero part T.
Here Λ = `formCoeff`, (S, M) ↦ ⋀_T M, and F = `scalarCoeff`, (S, M) ↦ T. -/
def contractionPow : ℕ → TotalH formCoeff scalarCoeff
  -- In degree zero: the projection of the exterior algebra onto its scalar part.
  | 0 => TotalH.homClass
      { app X := uliftFunctor.map <| AddCommGrpCat.ofHom
          (@algebraMapInv (toHodgeTest.obj X).baseAlg _
            ((toHodgeTest.obj X).Index → X.GenericRing) ..).toAddMonoidHom
        naturality _ _ f := AddCommGrpCat.ext fun x ↦
          congrArg ULift.up (algebraMapInv_exteriorMap (toHodgeTest.map f).2 x.down) }
  | h + 1 => TotalH.comp contractionCocycle.cohomClass (contractionPow h)

/-- The natural map Λ ⊗ Λ → Λ given by the wedge product in ⋀_T M. -/
abbrev wedgePairing : abTensor formCoeff formCoeff ⟶ formCoeff :=
  toHodgeTest.whiskerLeft exteriorAlg.mulPairing

seal PadicTest.genericAlg in
/-- The class `contractionPow h` is `k`-linear. For `t : k`, multiplication by `t` on `Λ = ⋀ M`
(`CoeffAction.act t` on `hodgeCoeff`), followed by `contractionPow h`, is `t • contractionPow h`,
where `k` acts on `F = T` by the `CoeffAction` instance on `scalarCoeff`. -/
lemma act_comp_contractionPow (t : k) (h : ℕ) :
    comp (TotalH.homClass (toHodgeTest.whiskerLeft (End.asHom (CoeffAction.act t))))
      (contractionPow h) =
      t • contractionPow h := by
  induction h with
  | zero =>
    -- `contractionPow 0` is the class of `algebraMapInv`, the degree-zero component, which is
    -- `k`-linear
    simp only [smul_eq_comp, contractionPow, ← homClass_comp]
    congr 1 with c
    exact congrArg ULift.up (algebraMapInv (R := c.GenericRing).map_smul_of_tower t _)
  | succ h ih =>
    -- the cocycle `contractionCocycle` commutes with multiplication by `t`, since contraction is
    -- semilinear
    set m : formCoeff ⟶ formCoeff := toHodgeTest.whiskerLeft (CoeffAction.act t).asHom
    have h_smul {c d : HodgeTatePair} (f : c ⟶ d) (z : ExteriorAlgebra c.GenericRing _) :
        contraction f.snd (t • z) = t • contraction f.snd z := by
      simpa using (contraction f.snd).map_smulₛₗ (t • 1) z
    have h_comm : comp contractionCocycle.cohomClass (.homClass m) =
        comp (.homClass m) contractionCocycle.cohomClass :=
      contractionCocycle.cohomClass_naturality contractionCocycle m m
        fun _ _ f ↦ ext fun x ↦ congrArg ULift.up (h_smul f x.down)
    rw [contractionPow, ← TotalH.comp_assoc_of_sq h_comm, ih, comp_smul]

seal PadicTest.genericAlg in
/-- On pairs `(S, M)` of a `p`-adic test `S` and a free module `M = T^n` over `T = S[1/p]`, let `Λ`
be `(S, M) ↦ ⋀_T M`. `contractionPow h` is the class in total Ext from `Λ` to `(S, M) ↦ T` given by
the `h`-th Yoneda power of the contraction class in `Ext¹(Λ, Λ)`, followed by the projection of
`⋀ M` onto degree zero. This class has weight `h`: for `t : k`, precomposing it with the
endomorphism of `Λ` induced by `m ↦ t • m` (`HodgeTest.scaleModule`, which multiplies forms of
degree `d` by `t ^ d`) gives `t ^ h • contractionPow h`. -/
lemma scaleModule_comp_contractionPow (t : k) (h : ℕ) :
    pullbackAlong (toHodgeTest.whiskerLeft (scaleModule t hodgeCoeff)) (contractionPow h) =
      t ^ h • contractionPow h := by
  induction h with
  | zero =>
    -- scaling the module by `t` leaves the degree-zero component unchanged
    simp only [contractionPow, ← homClass_comp, pow_zero, one_smul]
    congr with c x
    have h_deg_zero (y : ExteriorAlgebra c.GenericRing (Fin c.rank → c.GenericRing)) :
        algebraMapInv (exteriorMap (t • LinearMap.id) y) = algebraMapInv y :=
      algebraMapInv_exteriorMap _ y
    exact congrArg ULift.up (h_deg_zero x.down)
  | succ h ih =>
    -- moving the scaling `s` past the cocycle `contractionCocycle` costs one factor `t`
    set s : formCoeff ⟶ formCoeff := toHodgeTest.whiskerLeft (scaleModule t hodgeCoeff)
    set m : formCoeff ⟶ formCoeff := toHodgeTest.whiskerLeft (CoeffAction.act t).asHom
    have h_comm : comp contractionCocycle.cohomClass (.homClass (s ≫ m)) =
        pullbackAlong s contractionCocycle.cohomClass := by
      refine contractionCocycle.cohomClass_naturality contractionCocycle s (s ≫ m)
        fun (c d : HodgeTatePair) (f : c ⟶ d) ↦ ext fun x ↦ ?_
      have h_smul (v : Fin c.rank → c.GenericRing) : f.snd (t • v) = t • f.snd v := by
        simpa using f.snd.map_smulₛₗ (t • 1) v
      -- `exteriorMapSnd` keeps the form degree, so it commutes with the scaling. In both inductions
      -- `LinearMap.map_smul_of_tower` is left out: it would pull `t` out of `ι (t • v)`, so that
      -- `h_smul` and the induction hypothesis no longer match.
      have h_snd_scale (y : ExteriorAlgebra c.GenericRing (Fin c.rank → c.GenericRing)) :
          exteriorMapSnd f.snd (exteriorMap (t • LinearMap.id) y) =
            exteriorMap (t • LinearMap.id) (exteriorMapSnd f.snd y) := by
        induction y using left_induction <;>
          simp [*, Algebra.algebraMap_eq_smul_one, -LinearMap.map_smul_of_tower]
      -- contraction lowers the form degree by one, which costs one factor `t`
      have h_contraction_scale (y : ExteriorAlgebra c.GenericRing (Fin c.rank → c.GenericRing)) :
          contraction f.snd (exteriorMap (t • LinearMap.id) y) =
            t • exteriorMap (t • LinearMap.id) (contraction f.snd y) := by
        induction y using left_induction with
        | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
        | add y y' hy hy' => simp [hy, hy']
        | ι_mul y v hy =>
          simp [hy, h_snd_scale, h_smul, -LinearMap.map_smul_of_tower]
          module
      exact congrArg ULift.up (h_contraction_scale x.down)
    calc pullbackAlong s (comp contractionCocycle.cohomClass (contractionPow h))
        = comp contractionCocycle.cohomClass (pullbackAlong s (t • contractionPow h)) := by
          rw [← comp_assoc_of_sq h_comm, ← pullbackAlong_pullbackAlong, act_comp_contractionPow]
      _ = t ^ (h + 1) • contractionPow (h + 1) := by
          rw [comp_smul, ih, smul_smul, comp_smul, pow_succ', contractionPow]

end HodgeTatePair

end HodgeTatePairs

/-! ## The Hodge–Tate maps λ_h: naturality, scaling and the product rule -/

section HodgeTateMap

open CategoryTheory Abelian TensorProduct AddCommGrpCat TotalH HodgeTatePair Finset ExteriorAlgebra

variable {p : ℕ} {k : Type} [Field k] [EmbeddedInQpBar p k] {N N' : AbFunctor (CommAlg k)}

/-- For a functor `N` from `k`-algebras to abelian groups, the total cohomology on pairs `(S, M)`
of `(S, M) ↦ N(B_{S,M})` with coefficients `scalarCoeff`, `(S, M) ↦ T = S[1/p]`; the target of
`λ_h`. -/
abbrev PairH (N : CommAlg k ⥤ AddCommGrpCat) : Type 2 := TotalH (pairAlg ⋙ N) scalarCoeff

/-- The Hodge–Tate map `λ_h` on the degree-`q` Hodge cohomology of `N`. A class `x` is pulled back
along `B_{S,M} → T ⊕ M` to the cohomology on pairs, put in total degree `q`, and composed with
`contractionPow h`: the `h`-th power of the class of the contraction cocycle, followed by the
projection of `⋀ M` to degree zero. -/
def hodgeTateMap {q : ℕ} (h : ℕ) : HodgeH N q →ₗ[k] PairH N where
  toFun x := comp ((Comparison.restrict toHodgeTest hodgeCoeff).pull
    (Functor.whiskerRight toSqZero N) q x).toTotalH (contractionPow h)
  map_add' := by simp
  -- the scalar acts through the coefficients, and `act_comp_contractionPow` moves it past
  -- `contractionPow h`
  map_smul' := by
    simp [← comp_smul, ← act_comp_contractionPow, comp_assoc_of_eq, of_comp_homClass,
      Comparison.pull, H.map, H.push, Functor.mapExtAddHom, H.smul_eq_push,
      Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

/-- For `α : N' ⟶ N`, the `k`-linear pull-back from `PairH N` to `PairH N'` along the natural map
`N'(B_{S,M}) → N(B_{S,M})` induced by `α`. -/
def PairH.map (α : N' ⟶ N) : PairH N →ₗ[k] PairH N' where
  toAddHom := (pullbackAlong (pairAlg.whiskerLeft α)).toAddHom
  map_smul' := comp_smul

/-- The `k`-linear map from the degree-`n` cohomology on `p`-adic tests `S` of `S ↦ N(T)`,
`T = S[1/p]` (`genericOver`), with coefficients `genericCoeff` (`S ↦ T`), to `PairH N`: pull back
along `B_{S,M} → T` and include as the degree-`n` summand. -/
def restrictToPairs {n : ℕ} : H (genericOver ⋙ N) genericCoeff n →ₗ[k] PairH N where
  toFun := Ext.toTotalH ∘
    (Comparison.restrict toTest genericCoeff).pull (Functor.whiskerRight toGeneric N) n
  map_add' := by simp
  map_smul' t x := by
    -- both scalar actions are composition with the action of `t` on the coefficients
    simp [smul_eq_comp, of_comp_homClass, Comparison.pull, H.map, H.push, Functor.mapExtAddHom,
      H.smul_eq_push, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
    rfl

/-- `restrictToPairs` is natural in `N`: for `α : N' ⟶ N`, restricting the pull-back of `x` along
`α` gives `PairH.map α` of the restriction of `x`. -/
lemma restrictToPairs_map {n : ℕ} (α : N' ⟶ N) (x : H (genericOver ⋙ N) genericCoeff n) :
    restrictToPairs (H.map genericCoeff (genericOver.whiskerLeft α) n x) =
      PairH.map α (restrictToPairs x) := by
  -- restriction to pairs commutes with precomposition by the class of `α`
  have h_nat :
      comp ((Ext.mk₀ α).mapExactFunctor (restrictAlong pairAlg)).toTotalH (restrictToPairs x) =
        restrictToPairs (N := N')
          (((Ext.mk₀ α).mapExactFunctor (restrictAlong genericOver)).comp x (zero_add n)) :=
    Comparison.pull_comp_restrictAlong (.mk₀ α) x (zero_add n)
  show restrictToPairs ((Ext.mk₀ (genericOver.whiskerLeft α)).comp x (zero_add n)) =
    comp (Ext.mk₀ (pairAlg.whiskerLeft α)).toTotalH (restrictToPairs x)
  simpa [Ext.mapExactFunctor_mk₀] using h_nat.symm

/-- The Hodge–Tate map is natural in the functor `N` from `k`-algebras to abelian groups: for
`α : N' ⟶ N` and a Hodge class `x` on `N`, `λ_h` of the pull-back of `x` along `α` is `PairH.map α`
of `λ_h x`. -/
lemma hodgeTateMap_map {q h : ℕ} (α : N' ⟶ N) (x : HodgeH N q) :
    hodgeTateMap h (HodgeH.map α x) = PairH.map α (hodgeTateMap h x) := by
  -- restriction to pairs commutes with precomposition by the class of `α`; then compose with
  -- `contractionPow h`
  have h_nat :
      comp ((Ext.mk₀ α).mapExactFunctor (restrictAlong pairAlg)).toTotalH
          (comp ((Comparison.restrict toHodgeTest hodgeCoeff).pull
            (Functor.whiskerRight toSqZero N) q x).toTotalH (contractionPow h)) =
        comp ((Comparison.restrict toHodgeTest hodgeCoeff).pull (Functor.whiskerRight toSqZero N') q
          (((Ext.mk₀ α).mapExactFunctor (restrictAlong HodgeTest.sqZeroExt)).comp x
            (zero_add q))).toTotalH (contractionPow h) :=
    comp_assoc_of_eq (Comparison.pull_comp_restrictAlong (.mk₀ α) x (zero_add q)) (contractionPow h)
  -- both sides, written as precompositions with the classes of `α`
  show comp ((Comparison.restrict toHodgeTest hodgeCoeff).pull (Functor.whiskerRight toSqZero N') q
        ((Ext.mk₀ (HodgeTest.sqZeroExt.whiskerLeft α)).comp x (zero_add q))).toTotalH
      (contractionPow h) =
    comp (Ext.mk₀ (pairAlg.whiskerLeft α)).toTotalH
      (comp ((Comparison.restrict toHodgeTest hodgeCoeff).pull (Functor.whiskerRight toSqZero N) q
        x).toTotalH (contractionPow h))
  simpa [Ext.mapExactFunctor_mk₀] using h_nat.symm

/-- The map `λ_h` has weight `h`: for `t : k` it turns `HodgeH.scale t`, the endomorphism of Hodge
cohomology induced by `(a, m) ↦ (a, t m)` on `A ⊕ M`, into multiplication by `t ^ h`. -/
lemma hodgeTateMap_scale {q h : ℕ} (t : k) (x : HodgeH N q) :
    hodgeTateMap h (HodgeH.scale t x) = t ^ h • hodgeTateMap h x := by
  -- By `scaleModule_comp_contractionPow` the right side is the class of `x` pushed along the
  -- scaling by `t` of the coefficients, followed by `contractionPow h`.
  erw [← comp_smul, ← scaleModule_comp_contractionPow]
  -- Naturality for the scaling of the site: pulling `x` back along the scaling of the space is the
  -- same as pushing it along the scaling of the coefficients.
  erw [← (x.mapExactFunctor_restrictAlong_id ▸
    mapExactFunctor_naturality ((Functor.whiskeringLeft ..).map _) x :)]
  simp [hodgeTateMap, comp_assoc_of_eq, of_comp_homClass, Comparison.pull, H.map, H.push,
    Functor.mapExtAddHom, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  rfl

/-- For functors `M`, `L` on pairs (`M` with flat values) and `y` in the total cohomology of `L`
with coefficients `scalarCoeff` (`(S, M) ↦ T`), the `k`-linear map `x ↦ x × y` to the total
cohomology of `M ⊗ L` (`abTensor`, the objectwise tensor product): the external product
`x.cup y` followed by the multiplication `T ⊗ T → T`. -/
def HodgeTatePair.cross {M L : AbFunctor HodgeTatePair} [HasFlatValues M]
    (y : TotalH L scalarCoeff) :
    TotalH M scalarCoeff →ₗ[k] TotalH (abTensor M L) scalarCoeff where
  toFun x :=
    (x.cup y).comp
      (TotalH.homClass (toTest.whiskerLeft
        (PadicTest.genericAlg ⋙ forget₂ (CommAlg ℂ_[p]) (AlgCat ℂ_[p])).mulPairing))
  map_add' := by simp [TotalH.cup, comp_assoc]
  map_smul' t x := by
    -- the multiplication is linear in its first factor: `(t • a) * b = t • (a * b)`
    simp [smul_eq_comp, cup_comp_homClass_left, comp_assoc]
    repeat erw [← homClass_comp]
    refine congrArg (comp (x.cup y)) (congrArg TotalH.homClass ?_)
    exact abTensor_hom_ext fun _ _ _ ↦ congrArg _ (smul_mul_assoc ..)

set_option backward.isDefEq.respectTransparency false

/-- The cocycle on `formCoeff ⊗ formCoeff` (`Λ ⊗ Λ`, `Λ = ⋀ M`) with values in two copies of it.
At a morphism `f`, its `true` component is `D(f) ⊗ Λ(f)` and its `false` component is
`Λ(f) ⊗ D(f)`, where `D` is `contractionCocycle`. -/
def HodgeTatePair.tensorContractionCocycle :
    Cocycle (abTensor formCoeff formCoeff)
      (piAbFunctor fun _ : Bool ↦ abTensor formCoeff formCoeff) where
  component f :=
    ofHom <|
      .pi fun b ↦
        (cond b (abTensorMap (contractionCocycle.component f) (formCoeff.map f))
          (abTensorMap (formCoeff.map f) (contractionCocycle.component f))).hom
  cocycle_comp f g :=
    addCommGrp_tensor_hom_ext <| by
      simp [funext_iff, contractionCocycle.cocycle_comp, add_tmul, tmul_add, piAbFunctor,
        abTensor, Functor.curryObj]

/-- Let `M`, `L` be functors on pairs, `M` with flat values, `x` a class of degree `a` on `M` and
`y` a total class on `L`, both with coefficients `formCoeff` (`Λ = ⋀ M`). The `true` component
(`piAbFunctor.π _ true`) of the class of `tensorContractionCocycle`, after the external product of
`x` and `y`, is the class of `contractionCocycle` applied to the first factor `x`. -/
lemma HodgeTatePair.cup_comp_tensorContractionCocycle_π_true {a : ℕ}
    {M L : AbFunctor HodgeTatePair} [HasFlatValues M] (x : H M formCoeff a)
    (y : TotalH L formCoeff) :
    (comp (.cup x.toTotalH y) tensorContractionCocycle.cohomClass).comp
        (.homClass (piAbFunctor.π _ true)) =
      .cup (x.toTotalH.comp contractionCocycle.cohomClass) y := by
  -- `σ` splits the extension of `contractionCocycle` objectwise; tensored with the identity, its
  -- failure to be natural is the `true` component (`Cocycle.cohomClass_comp_eq_extClass`).
  let σ (c : HodgeTatePair) :
      contractionCocycle.extension.X₃.obj c ⟶ contractionCocycle.extension.X₂.obj c :=
    ofHom (.inr _ (formCoeff c))
  simp_rw [TotalH.cup, TotalH.map_comp, comp_assoc]
  -- `erw`: `cohomClass` is the class of the extension only after unfolding its definition.
  erw [map_extClass contractionCocycle.shortExact_extension]
  refine congrArg (_ ∘ _) <| .trans (tensorContractionCocycle.cohomClass_comp_eq_extClass
    (S := ⟨_, _, _⟩) _ (𝟙 _) (piAbFunctor.π _ true)
      (fun c ↦ by exact abTensorMap (σ c) (𝟙 _)) ?_ ?_)
    pullbackAlong_id
  · -- `σ ⊗ 𝟙` lifts the identity
    exact fun c ↦ addCommGrp_tensor_hom_ext <| by
      simp [Cocycle.extension, abTensor, σ, Functor.curryObj]
  · -- its failure to be natural is the `true` component
    exact fun c d f ↦ addCommGrp_tensor_hom_ext <| by
      simp [Cocycle.extension, abTensor, piAbFunctor, tensorContractionCocycle, σ, piAbFunctor.π,
        ← add_tmul, Functor.curryObj]

/-- Let `M`, `L` be functors on pairs, `M` with flat values, `x` a class of degree `a` on `M` and
`y` a total class on `L`, both with coefficients `formCoeff` (`Λ = ⋀ M`). The `false` component
(`piAbFunctor.π _ false`) of the class of `tensorContractionCocycle`, after the external product of
`x` and `y`, is the class of `contractionCocycle` applied to the second factor `y`, times the sign
`(-1) ^ a` for moving it past `x`. -/
lemma HodgeTatePair.cup_comp_tensorContractionCocycle_π_false {a : ℕ}
    {M L : AbFunctor HodgeTatePair} [HasFlatValues M] (x : H M formCoeff a)
    (y : TotalH L formCoeff) :
    (comp (.cup x.toTotalH y) tensorContractionCocycle.cohomClass).comp
        (.homClass (piAbFunctor.π _ false)) =
      (-1) ^ a • .cup x.toTotalH (y.comp contractionCocycle.cohomClass) := by
  -- as for the `true` component, with `σ` on the second factor
  let σ (c : HodgeTatePair) :
      contractionCocycle.extension.X₃.obj c ⟶ contractionCocycle.extension.X₂.obj c :=
    ofHom (.inr _ (formCoeff c))
  simp_rw [TotalH.cup, TotalH.map_comp, comp_assoc]
  -- `erw`: `cohomClass` is the class of the extension only after unfolding its definition.
  erw [← map_zsmul, map_extClass contractionCocycle.shortExact_extension,
    ← extClass_sign_comm (abTensor_shortExact contractionCocycle.shortExact_extension)]
  refine congrArg (_ ∘ _) <| .trans (tensorContractionCocycle.cohomClass_comp_eq_extClass
    (S := ⟨_, _, _⟩) _ (𝟙 _) (piAbFunctor.π _ false)
      (fun c ↦ by exact abTensorMap (𝟙 _) (σ c)) ?_ ?_)
    pullbackAlong_id
  · -- `𝟙 ⊗ σ` lifts the identity
    exact fun c ↦ addCommGrp_tensor_hom_ext <| by
      simp [abTensor, σ, Functor.curryObj]
  · -- its failure to be natural is the `false` component
    exact fun c d f ↦ addCommGrp_tensor_hom_ext <| by
      simp [abTensor, piAbFunctor, tensorContractionCocycle, σ, piAbFunctor.π,
        ← tmul_add, Functor.curryObj]

/-- The Leibniz rule for the contraction (`contraction_mul`) on classes. The `false` component of
`tensorContractionCocycle`, followed by the grade involution (scaling by `-1`) on the first
factor, plus its `true` component, followed by the wedge product, is the class of
`contractionCocycle` pulled back along the wedge product. -/
lemma HodgeTatePair.tensorContractionCocycle_comp_wedgePairing :
    (tensorContractionCocycle (p := p) (k := k)).cohomClass.comp (.homClass
        ((piAbFunctor.π _ false ≫
              abTensor.map (toHodgeTest.whiskerLeft (HodgeTest.scaleModule (-1 : k) _)) _ +
            piAbFunctor.π _ true) ≫ wedgePairing)) =
      pullbackAlong wedgePairing contractionCocycle.cohomClass :=
  tensorContractionCocycle.cohomClass_naturality contractionCocycle wedgePairing _
    fun (c d : HodgeTatePair) (_ : c ⟶ d) ↦ addCommGrp_tensor_hom_ext fun v w ↦
      congrArg _ (contraction_mul _ (neg_one_smul k) v.down w.down)

/-- The binomial rule for the powers of the contraction class. Pairs are `(S, M)` with `S` a
`p`-adic test and `M = T^n`, `T = S[1/p]`; let `M`, `L` be functors on pairs, `M` with flat values.
Write `u_l(z)` for a class `z` with coefficients `formCoeff` (`(S, M) ↦ ⋀_T M`) followed by
`contractionPow l`. This is the `l`-th Yoneda power of the contraction class in `Ext¹`, then the
projection of `⋀ M` onto `T`. Write `x ∧ y` for `TotalH.cup` followed by `wedgePairing`, and `X × Y`
for `cross Y X`, the external product followed by `T ⊗ T → T`. For `x` of degree `a` and any `y`,
`u_l(x ∧ y) = ∑_{h ≤ l} C(l, h) (-1)^((a + h)(l - h)) u_h(x) × u_{l-h}(y)`. -/
lemma HodgeTatePair.contractionPow_cup {a : ℕ} {M L : AbFunctor HodgeTatePair} [HasFlatValues M]
    (l : ℕ) (x : H M formCoeff a) (y : TotalH L formCoeff) :
    comp (TotalH.cup x.toTotalH y) (pullbackAlong wedgePairing (contractionPow l)) =
      ∑ h ∈ range (l + 1), l.choose h • (-1 : k) ^ ((a + h) * (l - h)) •
        cross (comp y (contractionPow (l - h))) (comp x.toTotalH (contractionPow h)) := by
  -- Induction on `l`, by Pascal's rule: the contraction is a derivation of `formCoeff`, so its
  -- class passes the product by acting on the first factor or, with a sign, on the second.
  induction l generalizing a y with
  | zero =>
    -- Both sides are the product followed by the class of a map `⋀ M ⊗ ⋀ M → T`; the two maps
    -- agree because the degree-zero component `algebraMapInv` is multiplicative.
    simp [cross, cup_comp_homClass_right, ← homClass_comp, contractionPow, comp_assoc,
      cup_comp_homClass_left]
    refine congrArg (comp (x.toTotalH.cup y)) (congrArg TotalH.homClass ?_)
    exact abTensor_hom_ext fun X _ _ ↦ congrArg _ ((algebraMapInv (R := X.GenericRing)).map_mul ..)
  | succ l ih =>
    -- By the Leibniz rule the class of `contractionCocycle` after the wedge product splits into the
    -- two components of `tensorContractionCocycle`, which act on `x` and, with a sign, on `y`.
    rw [sum_choose_succ_nsmul fun _ _ ↦ _, contractionPow,
      ← TotalH.comp_assoc_of_sq tensorContractionCocycle_comp_wedgePairing]
    -- Expand the sum, insert the two components, and apply `ih` to both terms.
    simp [TotalH.homClass, Ext.mk₀_add, homClass_comp, ← comp_assoc,
      cup_comp_tensorContractionCocycle_π_true, cup_comp_tensorContractionCocycle_π_false,
      ← cup_comp_homClass_left, contractionPow]
    simp [comp_of, ih, smul_sum, comp_assoc]
    -- Compare term by term; what is left is an identity of signs.
    congr! 2 with h h_mem
    · -- terms where the contraction acts on `y`: moving it past `x` gives `(-1) ^ a`, and the
      -- grade involution on `contractionPow h` gives `(-1) ^ h`
      have h_sign : (-1 : k) ^ ((a + h) * (l - h + 1)) =
          (-1) ^ a * (-1) ^ h * (-1) ^ ((a + h) * (l - h)) := by ring
      simp [Nat.lt_succ_iff.mp (Finset.mem_range.mp h_mem), h_sign, ← comp_of,
        scaleModule_comp_contractionPow, comp_smul, Nat.succ_sub, comp_assoc, contractionPow]
      module
    · -- terms where the contraction acts on `x`: the degrees `a + 1 + h` and `a + (h + 1)` agree
      simp [← comp_of, comp_assoc]
      module

/-- Product formula: let `N`, `N'` be functors from `k`-algebras to abelian groups, `x` a Hodge
class of degree `a` on `N` (with flat values) and `y` one of degree `b` on `N'`. Their product
`x ∧ y = cup exteriorAlg.mulPairing x y e`, through the wedge product, is a Hodge class of degree
`n = b + a` on `N ⊗ N'` (`abTensor`, objectwise), and `λ_l(x ∧ y) = ∑_{h ≤ l} C(l, h)
(-1)^((a + h)(l - h)) λ_h(x) × λ_{l-h}(y)`. On the right `New.Variety.HodgeTatePair.cross Y` is the
linear map `X ↦ X × Y`; the binomial coefficient and the sign multiply this map before it is applied
to `λ_h(x)`. -/
lemma hodgeTateMap_cup {n a b : ℕ} [HasFlatValues N] (x : HodgeH N a) (y : HodgeH N' b)
    (e : b + a = n) (l : ℕ) :
    hodgeTateMap l (N := abTensor N N') (cup exteriorAlg.mulPairing x y e) =
      ∑ h ∈ range (l + 1),
        (l.choose h • (-1 : k) ^ ((a + h) * (l - h)) • cross (hodgeTateMap (l - h) y))
          (hodgeTateMap h x) := by
  -- The restriction to `HodgeTatePair` respects products (`Comparison.pull_cup`), so this is
  -- `contractionPow_cup`.
  -- `erw`: the product is a Hodge class of `abTensor N N'` only after unfolding `HodgeH`
  erw [← contractionPow_cup, comp_assoc_of_eq (cup_of _ _ _ e)]
  have h_pull :
      (Comparison.restrict toHodgeTest hodgeCoeff).pull
          (Functor.whiskerRight toSqZero (abTensor N N')) n (cup exteriorAlg.mulPairing x y e) =
        cup wedgePairing
          ((Comparison.restrict toHodgeTest hodgeCoeff).pull (Functor.whiskerRight toSqZero N) a x)
          ((Comparison.restrict toHodgeTest hodgeCoeff).pull (Functor.whiskerRight toSqZero N') b y)
          e :=
    Comparison.pull_cup (by simp) x y e
  exact congrArg (fun z ↦ comp (Ext.toTotalH z) (contractionPow l)) h_pull

end HodgeTateMap

/-!
## Bijectivity of restriction along B_{S,M} → S[1/p] for chart-covered functors

`New.Variety.Comparison.pull` is the pull-back of classes between two sites, and
`New.Variety.genericCoeff` is the functor `S ↦ T`.
-/

section HodgeTateRestriction

open CategoryTheory Function TrivSqZeroExt Pi thickeningOver EtaleChart HodgeTatePair TotalH
  Comparison DirectSum Ideal

variable {p : ℕ} {k : Type} [Field k] [EmbeddedInQpBar p k]

/-- For a functor `N` from `k`-algebras to abelian groups: pull-back along `B_{S,M} → T`, from the
cohomology of `S ↦ N(T)` on `p`-adic tests `S` to that of `(S, M) ↦ N(B_{S,M})` on pairs `(S, M)`,
both with coefficients `T = S[1/p]`, is bijective in every degree. -/
def PairRestrictBijective (N : CommAlg k ⥤ AddCommGrpCat) : Prop :=
  (Comparison.restrict HodgeTatePair.toTest genericCoeff).IsBijective (N := genericOver ⋙ N)
    (Functor.whiskerRight toGeneric N)

/-- Under `New.Variety.PairRestrictBijective` the map `New.Variety.restrictToPairs` from degree `n`
to total cohomology on pairs is injective, for every `n`. -/
lemma PairRestrictBijective.injective_restrictToPairs {N : CommAlg k ⥤ AddCommGrpCat} {n : ℕ}
    (hN : PairRestrictBijective N) :
    Function.Injective (restrictToPairs (p := p) (k := k) (N := N) (n := n)) :=
  (DirectSum.of_injective n).comp (hN n).injective

/-- The class `contractionPow h` is homogeneous of degree `h`: it is the image under `DirectSum.of`
of a class of degree `h`. -/
lemma HodgeTatePair.exists_contractionPow_eq_directSum_of (h : ℕ) :
    ∃ y : H formCoeff scalarCoeff h, contractionPow (p := p) (k := k) h = DirectSum.of _ h y := by
  induction h with
  | zero => exact ⟨_, rfl⟩
  | succ h ih =>
    obtain ⟨y, hy⟩ := ih
    refine ⟨contractionCocycle.shortExact_extension.extClass.comp y (add_comm 1 h), ?_⟩
    erw [contractionPow, hy, comp_of _ _ (add_comm 1 h)]
    rfl

/-- If restriction along B_{S,M} → T = S[1/p] is bijective on the cohomology of N
(`New.Variety.PairRestrictBijective`), then for `x : HodgeH N q` the class `hodgeTateMap h x` is the
restriction (`New.Variety.restrictToPairs`) of a class of degree q + h on p-adic tests. -/
lemma PairRestrictBijective.exists_hodgeTateMap_eq {N : CommAlg k ⥤ AddCommGrpCat} {q : ℕ}
    (hN : PairRestrictBijective N) (h : ℕ) (x : HodgeH N q) :
    ∃ ξ : H (genericOver ⋙ N) genericCoeff (q + h),
      hodgeTateMap h x = restrictToPairs (n := q + h) ξ := by
  -- `contractionPow h` is homogeneous of degree `h`, so `hodgeTateMap h x` lies in degree `q + h`,
  -- where restriction is onto.
  obtain ⟨y, hy⟩ := HodgeTatePair.exists_contractionPow_eq_directSum_of (p := p) (k := k) h
  obtain ⟨ξ, hξ⟩ := (hN (q + h)).surjective
    (((Comparison.restrict toHodgeTest _).pull (Functor.whiskerRight toSqZero N) q x).comp y rfl)
  exact ⟨ξ, by simp [hodgeTateMap, restrictToPairs, comp_of, hy, hξ]⟩

/-- Let `A = (S, T ^ r)` and `D = (S', M')` be pairs, `f : S ⟶ S'` a map of tests and
`v i ∈ T' × M'` for `i < r`. Exactly one map of pairs `g : A ⟶ D` has map of tests `testMap g = f`
and semilinear part `moduleMap g : T ^ r → T' × M'` sending the `i`-th basis vector to `v i`. -/
lemma HodgeTatePair.existsUnique_hom (A D : HodgeTatePair) (f : A.test ⟶ D.test)
    (v : Fin A.rank → D.GenericRing × (Fin D.rank → D.GenericRing)) :
    ∃! g : A ⟶ D, (∀ i : Fin A.rank, moduleMap g (single i 1) = v i) ∧ testMap g = f := by
  refine ⟨⟨f, semilinearOfBasis _ v⟩, by simp [moduleMap, testMap], ?_⟩
  rintro ⟨_, φ⟩ ⟨hφ, rfl⟩
  refine congrArg _ ((Pi.basisFun A.GenericRing (Fin A.rank)).ext fun i ↦ ?_)
  -- on the `i`-th basis vector both semilinear maps give `v i`
  simpa using hφ i

/-- For a pair `A = (S, M)`, the map `toGeneric : B_{S,M} → T = S[1/p]` is a square-zero extension:
it is surjective and its kernel has square zero. -/
lemma HodgeTatePair.isSquareZero_toGeneric (A : HodgeTatePair) : IsSquareZero (toGeneric A) := by
  obtain ⟨h_proj_surj, -, -⟩ := exact_mulMu_proj A.test
  refine ⟨fun t ↦ ?_, ?_⟩
  · -- lift `t` along `thickeningOver.proj` to `b`; the pair `(b, (t, 0))` lies in the fibre product
    obtain ⟨b, hb⟩ := h_proj_surj t
    exact ⟨⟨(b, t, 0), hb⟩, rfl⟩
  · -- elements of the kernel are pairs `(a, (0, m))` with `a` in the kernel of
    -- `thickeningOver.proj`, whose square is zero
    rw [pow_two, eq_bot_iff, mul_le]
    rintro ⟨⟨a, _, m⟩, ha⟩ ⟨⟩ ⟨⟨b, _, m'⟩, hb⟩ ⟨⟩
    -- `a * b` lies in the square of the kernel of `thickeningProj`, which is zero
    have h_fst : a * b = 0 :=
      (pow_two _).ge.trans A.test.ker_thickeningProj_sq.le (mul_mem_mul ha hb)
    exact Subtype.ext (Prod.ext h_fst (inr_mul_inr _ m m'))

/-- The coefficients `genericCoeff` (`S ↦ T = S[1/p]`) are additive on `p`-adic tests
(`HasPartitions`): a decomposition of the ring of a test by idempotents gives one of the group. -/
lemma hasPartitions_genericCoeff : HasPartitions PadicTest.ringFunctor (genericCoeff (p := p)) :=
  hasPartitions_periodAlg _ (exists_periodAlg_iso_genericAlg (p := p)).choose

/-- The coefficients `scalarCoeff` (`(S, M) ↦ T`) on pairs are additive (`HasPartitions`, for the
rings of the underlying tests): a pair is cut along an idempotent by cutting its test and keeping
its rank. -/
lemma HodgeTatePair.hasPartitions_scalarCoeff :
    HasPartitions (HodgeTatePair.toTest ⋙ PadicTest.ringFunctor)
      (scalarCoeff (p := p) (k := k)) := by
  have h_generic := hasPartitions_genericCoeff (p := p)
  refine ⟨fun A e he he' ↦ ?_, fun _ _ ↦ h_generic.bijective_prod _ _⟩
  -- cut the test of `A` along `e`: `f` kills `e`, every map killing `e` factors through `f`, and
  -- `f` is onto with kernel in `(e)`
  obtain ⟨d, f, h_kill, h_factor, h_surj_ker⟩ := h_generic.exists_quotient _ e he he'
  obtain ⟨l, hl, rfl⟩ := (A.existsUnique_hom ⟨d, A.rank⟩ f fun i ↦ (0, single i 1)).exists
  refine ⟨_, l, h_kill, fun D g hg ↦ ?_, h_surj_ker⟩
  -- A map out of the cut pair is given by a map of tests and the images of the basis.
  obtain ⟨g₀, hg₀, hg₀_unique⟩ := h_factor _ _ hg
  refine (existsUnique_congr fun s ↦ ⟨fun hs ↦ ?_, ?_⟩).1
    (existsUnique_hom ⟨d, A.rank⟩ D g₀ fun i ↦ g.2 (single i 1))
  · -- `l ≫ s` and `g` have the same map of tests and send the basis to the same elements.
    -- `simpa [*]`: `hg₀` is stated between `toTest.obj` objects, the goal between `.test` objects,
    -- and a named simp set fails to match them.
    have h_comp : (∀ i : Fin A.rank, (l ≫ s).snd (single i 1) = g.snd (single i 1)) ∧
        (l ≫ s).fst = g.fst := by
      simpa [*]
    exact (A.existsUnique_hom D g.fst fun i ↦ g.snd (single i 1)).unique h_comp ⟨fun i ↦ rfl, rfl⟩
  · rintro rfl
    exact ⟨by simp [hl], hg₀_unique _ rfl⟩

/-- Let `X` be a functor from `k`-algebras to types such that every field-valued point of `X` lies
in an étale chart with `n` coordinates (`IsChartCovered n X`). Then `freeAb X`, the functor
`A ↦ ℤ[X(A)]`, satisfies `New.Variety.PairRestrictBijective`. With `T = S[1/p]`, this means that
pull-back along `B_{S,M} → T` is bijective in every degree, from the cohomology of `S ↦ ℤ[X(T)]` on
`p`-adic tests `S` to that of `(S, M) ↦ ℤ[X(B_{S,M})]` on pairs `(S, M)`, both with coefficients
`T`. -/
lemma IsChartCovered.pairRestrictBijective {n : ℕ} {X : CommAlg k ⥤ Type 1}
    [h : IsChartCovered n X] :
    PairRestrictBijective (freeAb X) := by
  -- Points in charts form a subfunctor `V` that is dense on tests and on pairs, so one may
  -- compare `V(T)` with its preimage in `X(B_{S,M})`. Over each point of `V(T)` the lifts are
  -- represented by one pair `(S, T ^ n)`, whose coefficients are `T` again (`HasUniversalPoints`).
  let V : Subfunctor X := ⨆ a : EtaleChart n X, a.locus
  have V_loc : IsZariskiLocallyTop (𝟭 _ ⋙ forget₂ ..) (V.whisker (𝟭 _)) :=
    isZariskiLocallyTop_of_open_cover fun K hK x ↦ by
      obtain ⟨a, ha⟩ := IsChartCovered.exists_chart K hK x
      exact ⟨a.locus, a.isOpenSubfunctor, ha, le_iSup locus a⟩
  -- The coefficients are additive on tests and on pairs, which gives Zariski descent; so `V`,
  -- being locally everything, is dense.
  have dense_T : IsCohomDense genericCoeff (V.whisker genericOver) :=
    hasZariskiDescent_genericOver (𝟭 _) hasPartitions_genericCoeff (V_loc.whisker _)
  let ρ : pairAlg ⋙ X ⟶ (HodgeTatePair.toTest ⋙ genericOver) ⋙ X := Functor.whiskerRight toGeneric X
  let V' : Subfunctor ((HodgeTatePair.toTest ⋙ genericOver) ⋙ X) :=
    V.whisker (HodgeTatePair.toTest ⋙ genericOver)
  have dense_B : IsCohomDense scalarCoeff (V'.preimage ρ) :=
    (hasZariskiDescent_genericOver _ hasPartitions_scalarCoeff (V_loc.whisker _)).preimage ρ
  refine ((Comparison.of ..).isBijective_congr (p := (V.whisker genericOver).ι)
      (V'.fromPreimage_ι ρ).symm dense_T.isCohomEquiv dense_B.isCohomEquiv).2
    (HasUniversalPoints.isBijective ?_)
  -- A point of `V(T)` is `X.map ζ a.point` for a chart `a`. Lift the values of its coordinates to
  -- `b i` in `B_S`; as `a` is étale, `ζ` lifts to `s : a.coordRing ⟶ B_{S, T ^ n}` with
  -- `a.coordinate i ↦ b i + e_i` (`etale_polyEval_iff`).
  rintro c ⟨_, _, ⟨_, ⟨a, ⟨⟩⟩, ⟨⟩⟩, ⟨ζ : a.coordRing ⟶ genericOver.obj c⟩, ⟨⟩⟩
  obtain ⟨h_proj_surj, -, -⟩ := exact_mulMu_proj c
  choose b hb using fun i : Fin n ↦ h_proj_surj (ζ (a.coordinate i))
  obtain ⟨s, rfl, hs⟩ := (etale_polyEval_iff.1 a.etale _ (isSquareZero_toGeneric ⟨c, n⟩) ζ
    (fun i ↦ ⟨⟨b i, _, single i 1⟩, hb i⟩) fun _ ↦ rfl).exists
  -- `s` is universal: a lift `ψ` over `f` comes from exactly one map of pairs `g` over `f`.
  have h_existsUnique_hom_of_lift (D : HodgeTatePair) (f : c ⟶ D.test)
    (ψ : a.coordRing ⟶ pairAlg.obj D)
      (hψ : (s ≫ toGeneric.app _) ≫ genericOver.map f = ψ ≫ toGeneric.app D) :
      ∃! g : (⟨c, n⟩ : HodgeTatePair) ⟶ D, s ≫ pairAlg.map g = ψ ∧ g.1 = f := by
    -- In `B_{S'}`, `ψ r` and the image of `s r` differ by some `mulMu D.test t`.
    obtain ⟨-, h_mulMu_inj, h_exact⟩ := exact_mulMu_proj D.test
    have h_exists_mulMu_eq (r : a.coordRing) :
        ∃ t, mulMu D.test t = (ψ r).val.fst - thickeningOver.map f (s r).val.fst := by
      refine (h_exact _).1 ?_
      erw [map_sub, proj.naturality_apply, (s _).2, (ψ _).2, ConcreteCategory.congr_hom hψ r,
        sub_self]
    choose t ht using h_exists_mulMu_eq
    -- `g` must send `e_i` to `(t (a.coordinate i), M'-part of ψ (a.coordinate i))`, and coordinates
    -- determine lifts.
    refine (existsUnique_congr fun g ↦ and_congr_left ?_).1
      (existsUnique_hom ⟨c, n⟩ D f fun i ↦ (t (a.coordinate i), (ψ (a.coordinate i)).val.snd.snd))
    rintro rfl
    refine (forall_congr' fun i ↦ ?_).trans ⟨a.lift_unique D.isSquareZero_toGeneric hψ, by tauto⟩
    -- compare components; `mulMu` is injective, and `g` acts on `b + e` by `f b + mulMu (g e).1`
    erw [Prod.ext_iff, ← h_mulMu_inj.eq_iff, ht, eq_sub_iff_add_eq', Subtype.ext_iff,
      Prod.ext_iff, Prod.ext_iff, and_iff_right (ConcreteCategory.congr_hom hψ _),
      AlgHom.comp_apply, hs]
    rfl
  have h_map_comp_point {A A' : CommAlg k} (φ : a.coordRing ⟶ A) (φ' : A ⟶ A') :
      X.map (φ ≫ φ') a.point = X.map φ' (X.map φ a.point) := X.map_comp_apply ..
  -- `using!`: the first and last goals hold only up to unfolding `toTest` and the subfunctor maps.
  refine ⟨⟨c, n⟩, ⟨X.map s a.point, le_iSup locus a _ ⟨⟨s ≫ _⟩, h_map_comp_point ..⟩⟩, 𝟙 c,
    by simpa using! Subtype.ext (h_map_comp_point ..).symm, fun D ⟨x, _⟩ f hx ↦ ?_,
    by simpa using! bijective_id⟩
  -- A point `x` of `X(B_D)` that reduces into the chart lies in it, the chart being open.
  replace hx :
      X.map ((s ≫ toGeneric.app _) ≫ genericOver.map f) a.point = X.map (toGeneric.app D) x :=
    (h_map_comp_point ..).trans (congrArg Subtype.val hx.symm)
  obtain ⟨⟨ψ : _ ⟶ _⟩, ⟨⟩⟩ := a.isOpenSubfunctor.mem_of_isSquareZero _ D.isSquareZero_toGeneric x
    ⟨_, hx⟩
  refine (existsUnique_congr fun g ↦ and_congr ?_ (by simp [HodgeTatePair.toTest])).1
    (h_existsUnique_hom_of_lift D f ψ (a.eq_comp_of_map_point_eq _ hx))
  erw [Subtype.ext_iff, ← (h_map_comp_point ..).congr_left, (a.injective _).eq_iff]

end HodgeTateRestriction

end New.Variety

end
