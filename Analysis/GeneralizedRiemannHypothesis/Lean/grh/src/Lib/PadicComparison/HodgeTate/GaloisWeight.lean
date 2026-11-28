import Lib.PadicComparison.HodgeTate.Map

/-!
# Galois twists and the weight of the Hodge–Tate map

An element `g` of `Gal(ℚ̄_p/ℚ_p)` twists a p-adic test `c` by precomposing its structure map
`O_C → R` with `g` (`New.Variety.PadicTest.twist`). The twist leaves the rings `R`, `K = R[1/p]` and
`B = W(R♭)[1/p] / (ker θ)²` unchanged. Write `μ = [ε] − 1` and `χ` for the cyclotomic character.
Suppose `g` fixes `E` and `New.Variety.restrictToPairs ξ` is the image under
`New.Variety.hodgeTateMap h` of a Hodge class defined over `E`, and that `χ(g⁻¹)` is the image in
ℚ̄_p of some `t : k`. Then the twist by `g` multiplies `New.Variety.restrictToPairs ξ` by
`χ(g⁻¹)^h`.

## Main definitions and results

* `New.Variety.thickeningOver.mulMu_twist`: the inclusion `ι : K → B` (multiplication by `μ`)
  changes by the cyclotomic character `χ(g⁻¹)` (`New.cyclotomicGp`), as `g⁻¹ μ ≡ χ(g⁻¹) μ` modulo
  `μ²`.
* `New.Variety.HodgeTatePair.galTwist`: the twist on pairs `(c, K^n)` (`New.Variety.HodgeTatePair`).
* `New.Variety.HodgeTatePair.contractionPow_galTwist`: the classes
  `New.Variety.HodgeTatePair.contractionPow` (the `h`-th power of the contraction class, then the
  projection to degree zero) are compatible with the twist.

Notions from other files:
* `New.Variety.PadicTest`: A p-adic test: a non-empty family of cells (`New.Variety.IsCell`) with a
  ring map from O_C to their product R.
* `New.Variety.thickeningOver.mulMu`: The additive map ι: K → B sending θ(x) to the class of μx,
  where μ = [ε] − 1.
* `New.Variety.HodgeTatePair`: A pair (S,M) of a p-adic test S and a free module M of finite rank
  over T = S[1/p]; `New.Variety.HodgeTatePair.pairAlg` sends it to B_{S,M} = B_S ×_T (T ⊕ M).
* `New.Variety.hodgeTateMap`: The map λ_h: restrict a Hodge class along B_{S,M} → T ⊕ M, apply the
  h-th power of the contraction class, and project ⋀M to degree zero.
* `New.Variety.restrictToPairs`: Restriction along B_{S,M} → T, from the cohomology of N(T) on
  p-adic tests S to that of N(B_{S,M}) on pairs. `New.Variety.PairRestrictBijective` says that it is
  bijective in all degrees.

## Relation to the literature

Known; see `Lib.PadicComparison.HodgeTate.PeriodMap` for sources.
-/

noncomputable section

namespace New.Variety

/-! ## Twisting p-adic tests, pairs and contraction classes -/

section GaloisTwist

open CategoryTheory Period PadicTest MulSemiringAction AddCommGrpCat TotalH

variable {p : ℕ} {k : Type} [Field k]

/-- The structure map `ℂ_p → R[1/p]` of the `g`-twist of a test `c` is `g` followed by the
structure map of `c`. -/
lemma PadicTest.genericStructureMap_twist [ThePrime p] (g : Gp p) (c : PadicTest) (z : ℂ_[p]) :
    (twist g c).genericStructureMap z = c.genericStructureMap (g • z) := by
  -- Ring maps out of the localization `ℂ_[p]` of `OC` at `p` are determined on `OC`.
  have h_eq : (twist g c).genericStructureMap =
      c.genericStructureMap.comp (toRingHom (Gp p) ℂ_[p] g) := by
    refine IsLocalization.ringHom_ext (.powers (p : OC)) ?_
    ext
    exact (genericStructureMap_coe ..).trans (c.genericStructureMap_coe _).symm
  exact RingHom.congr_fun h_eq z

/-- The lift of the `g`-twist of a test `c` to its thickening is `g` followed by the lift for `c`:
both lifts reduce to the structure map, and the lift is unique (`PadicTest.eq_uniqueLift`). -/
lemma PadicTest.uniqueLift_comp_eq_uniqueLift_twist [ThePrime p] (g : Gp p) (c : PadicTest) :
    c.uniqueLift.comp (g.toAlgHom.restrictScalars ℤ_[p]) = (PadicTest.twist g c).uniqueLift := by
  refine (PadicTest.twist g c).eq_uniqueLift _ fun z ↦ ?_
  rw [c.genericStructureMap_twist, smul_coe_Cp]
  exact c.thickeningProj_uniqueLift (g z)

/-- For a `p`-adic test `c` with ring `R`, let `ι = mulMu` be the additive map from `K = R[1/p]` to
`B = W(R♭)[1/p]/(ker θ)²` sending `θ(x)` to the class of `μx`, where `μ = [ε] − 1`. For `g ∈ G_p`,
the `g`-twist of `c` has the same `K` and `B`, and `ι` of `c` at `t` equals `ι` of the twist at
`χ(g⁻¹) t`. Here `χ` is the cyclotomic character, and `χ(g⁻¹)` is mapped into `K` by the structure
map `ℂ_p → K`. -/
lemma thickeningOver.mulMu_twist [EmbeddedInQpBar p k] (g : Gp p) (c : PadicTest)
    (t : c.GenericRing) :
    mulMu c t = mulMu (PadicTest.twist g c)
        (c.genericStructureMap (algebraMap ℤ_[p] (PadicAlgCl p) (cyclotomicGp g⁻¹).val) * t) := by
  -- The ring `c.Thickening` is the same for `c` and its twist `c'`, but the structure map is
  -- twisted by `g`. So `μ` for `c` is `g⁻¹ • μ ≡ χ(g⁻¹) μ` for `c'`, modulo `μ²`, which is zero in
  -- `c'.Thickening`.
  let c' : PadicTest := PadicTest.twist g c
  obtain ⟨x, rfl⟩ : ∃ x : c.Thickening, c.thickeningProj x = t := c.thickeningProj_surjective t
  obtain ⟨a, ha⟩ : ∃ a : Ainf, g⁻¹ • mu - (cyclotomicGp g⁻¹ : ℤ_[p]) • mu = mu ^ 2 * a :=
    Lift.mu_sq_dvd_smul_mu_sub g⁻¹
  have h_tw (a : Ainf) :
      algebraMap Ainf c.Thickening (g • a) = algebraMap Ainf c'.Thickening a := by
    refine congrArg (algebraMap (WittVector p c.TiltRing) c.Thickening) ?_
    ext
    exact (congrArg _ (pow_one _)).trans (tiltMap_comp ..).symm
  have h_mu : mu = g • ((cyclotomicGp g⁻¹).val • mu + mu ^ 2 * a) :=
    inv_smul_eq_iff.mp (eq_add_of_sub_eq' ha)
  have h_sq : algebraMap Ainf c'.Thickening mu ^ 2 = 0 :=
    c'.ker_thickeningProj_sq.le (Ideal.pow_mem_pow c'.thetaGeneric_mu 2)
  rw [mulMu_thickeningProj, h_mu, h_tw]
  -- On the right, lift the scalar to `c.Thickening` along `c.uniqueLift` and move it out of `mulMu`
  -- by `mulMu_proj_mul`. `erw`: the thickening and the generic ring of `c'` are those of `c` only
  -- up to unfolding the twist
  erw [← c.thickeningProj_uniqueLift, mulMu_proj_mul, mulMu_thickeningProj, AlgHom.commutes]
  simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, h_sq]
  -- what remains is associativity, in rings that agree only up to unfolding the twist
  exact mul_assoc _ _ _

/-- The natural map from `New.Variety.genericCoeff` after the `g`-twist to
`New.Variety.genericCoeff`. It is the identity on each `R[1/p]`. -/
def twistGenericCoeff [ThePrime p] (g : Gp p) :
    PadicTest.twist g ⋙ genericCoeff ⟶ genericCoeff where
  app c := ofHom (AddMonoidHom.id (ULift c.GenericRing))

/-- For `g` in the Galois group of `ℚ̄_p/ℚ_p`, the endofunctor of `New.Variety.HodgeTatePair`
twisting the structure map of the underlying test by `g` and keeping all other data. -/
def HodgeTatePair.galTwist [EmbeddedInQpBar p k] (g : Gp p) : HodgeTatePair ⥤ HodgeTatePair where
  obj X := ⟨PadicTest.twist g X.test, X.rank⟩
  map f := ⟨(PadicTest.twist g).map f.1, f.2⟩

/-- The identity of the exterior algebra of K^n, K = R[1/p], as a natural map from
`New.Variety.HodgeTatePair.formCoeff` to `New.Variety.HodgeTatePair.formCoeff` composed with the
g-twist. -/
def HodgeTatePair.twistForms [EmbeddedInQpBar p k] (g : Gp p) :
    formCoeff ⟶ galTwist g ⋙ formCoeff where
  app X := ofHom (AddMonoidHom.id (ULift
    (ExteriorAlgebra X.test.GenericRing ((toHodgeTest.obj X).Index → X.test.GenericRing))))

-- Unsealed, the closing `rfl` unfolds `contraction` instead of comparing its arguments.
seal contraction in
/-- The class `contractionPow h` is compatible with the `g`-twist. Restrict it along the twist of
pairs. Compose it with the identification `twistGenericCoeff g` of the coefficients. Then pull it
back along the identification `twistForms g` of the exterior algebras. The result is the class
`contractionPow h` itself. -/
lemma HodgeTatePair.contractionPow_galTwist [EmbeddedInQpBar p k] (g : Gp p) (h : ℕ) :
    pullbackAlong (twistForms g)
        (comp (TotalH.map (restrictAlong (galTwist g)) (contractionPow h))
          (TotalH.homClass (toTest.whiskerLeft (twistGenericCoeff g)))) =
      contractionPow h := by
  induction h with
  | zero =>
    -- both sides are the class of the projection to degree zero
    rw [contractionPow, map_homClass, pullbackAlong_pullbackAlong]
    -- `erw`: the exterior algebras of `Index → baseAlg` and of `Index → X.test.GenericRing` carry
    -- the same module structure only up to unfolding, so `homClass_comp` matches only with `erw`
    erw [← homClass_comp]
    rfl
  | succ h ih =>
    -- Move `twistForms g` past the class of the cocycle `contractionCocycle`, then use the
    -- induction hypothesis. The side goal, that `twistForms g` carries the twisted cocycle to
    -- `contractionCocycle`, holds by definition.
    rw [contractionPow, map_comp_assoc, Cocycle.map_cohomClass_restrict,
      ← comp_assoc_of_sq (contractionCocycle.cohomClass_naturality ..), ih]
    exact fun _ _ _ ↦ rfl

end GaloisTwist

/-! ## Galois action in weight h -/

section GaloisWeight

open CategoryTheory Functor TotalH HodgeTatePair

variable {p : ℕ} {k E : Type} [Field k] [EmbeddedInQpBar p k] {g : Gp p} [Field E] [Algebra E k]

/-- Let `g` in `Gal(ℚ̄_p/ℚ_p)` fix the subfield `E` of `k ⊆ ℚ̄_p`. Let `x` be a Hodge class of `N`
over `E`, meaning a degree-`q` Ext class from `(A, M) ↦ N(A ⊕ M)` to `(A, M) ↦ ⋀_A M`. Let `ξ` be a
degree-`n` class on `p`-adic tests `S` (families of valuation rings over O_C) with coefficients
`S[1/p]`, such that `hodgeTateMap h x.baseChange = restrictToPairs ξ`. Here `hodgeTateMap h` uses
the `h`-th power of the contraction class, and `restrictToPairs` is the restriction from tests to
pairs of a test and a free module. Let `t : k` map to the value of the cyclotomic character at
`g⁻¹`. Let `τ` be the identity of each ring `S[1/p]`, viewed as an `E`-algebra map from the ring of
`S` to that of its twist by `g`. Then the pull-back of `ξ` along the twist by `g`, `τ` and the
identification `twistGenericCoeff g` of the coefficients has the same image under `restrictToPairs`
as `t ^ h • ξ`. -/
theorem hodgeTateMap_galois_twist
    (hg : ∀ z : E, g (algebraMap k (PadicAlgCl p) (algebraMap E k z)) =
      algebraMap k (PadicAlgCl p) (algebraMap E k z))
    {N : AbFunctor (CommAlg E)} {q h n : ℕ} {x : HodgeH N q} {t : k}
    {ξ : H (genericOver ⋙ restrictAlg E k ⋙ N) genericCoeff n}
    (hξ : hodgeTateMap h x.baseChange = restrictToPairs ξ)
    (ht : algebraMap k (PadicAlgCl p) t = algebraMap ℤ_[p] (PadicAlgCl p) (cyclotomicGp g⁻¹).val) :
    let τ : genericOver ⋙ restrictAlg E k ⟶ PadicTest.twist g ⋙ genericOver ⋙ restrictAlg E k :=
      .mk fun (c : PadicTest) ↦
      CommAlg.homOfRingHom (.id c.GenericRing) fun (z : E) ↦ by
        symm
        erw [c.genericStructureMap_twist, smul_coe_Cp, hg]
        rfl
    restrictToPairs
        ((Comparison.of (PadicTest.twist g) (twistGenericCoeff g)).pull (whiskerRight τ N) n ξ :
        H (genericOver ⋙ restrictAlg E k ⋙ N) genericCoeff n) =
      restrictToPairs (t ^ h • ξ) := by
  -- The twist by `g`, combined with scaling the module of a pair by `t`, gives a map `T` over `E`
  -- from `pairAlg` to its twist. The claim is then a computation of Yoneda products: twisting moves
  -- past `contractionPow h` (`contractionPow_galTwist`) and turns into the scaling
  -- `HodgeTest.scaleModule t` (`pull_twist`).
  intro τ
  let φ : HodgeTest k ⥤ HodgeTest E := (HodgeTest.baseComparison (k := k) (E := E)).functor
  let σ : toHodgeTest ⋙ φ ⟶ galTwist g ⋙ toHodgeTest ⋙ φ :=
    toHodgeTest.whiskerLeft (HodgeTest.scaleModule t φ) ≫ .mk fun X ↦ ⟨τ X.test, .id⟩
  let B : HodgeTatePair ⥤ CommAlg E := (toHodgeTest ⋙ φ) ⋙ HodgeTest.sqZeroExt
  let S : B ⟶ galTwist g ⋙ B := whiskerRight σ HodgeTest.sqZeroExt
  -- The components of `T`: the identity on `thickeningOver` and `S` on the square-zero extension.
  -- They are `E`-linear because `g` fixes `E`.
  let A : HodgeTatePair ⥤ CommAlg E := pairAlg ⋙ restrictAlg E k
  let T₀ (X : HodgeTatePair) : A.obj X ⟶ (galTwist g ⋙ A).obj X := CommAlg.homOfRingHom
    ((RingHom.prodMap (.id _) (S X).hom.toRingHom).restrict _ _ (by tauto)) fun z ↦
      Subtype.ext (Prod.ext ((congrArg _ (hg z).symm).trans (DFunLike.congr_fun
        (PadicTest.uniqueLift_comp_eq_uniqueLift_twist g X.test) _)) ((S X).hom.commutes' z))
  have h_nat (X Y : HodgeTatePair) (f : X ⟶ Y) :
      A.map f ≫ T₀ Y = T₀ X ≫ (galTwist g ⋙ A).map f := by
    -- The factor `t` from `HodgeTest.scaleModule` is the factor `cyclotomicGp g⁻¹` by which the
    -- twist changes `mulMu` (`thickeningOver.mulMu_twist`).
    have h_scal (m : Fin X.rank → X.GenericRing) :
        Y.test.genericStructureMap (algebraMap ℤ_[p] (PadicAlgCl p) (cyclotomicGp g⁻¹).val) *
          (show Y.test.GenericRing from (f.snd m).1) = (f.snd (t • m)).1 := by
      rw [← ht, ← algebraMap_smul X.GenericRing, map_smulₛₗ, RingHom.coe_coe, AlgHom.commutes]
      rfl
    -- first component: `mulMu` and `h_scal`; second component: `S` is natural
    ext z
    refine Subtype.ext (Prod.ext ?_ (ConcreteCategory.congr_hom (S.naturality f) _))
    exact congrArg (_ + ·) ((thickeningOver.mulMu_twist g Y.test _).trans (congrArg _ (h_scal _)))
  -- Only the second component of `T` is used below.
  obtain ⟨T, hT⟩ : ∃ T : A ⟶ galTwist g ⋙ A,
      ∀ (X : HodgeTatePair) (x : A.obj X), (T X x).val.snd = S X x.val.snd :=
    ⟨⟨T₀, h_nat⟩, fun _ _ ↦ rfl⟩
  let y : H (A ⋙ N) (toHodgeTest ⋙ hodgeCoeff) q :=
    (Comparison.restrict toHodgeTest _).pull (whiskerRight toSqZero (restrictAlg E k ⋙ N)) q
      x.baseChange
  let α : TotalH (A ⋙ N) (galTwist g ⋙ A ⋙ N) := homClass (whiskerRight T N)
  let β : TotalH (galTwist g ⋙ scalarCoeff) scalarCoeff :=
    homClass (toTest.whiskerLeft (twistGenericCoeff g))
  let u : TotalH (galTwist g ⋙ formCoeff) scalarCoeff :=
    TotalH.comp (TotalH.map (restrictAlong (galTwist g)) (contractionPow h)) β
  let s : formCoeff ⟶ formCoeff := toHodgeTest.whiskerLeft (HodgeTest.scaleModule t hodgeCoeff)

  have h_tw : pullbackAlong (twistForms g) u = contractionPow h := contractionPow_galTwist g h
  -- The class `y` comes from the Hodge class `x` over `E`, so its twist along `T` is its scaling
  -- by `t`.
  have h_pull : TotalH.comp α (TotalH.map (restrictAlong (galTwist g)) y.toTotalH) =
      TotalH.comp y.toTotalH (homClass (s ≫ twistForms g)) := by
    refine pull_twist (Comparison.pull_trans _) σ (whiskerRight T N) (by ext; rfl) ?_
    ext : 2
    -- `using!`: the goal carries identity whiskerings `toHodgeTest.whiskerLeft (𝟙 _)` that `simp`
    -- does not remove; they unfold to `𝟙`
    simpa using! (N.map_commSq ⟨by ext; apply hT⟩).w
  -- Here `restrictToPairs ξ = TotalH.comp y.toTotalH (contractionPow h)` by `hξ`.
  calc
    _ = TotalH.comp α
        (TotalH.comp (TotalH.map (restrictAlong (galTwist g)) (restrictToPairs ξ)) β) := by
      -- `erw`: after unfolding `restrictToPairs`, the classes live over `(restrictAlong F).obj G`
      -- on one side and `F ⋙ G` on the other, which agree only up to unfolding
      erw [map_of, of_comp_homClass, pullbackAlong_of]
      simp [restrictToPairs, Comparison.pull, H.map, H.push, mapExactFunctor_mapExactFunctor,
        mapExtAddHom, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
      congr 3 with : 2
      exact (N.map_commSq ⟨by ext; apply congrArg TrivSqZeroExt.fst (hT ..)⟩).w.symm
    _ = TotalH.comp α (TotalH.comp (TotalH.map (restrictAlong (galTwist g)) y.toTotalH) u) := by
      rw [← hξ]
      exact congrArg _ (TotalH.map_comp_assoc ..)
    _ = TotalH.comp y.toTotalH (pullbackAlong (s ≫ twistForms g) u) := comp_assoc_of_sq h_pull _
    _ = TotalH.comp y.toTotalH (pullbackAlong s (contractionPow h)) := by
      rw [← pullbackAlong_pullbackAlong, h_tw]
    _ = restrictToPairs (t ^ h • ξ) := by
      -- scaling the module by `t` multiplies `contractionPow h` by `t ^ h`
      rw [restrictToPairs.map_smul, ← hξ, scaleModule_comp_contractionPow, comp_smul]
      rfl

end GaloisWeight

end New.Variety

end
