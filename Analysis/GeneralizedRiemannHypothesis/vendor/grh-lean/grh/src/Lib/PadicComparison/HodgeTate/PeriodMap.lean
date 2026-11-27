import Lib.GaloisRep.Main.LocalConditions
import Lib.PadicComparison.HodgeTate.GaloisWeight
import Lib.PadicComparison.Primitive.ComparisonTheorem
import Lib.PadicComparison.Primitive.Periods

/-!
# The period map for ℓ-adic cohomology on p-adic tests, and Hodge–Tate weights

This file compares the geometric cohomology `New.Variety.ellAdicCohom R Ω n` of an `R`-scheme `Y`
(`Ω` an `R`-algebra on which a group `Γ` acts by ring maps fixing the image of `R`), written
`V^n(Y)`, with the cohomology of the points of `Y` in `p`-adic tests. A vector has weight `h`
(`New.HasHodgeTateWeight`) if Galois acts on it by the `(-h)`-th power of the cyclotomic character.

## Main definitions and results

* `New.Variety.toTwistAlg`: the identity of a `p`-adic test as an `R`-algebra map to its Galois
  twist.
* `New.Variety.exists_period_map`: the period map is natural, Galois equivariant, and bijective for
  proper charted `Y`. It is the pull-back along the comparison of
  `New.Variety.exists_primitive_period_comparison`.
* `New.Variety.exists_hasHodgeTateWeight`: the value of the Hodge–Tate map on a Hodge class comes
  from a vector of weight `h`, naturally in maps to `Y`.

Notions from other files:
* `New.Variety.PadicTest`: A p-adic test c: a non-empty family of cells, whose product is the ring
  `c.ProdRing`, with a ring map from O_C, the integers of ℂ_p, to that product.
* `New.Variety.PadicTest.twist`: For g in G_p, the endofunctor of p-adic tests that keeps the ring
  and precomposes its structure map O_C → c.ProdRing with the action of g.

## Relation to the literature

Known result: The primitive comparison theorem and the period isomorphism. Here coefficients are
constant, schemes are proper and charted (`New.Variety.IsCharted`), cohomology is taken on test
rings, and the maximal ideal is put into the coefficients. The result is deduced from the duality
comparison on products of projective lines, without almost finiteness. Source: P. Scholze, p-adic
Hodge theory for rigid-analytic varieties, Forum Math. Pi 1 (2013), Thm 1.3 and 5.1; for the method,
B. Zavyalov, Poincaré duality in abstract 6-functor formalisms, arXiv 2301.03821, Thm 3.3.3 and
Appl. 1.3.4; Li–Reinecke–Zavyalov, arXiv 2410.08200, §6.4.

Known result: The Hodge–Tate map from Hodge cohomology to p-adic étale cohomology. The target here
is cohomology on test rings, which is not identified with étale cohomology. Only the natural
multiplicative map into the part of weight h is built, from the torsor of lifts modulo the square of
the kernel of Fontaine's map, and bijectivity is not proved. Source: Scholze, p-adic Hodge theory
for rigid-analytic varieties, Forum Math. Pi 1 (2013), Cor. 1.8; the construction follows Bhatt, The
Hodge–Tate decomposition via perfectoid spaces, Arizona Winter School 2017, §3.4.
-/

/-!
## The period map on p-adic tests

The period map compares the geometric `p`-adic cohomology `New.Variety.ellAdicCohom R Ω n` of an
`R`-scheme `Y`, extended to a period ring `K`, with the cohomology of the points of `Y` in `p`-adic
tests (`New.Variety.PadicTest`, `New.Variety.testPoints`) with coefficients `Ψ`. Here `θ` identifies
`Ψ c` with `K ⊗_S (S ⊗_{A_inf} W(c^♭))^`, the hat denoting `p`-adic completion, for an
`A_inf`-algebra `S`.
-/

namespace New.Variety

open CategoryTheory TensorProduct Function AlgebraicGeometry Functor AlgebraTensorModule Period
  Comparison PadicTest ModuleCat.Algebra Module

variable {p : ℕ} [ThePrime p] {R : CommRingCat} [Algebra R OC] [Algebra R Ω]
  {e : Ω →+* PadicAlgCl p} (he : ∀ r : R, e (algebraMap R Ω r) = (algebraMap R OC r : ℂ_[p]))
  {S : Type} [CommRing S] [Algebra Ainf S]
  (K : Type) [CommRing K] [Algebra S K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] {Ψ : PadicTest ⥤ ModuleCat K}
  (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ) (n : ℕ)
  {Γ : Type*} [Group Γ] [MulSemiringAction Γ Ω] [SMulCommClass Γ R Ω]
  {j : Γ → Gp p} (hj : ∀ (g : Γ) (x : Ω), j g (e x) = e (g • x))

/-- The identity of a test is a map of `R`-algebras to its twist by `j g`. Here
`algFunctor ⋙ restrictAlg R OC` sends a test `c` to the ring `c.ProdRing`, made an `R`-algebra
through `R → O_C`. -/
noncomputable def toTwistAlg (g : Γ) :
    algFunctor ⋙ restrictAlg R OC ⟶ PadicTest.twist (j g) ⋙ algFunctor ⋙ restrictAlg R OC where
  -- `g` fixes the image of `R` in `Ω`, so `j g` fixes its image in `OC`.
  app c := CommAlg.homOfRingHom (RingHom.id ((algFunctor ⋙ restrictAlg R OC).obj c)) fun z ↦
    congrArg c.structureMap (Subtype.ext (by simp [← he, hj]))

/-- A point of `Y` in a test is a point of `Y` in the twist of the test by `j g`. -/
noncomputable def toTwistPoints (g : Γ) (Y : Over (Spec R)) :
    testPoints.obj Y ⟶ PadicTest.twist (j g) ⋙ testPoints.obj Y :=
  whiskerRight (toTwistAlg he hj g) (algPointsOf R R Y)

/-- `ℚ_p` is a localization of `ℤ_p`, so the two scalar actions on `K ⊗ M` agree. -/
instance (M : ModuleCat ℚ_[p]) : CompatibleSMul ℤ_[p] ℚ_[p] K M :=
  IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors _) ..

section

variable {K n}

/-- The element `θ (a ⊗ 1 ⊗ w)` of `Ψ c`, for `a` in `K` and a Witt vector `w` over the tilt of
the test `c`. -/
noncomputable abbrev periodTmul (c : PadicTest) (a : K) (w : WittVector p c.TiltRing) : Ψ.obj c :=
  θ.hom.app c (a ⊗ₜ AdicCompletion.of _ _ (1 ⊗ₜ w))

/-- The map of coefficients `β`, from the twist of `Ψ` by `g` to `Ψ`, acts as `σ` on the elements
`θ (a ⊗ 1 ⊗ w)`, where `w` is a Witt vector whose coordinates are fixed by Frobenius.
`moduleCoeff Ψ` is `Ψ` with values lifted by `ULift`, and `⟨_⟩` wraps an element of `Ψ c`. -/
def ActsAsOnFrobeniusFixed (g : Gp p) (β : PadicTest.twist g ⋙ moduleCoeff Ψ ⟶ moduleCoeff Ψ)
    (σ : K → K) : Prop :=
  ∀ (c : PadicTest) (a : K) (w : WittVector p c.TiltRing), (∀ i : ℕ, w.coeff i ^ p = w.coeff i) →
    β.app c ⟨periodTmul θ ((PadicTest.twist g).obj c) a w⟩ = ⟨periodTmul θ c (σ a) w⟩

/-- A `p`-adic period map: `K`-linear maps `J Y` from `K ⊗ V^n(Y)` to `H^n` of the points of `Y`
in tests, with coefficients `Ψ`, that are natural, Galois equivariant and bijective on proper
charted `Y`. Here `V^n(Y)` is the geometric `p`-adic cohomology `ellAdicCohom R Ω n` of `Y`. -/
structure IsPadicPeriodMap
    (J : ∀ Y : Over (Spec R), K ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩ →ₗ[K]
      H (freeAb.obj (testPoints.obj Y)) (moduleCoeff Ψ) n) : Prop where
  /-- `J` commutes with the pull-back along `f : W ⟶ Y`. -/
  natural (W Y : Over (Spec R)) (f : W ⟶ Y) (x : K ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩) :
    J W ((((ellAdicCohom R Ω n).map f.op).hom.restrictScalars ℤ_[p]).baseChange K x) =
      H.map (moduleCoeff Ψ) (freeAb.map (testPoints.map f)) n (J Y x)
  /-- `J` carries `σ ⊗ g` to the pull-back along `β` and the twist by `j g`, if `β` acts as `σ`. -/
  equivariant (Y : Over (Spec R)) (g : Γ) (σ : K →ₗ[ℤ_[p]] K)
    (β : PadicTest.twist (j g) ⋙ moduleCoeff Ψ ⟶ moduleCoeff Ψ)
    (hβ : ActsAsOnFrobeniusFixed θ (j g) β σ) (x : K ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩) :
    J Y (TensorProduct.map σ
        ((ellAdicCohom.galoisAction R Ω Γ Y n g).restrictScalars ℤ_[p]) x) =
      (Comparison.of (PadicTest.twist (j g)) β).pull (freeAbMap (toTwistPoints he hj g Y)) n
        (J Y x)
  /-- `J Y` is bijective if `Y` is proper and charted over `Ω`. -/
  bijective (Y : Over (Spec R)) [IsCharted Y Ω] [IsProper Y.hom] : Bijective (J Y)

end

omit [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] in
/-- Let `γ` send `a ⊗ x` to `θ (a ⊗ 1 ⊗ w)`, where `w` is the Witt vector over the tilt obtained
from `x`, and let `β` act as `σ` on the elements `θ (a ⊗ 1 ⊗ w)` with `w` fixed by Frobenius
(`ActsAsOnFrobeniusFixed`). Then the comparison `x ↦ γ (σ a ⊗ x)` is the comparison
`x ↦ γ (a ⊗ x)` followed by `β`, since Witt vectors of locally constant `𝔽_p`-valued functions are
fixed by Frobenius. -/
private lemma coeffHom_eq_coeffHom_trans_of_actsAsOnFrobeniusFixed
    (γ : genericTest ⋙ asModules (wittLocConst p) ⋙ tensorWith K K ⟶ Ψ)
    (hγ : ∀ (c : PadicTest) (a : K) (x : (wittLocConst p).obj (genericTest.obj c)),
      γ.app c (a ⊗ₜ x) =
        θ.hom.app c (a ⊗ₜ wittToPeriodAlg S (tilt.obj c)
          (WittVector.map (locConstToTilt.app c).hom.toRingHom x)))
    {g : Gp p} {σ : K →ₗ[ℤ_[p]] K} {β : PadicTest.twist g ⋙ moduleCoeff Ψ ⟶ moduleCoeff Ψ}
    (hβ : ActsAsOnFrobeniusFixed θ g β σ) (a : K) :
    -- `cmp b` is the comparison `x ↦ γ (b ⊗ x)`
    let cmp (b : K) : Comparison ellAdicCoeff (moduleCoeff Ψ) :=
      ⟨genericTest, whiskerLeft genericTest (tensorWith.mk K b _) ≫ coeffMap γ⟩
    (cmp (σ a)).coeffHom = ((cmp a).trans (Comparison.of (PadicTest.twist g) β)).coeffHom := by
  intro cmp
  ext c ⟨w⟩
  let w' : WittVector p c.TiltRing := WittVector.map (locConstToTilt.app c).hom.toRingHom w
  have h_frob (i : ℕ) : w'.coeff i ^ p = w'.coeff i :=
    (map_pow ..).symm.trans (congrArg _ (LocallyConstant.ext fun _ ↦ ZMod.pow_card _))
  have h_acts : β.app c ⟨periodTmul θ ((PadicTest.twist g).obj c) a w'⟩ =
      ⟨periodTmul θ c (σ a) w'⟩ := hβ c a w' h_frob
  -- both sides are `θ (σ a ⊗ 1 ⊗ w')`: the left one by `hγ`, the right one by `hγ` and `hβ`
  have h_lhs : (cmp (σ a)).coeffHom.app c ⟨w⟩ = ⟨periodTmul θ c (σ a) w'⟩ :=
    congrArg ULift.up (hγ c (σ a) w)
  have h_rhs : ((cmp a).trans (Comparison.of (PadicTest.twist g) β)).coeffHom.app c ⟨w⟩ =
      β.app c ⟨periodTmul θ ((PadicTest.twist g).obj c) a w'⟩ :=
    congrArg (β.app c) (congrArg ULift.up (hγ (PadicTest.twist g c) a w))
  exact h_lhs.trans (h_rhs.trans h_acts).symm

/-- Let `(S, K)` be a period ring pair (`New.Variety.IsPeriodRingPair`: `S` is a `p`-torsion-free,
`p`-adically complete `A_inf`-algebra in which `p` divides `ξ`, and `τ` is a unit in `K`), with `K`
flat over `S`. Let `Ψ` be a functor from `p`-adic tests `B` to `K`-modules, identified by `θ` with
`K ⊗_S (p-adic completion of S ⊗_{A_inf} W(B^♭))`. Let `e : Ω →+* ℚ̄_p` agree with `R → O_C` on `R`,
and let `j : Γ → G_p` satisfy `j g (e x) = e (g • x)`. Then there are `K`-linear maps `J Y` from
`K ⊗ V^n(Y)` to `H^n` of `ℤ[Y(B)]` (the `R`-points of `Y` in tests), with coefficients `Ψ`, that
form a `p`-adic period map (`IsPadicPeriodMap`): natural in `Y`, Galois equivariant, and bijective
for proper charted `Y`. -/
lemma exists_period_map [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] Ainf S] [IsScalarTower ℤ_[p] S K]
    [Flat S K] (hS : IsPeriodRingPair p S K) :
    ∃ J : ∀ Y : Over (Spec R), K ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩ →ₗ[K]
      H (freeAb.obj (testPoints.obj Y)) (moduleCoeff Ψ) n, IsPadicPeriodMap he θ hj J := by
  -- `J` is the composite of `K ⊗ V^n(Y) = K ⊗ H^n(Y_Ω, ℤ_p)`, the map `baseChangeMap` that moves
  -- `K` into the coefficients, and the pull-back along the primitive comparison `γ`.
  let E (Y : Over (Spec R)) :=
    equivOfCompatibleSMul ℚ_[p] ℤ_[p] K K (ellAdicCohom R Ω n ⟨Y⟩) ≪≫ₗ cancelBaseChange ..
  -- `γ : K ⊗ W(LC(Spec c[1/p], 𝔽_p)) → Ψ c` sends `a ⊗ w` to `θ (a ⊗ 1 ⊗ w)` (`hγ`); it is
  -- bijective on cohomology as soon as `primitiveMap` is modulo `p`, given flat base change
  -- and finiteness (`hγ_bij`).
  obtain ⟨γ, hγ, hγ_bij⟩ := exists_primitive_period_comparison K θ hS
  have := Flat.trans ℤ_[p] ℚ_[p] K
  algebraize [(algebraMap _ ℂ_[p]).comp e]
  let α (Y : Over (Spec R)) :
      freeAb (testPoints Y) ⟶ genericTest ⋙ freeAb (testIncl ⋙ geomPoints R Ω Y) :=
    freeAbMap (toGenericPoints Ω he Y ≫ whiskerLeft _ (whiskerLeft _ (algToBaseChange Ω Y)))
  let J (Y : Over (Spec R)) : K ⊗[ℤ_[p]] (ellAdicCohom R Ω n).obj ⟨Y⟩ →ₗ[K]
      H (freeAb.obj (testPoints.obj Y)) (moduleCoeff Ψ) n :=
    pullₗ γ (α Y) n ∘ₗ
      baseChangeMap K K (freeAb.obj (testIncl ⋙ (geomPoints R Ω).obj Y))
        (asModules (wittLocConst p)) n ∘ₗ (E Y).toLinearMap
  -- On `a ⊗ x` the map `J` is the pull-back of `x` along the comparison `w ↦ γ (a ⊗ w)`.
  let cmp (a : K) : Comparison ellAdicCoeff (moduleCoeff Ψ) :=
    ⟨genericTest, whiskerLeft _ (tensorWith.mk K a _) ≫ coeffMap γ⟩
  have J_tmul (Y : Over (Spec R)) (a : K)
      (x : H (freeAb (testIncl ⋙ geomPoints R Ω Y)) ellAdicCoeff n) :
      J Y ((E Y).symm (a ⊗ₜ x)) = (cmp a).pull (α Y) n x := by
    -- `baseChangeMap` sends `a ⊗ x` to the push-forward of `x` along `w ↦ a ⊗ w`; pulling back
    -- along `γ` after that push-forward is pulling back along the composite `cmp a`.
    simp only [J, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact (pull_push ⟨_, _⟩ (h := rfl) ..).trans (Abelian.Ext.comp_mk₀_id _)
  refine ⟨J, fun W Y f x ↦ ?_, fun Y g σ β hβ x ↦ ?_, fun Y _ _ ↦ ?_⟩
  · -- Naturality in `Y`, checked on pure tensors.
    obtain ⟨x, rfl⟩ := (E Y).symm.surjective x
    induction x with
    | add x y hx hy => simp [hx, hy]
    | tmul a x =>
      rw [J_tmul]
      refine (J_tmul W a (x.map _ _ n)).trans (map_pull_eq_pull_map ?_ n x).symm
      exact freeAb.hom_ext fun _ _ ↦ rfl
  · -- Equivariance, checked on pure tensors.
    obtain ⟨x, rfl⟩ := (E Y).symm.surjective x
    induction x with
    | add x y hx hy => simp [hx, hy]
    | tmul a x =>
      -- The comparisons agree by `hβ`: Witt vectors of locally constant `𝔽_p`-valued functions
      -- are fixed by Frobenius.
      have h_coeff : (cmp (σ a)).coeffHom =
          ((cmp a).trans (Comparison.of (PadicTest.twist (j g)) β)).coeffHom :=
        coeffHom_eq_coeffHom_trans_of_actsAsOnFrobeniusFixed K θ γ hγ hβ a
      refine (J_tmul Y (σ a) (x.map _ _ n)).trans ?_
      rw [J_tmul, pull_trans, ← map_pull_eq_pull_map (Category.id_comp _), H.map_id]
      -- Two steps: the two pull-backs are along the same map of points, as `e` is equivariant;
      -- and along the same comparison, by `h_coeff`.
      refine (congrArg (fun f ↦ (cmp (σ a)).pull f n x)
        (?h_maps : _ = freeAbMap (toTwistPoints he hj g Y) ≫
          (Comparison.of (PadicTest.twist (j g)) β).functor.whiskerLeft (α Y))).trans ?h_cmp
      case h_cmp =>
        exact congrArg (fun φ ↦ Comparison.pull ⟨_, φ⟩ _ n x) h_coeff
      case h_maps =>
        refine freeAb.hom_ext fun c y ↦
          congrArg FreeAbelianGroup.of (baseChangeOf.ext ?_ fun z ↦ ?_)
        · exact congrArg ULift.up (Spec.map_comp_assoc (𝟙 _) ..)
        · -- `genericStructureMap_twist` matches the structure map of the twisted test only up to
          -- instances
          erw [eq_comm, genericStructureMap_twist, smul_coe_Cp, hj]
          rfl
  · -- For `Y` proper and charted each of the three factors is bijective: `E Y` as a linear
    -- equivalence, `baseChangeMap` by flat base change, the pull-back by
    -- `finite_and_primitive_comparison`. The acyclicity hypothesis of the latter is almost descent,
    -- which applies since `p ∣ ξ` in `S`.
    obtain ⟨h_geo, -, h_prim⟩ :=
      finite_and_primitive_comparison Ω (isAcyclicOnPerfect_almostCoeff hS.pFlat_smul_eq_zero) Y
    have h_pts : HasFlatBaseChange (freeAb (testPoints Y)) :=
      (isAffinelyCovered_algPointsOf (ι := algFunctor) (fun c ↦ c.isTest.isComparableRing)
        Y).hasFlatBaseChange
    exact (hγ_bij h_geo h_pts finite_padic_cohomology (h_prim he) n).comp
      ((h_geo ..).comp (E Y).bijective)

end New.Variety

/-! ## Hodge–Tate weights of values of the Hodge–Tate map -/

section HodgeTateVectors

open CategoryTheory AlgebraicGeometry New Period IsScalarTower Variety PadicTest freeAb H
  PairRestrictBijective ModuleCat.Algebra
open scoped TensorProduct

/-- Let `Y`, `W` be proper over `R`, with `Y` smooth of relative dimension `d` and charted over `Ω`.
Let `E` be a field between `R` and `Ω` that is mapped to `k ⊆ ℚ̄_p`, and `A` a subring of `Ω`
containing the image of `R`. Let `e : Ω → ℚ̄_p` be a `p`-adic place embedding for `A` over `E`
(`New.GaloisRep.PadicPlaceEmbedding`) agreeing with `E → k → ℚ̄_p` on `E`, and `ε` a section of
`k → ℚ̄_p`. Take any `h` and a Hodge class `x` of degree `q` of `Y` over `E` (in Ext^q from
`(S, M) ↦ ℤ[Y(S ⊕ M)]` to `(S, M) ↦ ⋀_S M`). Then there are a vector `v` of `ℂ_p ⊗ V^(q+h)(Y)` and
an `ε`-semilinear map `Θ` from `ℂ_p ⊗ V^(q+h)(W)` to cohomology on pairs with coefficients `S[1/p]`
(`PairH`) such that: (a) `v` has Hodge–Tate weight `h` for the decomposition group of `A` in
`Gal(Ω/E)`; (b) `hodgeTateMap h (u^* x) = Θ (u^* v)` for all `u : W ⟶ Y`, where `hodgeTateMap h`
pulls back along `B_{S,M} → T ⊕ M` and applies the `h`-th power of the contraction class. -/
lemma New.Variety.exists_hasHodgeTateWeight {p h : ℕ} {R : CommRingCat} {E k : Type} [Field k]
    [Field E] [EmbeddedInQpBar p k] [Algebra R Ω] [Algebra R E] [Algebra E k] [Algebra E Ω]
    [IsScalarTower R E Ω] {Y : Over (Spec R)} [IsCharted Y Ω] [IsProper Y.hom] {A : ClosurePlace}
    [I : GaloisRep.PadicPlaceEmbedding E A p] (hR : ∀ r : R, algebraMap R Ω r ∈ A)
    (he_compat : ∀ x : E, algebraMap k (PadicAlgCl p) (algebraMap E k x) = I.e (algebraMap E Ω x))
    (d : ℕ) [SmoothOfRelativeDimension d Y.hom] (ε : PadicAlgCl p →+* k)
    (hε_section : ∀ z : PadicAlgCl p, algebraMap k (PadicAlgCl p) (ε z) = z)
    {W : Over (Spec R)} [IsProper W.hom] {q : ℕ}
    (x : HodgeH (freeAb.obj ((algPoints E R).obj Y)) q) :
    ∃ v : ℂ_[p] ⊗[ℤ_[p]] (ellAdicCohom R Ω (q + h)).obj ⟨Y⟩,
      ∃ Θ : ℂ_[p] ⊗[ℤ_[p]] (ellAdicCohom R Ω (q + h)).obj ⟨W⟩ →ₛₗ[ε]
        PairH (restrictAlg E k ⋙ freeAb.obj (algPointsOf E R W)),
      -- (a) `v` has Hodge–Tate weight `h` under the decomposition group of `A`
      HasHodgeTateWeight (ellAdicCohom.galoisAction R Ω (decompGroup Gal(Ω/E) A) Y (q + h)) h v ∧
      -- (b) `Θ` sends the pull-back of `v` along any `u` to `hodgeTateMap h` of the pull-back of
      -- `x`
      ∀ u : W ⟶ Y, hodgeTateMap h (x.map (freeAb.map ((algPoints E R).map u))).baseChange =
        Θ ((((ellAdicCohom R Ω (q + h)).map u.op).hom.restrictScalars ℤ_[p]).baseChange ℂ_[p]
          v) := by
  -- `hodgeTateMap h x` comes from a class `ξ` on `p`-adic tests. The period map `J` and the passage
  -- `B` to integral points have the same target, and `J Y` is bijective; `v` is defined by
  -- `J Y v = B Y ξ`.
  obtain ⟨e, ⟨rfl, hj⟩, _⟩ := I
  -- `θ` identifies the period algebra of a test `c` with `c[1/p]`, through Fontaine's map.
  obtain ⟨θ, hθ⟩ := exists_periodAlg_iso_genericAlg
  -- As `R` maps into the place `A`, the embedding `e` carries it into `OC`.
  algebraize [theta.comp (algebraMap ℤ_[p] _), (algebraMap E k).comp (algebraMap R E),
    (.codRestrict (.comp (algebraMap ..) (e.comp _)) _ (by simpa) : R →+* OC)]
  have : IsScalarTower ℤ_[p] OC ℂ_[p] :=
    of_algebraMap_eq fun z ↦ ((OC.toPadicIntAlgHom _).commutes z).symm
  -- `J Z'` maps `ℂ_p ⊗ V^(q+h)(Z')` to `H^(q+h)` of the points of `Z'` in tests `c`, with
  -- coefficients `c[1/p]`; it is natural in `Z'`, Galois equivariant, and bijective for `Z'`
  -- proper and charted.
  obtain ⟨J, J_nat, J_twist, J_bij⟩ :=
    exists_period_map (R := R) (fun _ ↦ rfl) _ θ (q + h) hj isPeriodRingPair_OC
  have h_compat (r : R) : algebraMap k ℂ_[p] (algebraMap R k r) = algebraMap R OC r := by
    have h_e : algebraMap k (PadicAlgCl p) (algebraMap E k (algebraMap R E r)) =
        e (algebraMap R Ω r) := by
      rw [he_compat, ← algebraMap_apply R E Ω r]
      -- `I.e` is `e`: the instance `I` was taken apart above
      rfl
    exact congrArg (algebraMap (PadicAlgCl p) ℂ_[p]) h_e
  -- By the valuative criterion, points over `c[1/p]` of a proper scheme extend uniquely to `c`.
  let B {n : ℕ} (Z' : Over (Spec R)) [IsProper Z'.hom] :
      H (genericOver ⋙ restrictAlg E k ⋙ freeAb (algPointsOf E R Z')) genericCoeff n ≃ₗ[k] _ :=
    .ofBijective (mapₗ ..)
      (IsCohomEquiv.of_bijective (p := toGenericPoints k h_compat Z')
        (fun c ↦ c.bijective_generic_points) n)
  -- `J` is `ℂ_[p]`-linear, hence semilinear along the section `ε` of `k → PadicAlgCl p`.
  have J_semi (Z' : Over (Spec R)) (z : PadicAlgCl p)
      (y : ℂ_[p] ⊗[ℤ_[p]] (ellAdicCohom R Ω (q + h)).obj ⟨Z'⟩) : J Z' (z • y) = ε z • J Z' y := by
    -- `ε z` acts on the target through its image in `ℂ_[p]`, which is the image of `z`
    have h_scalar : algebraMap k ℂ_[p] (ε z) = algebraMap (PadicAlgCl p) ℂ_[p] z :=
      congrArg (algebraMap (PadicAlgCl p) ℂ_[p]) (hε_section z)
    change J Z' (z • y) = algebraMap k ℂ_[p] (ε z) • J Z' y
    rw [h_scalar, ← (J Z').map_smul, _root_.algebraMap_smul]
  -- `Y` is smooth, so covered by étale charts.
  have h_den : PairRestrictBijective (restrictAlg E k ⋙ freeAb (algPointsOf E R Y)) :=
    (hasAtlas_algPointsOf d).isChartCovered.pairRestrictBijective
  obtain ⟨ξ, hξ⟩ : ∃ ξ : H (genericOver ⋙ restrictAlg E k ⋙ freeAb (algPointsOf E R Y))
      genericCoeff (q + h), hodgeTateMap h x.baseChange = restrictToPairs (n := q + h) ξ :=
    h_den.exists_hodgeTateMap_eq h _
  obtain ⟨v, hv⟩ := (J_bij Y).surjective (B Y ξ)
  -- `Θ` is `J W` followed by the inverse of `B W` and by `restrictToPairs`.
  refine ⟨v, restrictToPairs ∘ₛₗ (B W).symm.comp ⟨_, J_semi W⟩, fun g ↦ (J_bij Y).injective ?_,
    fun u ↦ ?_⟩
  · -- `J` turns the action of `g` into the pull-back along the twist of tests by `toGp g`. That
    -- pull-back commutes with `B` and multiplies `ξ` by the `h`-th power of the cyclotomic
    -- character of `(toGp g)⁻¹` (`hodgeTateMap_galois_twist`, `restrictToPairs` being injective).
    have h_fix (z : E) : toGp g (algebraMap k _ (algebraMap E k z)) =
        algebraMap k _ (algebraMap E k z) := by simp [he_compat, hj]
    calc
      _ = (Comparison.of _ (twistGenericCoeff (toGp g))).pull
          (freeAbMap (toTwistPoints (fun _ ↦ rfl) hj g Y)) (q + h) (J Y v) := by
        refine J_twist Y g _ (twistGenericCoeff _) (fun c a w _ ↦ ?_) v
        unfold periodTmul
        -- `hθ` and `genericStructureMap_twist` match the twisted test only up to instances
        erw [hθ, hθ, genericStructureMap_twist]
        rfl
      _ = B Y (ε (algebraMap _ _ (cyclotomicGp (toGp g)⁻¹).val) ^ h • ξ) := by
        -- `g` multiplies `ξ` by this scalar
        have h_weight := h_den.injective_restrictToPairs
          (hodgeTateMap_galois_twist h_fix hξ (hε_section _))
        rw [hv]
        refine (Comparison.map_pull_eq_pull_map (hom_ext fun c _ ↦ ?_) ..).symm.trans
          (congrArg (B Y) h_weight)
        -- The twist of points is compatible with passing to `c[1/p]`: functoriality of `Spec`.
        refine congrArg FreeAbelianGroup.of (congrArg ULift.up (Over.OverMorphism.ext ?_))
        exact
          (Spec.map_comp_assoc (CommRingCat.ofHom (algebraMap c.ProdRing c.GenericRing)) (𝟙 _)
            _).symm.trans
          (Spec.map_comp_assoc (𝟙 _) (CommRingCat.ofHom (algebraMap c.ProdRing c.GenericRing)) _)
      _ = J Y ((cyclotomicGp (toGp g) ^ (-h : ℤ)).val • v) := by
        simp [algebra_compatible_smul (PadicAlgCl p), J_semi, hv]
  · -- Naturality of `hodgeTateMap`, `restrictToPairs`, `J` and `B` in `u`.
    simp [hodgeTateMap_map, hξ, J_nat, hv, ← restrictToPairs_map]
    -- It remains that `B` commutes with the pull-back along `u`: `B` is `mapₗ` along the maps
    -- `toGenericPoints`, which are natural in the scheme.
    rw [(B W).symm_apply_eq.mpr]
    refine (map_comp _ (freeAb.map (toGenericPoints k h_compat Y)) ξ).symm.trans
      (.trans ?_ (map_comp (freeAb.map (toGenericPoints k h_compat W)) _ ξ))
    -- the two composite maps of points agree
    exact congrArg (H.map genericCoeff · (q + h) ξ) hom_ext

end HodgeTateVectors
