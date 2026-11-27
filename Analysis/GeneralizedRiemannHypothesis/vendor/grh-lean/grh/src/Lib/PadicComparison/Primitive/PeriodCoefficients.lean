import Lib.Cohomology.TorsionTheories
import Lib.PadicComparison.Descent.AlmostDescent
import Lib.PadicComparison.HodgeTate.GenericFibre
import Lib.PadicHodge.ArtinSchreierSequence

/-!
# Tilts and period coefficients of p-adic tests: products, comparisons, theories

This file treats the `p`-adic side of the comparison of cohomologies. A `p`-adic test `c`
(`New.Variety.PadicTest`) has a ring `R = c.ProdRing`, a generic ring `R[1/p] = c.GenericRing` and a
tilt `R♭` (`New.Variety.PadicTest.tilt`), an algebra over `O♭ = OFlat`. Here `^` denotes `p`-adic
completion. `S` is an `A_inf`-algebra and `K` is an `S`-algebra.

## Main definitions and results

* `New.Variety.bijective_prod_tilt`: bijectivity of `x ↦ (f x, g x)`, which recognises a product,
  passes from the rings of `p`-adic tests to their tilts.
* `New.Variety.IsPeriodRingPair`: `S` is `p`-torsion-free and `p`-complete, `p` divides the image of
  `ξ`, and `τ` is a unit in `K`.
* `New.Variety.hasPartitions_periodAlg`: a functor `Ψ` with an isomorphism `θ` from the period
  coefficients `asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K` turns a product of two tests into a
  product (`New.Variety.HasPartitions`).
* `New.Variety.CoeffCompBijective.periodAlg_of_almostCoeff`: for an `A_inf`-algebra `S` with
  `IsPeriodRingPair p S K` and `Flat S K`, under base-change hypotheses on `N` and `N'` and with
  `ψ`, `ψ'` perfect and torsion-free, bijectivity of a comparison of cohomology groups
  (`New.Variety.CoeffCompBijective`) passes from the coefficients `b ↦ b ⊗ (O♭ ⊗ S) ⊗ 𝔪`
  (`New.Variety.almostCoeff`) to the coefficients `b ↦ K ⊗ (S ⊗ W(b))^` (`New.Variety.periodAlg`).
  The bridge is the ideal `W(𝔪)` of `A_inf` (`New.Lift.wittOfMaxIdeal`). It reduces to `𝔪` modulo
  `p` and contains `τ` (`New.Period.tau`).
* `New.Variety.primitiveMap`: the `O♭`-algebra map `O♭ ⊗_{𝔽_p} LC(Spec R[1/p]) → R♭` that extends
  `New.Variety.locConstToTilt`, where `LC` denotes locally constant functions.
* `New.Variety.tiltTheory`: with coefficients `R ↦ R♭ ⊗_{O♭} M`, a theory (`New.Variety.Theory`)
  along `New.Variety.genericTestOver`.

Notions from other files:
* `New.Period.OFlat`: the ring `O♭`, the inverse limit of `O_C / p` along `x ↦ x ^ p`.
* `New.Variety.IsPerfectTorsionFree b`: the `O♭`-algebra `b` is perfect, and `pFlat`, the class of
  `ξ` modulo `p`, is a non-zero-divisor on it.
* `New.Variety.CoeffCompBijective β α F`: the comparison of cohomology groups along `β` and `α` is
  bijective in every degree for the coefficients `F`.
* `New.Variety.moduleCoeff F`: a functor `F` to modules, read as a functor to abelian groups, to
  serve as coefficients of cohomology.

## Relation to the literature

Known; see `Lib.PadicComparison.Descent.TestCovers` and `Lib.PadicComparison.HodgeTate.PeriodMap`
for sources.
-/

noncomputable section

namespace New.Variety

/-!
## Products of p-adic tests under tilting and product-preserving functors

A product of two objects is recognised here by the map `x ↦ (f x, g x)` being bijective.
-/

section TiltProducts

open CategoryTheory Limits PadicTest Perfection Equiv Function

/-- If `x ↦ (f x, g x)` is bijective for linear maps `f : X ⟶ Y` and `g : X ⟶ Z`, then so is
`x ↦ (U.map f x, U.map g x)` for every functor `U` from modules to types that preserves finite
products. -/
lemma _root_.Function.Bijective.map_prod {S : Type*} [Ring S] {X Y Z : ModuleCat S} {f : X ⟶ Y}
    {g : X ⟶ Z} (hfg : Bijective fun x : X ↦ (f x, g x)) (U : ModuleCat S ⥤ Type*)
    [PreservesFiniteProducts U] :
    Bijective fun x : U.obj X ↦ (U.map f x, U.map g x) := by
  -- `X` with `f` and `g` is a product of `Y` and `Z`, so its image under `U` is a product of types.
  have h_iso : IsIso ((Y.binaryProductLimitCone Z).isLimit.lift (BinaryFan.mk f g)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hfg
  have h_prod : IsLimit (BinaryFan.mk f g) := (Y.binaryProductLimitCone Z).isLimit.ofPointIso
  exact ((mapIsLimitOfPreservesOfIsLimit U _ _ h_prod).conePointUniqueUpToIso
    (Types.binaryProductLimit (U.obj Y) (U.obj Z))).toEquiv.bijective

/-- Tilting keeps the product of two tests: if maps of `p`-adic tests `f : c ⟶ d` and `g : c ⟶ d'`
present the ring of `c` as the product of the rings of `d` and `d'`, then the induced maps present
the tilt of `c`, read as an `O♭`-module (`asModules tilt`), as the product of the tilts of `d` and
`d'`. -/
lemma bijective_prod_tilt {p : ℕ} [ThePrime p] {c d d' : PadicTest} (f : c ⟶ d) (g : c ⟶ d')
    (hfg : Bijective fun x : c.ProdRing ↦ (f.toRingHom x, g.toRingHom x)) :
    Bijective fun x : (asModules tilt).obj c ↦
      ((asModules tilt).map f x, (asModules tilt).map g x) := by
  -- As a set, the tilt of a test is the set of sequences `x` in its ring with
  -- `x (n + 1) ^ p = x n`, and such sequences in a product are pairs of such sequences.
  let e {b : PadicTest} : Perfection b.ProdRing p ≃ tilt.obj b :=
    (quotientMulEquiv p (Ideal.span {(p : b.ProdRing)})).toEquiv
  let seqs : (ℕ → c.ProdRing) ≃ (ℕ → d.ProdRing) × (ℕ → d'.ProdRing) :=
    (ofBijective _ hfg.comp_left).trans
      (arrowProdEquivProdArrow ℕ (fun _ ↦ d.ProdRing) (fun _ ↦ d'.ProdRing))
  have compatible_iff (x : ℕ → c.ProdRing) : (∀ n : ℕ, x (n + 1) ^ p = x n) ↔
      (∀ n : ℕ, (seqs x).fst (n + 1) ^ p = (seqs x).fst n) ∧
        ∀ n : ℕ, (seqs x).snd (n + 1) ^ p = (seqs x).snd n := by
    simp [seqs, forall_and, ← hfg.injective.eq_iff]
  let perf : Perfection c.ProdRing p ≃ Perfection d.ProdRing p × Perfection d'.ProdRing p :=
    (seqs.subtypeEquiv compatible_iff).trans subtypeProdEquivProd
  -- By definition of the tilt of a map, the map in question composed with `e` is `perf` followed
  -- by `e × e`.
  exact (e.bijective_comp _).mp (perf.trans (e.prodCongr e)).bijective

end TiltProducts

/-!
## Period ring pairs and additivity of period coefficients

Let `S` be an `A_inf`-algebra and `K` an `S`-algebra. The period coefficient sends a `p`-adic test
with ring `R` to `K ⊗ (S ⊗ W(R♭))^`, where `^` is `p`-adic completion. `Ψ` is any functor
isomorphic to it.
-/

section PeriodPairs

open CategoryTheory Algebra TensorProduct Period PadicTest Equiv

variable (p : ℕ) (S : Type) [CommRing S]
  (K : Type _) [CommRing K] [Algebra S K] [ThePrime p] [Algebra Ainf S]
  {Ψ : PadicTest ⥤ ModuleCat K}

/-- The `A_inf`-algebra `S` is `p`-torsion-free and `p`-adically complete, `p` divides the image of
`ξ` in `S`, and the image of `τ` in the `S`-algebra `K` is a unit. -/
structure IsPeriodRingPair extends isCompleteTorsionFree : IsCompleteTorsionFree S where
  /-- The prime `p` divides the image of `ξ` in `S`. -/
  dvd_xi : (p : S) ∣ algebraMap Ainf S xi
  /-- The image of `τ` in `K` is a unit. -/
  isUnit_tau : IsUnit (algebraMap S K (algebraMap Ainf S tau))

variable {p S}

/-- `O_C` and `ℂ_p` form a period ring pair: `O_C` is `p`-torsion-free and `p`-complete, `θ ξ = 0`
for `θ = theta`, the structure map `A_inf → O_C`, and `θ τ ≠ 0` is a unit of the field `ℂ_p`. -/
lemma isPeriodRingPair_OC : IsPeriodRingPair p OC ℂ_[p] where
  regular := .of_ne_zero NeZero.out
  complete := {}
  -- the structure map `Ainf → OC` is `theta`, which kills `xi`
  dvd_xi := ⟨0, theta_xi.trans (mul_zero _).symm⟩
  -- `theta tau` is not `0`, so it is a unit of the field
  isUnit_tau := by simp [RingHom.algebraMap_toAlgebra]

/-- Let `Ψ` be isomorphic (by `θ`) to the period coefficient `c ↦ K ⊗ (S ⊗ W(R♭))^`. Then `Ψ` has
partitions: tests can be cut along idempotents, and `Ψ` sends a product of two tests to the
product of its values. -/
lemma hasPartitions_periodAlg (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ) :
    HasPartitions ringFunctor (moduleCoeff Ψ) := by
  refine ⟨exists_isQuotientByElem, fun {A B₁ B₂ : PadicTest} f g hfg ↦ ?_⟩
  -- Tilting keeps the product, and so do Witt vectors, which are sequences of coordinates.
  let e {R : Type} : WittVector p R ≃ (ℕ → R) := mk WittVector.coeff .mk'
  let W : PadicTest ⥤ ModuleCat Ainf := asModules (tilt ⋙ wittFunctor)
  have h_witt : Function.Bijective fun x : W.obj A ↦ (W.map f x, W.map g x) :=
    ((arrowProdEquivProdArrow ℕ (fun _ ↦ tilt.obj B₁) (fun _ ↦ tilt.obj B₂)).trans
      (e.prodCongr e).symm).bijective.comp
      ((bijective_prod_tilt f g hfg).comp_left.comp e.bijective)
  -- So do base change to `S`, completion of modules and base change to `K`.
  let Φ : PadicTest ⥤ ModuleCat K :=
    asModules (tilt ⋙ wittFunctor ⋙ algBaseChange S) ⋙ moduleCompletion S p ⋙ tensorWith K K
  have h_ten : Function.Bijective fun x : Φ.obj A ↦ (Φ.map f x, Φ.map g x) :=
    (h_witt.map_prod (tensorWith S S ⋙ forget _)).map_prod
      (moduleCompletion S p ⋙ tensorWith K K ⋙ forget _)
  -- The composite `Φ` is isomorphic to `Ψ`, by `moduleCompletionIso` and `θ`.
  let θ' : Φ ≅ Ψ :=
    (Functor.isoWhiskerRight
      ((tilt ⋙ wittFunctor ⋙ algBaseChange S).isoWhiskerLeft (moduleCompletionIso S p)) _ ≪≫ θ :)
  -- The square of `θ'` with the two pairs of maps commutes, by naturality of `θ'`.
  have h_comm (x : Φ.obj A) : (Ψ.map f (θ'.hom.app A x), Ψ.map g (θ'.hom.app A x)) =
      Prod.map (θ'.hom.app B₁) (θ'.hom.app B₂) (Φ.map f x, Φ.map g x) := by
    simp
  have hθ' (A : PadicTest) : Function.Bijective (θ'.hom.app A) := (θ'.app A).toLinearEquiv.bijective
  exact ((Comparison.bijective_iff_of_comm_sq h_comm (hθ' A) ((hθ' B₁).prodMap (hθ' B₂))).mp
    h_ten).map_prod (forget _ ⋙ uliftFunctor)

variable {K}

/-- For a period ring pair, `pFlat`, the class of `ξ` modulo `p`, kills `O♭ ⊗ S`. -/
lemma IsPeriodRingPair.pFlat_smul_eq_zero (hK : IsPeriodRingPair p S K) (x : OFlat ⊗[Ainf] S) :
    pFlat • x = 0 := by
  -- `pFlat` acts as `xi`, whose image in `S` is a multiple of `p`; and `p = 0` in `OFlat ⊗ S`.
  have h_dvd : (p : OFlat ⊗[Ainf] S) ∣ algebraMap Ainf (OFlat ⊗[Ainf] S) xi := by
    simpa using map_dvd (includeRight (R := Ainf) (A := OFlat)) hK.dvd_xi
  change xi • x = 0
  simpa [Algebra.smul_def, natCast_eq_zero_of_algebra_oFlat] using h_dvd.mul_right x

end PeriodPairs

/-! ## Passing bijectivity from almost coefficients to period coefficients -/

section PeriodLifting

open CategoryTheory TensorProduct Function Functor Module LinearMap AlgebraTensorModule Period Lift
  WittVector AdicCompletion Submodule ModuleCat Comparison AddCommGrpCat

/-- If `p * y` lies in `W(𝔪) = wittOfMaxIdeal`, for `𝔪` the maximal ideal of `O♭`, so does `y`:
`W(𝔪)` is the kernel of the map to the Witt vectors of the residue field, a domain in which
`p ≠ 0`. -/
private lemma mem_wittOfMaxIdeal_of_natCast_mul_mem {p : ℕ} [ThePrime p] {y : Ainf}
    (h : (p : Ainf) * y ∈ wittOfMaxIdeal) : y ∈ wittOfMaxIdeal := by
  aesop (add simp [wittOfMaxIdeal, p_nonzero])

/-- There is a linear map `W(𝔪) → 𝔪` that is onto with kernel `p W(𝔪)`: the zeroth coordinate.
Here `𝔪` is the maximal ideal of `O♭` and `W(𝔪) = wittOfMaxIdeal`. -/
lemma exists_isReductionMod_wittOfMaxIdeal {p : ℕ} [ThePrime p] :
    ∃ c : wittOfMaxIdeal →ₗ[Ainf] MaxIdealFlat, IsReductionMod p c := by
  let c : wittOfMaxIdeal →ₗ[Ainf] MaxIdealFlat := (Algebra.linearMap Ainf OFlat).restrict
    (q := (IsLocalRing.maximalIdeal OFlat).restrictScalars Ainf) fun _ hx ↦
      mem_wittOfMaxIdeal.mp hx 0
  obtain ⟨(h_mod : IsReductionMod p (constantCoeff : Ainf →+* OFlat)), -⟩ :=
    isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat OFlat
  refine ⟨c, ?_, ?_⟩
  · -- Onto: `y ∈ 𝔪` is the zeroth coordinate of its Teichmüller lift `[y] ∈ W(𝔪)`.
    exact fun y ↦ ⟨⟨teichmuller p (y : OFlat), teichmuller_mem_wittOfMaxIdeal y.prop⟩, rfl⟩
  -- The kernel: `c x = 0` says that the zeroth coordinate of `x` vanishes, that is, `x ∈ p A_inf`;
  -- and if `p y` lies in `W(𝔪)` then so does `y`.
  rintro ⟨x, hx⟩
  have h_zero_iff : c ⟨x, hx⟩ = 0 ↔ x ∈ Set.range fun y : Ainf ↦ p • y :=
    Subtype.ext_iff.trans (h_mod.right x)
  refine h_zero_iff.trans ?_
  suffices h_iff : (∃ y : Ainf, p * y = x) ↔ ∃ y ∈ wittOfMaxIdeal, p * y = x by
    simpa [Subtype.ext_iff] using h_iff
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, mem_wittOfMaxIdeal_of_natCast_mul_mem hx, rfl⟩
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩

/-- There are `S`-linear maps between `S ⊗ W(𝔪)` and `S`, with `W(𝔪) = wittOfMaxIdeal`, that compose
to `τ` in both orders: `s ⊗ w ↦ w s` and `s ↦ s ⊗ τ`. -/
lemma exists_comp_eq_tau_smul_id {p : ℕ} [ThePrime p] (S : Type*) [CommRing S] [Algebra Ainf S] :
    ∃ (u : S ⊗[Ainf] wittOfMaxIdeal →ₗ[S] S) (v : S →ₗ[S] S ⊗[Ainf] wittOfMaxIdeal),
      v ∘ₗ u = algebraMap Ainf S tau • LinearMap.id ∧
      u ∘ₗ v = algebraMap Ainf S tau • LinearMap.id := by
  refine ⟨liftBaseChange S (wittOfMaxIdeal.subtype.smulRight 1),
    toSpanSingleton S _ (1 ⊗ₜ ⟨tau, toWittResidue_tau⟩), ?_, ?_⟩
  · -- On `1 ⊗ w` both sides are `1 ⊗ w τ`: the scalar `w`, or `τ`, moves through the tensor sign.
    ext w
    have h_comm : (w : Ainf) • (⟨tau, toWittResidue_tau⟩ : wittOfMaxIdeal) = tau • w :=
      Subtype.ext (mul_comm _ _)
    simp [← tmul_smul, h_comm]
  · -- `u (v 1) = u (1 ⊗ τ) = τ`.
    ext
    simp [Algebra.algebraMap_eq_smul_one]

/-- The completed step of `CoeffCompBijective.periodAlg_of_almostCoeff`. Let `ψ`, `ψ'` be functors
to `O♭`-algebras with perfect values on which `pFlat` is regular, compared by `β` along `φ`, and let
`S` be a `p`-torsion-free `A_inf`-algebra; `α : N' ⟶ φ ⋙ N` compares `N` and `N'`, the functors on
`C` and `C'` whose cohomology is taken. If the comparison is bijective for the coefficients
`b ↦ b ⊗ (O♭ ⊗ S) ⊗ 𝔪`, then it is bijective for the coefficients `b ↦ ((S ⊗ W(𝔪)) ⊗ W(b))^`. Here
`𝔪` is the maximal ideal of `O♭`, `W(𝔪) = wittOfMaxIdeal`, and `^` is the `p`-adic completion. -/
private lemma CoeffCompBijective.completion_wittOfMaxIdeal_of_almostCoeff {C C' : Type 1}
    [Category C] [Category C'] {p : ℕ} [ThePrime p] {N : AbFunctor C} {N' : AbFunctor C'}
    {φ : C' ⥤ C} {α : N' ⟶ φ ⋙ N} {S : Type} [CommRing S] [Algebra Ainf S]
    (h_reg : IsSMulRegular S p) {ψ : C ⥤ CommAlg OFlat} {ψ' : C' ⥤ CommAlg OFlat}
    {β : φ ⋙ ψ ⟶ ψ'} (hψ : ∀ A : C, IsPerfectTorsionFree (ψ A))
    (hψ' : ∀ A : C', IsPerfectTorsionFree (ψ' A))
    (h_red : CoeffCompBijective β α (almostCoeff (OFlat ⊗[Ainf] S))) :
    CoeffCompBijective β α ((asModules (wittFunctor (k := OFlat)) ⋙
      tensorWith S (S ⊗[Ainf] wittOfMaxIdeal)) ⋙ moduleCompletion S p) := by
  -- Put `P b = (S ⊗ W(𝔪)) ⊗ W(b)`. The zeroth coordinates give a natural map
  -- `red b : P b → b ⊗ (O♭ ⊗ S) ⊗ 𝔪` that kills `p` and is reduction modulo `p` for perfect `b`.
  -- It induces `redCompl` on the completion of `P`, to which the adic step lifts `h_red`.
  obtain ⟨(h_modW : IsReductionMod p (constantCoeff : Ainf →+* OFlat)),
    (h_witt : IsCompleteTorsionFree Ainf), -⟩ :=
      isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat OFlat
  obtain ⟨c, hc⟩ : ∃ c : wittOfMaxIdeal →ₗ[Ainf] MaxIdealFlat, IsReductionMod p c :=
    exists_isReductionMod_wittOfMaxIdeal
  let P : CommAlg OFlat ⥤ ModuleCat S :=
    asModules (wittFunctor (k := OFlat)) ⋙ tensorWith S (S ⊗[Ainf] wittOfMaxIdeal)
  let Q : ModuleCat S ⥤ ModuleCat S := moduleCompletion S p
  -- `red b` takes zeroth coordinates, applies `c`, then rearranges the factors.
  have h_smul : CompatibleSMul Ainf OFlat (OFlat ⊗[Ainf] S) MaxIdealFlat :=
    CompatibleSMul.of_algebraMap_surjective (OFlat ⊗[Ainf] S) MaxIdealFlat h_modW.left
  let rearrange (b : CommAlg OFlat) : S ⊗[Ainf] MaxIdealFlat ⊗[Ainf] b ≃ₗ[Ainf]
      b ⊗[OFlat] (OFlat ⊗[Ainf] S ⊗[OFlat] MaxIdealFlat) :=
    TensorProduct.comm Ainf (S ⊗[Ainf] MaxIdealFlat) b ≪≫ₗ
      LinearEquiv.restrictScalars Ainf
        ((cancelBaseChange Ainf OFlat OFlat b (S ⊗[Ainf] MaxIdealFlat)).symm ≪≫ₗ .lTensor b
          ((assoc Ainf Ainf OFlat OFlat S MaxIdealFlat).symm ≪≫ₗ
            equivOfCompatibleSMul OFlat Ainf OFlat (OFlat ⊗[Ainf] S) MaxIdealFlat))
  let red (b : CommAlg OFlat) : P.obj b →+ (almostCoeff (OFlat ⊗[Ainf] S)).obj b :=
    ((rearrange b).toLinearMap ∘ₗ (c.lTensor S).rTensor b ∘ₗ
      (wittConstCoeff b).lTensor _).toAddMonoidHom
  have h_red_zero (b : CommAlg OFlat) :
      ∀ x ∈ Ideal.span {(p : S)} ^ 1 • (⊤ : Submodule S (P.obj b)), red b x = 0 := by
    -- A multiple of `p` goes to `p` times an element of an `O♭`-module, where `p = 0`.
    intro x hx
    obtain ⟨y, rfl⟩ : ∃ y : P.obj b, p ^ 1 • y = x := nsmulRange.mem_span_pow_smul_top_iff.mp hx
    simp [natCast_eq_zero_of_algebra_oFlat, ← Nat.cast_smul_eq_nsmul OFlat]
  have h_red_nat {b b' : CommAlg OFlat} (f : b ⟶ b') :
      (red b').comp (P.map f).hom.toAddMonoidHom =
        ((almostCoeff (OFlat ⊗[Ainf] S)).map f).hom.toAddMonoidHom.comp (red b) :=
    tmul_ext fun _ _ ↦ rfl
  -- For perfect `b`, `red b` is reduction modulo `p`: so is `wittConstCoeff b`, and `c` becomes
  -- bijective after tensoring with `b`, which `p` kills.
  have h_red_mod (b : CommAlg OFlat) [PerfectRing b p] : IsReductionMod p (red b) := by
    have h_bij : Bijective ((rearrange b).toLinearMap ∘ₗ (c.lTensor S).rTensor b) :=
      (rearrange b).bijective.comp
        ((hc.lTensor _).bijective_rTensor _ (by simp [natCast_eq_zero_of_algebra_oFlat]))
    have h_mod : IsReductionMod p ((wittConstCoeff b).lTensor (S ⊗[Ainf] wittOfMaxIdeal)) :=
      (isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat b).left.lTensor _
    exact ⟨h_bij.surjective.comp h_mod.left,
      fun x ↦ (map_eq_zero_iff _ h_bij.injective).trans (h_mod.right x)⟩
  -- As `red b` kills `p P b`, it induces a natural map on the completion, via `P b / p`.
  let redCompl : (P ⋙ Q) ⋙ forget₂ _ Ab ⟶ almostCoeff (OFlat ⊗[Ainf] S) ⋙ forget₂ _ Ab :=
    { app b := ofHom <| (QuotientAddGroup.lift _ (red b) (h_red_zero b)).comp
        (AdicCompletion.eval _ _ 1).toAddMonoidHom
      naturality _ _ f :=
        ConcreteCategory.coe_ext (map_ext _ fun x ↦ DFunLike.congr_fun (h_red_nat f) (x 1)) }
  have h_fg : (Ideal.span {(p : S)}).FG := fg_span_singleton _
  have h_compl_mod (b : CommAlg OFlat) [PerfectRing b p] :
      IsReductionMod p fun y : (P ⋙ Q).obj b ↦ redCompl.app b y := by
    refine ⟨.of_comp (g := of _ _) (h_red_mod b).left,
      fun y : AdicCompletion (Ideal.span {(p : S)}) (P.obj b) ↦ ?_⟩
    obtain ⟨x, hx⟩ : ∃ x : P.obj b,
        (Ideal.span {(p : S)} ^ 1 • (⊤ : Submodule S (P.obj b))).mkQ x = y.val 1 :=
      mkQ_surjective _ (y.val 1)
    -- `redCompl y = red x`, and `x ∈ p P b` if and only if `y` vanishes modulo `p`.
    have hxy : redCompl.app b y = red b x := congrArg (Quot.lift _ _) hx.symm
    have h_ker : y ∈ (AdicCompletion.eval (Ideal.span {(p : S)}) (P.obj b) 1).ker ↔
        y ∈ nsmulRange p _ := by
      rw [← pow_smul_top_eq_ker_eval h_fg, nsmulRange.mem_span_pow_smul_top_iff, pow_one]
    have h_rep_zero : y.val 1 = 0 ↔ x ∈ nsmulRange p _ := by
      rw [← hx, mkQ_apply, Submodule.Quotient.mk_eq_zero, nsmulRange.mem_span_pow_smul_top_iff,
        pow_one]
    show redCompl.app b y = 0 ↔ ∃ z, p • z = y
    rw [hxy, (h_red_mod b).right x]
    exact h_rep_zero.symm.trans h_ker
  -- So on values with `IsPerfectTorsionFree` the sequence of `p` and `redCompl` is short exact.
  have h_exact {D : Type 1} [Category D] {χ : D ⥤ CommAlg OFlat}
      (hχ : ∀ A : D, IsPerfectTorsionFree (χ.obj A)) :
      ModShortExact (Φ := χ ⋙ P ⋙ Q) (G := moduleCoeff (χ ⋙ almostCoeff (OFlat ⊗[Ainf] S)))
        (p : S) (whiskerRight (χ.whiskerLeft redCompl) uliftFunctor) := by
    refine modShortExact_of_isReductionMod (Φ := χ ⋙ P ⋙ Q) (q := χ.whiskerLeft redCompl) fun A ↦ ?_
    have h_perf : PerfectRing (χ.obj A) p := (hχ A).left
    have h_reg_tensor : IsSMulRegular (S ⊗[Ainf] wittOfMaxIdeal) p :=
      isSMulRegular_tensor_of_flat_mod c h_modW hc
        (h_witt.regular.submodule (wittOfMaxIdeal.restrictScalars ℕ) _) h_reg
    exact ⟨Adic.isSMulRegular_completion (isSMulRegular_tensor_witt h_reg_tensor (hχ A)),
      h_compl_mod _⟩
  -- A comparison of derived complete cohomology groups is bijective if it is so modulo `p`.
  have h_dc {D : Type 1} [Category D] (χ : D ⥤ CommAlg OFlat) (L : AbFunctor D) (n : ℕ) :
      IsDerivedComplete (p : S) (H L (moduleCoeff (χ ⋙ P ⋙ Q)) n) :=
    .cohomology (fun _ ↦ .of_isAdicComplete (isAdicComplete h_fg)) L n
  refine .of_mod (h_exact hψ) (h_exact hψ') ?_ (fun n _ ↦ h_dc ψ N n) (h_dc ψ' N') h_red
  -- The square of `redCompl` and `β` commutes: it is its naturality, read in `ULift`.
  ext A x
  exact congrArg ULift.up (ConcreteCategory.congr_hom (redCompl.naturality (β.app A)) x.down)

/-- After `p`-adic completion and `K ⊗ –`, the functors `b ↦ (S ⊗ W(𝔪)) ⊗ W(b)` and
`b ↦ S ⊗ W(b)` are isomorphic, for a period ring pair `(S, K)`: tensored with `W(b)`, the maps of
`exists_comp_eq_tau_smul_id` compose to `τ`, a unit of `K`. Here `W(𝔪) = wittOfMaxIdeal`, for `𝔪`
the maximal ideal of `O♭`. -/
private lemma nonempty_completion_wittOfMaxIdeal_iso {p : ℕ} [ThePrime p] {S K : Type}
    [CommRing S] [Algebra Ainf S] [CommRing K] [Algebra S K] (hK : IsPeriodRingPair p S K) :
    Nonempty ((asModules (wittFunctor (k := OFlat)) ⋙ tensorWith S (S ⊗[Ainf] wittOfMaxIdeal)) ⋙
        moduleCompletion S p ⋙ tensorWith K K ≅
      asModules (wittFunctor (k := OFlat) ⋙ algBaseChange S) ⋙ moduleCompletion S p ⋙
        tensorWith K K) := by
  let P : CommAlg OFlat ⥤ ModuleCat S :=
    asModules (wittFunctor (k := OFlat)) ⋙ tensorWith S (S ⊗[Ainf] wittOfMaxIdeal)
  let Q : ModuleCat S ⥤ ModuleCat S := moduleCompletion S p
  let B : CommAlg OFlat ⥤ CommAlg S := wittFunctor (k := OFlat) ⋙ algBaseChange S
  let G : ModuleCat S ⥤ ModuleCat K := Q ⋙ tensorWith K K
  let τ : S := algebraMap Ainf S tau
  obtain ⟨u₀, v₀, huv₀, hvu₀⟩ := exists_comp_eq_tau_smul_id (p := p) S
  -- Tensoring `u₀`, `v₀` with `W(b)` gives maps `u`, `v` between `P b` and `B b` that compose to
  -- `τ` in both orders.
  let u : P ⟶ asModules B :=
    { app _ := ↟(rTensor _ _ u₀)
      naturality b b' f := hom_ext (tmul_ext fun _ _ ↦ rfl) }
  let v (b : CommAlg OFlat) : (asModules B).obj b ⟶ P.obj b := ↟(rTensor _ _ v₀)
  have huv (b : CommAlg OFlat) : u.app b ≫ v b = τ • 𝟙 (P.obj b) :=
    hom_ext (tmul_ext fun m x ↦ congrArg (fun w ↦ w ⊗ₜ x) (LinearMap.congr_fun huv₀ m))
  have hvu (b : CommAlg OFlat) : v b ≫ u.app b = τ • 𝟙 ((asModules B).obj b) :=
    hom_ext (tmul_ext fun m x ↦ congrArg (fun w ↦ w ⊗ₜ x) (LinearMap.congr_fun hvu₀ m))
  -- `G` sends multiplication by `τ` to a bijection, as `τ` is a unit of `K`.
  have h_tau {X Y : ModuleCat S} (f : X ⟶ Y) (g : Y ⟶ X) (hgf : g ≫ f = τ • 𝟙 Y) :
      Bijective (G.map g ≫ G.map f) := by
    have h_Q : Q.map (τ • 𝟙 Y) = τ • 𝟙 (Q.obj Y) := hom_ext (map_ext'' _ rfl)
    rw [← G.map_comp, hgf, Functor.comp_map, h_Q]
    -- On `K ⊗ Q Y`, `τ • –` is multiplication by the unit `τ` of `K`.
    have h_fun : ⇑(ConcreteCategory.hom ((tensorWith K K).map (τ • 𝟙 (Q.obj Y)))) =
        fun a : K ⊗[S] Q.obj Y ↦ algebraMap S K τ • a := by
      refine funext fun a : K ⊗[S] Q.obj Y ↦ ?_
      -- Both sides are `τ • a`: `simp` unfolds the base change, and the rest is by definition.
      simp [tensorWith, algebraMap_smul]
      rfl
    rw [h_fun]
    exact hK.isUnit_tau.smul_bijective
  exact ⟨isoOfAppBijective (whiskerRight u G) fun b ↦
    ⟨.of_comp (h_tau _ _ (huv b)).injective, .of_comp (h_tau _ _ (hvu b)).surjective⟩⟩

/-- Let `ψ`, `ψ'` be functors to `O♭`-algebras with perfect values on which `pFlat` is regular,
compared by `β` along `φ`, and let `α : N' ⟶ φ ⋙ N`. Let `S` be an `A_inf`-algebra and `K` a flat
`S`-algebra that form a `New.Variety.IsPeriodRingPair`. Suppose that the cohomology of `N` commutes
with flat extension of coefficients. Suppose also that the cohomology of `N'` commutes with `K ⊗ –`
for coefficients that factor through `ψ'`. If the comparison is bijective for the coefficients
`b ↦ b ⊗ (O♭ ⊗ S) ⊗ 𝔪`, `𝔪` the maximal ideal of `O♭`, then it is bijective for the
coefficients `b ↦ K ⊗ (S ⊗ W(b))^`, with `^` the `p`-adic completion. -/
lemma CoeffCompBijective.periodAlg_of_almostCoeff {C C' : Type 1} [Category C] [Category C'] {p : ℕ}
    [ThePrime p] {N : AbFunctor C} {N' : AbFunctor C'} {φ : C' ⥤ C} {α : N' ⟶ φ ⋙ N}
    (hN : HasFlatBaseChange N) {S K : Type} [CommRing S] [Algebra Ainf S] [CommRing K] [Algebra S K]
    [Flat S K] (hK : IsPeriodRingPair p S K) {ψ : C ⥤ CommAlg OFlat} {ψ' : C' ⥤ CommAlg OFlat}
    {β : φ ⋙ ψ ⟶ ψ'}
    (hN' : ∀ G : CommAlg OFlat ⥤ ModuleCat S,
      AllBijective fun n : ℕ ↦ baseChangeMap K K N' (ψ' ⋙ G) n)
    (hψ : ∀ A : C, IsPerfectTorsionFree (ψ A)) (hψ' : ∀ A : C', IsPerfectTorsionFree (ψ' A))
    (h_red : CoeffCompBijective β α (almostCoeff (OFlat ⊗[Ainf] S))) :
    CoeffCompBijective β α (asModules (periodAlg S) ⋙ tensorWith K K) := by
  -- Put `P b = (S ⊗ W(𝔪)) ⊗ W(b)`. Bijectivity lifts from `h_red` to the completion of `P` and
  -- passes to `K ⊗ –` by flatness. After completion and `K ⊗ –`, `P` is isomorphic to
  -- `b ↦ S ⊗ W(b)`, as `τ` is a unit of `K`.
  let P : CommAlg OFlat ⥤ ModuleCat S :=
    asModules (wittFunctor (k := OFlat)) ⋙ tensorWith S (S ⊗[Ainf] wittOfMaxIdeal)
  let B : CommAlg OFlat ⥤ CommAlg S := wittFunctor (k := OFlat) ⋙ algBaseChange S
  let G : ModuleCat S ⥤ ModuleCat K := moduleCompletion S p ⋙ tensorWith K K
  have h_cpl : CoeffCompBijective β α (P ⋙ moduleCompletion S p) :=
    .completion_wittOfMaxIdeal_of_almostCoeff hK.regular hψ hψ' h_red
  obtain ⟨U⟩ : Nonempty (P ⋙ G ≅ asModules B ⋙ G) := nonempty_completion_wittOfMaxIdeal_iso hK
  -- Transport along `U` and along `moduleCompletionIso`, which compares the completions of
  -- modules and of algebras.
  let V : P ⋙ G ≅ B ⋙ asModules (algCompletion S p) ⋙ tensorWith K K :=
    U ≪≫ B.isoWhiskerLeft (isoWhiskerRight (moduleCompletionIso S p) _)
  let γ := isoWhiskerRight V (moduleCoeff (𝟭 (ModuleCat K)))
  refine (isBijective_iff_of_coeff_iso (c := ⟨φ, _⟩) (ψ.whiskerLeft γ.hom) _
    (whiskerLeft_comp_whiskerRight β γ.hom)).mp ?_
  -- By `hN` and `hN'`, `K ⊗ –` carries `h_cpl` to the coefficients `P ⋙ G`.
  exact (IsBijective.baseChangeMap_bijective_iff h_cpl hN).mp (hN' _)

end PeriodLifting

/-!
## Near-zero submodules and the generic fibre of a p-adic test

* `New.Variety.PadicTest.nearZeros`: the submodule of near-zero elements.
* `New.Variety.PadicTest.bijective_locConstAlg_map_algebraMap`: locally constant functions on
  `Spec R` and on `Spec R[1/p]` correspond.
* `New.Variety.genericTestOver`: the functor `c ↦ R[1/p]` to tests over `Ω`.
-/

section TiltedTheoryA

open CategoryTheory TensorProduct PrimeSpectrum Functor CommRingCat Ideal PadicTest MonoidalCategory
  Quotient RingHom LocallyConstant Submodule CommAlgCat ZMod

variable {p : ℕ} [ThePrime p] (c : PadicTest) (I : Ideal c.GenericRing)
  {S X : Type _} [CommRing S] [AddCommMonoid X]

/-- For an additive functor `F` of modules, `moduleCoeff F` is additive. -/
instance (F : ModuleCat S ⥤ ModuleCat S) [F.Additive] : (moduleCoeff F).Additive :=
  instAdditiveComp ..

/-- Near-zero elements. Let `κ f` be submodules of `X` indexed by maps of tests `f : c ⟶ d`, and
let `I` be an ideal of `R[1/p] = c.GenericRing`. This is the submodule of the `y` for which some
`a ∈ I` has `y ∈ κ f` whenever `f` makes `1 - a` a unit. -/
def PadicTest.nearZeros [Module S X] (κ : ∀ {d : PadicTest}, (c ⟶ d) → Submodule S X) :
    Submodule S X where
  carrier :=
    {y : X | ∃ a ∈ I, ∀ (d : PadicTest) (f : c ⟶ d), IsUnit (mapGeneric f (1 - a)) → y ∈ κ f}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    -- `1 - (a + (1 - a) * b) = (1 - a) * (1 - b)` is a unit only where both factors are.
    refine ⟨a + (1 - a) * b, I.add_mem ha (I.mul_mem_left _ hb), fun d f hf ↦ ?_⟩
    rw [← sub_sub, ← mul_one_sub, map_mul, IsUnit.mul_iff] at hf
    exact add_mem (hx d f hf.1) (hy d f hf.2)
  smul_mem' s y := fun ⟨a, ha, hy⟩ ↦ ⟨a, ha, fun d f hf ↦ (κ f).smul_mem s (hy d f hf)⟩

variable (Ω : Type) [CommRing Ω] [Algebra Ω ℂ_[p]]

/-- Every locally constant function on `Spec R[1/p]` with values in `ZMod p` extends uniquely to
`Spec R`, for the ring `R = c.ProdRing` of a `p`-adic test. -/
lemma PadicTest.bijective_locConstAlg_map_algebraMap :
    Function.Bijective (locConstAlg.map (ofHom (algebraMap c.ProdRing c.GenericRing))).hom := by
  -- `R → R[1/p]` is injective, so the map of spectra has dense image.
  have h_dense : DenseRange (PrimeSpectrum.comap (algebraMap c.ProdRing c.GenericRing)) :=
    (denseRange_comap_iff_ker_le_nilRadical _).mpr
      (bot_le.trans' c.eq_zero_of_algebraMap_genericRing)
  refine ⟨fun x y hxy ↦ coe_injective ?_, comapAddMonoidHom_surjective_of_isComparableRing _
    (c.isTest.isComparableRing_of_associated exists_associated_localization)⟩
  exact h_dense.equalizer x.continuous y.continuous (coe_inj.mpr hxy)

/-- The functor sending a `p`-adic test with ring `R` to `R[1/p]`, a test over `Ω` with algebra
structure through `Ω → ℂ_p`. -/
def genericTestOver : PadicTest ⥤ TestOver Ω :=
  ObjectProperty.lift _ (genericAlg ⋙ restrictAlg Ω (ℂ_[p])) (·.isTest.localization)

end TiltedTheoryA

/-!
## Locally constant functions into the tilt and the theory R♭ ⊗ M

Take an ideal `I` of `R[1/p]`. The maps of tests that kill `I` are those whose tilt factors through
the perfect quotient of `R♭` by the ideal `New.Variety.PadicTest.tiltNearZeros`.
-/

section TiltedTheory

open CategoryTheory TensorProduct PrimeSpectrum Functor CommRingCat Ideal Period PadicTest
  MonoidalCategory Quotient RingHom IsLocalization Away NeZero Perfection LocallyConstant Submodule
  CommAlgCat ZMod

section

variable {p : ℕ} [ThePrime p] (c : PadicTest) (I : Ideal c.GenericRing)

/-- The ideal of the tilt `R♭` of `c` of the elements `y` for which some `a ∈ I` has `g♭ y = 0`
for every map of tests `g` that makes `1 - a` a unit, `g♭` the map of tilts: the near-zero
elements (`PadicTest.nearZeros`) for the kernels of the maps of tilts. -/
def PadicTest.tiltNearZeros : Ideal (TiltRing c) :=
  c.nearZeros I fun g ↦ ker (tilt.map g).hom

/-- For a `p`-adic test `c` with ring `R = c.ProdRing`, the natural map of `𝔽_p`-algebras from the
locally constant functions `Spec R[1/p] → 𝔽_p` to the tilt `R♭`. A function is extended to
`Spec R`, restricted to `Spec (R/p)` and read as the element `x` of `R/p` whose germ at each prime
is the value there. It goes to the constant sequence `(x, x, …)`, which lies in `R♭` because
`t ^ p = t` in `𝔽_p`. -/
def locConstToTilt : genericTest ⋙ testIncl ⋙ locConstAlg ⟶ tilt ⋙ restrictAlg (ZMod p) OFlat := by
  let (c : PadicTest) : Algebra (ZMod p) (ModP c.ProdRing p) := algebra ..
  -- `φ c` reads a locally constant function `x` on `Spec (R/p)` as the element of `R/p` whose germ
  -- at each prime `q` is the constant `x q`; here `R = c.ProdRing`.
  choose φ hφ using fun c : PadicTest ↦
    exists_ringHom_of_locallyConstant (ZMod p) (ModP c.ProdRing p)
  -- First map: extend a locally constant function from `Spec R[1/p]` to `Spec R` (the inverse of
  -- restriction). Second map: restrict it to `Spec (R/p)`, read it by `φ` as an element of `R/p`,
  -- and take the constant sequence.
  refine (NatIso.ofComponents (F := ringFunctor ⋙ locConstAlg)
      (G := genericTest ⋙ testIncl ⋙ locConstAlg)
      (fun c ↦ isoMk (.ofBijective
        (locConstAlg.map (ofHom (algebraMap c.ProdRing c.GenericRing))).1
        c.bijective_locConstAlg_map_algebraMap))
      fun _ ↦ ?restrict).inv ≫
    { app c := ConcreteCategory.ofHom (.mk'
        (.codRestrict (.pi fun _ ↦ (φ c).comp (locConstAlg.map (ofHom (mk _))).1.1) (subring ..)
          fun x n ↦ ?root) (map_smul _))
      naturality c d f := ?natural }
  case restrict => exact (locConstAlg.map_commSq ⟨hom_ext (ext (mapGeneric_algebraMap _))⟩).w.symm
  -- The constant sequence lies in the tilt, because `t ^ p = t` in `ZMod p`.
  case root => exact (map_pow (φ c) ..).symm.trans (congrArg _ (ext fun _ ↦ ZMod.pow_card _))
  case natural =>
    -- Compare the images in the localisation of `d.ProdRing/p` at each prime `q`; by `hφ` both are
    -- the value of the function at the image of `q`.
    ext x
    refine ext fun n ↦ toPiLocalization_injective _ (funext fun q ↦ .trans ?_
      (Localization.localRingHom_to_map _ _ (quotientMap _ f.1 (by simp)) (comap_asIdeal ..) _))
    erw [hφ, eq_comm, ← RingHom.comp_apply, ext_zmod (.comp ..)]
    exact .symm (hφ ..)

/-- The functor from test rings to `O♭`-algebras sending `A` to `O♭ ⊗_{𝔽_p} LC(A)`, where `LC(A)` is
the ring of locally constant functions `Spec A → 𝔽_p`. -/
abbrev oFlatLocConst : TestRing ⥤ CommAlg OFlat := (testIncl ⋙ locConstAlg) ⋙ algBaseChange OFlat

/-- The natural map of `O♭`-algebras `O♭ ⊗_{𝔽_p} LC(Spec R[1/p]) → R♭` for `p`-adic tests with
ring `R`, where `LC` denotes the locally constant `𝔽_p`-valued functions. It is the extension of
`locConstToTilt` to `O♭`-algebras, its transpose under base change to `O♭`. -/
def primitiveMap : genericTest ⋙ oFlatLocConst ⟶ tilt :=
  (baseChangeTranspose (genericTest ⋙ testIncl ⋙ locConstAlg) tilt).invFun locConstToTilt

/-- Let `f : c ⟶ d` be a map of `p`-adic tests and `I` an ideal of the generic ring `R[1/p]` of `c`.
Suppose the map of tilts `f♭` kills the ideal `PadicTest.tiltNearZeros c I`, which consists of the
elements `y` of the tilt `R♭` for which some `a ∈ I` has `g♭ y = 0` for every map of tests `g` out
of `c` that makes `1 - a` a unit. Then the induced map `mapGeneric f` of generic rings kills `I`. -/
lemma PadicTest.le_ker_of_tiltNearZeros_le_ker {d : PadicTest} (f : c ⟶ d)
    (hf : c.tiltNearZeros I ≤ ker (tilt.map f).hom) : I ≤ ker (mapGeneric f) := by
  -- Up to a unit `a` comes from some `r` in `c.ProdRing`, and it is enough that every `p ^ n`
  -- divides `f r`. An idempotent `e` with `r ∣ e * p ^ n` and `p ^ n ∣ (1 - e) * r` lies in `I`;
  -- its constant sequence lies in `c.tiltNearZeros I`, so `f e` vanishes modulo `p`, `1 - f e` is
  -- a unit and `p ^ n ∣ f r`.
  intro a ha
  let ι : c.ProdRing →+* c.GenericRing := algebraMap c.ProdRing c.GenericRing
  obtain ⟨r, hr⟩ : ∃ r : c.ProdRing, Associated (ι r) a := exists_associated_localization a
  suffices h_zero : f.toRingHom r = 0 from
    mem_of_dvd _ hr.dvd (by rw [mem_ker, mapGeneric_algebraMap, h_zero, map_zero])
  refine eq_of_forall_pow_dvd_sub (p : d.ProdRing) fun n ↦ ?_
  obtain ⟨e, he, h_dvd, h_dvd'⟩ :
      ∃ e : c.ProdRing, IsIdempotentElem e ∧ r ∣ e * p ^ n ∧ (p : c.ProdRing) ^ n ∣ (1 - e) * r :=
    c.isTest.isComparableRing r (p ^ n)
  -- As `a ∣ r ∣ e * p ^ n` and `p` is a unit of `c.GenericRing`, the idempotent `e` lies in `I`.
  have h_dvd_image : ι r ∣ ι e * ι p ^ n := by simpa only [map_mul, map_pow] using map_dvd ι h_dvd
  have he_mem : ι e ∈ I := I.mem_of_dvd
    (hr.dvd'.trans ((algebraMap_pow_isUnit (p : c.ProdRing) n).dvd_mul_right.mp h_dvd_image)) ha
  -- The constant sequence `ε = (e, e, …)` lies in the tilt, as `e ^ p = e`, and it dies wherever
  -- `1 - e` is a unit.
  let ε : TiltRing c := ⟨fun _ ↦ e, fun _ ↦ congrArg _ (he.pow_eq (NeZero.ne p))⟩
  have hε : ε ∈ c.tiltNearZeros I := by
    refine ⟨ι e, he_mem, fun d' g hg ↦ ?_⟩
    -- `1 - e` is idempotent, so its image is `1` where it is a unit, and then `g e = 0`.
    have h_one : mapGeneric g (1 - ι e) = 1 := hg.mul_eq_left.mp ((he.map ι).one_sub.map _).eq
    rw [_root_.map_sub, map_one, sub_eq_self, c.mapGeneric_algebraMap g e] at h_one
    have h_kill : g.toRingHom e = 0 := d'.eq_zero_of_algebraMap_genericRing _ h_one
    -- Every coordinate of `g♭ ε` is the class of `g e = 0`.
    exact Subtype.ext (funext fun _ ↦ (congrArg (Ideal.Quotient.mk _) h_kill).trans (map_zero _))
  -- So `f♭ ε = 0`, and its zeroth coordinate says that `f e` vanishes modulo `p`.
  have h_mod : f.toRingHom e ∈ Ideal.span {(p : d.ProdRing)} := eq_zero_iff_mem.mp <|
    (congrArg (Perfection.coeff (ModP d.ProdRing p) p 0) (hf hε)).trans (map_zero _)
  -- Then `f e` lies in the Jacobson radical, `1 - f e` is a unit, and `p ^ n ∣ (1 - f e) * f r`
  -- gives `p ^ n ∣ f r`.
  have h_unit : IsUnit (1 - f.toRingHom e) := by
    simpa [neg_add_eq_sub] using mem_jacobson_bot.mp (HenselianRing.jac h_mod) (-1)
  exact h_unit.dvd_mul_left.mp (by simpa using map_dvd f.toRingHom h_dvd')

/-- For an ideal `I` of the generic ring `R[1/p]` of `c`, the quotient of the tilt `R♭` by the
ideal `PadicTest.tiltNearZeros c I` is perfect. -/
lemma PadicTest.perfectRing_quotient_tiltNearZeros :
    PerfectRing (TiltRing c ⧸ c.tiltNearZeros I) p := by
  -- The ideal is radical, since the kernel of a map to a reduced ring is radical.
  have h_reduced : IsReduced (TiltRing c ⧸ c.tiltNearZeros I) := by
    refine (isRadical_iff_quotient_reduced _).mp fun y hy_rad ↦ ?_
    obtain ⟨n, a, ha, hy_pow⟩ : ∃ n : ℕ, ∃ a ∈ I, ∀ (d : PadicTest) (f : c ⟶ d),
        IsUnit (mapGeneric f (1 - a)) → y ^ n ∈ ker (tilt.map f).hom := hy_rad
    refine ⟨a, ha, fun d f hf ↦ ?_⟩
    have : IsReduced (tilt.obj d) := isReduced_of_perfectRing (isPerfectTorsionFree_tilt d).left
    exact isRadical_bot.comap _ ⟨n, hy_pow d f hf⟩
  -- Every class is a `p`-th power, since the tilt itself is perfect.
  refine perfectRing_of_pow_surjective natCast_eq_zero_of_algebra_oFlat fun z ↦ ?_
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, rfl⟩ : ∃ x : TiltRing c, x ^ p = y :=
    c.isPerfectTorsionFree_tilt.left.bijective_frobenius.surjective y
  exact ⟨Ideal.Quotient.mk _ x, (map_pow _ x p).symm⟩

/-- Let `M` be an `O♭`-module and `J = PadicTest.tiltNearZeros c I`. Let `x ∈ R♭ ⊗_{O♭} M` have
image zero in `(R♭ ⧸ J) ⊗ M`. Then the same holds for `x` and the maps `g♭ ⊗ M`, `g♭` the map of
tilts: for some `a ∈ I`, `(g♭ ⊗ M) x = 0` for every map of tests `g` that makes `1 - a` a unit. -/
lemma PadicTest.mem_nearZeros_of_rTensor_eq_zero (M : ModuleCat OFlat) (x : TiltRing c ⊗[OFlat] M)
    (hx : (mkₐ OFlat (c.tiltNearZeros I)).toLinearMap.rTensor M x = 0) :
    x ∈ c.nearZeros I fun {d : PadicTest} (f : c ⟶ d) ↦
      ((tilt ⋙ tensorCoeff M).map f).hom.ker := by
  let J : Submodule OFlat (TiltRing c) := (c.tiltNearZeros I).restrictScalars OFlat
  -- By right exactness `x` is a sum of tensors `y ⊗ m` with `y` in `J`. The set is written in the
  -- form used by `range_map_eq_span_tmul`.
  have h_span : x ∈ Submodule.span OFlat
      {t : TiltRing c ⊗[OFlat] M | ∃ (y : J) (m : M), J.subtype y ⊗ₜ LinearMap.id m = t} :=
    (range_map_eq_span_tmul ..).le ((rTensor_mkQ M J).le hx)
  -- Each `y ⊗ m` with `y ∈ J` dies along the maps along which `y` dies.
  refine mem_span.mp h_span _ ?_
  rintro _ ⟨⟨y, a, ha, hy⟩, m, rfl⟩
  refine ⟨a, ha, fun d f hf ↦ ?_⟩
  -- The map `f♭ ⊗ M` sends `y ⊗ m` to `f♭ y ⊗ m = 0`.
  exact (congrArg (fun z : tilt.obj d ↦ z ⊗ₜ[OFlat] m) (hy d f hf)).trans (zero_tmul _ m)

end

/-- The theory (`New.Variety.Theory`, for the prime `ℓ = p`) on `p`-adic tests along `R ↦ R[1/p]`
(`New.Variety.genericTestOver`), with coefficients `R ↦ R♭ ⊗_{O♭} M`. It needs `p` invertible in
`Ω`, and every perfect `O♭`-algebra acyclic for these coefficients (`ac`,
`New.Variety.IsAcyclicOnPerfect`). For an ideal `I` of `R[1/p]`, the maps of tests that kill `I` are
those whose tilt factors, uniquely, through the perfect quotient `R♭ ⧸ J`, with
`J = PadicTest.tiltNearZeros c I`. Besides `p` killing the coefficients and Zariski descent (tilting
and `· ⊗ M` keep products), this gives the two other properties of a theory: restriction of
cohomology to these maps is onto, and a section that dies along them vanishes near every maximal
ideal containing `I`. -/
def tiltTheory {p : ℕ} (Ω : Type) [CommRing Ω] [InvertsPrime Ω p] [Algebra Ω ℂ_[p]]
    (M : ModuleCat OFlat) (ac : IsAcyclicOnPerfect (moduleCoeff (tensorCoeff M))) :
    Theory (genericTestOver Ω) :=
  let J (c : PadicTest) (I : Ideal c.GenericRing) : Ideal (TiltRing c) :=
    c.nearZeros I fun f ↦ ker (tilt.map f).hom
  -- The maps that kill `I` are those whose tilt factors, uniquely, through the perfect algebra
  -- `TiltRing c ⧸ J c I`.
  have h_supp (c : PadicTest) (I : Ideal c.GenericRing) :=
    surjective_and_map_eq_zero_of_quotient_sieve tilt
      (R := killingMaps (ringOf (genericTestOver Ω)) I)
      (CommAlgCat.ofHom (mkₐ OFlat (J c I)))
      (fun {d} f hf ↦ by
        have h_kill : ∀ y ∈ J c I, (tilt.map f).hom y = 0 := fun y ⟨a, ha, hy⟩ ↦
          hy d f (by simp [show mapGeneric f a = 0 from le_comap_of_map_le hf.le ha])
        refine ⟨ofHom (liftₐ _ (tilt.map f).hom h_kill), rfl, fun g hg ↦ ?_⟩
        ext ⟨y⟩
        exact ConcreteCategory.congr_hom hg y)
      (fun f g hg ↦ (map_eq_bot_iff_le_ker _).2 <| c.le_ker_of_tiltNearZeros_le_ker I f fun y hy ↦
        RingHom.mem_ker.mpr <| (ConcreteCategory.congr_hom hg y).symm.trans
          (mk_ker.ge.trans (ker_le_comap (K := ker g.hom) _) hy))
      (@ac (CommAlgCat.of OFlat (c.TiltRing ⧸ J c I)) (c.perfectRing_quotient_tiltNearZeros I))
  { functor := tilt ⋙ moduleCoeff (tensorCoeff M)
    prime_smul_eq_zero c x := ULift.down_injective (show p • x.down = 0 by
      simp [natCast_eq_zero_of_algebra_oFlat, ← Nat.cast_smul_eq_nsmul OFlat])
    -- Zariski descent: tilting and `· ⊗ M` keep the product of two tests. The rings `R[1/p]` do
    -- not depend on the ground field in `hasZariskiDescent_genericOver`, so `ℚ` will do.
    zariski_descent :=
      letI : EmbeddedInQpBar p ℚ := {}
      hasZariskiDescent_genericOver (k := ℚ) (𝟭 PadicTest)
        ⟨exists_isQuotientByElem, fun f g hfg ↦ (bijective_prod_tilt f g hfg).map_prod
          (moduleCoeff (MonoidalCategory.tensorRight M) ⋙ forget AddCommGrpCat)⟩
    -- By `h_supp` it is enough that `R♭ ⊗ M → (R♭ ⧸ J) ⊗ M` is onto.
    restrict_surjective c I :=
      (h_supp c I).1 (ULift.map_surjective.2 (LinearMap.rTensor_surjective M Quot.exists_rep))
    dies_near c I x hx n hn hI := by
      -- By `h_supp`, `x` has image zero in `(R♭ ⧸ J) ⊗ M`.
      obtain ⟨a, ha, h_dies⟩ :=
        c.mem_nearZeros_of_rTensor_eq_zero I M x.down (congrArg ULift.down ((h_supp c I).2 x hx))
      -- `1 - a ∉ n`, since `a ∈ I ≤ n` and `1 ∉ n`.
      exact ⟨(1 - a : c.GenericRing), (n.sub_mem_iff_left (hI ha)).1.mt n.one_notMem, fun d f hf ↦
        congrArg _ (h_dies d f hf)⟩ }

end TiltedTheory

end New.Variety

end
