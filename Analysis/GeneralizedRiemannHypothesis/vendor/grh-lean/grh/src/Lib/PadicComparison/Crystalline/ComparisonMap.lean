import Lib.PadicComparison.Crystalline.DividedPowerEnvelope
import Lib.PadicComparison.Primitive.PeriodCoefficients

/-!
# Crystalline comparison: bijectivity on étale charts and spanning of period cohomology

Write A_inf = `New.Period.Ainf`, A_max = `New.Period.Amax`, B_max = `New.Period.Bmax`, and 𝔡(B) =
`New.Variety.pdIdeal` B for the ideal of the x with n! ∣ x^n for all n. Here ξ = `New.Period.xi`
generates the kernel of θ : A_inf → O_C. Fix an action of A_inf on A_max satisfying
`New.Variety.CrysPeriodAlgebra`. For a functor P on O_C-algebras, the crystalline comparison
compares two cohomologies. The first is that of D ↦ P(D/𝔡(D)) on p-torsion-free p-complete
A_max-algebras D, with coefficients B_max ⊗ D. The second is that of P on p-adic tests. Finally, let
S be a complete discrete valuation ring with uniformiser p, let O_C be an algebra over a ring R with
a map R → S/𝔡(S), let A_max be an S-algebra, and assume a given natural map from D ↦ D/𝔡(D) (as
R-algebras via O_C → A_max/𝔡(A_max)) to D ↦ D/𝔡(D) (via R → S/𝔡(S)) on p-torsion-free p-complete
A_max-algebras is an isomorphism; let V be a subfunctor of a functor X on R-algebras with
`New.Variety.IsCharting` V (V covers X and is built from charts étale over tori). Then the classes
pulled back from D ↦ V(D/𝔡) on p-torsion-free p-complete S-algebras span the period cohomology of V
over B_max when it is finite.

## Main definitions and results

* `New.Variety.CrysPeriodAlgebra`: the properties of an A_inf-algebra structure on A_max that the
  comparison needs.
* `New.Variety.exists_crysPeriodAlgebra`: for each y in O_C with p ∣ y^N, there is an algebra
  structure as in `New.Variety.CrysPeriodAlgebra` that is equivariant for Frobenius and Galois and
  whose map O_C → A_max/𝔡(A_max) kills y.
* `New.Variety.HasCrysComparison`: the comparison along `New.Variety.crysThickening` and
  `New.Variety.testToPdReduction` is bijective in every degree.
* `New.Variety.hasCrysComparison_of_witt`, `New.Variety.hasCrysComparison_of_etale`:
  `New.Variety.HasCrysComparison` holds for P = Hom_{A_inf}(T, −), with scalars restricted from O_C
  to A_inf, when the A_inf-algebra T maps to W(b), for a perfect π-torsion-free O^♭-algebra b, by a
  map bijective on p-adic completions. It also holds for P = Hom(B, −) with B étale over O_C[G],
  where G is a ℚ≥0-module.
* `New.Variety.hasCrysComparison_chart`: the comparison holds for Hom_R(B, −) on O_C-algebras when B
  is étale over R[X_1, …, X_d], each X_i going to a unit t_i. Adjoining all roots of the t_i reduces
  it to `New.Variety.hasCrysComparison_of_etale`.
* `New.Variety.span_range_crysComparison_pull_eq_top`: for S a complete discrete valuation ring with
  uniformiser p, the classes pulled back from the cohomology of D ↦ V(D/𝔡) span the period
  cohomology of V over B_max when it is finite.

Notions from other files:
* `New.OC`: The ring of integers O_C of the field C_p of p-adic complex numbers.
* `New.Period.OFlat`: The ring O^♭, the inverse limit of O_C/p along x ↦ x^p;
  π = p♭ = `New.Variety.pFlat` is ξ mod p, the zeroth Witt coefficient of ξ.
* `New.Variety.PadicTest`: A p-adic test: a non-empty family of cells (`New.Variety.IsCell`) with a
  ring map from O_C to their product S (`ProdRing`); S^♭ is the tilt of S and θ : W(S^♭) → S is
  Fontaine's map.
* `New.Period.Amax`: Colmez's period ring A_max, the p-adic completion of A_inf[X]/(pX − ξ).
* `New.Variety.compatibleRoots`: The functor of characters ℚ≥0 → A on O_C-algebras A, with the twist
  by s ↦ (ε^s)^♯ as an endomorphism (a functor on O_C-algebras × Bℕ, `New.Variety.TimesBNat`).
* `New.Variety.IsLine`: A map Y → U from a functor with an endomorphism is a line if the cohomology
  of U maps bijectively to that of Y on the product with Bℕ.

## Relation to the literature

Known result: Crystalline comparison for p-adic étale cohomology with good reduction. Only
crystallinity is proved here. It is for cohomology on p-adic test rings, which is not identified
with étale cohomology. There is no filtration and no identification with crystalline cohomology.
Invariants come from p-complete torsion-free rings modulo elements with divided powers, and they are
compared on toric towers one coordinate at a time. Source: Bhatt, Morrow, Scholze, Integral p-adic
Hodge theory, 2018, Publ. IHÉS 128, Thm 1.1(i) (first proved in Faltings, Crystalline cohomology and
p-adic Galois representations, 1989); for the site, Bhatt, Prismatic F-gauges, 2022, Rem. 2.5.12;
for the line lemma, Andreatta–Brinon, Acyclicité géométrique de B_cris relatif, 2013, Comment. Math.
Helv. 88.
-/

noncomputable section

namespace New.Variety

/-!
## Frobenius-twisted actions of A_inf on A_max and their existence

The crystalline comparison uses A_max = `New.Period.Amax` as an algebra over A_inf =
`New.Period.Ainf` through a structure as in `New.Variety.CrysPeriodAlgebra`;
`New.Variety.exists_crysPeriodAlgebra` builds one from the usual map composed with a power of
Frobenius.

* `New.Variety.integersToPdQuotient`: the ring map O_C → A_max/𝔡(A_max) induced by such an algebra
  structure.
-/

section CrystallinePeriod

open CategoryTheory Ideal Quotient Period Amax WittVector Algebra Lift

variable {p : ℕ} [ThePrime p]

/-- B_max is flat over A_max. -/
instance : Module.Flat Amax Bmax := by apply_rules +allowSynthFailures [Localization.flat]

/-- The coefficient functor on p-torsion-free p-complete A_max-algebras sending D to B_max
⊗_{A_max} D. -/
abbrev crysPeriodCoeff : AbFunctor (CrysTest Amax) :=
  moduleCoeff (asModules (ObjectProperty.ι _) ⋙ tensorWith Bmax Bmax)

/-- Conditions on an A_inf-algebra structure on A_max: A_max is p-torsion-free and p-complete, p
divides the image of ξ, the image of τ becomes a unit in B_max (`New.Variety.IsPeriodRingPair`), p³
divides the image of μ, and the image of μ becomes a unit in B_max. Here μ = [ε] − 1
(`New.Period.mu`) and τ = [ε^{1/p}] − 1 (`New.Period.tau`), so that ξτ = μ. -/
class CrysPeriodAlgebra extends Algebra Ainf Amax, IsPeriodRingPair p Amax Bmax where
  /-- The image of μ in A_max is divisible by p³. -/
  p_cube_dvd_mu : (p : Amax) ^ 3 ∣ algebraMap mu
  /-- The image of μ in B_max is a unit. -/
  isUnit_mu : IsUnit (ofId Amax Bmax (algebraMap mu))

/-- The ring map O_C → A_max/𝔡(A_max) obtained by factoring A_inf → A_max/𝔡(A_max) through
Fontaine's surjection θ: A_inf → O_C. -/
def integersToPdQuotient [h : CrysPeriodAlgebra] : OC →+* Amax ⧸ pdIdeal Amax :=
  -- The kernel of `theta` is generated by `xi`, whose image is a multiple of `p ∈ pdIdeal Amax`.
  RingHom.liftOfSurjective theta theta_surjective
    ⟨algebraMap Ainf (Amax ⧸ pdIdeal Amax), fun _ ha ↦
      eq_zero_iff_mem.mpr
        (mem_of_dvd (pdIdeal Amax) (by grw [h.dvd_xi, theta_eq_zero_iff_xi_dvd.mp ha])
          h.p_mem_pdIdeal)⟩

/-- For t in O^♭, the map `New.Variety.integersToPdQuotient` sends the untilt t^♯ of t to the class
of the image of the Teichmüller lift [t] under the algebra structure h. -/
lemma integersToPdQuotient_untilt [h : CrysPeriodAlgebra] (t : OFlat) :
    integersToPdQuotient t.untilt = h.algebraMap (teichmuller p t) := by
  rw [← theta_teichmuller t]
  exact theta.liftOfSurjective_comp_apply ..

/-- For every N and every y in O_C with p dividing y^N, there is an A_inf-algebra structure on
A_max, satisfying `New.Variety.CrysPeriodAlgebra`, such that (a) ℤ_p acts on A_max through A_inf as
it does directly, (b) the structure map commutes with the action of the monoid
`New.Period.FrobGal` generated by Frobenius and G_p, and (c) the map O_C → A_max/𝔡(A_max) of
`New.Variety.integersToPdQuotient` kills y. -/
lemma exists_crysPeriodAlgebra {N : ℕ} {y : OC} (hy : ↑p ∣ y ^ N) :
    ∃ h : CrysPeriodAlgebra,
      -- (a)
      IsScalarTower ℤ_[p] Ainf Amax ∧
      -- (b)
      (∀ (m : FrobGal) (a : Ainf), m • h.algebraMap a = h.algebraMap (m • a)) ∧
      -- (c)
      integersToPdQuotient y = 0 := by
  -- Let `Ainf` act through `σ = φ ^ max N 3` followed by the usual map to `Amax`.
  -- The usual map sends the ideal `(p, ξ)` into `(p)`, and its powers into the powers of `(p)`.
  have p_dvd_algebraMap_of_mem {a : Ainf} (ha : a ∈ span {↑p, xi}) :
      (p : Amax) ∣ algebraMap Ainf Amax a := by
    simpa using p_pow_dvd_of_mem_pow (n := 1) (by rwa [pow_one])
  let σ : FrobGal := (.ofAdd (N ⊔ 3), 1)
  -- `σ μ = [ε] ^ p ^ max N 3 - 1` lies in `(p, ξ) ^ max N 3`, as `[ε] ≡ 1` modulo `ξ`.
  have h_xi_dvd : xi ∣ teichmuller p epsTilt - 1 := Dvd.intro tau xi_mul_tau
  have hmu : σ • mu ∈ span {↑p, xi} ^ (N ⊔ 3) := by
    simpa [σ, mu, FrobGal.smul_def] using pow_p_pow_sub_mem_of_xi_dvd h_xi_dvd (N ⊔ 3)
  let twisted : Algebra Ainf Amax := compHom Amax (MulSemiringAction.toRingHom FrobGal Ainf σ)
  -- Both `τ` and `μ` divide `μ`, so their images under `σ` become units of B_max.
  let h : CrysPeriodAlgebra :=
    { toAlgebra := twisted
      isCompleteTorsionFree := { regular := .of_ne_zero NeZero.out, complete := {} }
      dvd_xi := p_dvd_algebraMap_of_mem (smul_xi_mem_span σ)
      isUnit_tau := isUnit_smul_of_dvd_mu σ (Dvd.intro_left xi xi_mul_tau)
      p_cube_dvd_mu := p_pow_dvd_of_mem_pow (pow_le_pow_right le_sup_right hmu)
      isUnit_mu := isUnit_smul_of_dvd_mu σ dvd_rfl }
  refine ⟨h, .of_algebraMap_eq fun x ↦ ?_, ?_, ?_⟩
  · -- `σ` fixes `ℤ_[p]`
    rw [compHom_algebraMap_eq]
    aesop
  · -- `σ` is central in `FrobGal`
    simp [σ, compHom_algebraMap_eq, smul_smul, mul_comm]
  · -- Write `y = t♯`; its image is the class of `σ [t]`, which is in `(p, ξ)` since the constant
    -- coefficient `σ t` has untilt `y ^ p ^ max N 3`, a multiple of `y ^ N`, hence of `p`.
    obtain ⟨t, rfl⟩ := untilt_surjective_of_isAbsIntegrallyClosed (p := p) y
    have hσt : σ • (teichmuller p t : Ainf) ∈ span {↑p, xi} := by
      -- Compare constant coefficients, then their untilts; that of `ξ` divides `p`.
      grw [Witt.mem_span_pair_iff, ← untilt_dvd_iff, untilt_constantCoeff_xi_dvd_p, hy]
      simp [σ, untilt_frobGal_smul, smul_teichmuller, pow_dvd_pow,
        (Nat.lt_pow_self Fact.out).le.trans']
    rw [integersToPdQuotient_untilt t]
    exact eq_zero_iff_mem.mpr (mem_of_dvd _ (p_dvd_algebraMap_of_mem hσt) h.p_mem_pdIdeal)

end CrystallinePeriod

/-!
## The comparison map and its bijectivity for étale algebras over O_C[G]

* `New.Variety.crysThickening`: a test S goes to D_S, the p-adic completion of A_max ⊗ W(S^♭).
* `New.Variety.testToPdReduction`: the O_C-algebra map S → D_S/𝔡(D_S) with θ(x) ↦ 1 ⊗ x.
-/

section CrystallineEtale

open CategoryTheory ConcreteCategory Ideal Function Period ObjectProperty CommAlgCat ULift RingHom
  PadicTest
open WittVector hiding map_surjective

variable {p : ℕ} [ThePrime p] [h : CrysPeriodAlgebra]

/-- The functor sending a p-adic test S to the p-adic completion of A_max ⊗_{A_inf} W(S^♭), a
p-torsion-free p-complete A_max-algebra. -/
def crysThickening : PadicTest ⥤ CrysTest Amax :=
  ObjectProperty.lift _ (tilt ⋙ periodAlg Amax) fun c : PadicTest ↦
    isCompleteTorsionFree_completion
      (isSMulRegular_tensor_witt h.regular c.isPerfectTorsionFree_tilt)

/-- The quotient map E → E/𝔡(E), natural in the p-torsion-free p-complete A_max-algebra E, as a map
of A_inf-algebras; A_inf acts on E through the algebra structure h and on E/𝔡(E) through θ and
`New.Variety.integersToPdQuotient`. -/
def toPdReduction :
    ObjectProperty.ι _ ⋙ restrictAlg Ainf Amax ⟶
      pdReduction integersToPdQuotient ⋙ restrictAlg Ainf OC where
  app E :=
    CommAlg.homOfRingHom (pdQuotientMk _) fun a ↦ by
      -- An element `a` of `Ainf` acts on `E ⧸ pdIdeal E` through `integersToPdQuotient (θ a)`, the
      -- image of `a` by the lift along `θ`. `erw`: the algebra structure needs unfolding.
      erw [eq_comm, RingHom.comp_apply, RingHom.comp_apply, liftOfSurjective_comp_apply]
      rfl

/-- For a p-adic test with ring S, the O_C-algebra map S → D/𝔡(D), where D is the p-adic completion
of A_max ⊗ W(S^♭): the inverse of the isomorphism O_C ⊗ W(S^♭) ≅ S
(`New.Variety.PadicTest.thetaIso`) followed by the map O_C ⊗ W(S^♭) → D/𝔡(D) induced by W(S^♭) → D
and `New.Variety.toPdReduction`. It sends θ(x) to the class of 1 ⊗ x
(`New.Variety.testToPdReduction_theta`). -/
@[irreducible]
def testToPdReduction : algFunctor ⟶ crysThickening ⋙ pdReduction integersToPdQuotient :=
  -- The `Ainf`-algebra map `W A → Amax ⊗ W A → periodAlg A`, to be applied to the tilt `A` of the
  -- test's ring `S`.
  let toAm :=
    baseChangeTranspose wittFunctor (periodAlg Amax)
      (wittFunctor.whiskerLeft ((algBaseChange Amax).whiskerLeft (algCompletion.of Amax p)))
  -- It is followed by reduction modulo `𝔡` and extended `OC`-linearly to `OC ⊗ W A ≅ S`.
  thetaIso.inv ≫
    (baseChangeTranspose ..).invFun
      (tilt.whiskerLeft toAm ≫ by exact crysThickening.whiskerLeft toPdReduction)

/-- For a p-adic test `c` with ring S and x in W(S^♭), `New.Variety.testToPdReduction` sends θ(x), θ
Fontaine's map, to the class of 1 ⊗ x in D/𝔡(D), D the p-adic completion of A_max ⊗ W(S^♭) over
A_inf. Here `.of _ _` is the map `AdicCompletion.of` into D and `Quot.mk _` the class modulo
𝔡(D). -/
lemma testToPdReduction_theta (c : PadicTest) (x : WittVector p (PreTilt c.ProdRing p)) :
    testToPdReduction c (fontaineTheta c.ProdRing p x) = Quot.mk _ (.of _ _ (1 ⊗ₜ x)) := by
  -- `θ x` is the image of `1 ⊗ₜ x` under `thetaIso`, which cancels against its inverse in
  -- `testToPdReduction`; the remaining map sends `s ⊗ₜ x` to `s` times the class of `1 ⊗ₜ x`.
  refine .trans ?_ (one_smul OC _)
  -- `erw`: the rewrites need the irreducible `testToPdReduction` and the coercions of `thetaIso`
  -- unfolded.
  erw [← thetaIso_hom_one_tmul, testToPdReduction, ← NatTrans.comp_app_apply, Iso.hom_inv_id_assoc]
  rfl

/-- For a functor P from O_C-algebras to types, `HasCrysComparison P` says that restriction along
`New.Variety.crysThickening` and `New.Variety.testToPdReduction` is bijective in every degree. It
goes from the cohomology of D ↦ P(D/𝔡(D)) on p-torsion-free p-complete A_max-algebras D, with
coefficients B_max ⊗ D, to that of S ↦ P(S) on p-adic tests, with coefficients B_max ⊗ D_S,
D_S = `crysThickening` S. -/
def HasCrysComparison : CommAlg OC ⥤ Type 1 → Prop :=
  (Comparison.restrict crysThickening crysPeriodCoeff).IsBijectiveOn testToPdReduction

/-- Let E be a p-torsion-free p-complete A_max-algebra, 𝔡(E) the ideal `New.Variety.pdIdeal`, and b
a perfect O^♭-algebra, with A_inf acting on A_max through the standing structure
`h : CrysPeriodAlgebra`. Then every A_inf-algebra map from the Witt vectors W(b) to E/𝔡(E) lifts
uniquely to an A_inf-algebra map W(b) → E. Here A_inf acts on E/𝔡(E) through θ and
`integersToPdQuotient`, and the lift means that composing with the quotient map
`New.Variety.toPdReduction` : E → E/𝔡(E) is a bijection. -/
lemma bijective_comp_toPdReduction_app (E : CrysTest Amax) (b : CommAlg OFlat) [PerfectRing b p] :
    Bijective fun g : wittFunctor.obj b ⟶ (restrictAlg Ainf Amax).obj E.obj ↦
      g ≫ toPdReduction.app E := by
  rw [bijective_iff_existsUnique]
  rintro ⟨f, f_comm⟩
  -- `p = 0` in `E / 𝔡`, so `f` kills `p W b` and factors as `F ∘ constantCoeff`.
  obtain ⟨-, -, h_ker, -⟩ := isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat b
  have ker_le : RingHom.ker constantCoeff ≤ RingHom.ker f := by
    rw [h_ker]
    exact (span_singleton_le_iff_mem _).mpr ((map_natCast f p).trans E.p_eq_zero_mod_pdIdeal)
  obtain ⟨F, rfl⟩ : ∃ F : b →+* E.obj ⧸ pdIdeal E.obj, F.comp constantCoeff = f :=
    ⟨_, constantCoeff.liftOfSurjective_comp (constantCoeff_surjective p) ⟨f, ker_le⟩⟩
  obtain ⟨w, hw, w_unique⟩ :
      ∃! w : WittVector p b →+* E.obj, ∀ x : WittVector p b,
        pdQuotientMk E.obj (w x) = F (x.coeff 0) :=
    E.property.existsUnique_witt_lift natCast_eq_zero_of_algebra_oFlat F
  -- `w` is `Ainf`-linear: on `Ainf = W OFlat` both sides lift the same map to `E / 𝔡`.
  have w_comm : w.comp (WittVector.map (algebraMap OFlat b)) =
      algebraMap Ainf ((restrictAlg Ainf Amax).obj E.obj) :=
    (E.property.existsUnique_witt_lift natCast_eq_zero_of_algebra_oFlat
        (F.comp (algebraMap OFlat b))).unique (fun x ↦ hw (.map _ x))
      fun x ↦ ((toPdReduction.app E).hom.commutes x).trans (f_comm x).symm
  refine ⟨CommAlg.homOfRingHom w (RingHom.congr_fun w_comm), ext_apply hw, ?_⟩
  -- Any other lift `g` lifts `F ∘ constantCoeff` as `w` does, so it is `w`.
  intro g hg
  have hg_eq_w : g.hom.toRingHom = w := w_unique _ (ConcreteCategory.congr_hom hg)
  exact ext_apply (RingHom.congr_fun hg_eq_w)

open scoped TensorProduct in
/-- Let b be a perfect π-torsion-free O^♭-algebra (π = ξ mod p, `New.Variety.pFlat`), and let
k : T → W(b) be an A_inf-algebra map that induces a bijection of p-adic completions. Then the
crystalline comparison `New.Variety.HasCrysComparison` is bijective for S ↦ Hom_{A_inf}(T, S) on
O_C-algebras, with scalars restricted to A_inf. -/
lemma hasCrysComparison_of_witt (b : FullSubcategory IsPerfectTorsionFree)
    {T : CommAlg (WittVector p OFlat)} (k : T ⟶ wittFunctor.obj b.obj)
    (hk : IsCompletionBijective p k.hom.toLinearMap) :
    HasCrysComparison (restrictAlg Ainf OC ⋙ reprBy T) := by
  -- Both `Hom(T, E / 𝔡)` on `CrysTest Amax` and `Hom(T, S)` on tests are represented through `b`:
  -- the first by `A = periodAlg b`, the second is `Hom(b, S^♭)`. So the claim is the comparison for
  -- these functors (`Comparison.isBijective_congr`), where both cohomologies are read off at `b`.
  obtain ⟨h_perf, h_reg⟩ : PerfectRing b.obj p ∧ IsSMulRegular b.obj pFlat := b.property
  let A : CrysTest Amax := ⟨(periodAlg Amax).obj b.obj,
    isCompleteTorsionFree_completion (isSMulRegular_tensor_witt h.regular ⟨h_perf, h_reg⟩)⟩
  let toAm : tilt ⋙ reprBy b.obj ⟶ crysThickening ⋙ reprBy A :=
    tilt.whiskerLeft (pointMap (Y := periodAlg .. ⋙ reprBy _) ⟨𝟙 _⟩) ≫
      .mk fun _ ↦ by exact ↾fun f ↦ ⟨⟨f.down⟩⟩
  refine Iff.mpr (Comparison.isBijective_congr (v := toAm)
    (p := pointMap ⟨k ≫ algBaseChangeAdj.homEquiv _ _ ((algCompletion.of ..).app _) ≫
      toPdReduction.app A⟩)
    (p' := homTiltIso.hom ≫ algFunctor.whiskerLeft (pointMap ⟨k ≫ algBaseChangeAdj.unit.app _⟩)) ?_
    (.of_bijective fun E ↦ ?_) (.of_bijective fun c ↦ ?_)) ?_
  · -- The square commutes: both ways send `x` in `W b` to the class of `1 ⊗ₜ x`
    -- (`testToPdReduction_theta`).
    ext
    refine up_inj.mpr (ext_apply fun _ ↦ (congrArg _ (thetaIso_hom_one_tmul ..)).trans ?_)
    exact (testToPdReduction_theta ..).trans (congrArg _ (.symm (adicMap_algebraMap ..)))
  · -- `Hom(A, E) = Hom(Amax ⊗ W b, E) = Hom(W b, E) = Hom(W b, E / 𝔡) = Hom(T, E / 𝔡)`; the ring
    -- `E / 𝔡` is complete because `p = 0` there.
    let X : CommAlg Amax := (algBaseChange Amax).obj (wittFunctor.obj b.obj)
    have bij_cpl : Bijective fun g : (algCompletion Amax p).obj X ⟶ E.obj ↦
        (algCompletion.of Amax p).app X ≫ g :=
      (isCompletionBijective_completion (S := Amax) (B := X)).comp_bijective
        ((algCompletion.of Amax p).app X) E.property.complete
    refine map_bijective.mpr ((hk.comp_bijective _ ?_).comp
      ((bijective_comp_toPdReduction_app E b.obj).comp
      ((algBaseChangeAdj.homEquiv _ _).bijective.comp
        (bij_cpl.comp InducedCategory.homEquiv.bijective))))
    -- `p = 0` in `E / 𝔡`, so the `p`-adic topology there is discrete.
    show IsAdicComplete (span {(p : E.obj ⧸ pdIdeal E.obj)}) (E.obj ⧸ pdIdeal E.obj)
    rw [E.p_eq_zero_mod_pdIdeal, span_singleton_zero]
    infer_instance
  · -- `Hom(b, S^♭) = Hom(OC ⊗ W b, S) = Hom(W b, S) = Hom(T, S)`.
    exact ((map_bijective.mpr (hk.comp_bijective _ c.isAdicComplete_prodRing)).comp
      (pointMap_algBaseChange_unit_bijective ..)).comp
      (homTiltIso.app _).toEquiv.bijective
  · -- Almost descent (`isAcyclicOnPerfect_almostCoeff`) gives the comparison for the coefficients
    -- `b ⊗ (OFlat ⊗ Amax) ⊗ 𝔪`; `CoeffCompBijective.periodAlg_of_almostCoeff` lifts it to the
    -- coefficients `Bmax ⊗ periodAlg b`. In both uses of `transfer` the maps of coefficients are
    -- identities and the points correspond by definition.
    let tiltTorsionFree : PadicTest ⥤ FullSubcategory IsPerfectTorsionFree :=
      lift _ tilt isPerfectTorsionFree_tilt
    let u : tilt ⋙ reprBy b.obj ⟶ tiltTorsionFree ⋙ reprBy b := .mk fun _ ↦ ↾fun f ↦ ⟨⟨f.down⟩⟩
    have h_almost : CoeffCompBijective (𝟙 (tiltTorsionFree ⋙ ι _)) (freeAbMap u)
        (almostCoeff (OFlat ⊗[Ainf] Amax)) := by
      refine (isAcyclicOnPerfect_almostCoeff h.pFlat_smul_eq_zero b.obj).transfer bijective_id
        fun c f x ↦ ?_
      rw [Functor.whiskerRight_id']
      rfl
    have h_period : CoeffCompBijective (𝟙 (tiltTorsionFree ⋙ ι _)) (freeAbMap u)
        (asModules (periodAlg Amax) ⋙ tensorWith Bmax Bmax) :=
      h_almost.periodAlg_of_almostCoeff (hasFlatBaseChange_freeAb_reprBy _) h.toIsPeriodRingPair
        (fun _ _ ↦ hasFlatBaseChange_of_iso_reprBy homTiltIso.symm ..) (fun b ↦ b.property)
        isPerfectTorsionFree_tilt
    refine .transfer h_period bijective_id fun c f x ↦ ?_
    rw [Functor.whiskerRight_id']
    rfl

omit h in
open AddMonoidAlgebra Algebra TensorProduct AlgebraMonoidAlgebra in
/-- Let G be a commutative monoid that is a module over ℚ≥0, T an étale algebra over the monoid
algebra A_inf[G] (and an A_inf-algebra through it), and b = O^♭[G] ⊗_{A_inf[G]} T, assumed perfect.
Then there is an A_inf-algebra map k : T → W(b) that induces a bijection of p-adic completions. -/
private lemma exists_isCompletionBijective_witt_tensor (G : Type) [AddCommMonoid.{0} G]
    [Module ℚ≥0 G] (T : CommAlg Ainf[G]) [Etale Ainf[G] T] [Algebra Ainf T]
    [IsScalarTower Ainf Ainf[G] T]
    (h_perf : PerfectRing (CommAlgCat.of OFlat (OFlat[G] ⊗[Ainf[G]] T)) p) :
    ∃ k : CommAlgCat.of Ainf T ⟶ wittFunctor.obj (CommAlgCat.of OFlat (OFlat[G] ⊗[Ainf[G]] T)),
      IsCompletionBijective p k.hom.toLinearMap := by
  -- `T` is formally smooth over `W = Ainf[G]` and `W(b)` is `p`-complete, so `t ↦ 1 ⊗ t` lifts to
  -- `κ : T → W(b)`; as `T → b` is reduction modulo `p` and `W(b)` is `p`-torsion-free, `κ` is
  -- bijective modulo every power of `p`.
  let W : Type := Ainf[G]
  let b : CommAlg OFlat := CommAlgCat.of OFlat (OFlat[G] ⊗[W] T)
  -- `W(b)` is `p`-torsion-free and `p`-complete (`h_ct`), and `W(b) → b` is onto with kernel `(p)`.
  obtain ⟨h_mod, h_ct, h_ker, -⟩ :
      IsReductionMod p (constantCoeff : WittVector p b →+* b) ∧
        IsCompleteTorsionFree (WittVector p b) ∧
        RingHom.ker (constantCoeff : WittVector p b →+* b) = span {(p : WittVector p b)} ∧ _ :=
    isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat b
  -- `W(b)` is a `W`-algebra, the elements of `G` going to Teichmüller representatives.
  let wittAlgebra : Algebra (WittVector p OFlat)[G] (WittVector p b) :=
    (liftNCRingHom (map (algebraMap OFlat b)) ((teichmuller p).comp
      (includeLeftRingHom.toMonoidHom.comp (of OFlat G))) fun _ _ ↦ .all ..).toAlgebra
  have h_constantCoeff_comp :
      constantCoeff.comp (algebraMap W (WittVector p b)) = algebraMap W b := by
    -- on `Ainf`, and on the elements of `G`, sent to Teichmüller representatives
    ext <;> simp [b, W, algebraMap_toAlgebra, ← AddMonoidAlgebra.one_def,
      ← Algebra.TensorProduct.one_def]
  let coeff₀ : WittVector p b →ₐ[W] b :=
    ⟨constantCoeff, fun a ↦ RingHom.congr_fun h_constantCoeff_comp a⟩
  obtain ⟨h_constantCoeff_surj, -⟩ := h_mod
  let e : (WittVector p b ⧸ ker coeff₀) ≃ₐ[W] b :=
    quotientKerAlgEquivOfSurjective h_constantCoeff_surj
  have h_complete : IsAdicComplete (ker coeff₀) (WittVector p b) := by
    rw [show ker coeff₀ = span {(p : WittVector p b)} from h_ker]
    exact h_ct.complete
  obtain ⟨κ, hκ⟩ : ∃ κ : T →ₐ[W] WittVector p b,
      (Ideal.Quotient.mkₐ W (ker coeff₀)).comp κ = e.symm.toAlgHom.comp includeRight :=
    FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (e.symm.toAlgHom.comp includeRight)
  have hκ_coeff (t : T) : constantCoeff (κ t) = (1 ⊗ₜ t : b) :=
    e.eq_symm_apply.mp (AlgHom.congr_fun hκ t)
  -- `κ` is `Ainf`-linear, as `Ainf` acts on `T` through `W`.
  have hκ_algebraMap (a : Ainf) :
      κ (algebraMap Ainf T a) = WittVector.map (algebraMap OFlat b) a := by
    rw [IsScalarTower.algebraMap_apply Ainf W T, κ.commutes]
    -- `erw`: the `W`-algebra structure on `W(b)` is `wittAlgebra`, which `rw` does not unfold.
    erw [liftNC_single, map_one, mul_one, Algebra.algebraMap_self_apply]
  let k : .of Ainf T ⟶ wittFunctor.obj b := CommAlg.homOfRingHom κ.toRingHom hκ_algebraMap
  refine ⟨k, ?_⟩
  -- `T → b` is onto with kernel `p T`, being a base change of `Ainf → OFlat`. Hence `κ` is
  -- bijective modulo `p`.
  have h_surj (y : WittVector p b) : ∃ t : T, ↑p ∣ y - κ t := by
    obtain ⟨t, ht⟩ : ∃ t : T, (1 ⊗ₜ[W] t : b) = y.coeff 0 :=
      mk_surjective W T OFlat[G] (map_surjective _ (constantCoeff_surjective p)) (y.coeff 0)
    refine ⟨t, mem_span_singleton.mp (h_ker.le ?_)⟩
    exact (sub_mem_ker_iff _).2 ((hκ_coeff t).trans ht).symm
  have h_dvd (t : T) (ht : ↑p ∣ κ t) : ↑p ∣ t := by
    have h_κ_mem : constantCoeff (κ t) = 0 := h_ker.ge (mem_span_singleton.mpr ht)
    have h_one_tmul : (1 ⊗ₜ[W] t : b) = 0 := (hκ_coeff t).symm.trans h_κ_mem
    -- Cancel `W`: `b = O^♭ ⊗_{Ainf} T`, and `T → O^♭ ⊗_{Ainf} T` is reduction modulo `p`.
    have h_zero : algebraMap Ainf OFlat 1 ⊗ₜ[Ainf] t = 0 := by
      let cancelBaseChange : OFlat[G] ⊗[W] T ≃ₐ[OFlat] OFlat ⊗[Ainf] T :=
        IsPushout.cancelBaseChangeAlg Ainf OFlat W OFlat[G] T
      apply cancelBaseChange.symm.injective
      simpa [cancelBaseChange, ← AddMonoidAlgebra.one_def] using h_one_tmul
    -- The first clause of `isReductionMod_constantCoeff_and_isCompleteTorsionFree`, with `S` left
    -- to unification: naming `S` and the clause makes the unification of the two linear maps time
    -- out.
    obtain ⟨-, h_exact⟩ : IsReductionMod p ((Algebra.linearMap Ainf OFlat).lTensor T) :=
      (isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat _).1.lTensor _
    obtain ⟨y, hy⟩ : ∃ y : T ⊗[Ainf] Ainf, p • y = t ⊗ₜ 1 :=
      (h_exact (t ⊗ₜ 1)).mp ((TensorProduct.comm ..).injective h_zero)
    exact ⟨TensorProduct.rid Ainf T y,
      by simpa [← nsmul_eq_mul] using congrArg (TensorProduct.rid Ainf T) hy.symm⟩
  -- As `W(b)` is `p`-torsion-free, injectivity modulo `p` passes to all powers of `p`.
  have h_map_mul (t : T) : k.hom ((p : T) * t) = (p : wittFunctor.obj b) * k.hom t := by simp
  have h_p_mem : (p : WittVector p b) ∈ nonZeroDivisors (WittVector p b) :=
    mem_nonZeroDivisors_iff_left.mpr fun x hx ↦
      h_ct.regular.right_eq_zero_of_smul (by rwa [nsmul_eq_mul])
  exact .of_dvd_sub_of_pow_dvd _ h_surj fun n t ↦ pow_dvd_of_map h_map_mul h_p_mem h_dvd

open AddMonoidAlgebra Algebra TensorProduct AlgebraMonoidAlgebra in
/-- Let G be a commutative (additive) monoid that is a module over ℚ≥0, and B an O_C-algebra étale
over the monoid algebra O_C[G] compatibly with O_C, with A_max carrying the standing structure
`CrysPeriodAlgebra`. Then for P = Hom(B, −), restriction along `crysThickening` and
`testToPdReduction` is bijective in every degree (`New.Variety.HasCrysComparison`). The map goes
from the cohomology of D ↦ Hom(B, D/𝔡(D)) on p-torsion-free p-complete A_max-algebras D, with
coefficients B_max ⊗ D and 𝔡 the ideal `New.Variety.pdIdeal`, to the cohomology of S ↦ Hom(B, S) on
p-adic tests. -/
lemma hasCrysComparison_of_etale (G : Type) [AddCommMonoid.{0} G] [Module ℚ≥0 G] (B : CommAlg OC)
    [Algebra OC[G] B] [IsScalarTower OC OC[G] B] [Etale OC[G] B] :
    HasCrysComparison (reprBy B) := by
  -- Lift `B` to an étale `T` over `W = Ainf[G]` and let `b` be its base change to `OFlat[G]`, a
  -- perfect ring. A map `T → W(b)` that is bijective on `p`-adic completions feeds
  -- `hasCrysComparison_of_witt`.
  let W : Type := Ainf[G]
  obtain ⟨T, h_etale, ⟨liftIso⟩⟩ :
      ∃ T : CommAlg W, Etale W T ∧ Nonempty (OC[G] ⊗[W] T ≃ₐ[OC[G]] B) :=
    exists_etale_lift W OC[G] B (map_surjective _ theta_surjective)
  algebraize [(algebraMap W T).comp (algebraMap Ainf W)]
  let bc S [CommRing S] [Algebra Ainf S] : S[G] ⊗[W] T ≃ₐ[S] S ⊗[Ainf] T :=
    IsPushout.cancelBaseChangeAlg Ainf S W S[G] T
  let b : CommAlg OFlat := CommAlgCat.of OFlat (OFlat[G] ⊗[W] T)
  have h_perf : PerfectRing b p :=
    perfectRing_of_etale _ b (k := perfectRing_monoidAlgebra G) natCast_eq_zero_of_algebra_oFlat
  -- `b` is flat over `OFlat`.
  have h_reg : IsSMulRegular b pFlat :=
    (Module.Flat.trans _ OFlat[G] _).isTorsionFree.isSMulRegular (.of_ne_zero pFlat_ne_zero)
  obtain ⟨k, hk⟩ : ∃ k : CommAlgCat.of Ainf T ⟶ wittFunctor.obj b,
      IsCompletionBijective p k.hom.toLinearMap :=
    exists_isCompletionBijective_witt_tensor G T h_perf
  -- `B ≅ OC ⊗ T`, so `Hom(B, -)` on `OC`-algebras is `Hom(T, -)` over `Ainf`.
  let iso : reprBy B ≅ restrictAlg Ainf OC ⋙ reprBy (.of Ainf T) :=
    reprFunctor.mapIso (isoMk ((bc _).symm.trans (liftIso.restrictScalars _))).op ≪≫
      isoOfAppBijective _ (pointMap_algBaseChange_unit_bijective (.of Ainf T))
  have h_witt : HasCrysComparison (restrictAlg Ainf OC ⋙ reprBy (.of Ainf T)) :=
    hasCrysComparison_of_witt ⟨b, h_perf, h_reg⟩ k hk
  -- `(… :)` elaborates the term before unifying it with the goal
  exact (((Comparison.isClosedClass (.restrict crysThickening crysPeriodCoeff)
    testToPdReduction).iff_of_isIso (freeAb.map iso.hom)).mpr h_witt :)

end CrystallineEtale

/-!
## Root systems of a unit form a line on p-torsion-free p-complete A_max-algebras

Here 𝔡(D) is the ideal `New.Variety.pdIdeal` of the x with n! ∣ x^n for all n, and a unit is taken
in D/𝔡(D).
-/

section CrystallineLines

open Nat AddMonoidAlgebra CategoryTheory Function Period SModEq WittVector NNRat Envelope

variable {p : ℕ} [ThePrime p]
/-- Let a ∈ ℚ≥0 have denominator greater than 1, so that a is not an integer. Then
p · ([ε^a] − 1) divides μ = [ε] − 1 in A_max, where [ε^a] is the Teichmüller lift of ε^a
(`New.Variety.epsPowNNRat`) mapped from A_inf to A_max by the algebra structure that
`CrysPeriodAlgebra` fixes. -/
lemma CrysPeriodAlgebra.p_mul_teichmuller_sub_one_dvd {p : ℕ} [ThePrime p] [h : CrysPeriodAlgebra]
    {a : ℚ≥0} (ha : 1 < a.den) :
    ↑p * (algebraMap Ainf Amax (teichmuller p (epsPowNNRat (Multiplicative.ofAdd a))) - 1) ∣
      algebraMap Ainf Amax mu := by
  -- Let `a = m / l` in lowest terms and `x = [ε ^ (1 / l)]`. Then `[ε ^ a] - 1` and `μ` are
  -- `x - 1` times `∑ i < m, x ^ i` and `∑ i < l, x ^ i`; `θ x` is a primitive `l`-th root of unity.
  let x : Ainf := teichmuller p (epsPowNNRat (.ofAdd (a.den : ℚ≥0)⁻¹))
  let ι : Ainf →+* Amax := algebraMap Ainf Amax
  have h_prim : IsPrimitiveRoot (epsPow (Multiplicative.ofAdd (a.den : ℚ)⁻¹)).untilt a.den := by
    simpa using isPrimitiveRoot_untilt_epsPow (.ofAdd (a.den : ℚ)⁻¹)
  -- `θ` kills the sum of `l` terms, so `ξ` divides it, and `p` divides the image of `ξ`
  have h_theta : theta (∑ i ∈ Finset.range a.den, x ^ i) = 0 := by
    simpa [x, theta_teichmuller] using h_prim.geom_sum_eq_zero ha
  have h_den : ↑p ∣ ι (∑ i ∈ Finset.range a.den, x ^ i) :=
    h.dvd_xi.trans (map_dvd ι (theta_eq_zero_iff_xi_dvd.mp h_theta))
  -- the sum of `m` terms is a cyclotomic unit modulo the divided power ideal, hence a unit
  have h_num_mod : IsUnit (pdQuotientMk Amax (∑ i ∈ Finset.range a.num, ι x ^ i)) := by
    simpa [x, ι, integersToPdQuotient_untilt] using!
      (h_prim.geom_sum_isUnit ha a.coprime_num_den).map integersToPdQuotient
  have h_num : IsUnit (∑ i ∈ Finset.range a.num, ι x ^ i) :=
    h.isLocalHom_pdQuotientMk.map_nonunit _ h_num_mod
  have h_dvd_pow : p * (ι x ^ a.num - 1) ∣ ι x ^ a.den - 1 := by
    simpa [geom_sum_mul] using mul_dvd_mul h_den (h_num.mul_left_dvd.mpr (refl (ι x - 1)))
  -- `x ^ m = [ε ^ a]` and `x ^ l = [ε]`
  have h_pow_num : ι x ^ a.num = ι (teichmuller p (epsPowNNRat (.ofAdd a))) := by
    simp [x, ι, ← map_pow, ← ofAdd_nsmul, ← cast_def, ← division_def]
  have h_pow_den : ι x ^ a.den - 1 = ι mu := by
    simp [x, ι, ← epsPow_one, ← map_pow, ← ofAdd_nsmul, mu]
  rwa [h_pow_num, h_pow_den] at h_dvd_pow

/-- The split of c ∈ ℚ≥0 into its fractional part c − ⌊c⌋, in [0, 1), and its integral part ⌊c⌋. -/
private def _root_.NNRat.equivIcoProdNat : ℚ≥0 ≃ Set.Ico (0 : ℚ≥0) 1 × ℕ where
  toFun c := (⟨c - ⌊c⌋₊, by simp [tsub_lt_iff_left, floor_le, lt_floor_add_one]⟩, ⌊c⌋₊)
  invFun := fun (a, n) ↦ a + n
  left_inv := by aesop_cat (add simp floor_le)
  right_inv := by aesop_cat (add simp [floor_add_natCast, floor_le])

/-- For t in a p-torsion-free p-complete A_max-algebra A, the element t − v of A[ℚ≥0], where
`single a 1` stands for v^a. -/
private abbrev lineGen {A : CrysTest Amax} (t : A.obj) : A.obj[ℚ≥0] := single 0 t - single 1 1

/-- The divided power envelope of A[ℚ≥0] along t − v (`lineGen`). -/
private abbrev lineEnvelope {A : CrysTest Amax} (t : A.obj) : CrysTest Amax :=
  Envelope _ {lineGen t}

/-- The map from A to the envelope `lineEnvelope t`. -/
private abbrev lineEnvelope.incl {A : CrysTest Amax} (t : A.obj) : A ⟶ lineEnvelope t :=
  ⟨CommAlgCat.ofHom (Algebra.algHom ..)⟩

/-- The character a ↦ v^a of ℚ≥0 in the envelope `lineEnvelope t`. -/
private abbrev lineEnvelope.var {A : CrysTest Amax} (t : A.obj) :
    Multiplicative ℚ≥0 →* (lineEnvelope t).obj :=
  (algebraMap A.obj[ℚ≥0] (lineEnvelope t).obj).toMonoidHom.comp (of A.obj ℚ≥0)

/-- In the envelope `lineEnvelope t`, the variable v and t agree modulo 𝔡, because t − v has
divided powers there. -/
private lemma pdQuotientMk_lineEnvelope_var_ofAdd_one {A : CrysTest Amax} (t : A.obj) :
    pdQuotientMk (lineEnvelope t).obj (lineEnvelope.var t (.ofAdd 1)) =
      pdQuotientMk (lineEnvelope t).obj (algebraMap A.obj (lineEnvelope t).obj t) := by
  have h_sub_mem : algebraMap A.obj (lineEnvelope t).obj t - lineEnvelope.var t (.ofAdd 1) ∈
      pdIdeal (lineEnvelope t).obj := by
    simpa [lineGen] using! algebraMap_mem_pdIdeal (A.obj[ℚ≥0]) {lineGen t} rfl
  exact (Ideal.Quotient.eq.mpr h_sub_mem).symm

/-- The point of the root systems of t modulo 𝔡 at the envelope `lineEnvelope t`: the variable v
modulo 𝔡, and the map from A. -/
private abbrev lineEnvelope.point [CrysPeriodAlgebra] {A : CrysTest Amax} (t : A.obj) :
    (TimesBNat.incl _ ⋙ compatibleRootsAt (pdReduction integersToPdQuotient) ⟨⟦t⟧⟩)
      (lineEnvelope t) :=
  ⟨(⟨(pdQuotientMk _).toMonoidHom.comp (lineEnvelope.var t)⟩, ⟨lineEnvelope.incl t⟩),
    congrArg ULift.up (pdQuotientMk_lineEnvelope_var_ofAdd_one t)⟩

/-- The envelope `lineEnvelope t` with its point `lineEnvelope.point t` represents the root systems
of t modulo 𝔡: for every p-torsion-free p-complete A_max-algebra B, a map f : A → B with a
character of ℚ≥0 in B/𝔡(B) whose value at 1 is f(t) modulo 𝔡 comes from exactly one map from the
envelope to B. -/
private lemma bijective_pointMap_lineEnvelope_point [CrysPeriodAlgebra]
    {A : CrysTest Amax} (t : A.obj) (B : CrysTest Amax) :
    Bijective (pointMap (lineEnvelope.point t) B) := by
  let z : A[ℚ≥0] := lineGen t
  let E : CrysTest Amax := lineEnvelope t
  let i : A ⟶ E := lineEnvelope.incl t
  let v : Multiplicative ℚ≥0 →* E := lineEnvelope.var t
  refine (bijective_iff_existsUnique _).2 ?_
  rintro ⟨⟨⟨w⟩, ⟨f⟩⟩, hw⟩
  -- a root system in `B / 𝔡` lifts uniquely to `χ` in `B`; `(f, χ)` factors uniquely through `E`
  obtain ⟨χ, rfl⟩ := B.property.monoidHom_lift_bijective.surjective w
  have h_diff_mem : f.hom.hom t - χ (.ofAdd 1) ∈ pdIdeal B :=
    SModEq.sub_mem.mp (ULift.ext_iff.mp hw).symm
  have h_lift_mem : ∀ y ∈ ({z} : Set A[ℚ≥0]),
      liftNCAlgHom f.hom.hom χ (fun _ _ ↦ Commute.all _ _) y ∈ pdIdeal B := by
    simpa [z, lineGen] using h_diff_mem
  obtain ⟨g, hg, g_unique⟩ :=
    existsUnique_lift _ {z} (liftNCAlgHom f.hom.hom χ fun _ _ ↦ Commute.all _ _) h_lift_mem
  have hg_v : MonoidHom.comp g.hom.hom v = χ := by
    ext a
    exact (DFunLike.congr_fun hg _).trans (by simp)
  have hg_i : i ≫ g = f := by
    ext c
    exact (DFunLike.congr_fun hg _).trans (by simp)
  subst hg_v hg_i
  refine ⟨⟨g⟩, rfl, ?_⟩
  rintro ⟨g'⟩ hg'
  -- `g'` agrees with `g` on `v`, because lifts of root systems are unique, and on `A`
  obtain ⟨h_roots, h_maps⟩ := Prod.ext_iff.mp (Subtype.ext_iff.mp hg')
  have h_roots_mod : (pdQuotientMk B).toMonoidHom.comp (MonoidHom.comp g'.hom.hom v) =
      (pdQuotientMk B).toMonoidHom.comp (MonoidHom.comp g.hom.hom v) :=
    congrArg ULift.down h_roots
  have hv : MonoidHom.comp g'.hom.hom v = MonoidHom.comp g.hom.hom v :=
    B.property.monoidHom_lift_bijective.injective h_roots_mod
  have hi : i ≫ g' = i ≫ g := congrArg ULift.down h_maps
  refine congrArg ULift.up (g_unique g' ?_)
  rw [← hg]
  exact algHom_ext' hv (congrArg (·.hom.hom) hi)

/-- Let t ∈ A be a unit modulo 𝔡(A), E = `lineEnvelope t` with the map i from A and the variable
v, and γ an endomorphism of E that fixes A (`hγ_fix`) and multiplies v^a by [ε^a] for every
a ∈ ℚ≥0 (`hγ_v`). Then B_max ⊗ − (`crysPeriodCoeff`) turns i and γ into a Koszul-exact pair. -/
private lemma koszulExact_lineEnvelope {p : ℕ} [ThePrime p] [h : CrysPeriodAlgebra]
    {A : CrysTest Amax} {t : A.obj} (ht : IsUnit (pdQuotientMk A.obj t))
    (γ : lineEnvelope t ⟶ lineEnvelope t)
    (hγ_fix : (lineEnvelope.incl t ≫ γ).hom.hom = (lineEnvelope.incl t).hom.hom)
    (hγ_v : MonoidHom.comp γ.hom.hom (lineEnvelope.var t) =
      (algebraMap Amax (lineEnvelope t).obj).toMonoidHom.comp
        ((algebraMap Ainf Amax).toMonoidHom.comp ((teichmuller p).comp epsPowNNRat)) *
        lineEnvelope.var t) :
    KoszulExact (crysPeriodCoeff.map (lineEnvelope.incl t)) (crysPeriodCoeff.map γ) := by
  let z : A[ℚ≥0] := lineGen t
  let E : CrysTest Amax := lineEnvelope t
  -- the algebra structures on `E` are fixed once, so that later steps do not search for them
  let algebra_A_E : Algebra A E := inferInstance
  let algebra_preEnvelope_E : Algebra (preEnvelope {z}) E := inferInstance
  let v : Multiplicative ℚ≥0 →* E := lineEnvelope.var t
  let e : Multiplicative ℚ≥0 →* Amax :=
    (algebraMap Ainf Amax).toMonoidHom.comp ((teichmuller p).comp epsPowNNRat)
  let γ' : E →ₐ[A] E := ⟨γ.hom.hom, fun c ↦ DFunLike.congr_fun hγ_fix c⟩
  -- the basis `v ^ a * y n` of the uncompleted envelope, with `z ^ n = n ! * y n`
  obtain ⟨y, b, hb, hz⟩ : ∃ (y : ℕ → preEnvelope {z})
      (b : Module.Basis (Set.Ico (0 : ℚ≥0) 1 × ℕ) A (preEnvelope {z})),
      (∀ a n, b (a, n) = algebraMap A[ℚ≥0] _ (single (a : ℚ≥0) 1) * y n) ∧
        ∀ n, algebraMap A[ℚ≥0] _ z ^ n = n ! * y n :=
    exists_preEnvelope_basis A z ((basis ..).reindex NNRat.equivIcoProdNat) (single · 1)
      (by simp [NNRat.equivIcoProdNat]) rfl
  have v_unit_mod : IsUnit (pdQuotientMk E (v (.ofAdd 1))) := by
    rw [pdQuotientMk_lineEnvelope_var_ofAdd_one t]
    exact ht.map (pdQuotientMap _)
  have v_unit : IsUnit (v (.ofAdd 1)) := E.property.isLocalHom_pdQuotientMk.map_nonunit _ v_unit_mod
  -- apply `koszulExact_pd_line` with `q = μ` and `η = [ε ^ a] - 1`; for `0 < a < 1`, `p * η`
  -- divides `μ`
  refine koszulExact_pd_line A E isCompletionBijective_completion (b := b)
    (u := fun a ↦ v (.ofAdd (a : ℚ≥0))) (y := fun n ↦ algebraMap _ E (y n)) (t := t)
    (fun a n ↦ ?_) (fun n ↦ ?_) v_unit rfl
    h.p_cube_dvd_mu h.isUnit_mu γ' ?_ fun a ha ↦ ⟨e (.ofAdd (a : ℚ≥0)) - 1, ?_, ?_⟩
  · -- `hb`: the basis is `v ^ a` times the divided powers `y n`
    exact (congrArg (algebraMap (preEnvelope {z}) E) (hb a n)).trans (map_mul ..)
  · -- `hy`: `(t - v) ^ n = n ! * y n`
    have hz_E : algebraMap A[ℚ≥0] E z = algebraMap A E t - v (.ofAdd 1) := map_sub ..
    simpa [← hz_E] using! congrArg (algebraMap (preEnvelope {z}) E) (hz n)
  · -- `hγv`: `γ v = (μ + 1) • v`, as `[ε] = μ + 1`
    have h_one : γ' (v (.ofAdd 1)) = algebraMap Amax E (e (.ofAdd 1)) * v (.ofAdd 1) :=
      DFunLike.congr_fun hγ_v _
    simpa [e, ← epsPow_one, mu, Algebra.smul_def] using h_one
  · -- `hγu`: `γ (v ^ a) = (η + 1) • v ^ a` with `η = [ε ^ a] - 1`
    have h_a : γ' (v (.ofAdd (a : ℚ≥0))) =
        algebraMap Amax E (e (.ofAdd (a : ℚ≥0))) * v (.ofAdd (a : ℚ≥0)) :=
      DFunLike.congr_fun hγ_v _
    simpa [Algebra.smul_def] using h_a
  · -- `hγu`: `p * η` divides `μ`, as `a` lies strictly between `0` and `1` and is not an
    -- integer
    obtain ⟨-, h_lt_one⟩ : 0 ≤ (a : ℚ≥0) ∧ (a : ℚ≥0) < 1 := a.property
    have h_den : 1 < (a : ℚ≥0).den := by
      refine Nat.lt_of_le_of_ne (a : ℚ≥0).den_pos fun h_den_eq ↦ ha ?_
      simpa [← h_den_eq, lt_def, num] using h_lt_one
    exact h.p_mul_teichmuller_sub_one_dvd h_den

/-- Let A be a p-torsion-free p-complete A_max-algebra (with the standing structure
`CrysPeriodAlgebra`) and y a unit of A/𝔡(A), where 𝔡 is the ideal `New.Variety.pdIdeal` and
`pdReduction` sends D to D/𝔡(D), an O_C-algebra through `integersToPdQuotient`. On such algebras D,
let Y(D) be the pairs of a map f : A → D and a character s : ℚ≥0 → D/𝔡(D) with s(1) = f(y), with the
twist multiplying s by the image of a ↦ (ε^a)^♯. Then forgetting s induces a bijection, in every
degree, from the cohomology of Hom(A, −) to that of Y on the product with Bℕ (the homotopy quotient
by the twist), with coefficients D ↦ B_max ⊗_{A_max} D (`crysPeriodCoeff`). -/
lemma compatibleRootsAreLines_crysTest {p : ℕ} [ThePrime p] [h : CrysPeriodAlgebra] :
    CompatibleRootsAreLines crysPeriodCoeff (pdReduction integersToPdQuotient) := by
  -- Write `𝔡` for the divided power ideal `pdIdeal`. The root systems of `t` modulo `𝔡` are
  -- represented by the divided power envelope `E` of `A[v ^ ℚ≥0]` along `z = t - v`. It has the
  -- topological basis `v ^ a * z ^ n / n !`, `0 ≤ a < 1`, and the twist `γ` multiplies `v ^ a` by
  -- `[ε ^ a]`; `koszulExact_lineEnvelope` gives the exactness that `IsLine.of_acyclic` asks for.
  rintro A ⟨⟨t⟩⟩ ht
  let E : CrysTest Amax := lineEnvelope t
  let i : A ⟶ E := lineEnvelope.incl t
  let v : Multiplicative ℚ≥0 →* E := lineEnvelope.var t
  let x : (TimesBNat.incl _ ⋙ compatibleRootsAt (pdReduction integersToPdQuotient) ⟨⟦t⟧⟩) E :=
    lineEnvelope.point t
  have x_univ : ∀ B : CrysTest Amax, Bijective (pointMap x B) :=
    bijective_pointMap_lineEnvelope_point t
  -- the twist of the universal point is induced by an endomorphism `γ` of `E`
  obtain ⟨⟨γ⟩, hγ⟩ := (x_univ E).surjective ((TimesBNat.shiftEnd _ 1).asHom.app E x)
  obtain ⟨hγ_roots, hγ_maps⟩ := Prod.ext_iff.mp (Subtype.ext_iff.mp hγ)
  refine .of_acyclic (ψ := 𝟭 _) (F' := crysPeriodCoeff) (isoOfAppBijective _ x_univ)
    (IsCohomEquiv.of_isIso _).bij i γ (fun D f ↦ rfl) ⟨uliftCoyonedaEquiv.injective hγ⟩ ?_
  -- `γ (v ^ a) = [ε ^ a] * v ^ a`: this holds modulo `𝔡`, and lifts of root systems are unique
  let e : Multiplicative ℚ≥0 →* Amax :=
    (algebraMap Ainf Amax).toMonoidHom.comp ((teichmuller p).comp epsPowNNRat)
  have hγ_v : MonoidHom.comp γ.hom.hom v = (algebraMap Amax E).toMonoidHom.comp e * v := by
    refine E.property.monoidHom_lift_bijective.injective (MonoidHom.ext fun a ↦ ?_)
    refine (DFunLike.congr_fun (congrArg ULift.down hγ_roots) a).trans ?_
    exact congrArg (pdQuotientMap _ · * _) (integersToPdQuotient_untilt _)
  -- `γ` fixes the image of `A`
  have hγ_i : i ≫ γ = i := congrArg ULift.down hγ_maps
  exact koszulExact_lineEnvelope ht γ (by rw [hγ_i]) hγ_v

end CrystallineLines

/-!
## The comparison on a chart étale over a torus

A root system of t is a character of ℚ≥0 with value t at 1.
-/

section CrystallineChart

open CategoryTheory AddMonoidAlgebra CommRingCat RingHom TensorProduct Function
  Algebra.TensorProduct MvPolynomial Fin Comparison TimesBNat Functor ULift

variable {p : ℕ} [ThePrime p]

/-- Let P be a closed class of functors from C × Bℕ to abelian groups (`IsClosedClass`: P holds
for zero objects, and along a short exact sequence whose first term is in P, the middle term is in
P exactly when the last one is). If P holds for the free abelian group functor of Y × ℕ (Y
restricted to C, times ℕ with its shift), then it holds for that of Y: the short exact sequence
`TimesBNat.shortExact_induced` resolves ℤ[Y] by two copies of ℤ[Y × ℕ]. -/
lemma IsClosedClass.of_prod_nat {C : Type 1} [Category C] {P : (TimesBNat C ⥤ Ab) → Prop}
    (hP : IsClosedClass P) {Y : TimesBNat C ⥤ Type 1}
    (h : P (freeAb (MonoidalCategory.tensorObj (TimesBNat.fst C ⋙ incl C ⋙ Y) natWithShift))) :
    P (freeAb Y) := by
  obtain ⟨-, h_two_of_three⟩ := hP
  obtain ⟨w, h_exact⟩ := shortExact_induced Y
  exact (h_two_of_three _ h_exact h).mp h

variable {C C' : Type 1} [Category C] [Category C']
  {F : AbFunctor C} {F' : AbFunctor C'} {c : Comparison (C := C) (C' := C') F F'}
  {ψ : C ⥤ CommAlg OC} {ψ' : C' ⥤ CommAlg OC} {η : ψ' ⟶ c.functor ⋙ ψ} in
/-- Let c be a comparison from F on C to F' on C' (a functor φ : C' ⥤ C with a map of coefficients),
ψ and ψ' functors to O_C-algebras with η : ψ' ⟶ φ ⋙ ψ, and U a functor on O_C-algebras. Let t₁, …,
t_n be unit-valued functions on U (`h_unit`), x a point of U(T), and r_i root systems of the t_i(x),
that is, characters of ℚ≥0 with r_i(1) = t_i(x) (`h_root`). Suppose that T, with x and the r_i,
represents the points y of U together with root systems s_i of the t_i(y) (`h_rep`). Suppose root
systems form lines (`CompatibleRootsAreLines`) for ψ with F and for ψ' with F': for each unit of
ψ(A), projecting its root systems to Hom(A, −) is bijective on cohomology. Then bijectivity of c on
the functor represented by T (`hT`) implies bijectivity on U. Here c is bijective on P when the maps
Hⁿ(ψ ⋙ P, F) → Hⁿ(ψ' ⋙ P, F') induced along η are bijective for all n. -/
lemma Comparison.IsBijective.isBijectiveOn_of_compatibleRoots {n : ℕ} {U : CommAlg OC ⥤ Type 1}
    {T : CommAlg OC} (h_lines : CompatibleRootsAreLines F ψ)
    (h_lines' : CompatibleRootsAreLines F' ψ')
    (hT : c.IsBijectiveOn η (reprBy T)) (t : Fin n → (U ⟶ underlyingSet))
    (x : (fun X : Type 1 ↦ X) (U.obj T))
    (r : Fin n → Multiplicative ℚ≥0 →* T)
    (h_unit : ∀ (i : Fin n) (A : CommAlg OC) (y : (fun X : Type 1 ↦ X) (U.obj A)),
      IsUnit (t i A y).down)
    (h_root : ∀ i : Fin n, ⟨r i (Multiplicative.ofAdd 1)⟩ = t i T x)
    (h_rep : ∀ (A : CommAlg OC) (y : (fun X : Type 1 ↦ X) (U.obj A))
      (s : Fin n → Multiplicative ℚ≥0 →* A),
      (∀ i : Fin n, ⟨s i (Multiplicative.ofAdd 1)⟩ = t i A y) →
      ∃! f : (reprBy T).obj A,
        pointMap x A f = y ∧ ∀ i : Fin n, MonoidHom.comp f.down.hom (r i) = s i) :
    c.IsBijectiveOn η U := by
  -- Induction on the number of units, adjoining the roots of `t 0` first.
  induction n generalizing U with
  | zero =>
    -- With no unit, `h_rep` says that `x` represents `U`.
    have h_bij : AllBijective fun A : CommAlg OC ↦ (pointMap x).app A := by
      simp_all [AllBijective, bijective_iff_existsUnique]
    exact (c.isClosedClass η).freeAb_of_bijective (pointMap x) h_bij hT
  | succ n ih =>
    -- `Y` is the functor of points of `U` with a root system of `t 0`, with its action of `ℕ`. It
    -- is a line over `U` on both sides, because its fibres over points are.
    let Y : TimesBNat (CommAlg OC) ⥤ Type 1 := fibreProd compatibleRoots.atOne (whiskerLeft _ (t 0))
    let a : Y ⟶ TimesBNat.fst _ ⋙ U := fibreProd.snd ..
    have h_line {D : Type 1} [Category D] {G : AbFunctor D} {χ : D ⥤ CommAlg OC}
        (h : CompatibleRootsAreLines G χ) : IsLine G ((χ.prod _).whiskerLeft a) :=
      isBijective_of_fibres (χ.whiskerLeft (t 0))
        (isPullback_fibreProd.map (Variety.restrictAlong _)) fun B y ↦ h _ _ (h_unit 0 _ _)
    -- With the action forgotten, `Y` carries the `n` other units and is covered by `ih`.
    have hY : c.IsBijectiveOn η (incl _ ⋙ Y) := by
      refine ih ((incl _).whiskerLeft a ≫ t ·.succ) ⟨(_, _), h_root 0⟩ _
        (fun i B y ↦ h_unit i.succ B _) (tail h_root) ?_
      rintro A ⟨⟨⟨s₀⟩, y⟩, hs₀⟩ s hs
      -- A root system `s₀` of `t 0` and root systems `s` of the others are one tuple `cons s₀ s`.
      refine (existsUnique_congr fun f ↦ ?_).1 (h_rep A y (cons s₀ s) (cases hs₀ hs))
      -- a point of `Y` is a subtype only after unfolding `fibreProd`, which `rw` does not do
      erw [Subtype.ext_iff, Prod.mk_inj, up_inj, forall_fin_succ]
      tauto
    let c' : Comparison (TimesBNat.fst C ⋙ F) (TimesBNat.fst C' ⋙ F') :=
      ⟨c.functor.prod (𝟭 _), (TimesBNat.fst C').whiskerLeft c.coeffHom⟩
    -- The comparison `c'` over `C × Bℕ` is bijective on `Y × ℕ`, which on both sides has the
    -- cohomology of `Y` with the action forgotten (`isLine_fst`); hence it is bijective on
    -- `Y`.
    have hY' : c'.IsBijectiveOn (ψ := ψ.prod (𝟭 _)) (η.prod (𝟙 _)) Y := by
      -- `(… :)` elaborates the term before unifying it with the goal
      refine ((c'.isClosedClass (ψ := ψ.prod (𝟭 _)) (η.prod (𝟙 _))).of_prod_nat (Y := Y)
        fun m ↦ ?_ :)
      refine ((isLine_fst (X := ψ ⋙ incl _ ⋙ Y) m).of_comp_iff _).1 ?_
      refine (funext pull_trans).symm.subst (hY.trans isLine_fst ?_ m)
      exact freeAb.hom_ext fun _ _ ↦ rfl
    -- Both lines carry the bijection from `Y` down to `U`.
    refine ((h_line h_lines').trans_iff ?_).1 ((h_line h_lines).trans hY' rfl)
    exact freeAb.hom_ext fun _ _ ↦ rfl

/-- Assume the conditions `CrysPeriodAlgebra` on A_max. On p-adic tests (`PadicTest.algFunctor`
sends a test to its O_C-algebra), the root systems of every unit form a line
(`CompatibleRootsAreLines`) for the coefficients of the crystalline comparison, B_max ⊗ D read on
the thickening `crysThickening` of the test. That is, for every test A and unit y of its
O_C-algebra, the projection from the root systems of y to Hom(A, −) is bijective on cohomology with
these coefficients. -/
lemma compatibleRootsAreLines_padicTest [h : CrysPeriodAlgebra] :
    CompatibleRootsAreLines (crysThickening ⋙ crysPeriodCoeff) PadicTest.algFunctor := by
  intro c v hv
  -- The fibre `Y` is a line for the coefficients `S^♭ ⊗ (O^♭ ⊗ A_max) ⊗ 𝔪` (`h_line`), and it has
  -- flat base change once the action of `ℕ` is forgotten (`h_fp`).
  obtain ⟨h_fp, h_line⟩ := c.isLine_compatibleRoots
    (isAcyclicOnPerfect_almostCoeff h.pFlat_smul_eq_zero) v
    hv
  let Y : PadicTest × SingleObj (Multiplicative ℕ) ⥤ Type 1 :=
    compatibleRootsAt PadicTest.algFunctor v
  -- Base change to `Period.Bmax` holds for `Y × ℕ` by `isLine_fst`, hence for `Y`.
  have h_flat (G : CommAlg Period.OFlat ⥤ ModuleCat Period.Amax) :
      AllBijective
        (baseChangeMap Period.Bmax Period.Bmax (freeAb Y)
          ((TimesBNat.fst PadicTest ⋙ PadicTest.tilt) ⋙ G) ·) := by
    have h_nat :=
      (isLine_fst.baseChangeMap_bijective_iff (T := Period.Bmax) (M := Period.Bmax)
          (Φ := PadicTest.tilt ⋙ G) (β := 𝟙 _) h_fp).mpr
        ((coeffCompBijective_id_iff_restrict (.refl _)).mpr isLine_fst)
    -- `(… :)` elaborates the term first; unifying it with the goal directly times out
    exact (HasBaseChange.devissage.isClosedClass.of_prod_nat h_nat :)
  -- Lift from these coefficients to `B_max ⊗ (A_max ⊗ W(S^♭))^`.
  -- `(… :)` elaborates the term first; unifying it with the goal directly times out
  exact ((coeffCompBijective_id_iff_restrict (.refl _)).mp
    (.periodAlg_of_almostCoeff (hasFlatBaseChange_freeAb_reprBy _) h.toIsPeriodRingPair h_flat
      PadicTest.isPerfectTorsionFree_tilt (fun X ↦ X.fst.isPerfectTorsionFree_tilt)
      ((coeffCompBijective_id_iff_restrict (.refl _)).mpr h_line)) :)

/-- Crystalline comparison on a chart. Assume `New.Variety.CrysPeriodAlgebra`, let O_C be an
R-algebra, and let t_1, …, t_d be units of the R-algebra B such that the map R[X_1, …, X_d] → B,
X_i ↦ t_i (`polyEval t`), is étale. Then the functor of R-algebra maps from B to O_C-algebras
satisfies `New.Variety.HasCrysComparison`: restriction from p-complete p-torsion-free A_max-algebras
to p-adic tests is bijective on cohomology. -/
lemma hasCrysComparison_chart [h : CrysPeriodAlgebra] {R : Type} [CommRing R] [Algebra R OC] {d : ℕ}
    {B : CommAlg R} (t : Fin d → B) (ht : Etale (polyEval t)) (hu : ∀ i : Fin d, IsUnit (t i)) :
    HasCrysComparison (restrictAlg R OC ⋙ reprBy B) := by
  -- Adjoin all roots of the `t i`: `B' = OC[G] ⊗ B` over `R[X]`, `G = ℚ≥0 ^ d`, is étale over the
  -- monoid algebra, and it represents points of `B` together with root systems of the `t i`.
  let G : Type := Fin d → ℚ≥0
  let g : MvPolynomial (Fin d) R →ₐ[R] OC[G] := aeval fun i ↦ of OC G (Pi.single i 1)
  algebraize [g.toRingHom, polyEval t]
  let B' : CommAlg OC := .of _ (OC[G] ⊗[MvPolynomial (Fin d) R] B)
  have tmul_eq (x : MvPolynomial (Fin d) R) : g x ⊗ₜ 1 = 1 ⊗ₜ polyEval t x := tmul_one_eq_one_tmul x
  -- Algebra maps from `OC[G]` are `d`-tuples of characters of `ℚ≥0`.
  let e (A : CommAlg OC) : (OC[G] →ₐ[OC] A) ≃ (Fin d → Multiplicative ℚ≥0 →* A) :=
    (lift OC A G).symm.trans (Pi.monoidHomMulEquiv (fun _ ↦ Multiplicative _) A).1
  -- The universal point is `b ↦ 1 ⊗ b`; the universal root systems are `e _ includeLeft`.
  let x : (restrictAlg R _ ⋙ reprBy B).obj B' :=
    ⟨CommAlg.homOfRingHom includeRight.1 fun c ↦ by simpa using! (tmul_eq (C c)).symm⟩
  refine .isBijectiveOn_of_compatibleRoots compatibleRootsAreLines_crysTest
    compatibleRootsAreLines_padicTest
    (hasCrysComparison_of_etale G B') (fun i ↦ {app _ := ↾fun y ↦ ⟨y.down.hom (t i)⟩}) x
    (e _ includeLeft) (fun i _ _ ↦ (hu i).map _)
    (fun i ↦ up_inj.2 (by simpa [g] using! tmul_eq (X i))) fun A ⟨y⟩ ↦ ?_
  -- A point `y` of `B` and a map `F` from `OC[G]` that agree on `R[X]` glue uniquely through `B'`.
  refine (e A).forall_congr_right.1 fun F hF ↦ ?_
  have pushout := isPushout_tensorProduct (MvPolynomial (Fin d) R) OC[G] B
  -- `F` and `y` agree on `R[X]`; after `simp` both goals are the commuting facts
  obtain ⟨f, hf_left, hf_right⟩ := pushout.exists_desc (ofHom F.1) (ofHom y.1.1) <| by
    ext c <;> simp [g, algebraMap_toAlgebra]
    · -- On constants both are maps of `R`-algebras.
      exact (F.commutes _).trans (y.hom.commutes _).symm
    · exact up_inj.1 (hF _)
  refine ⟨⟨CommAlg.homOfRingHom f.hom fun c ↦
    (ConcreteCategory.congr_hom hf_left _).trans (F.commutes c)⟩, ⟨?_, fun i ↦ ?_⟩, ?_⟩
  · exact congr(⟨CommAlg.homOfRingHom $hf_right.1 _⟩)
  · ext
    exact ConcreteCategory.congr_hom hf_left _
  · -- Uniqueness: `y` and `F` are the restrictions of `f'` to the two factors.
    rintro ⟨f'⟩ ⟨⟨⟩, hf'⟩
    cases (e A).injective (a₁ := f'.1.comp includeLeft) (funext hf')
    cases pushout.hom_ext hf_left hf_right
    rfl

end CrystallineChart

/-!
## Spanning of period cohomology by crystalline classes

Here S is a ring with a map r : R → S/𝔡(S), O_C is an R-algebra, A_max an S-algebra, and V a
subfunctor of a functor X on R-algebras.

* `New.Variety.crysComparison`, `New.Variety.toCrysPoints`: the comparison from p-torsion-free
  p-complete S-algebras to p-adic tests, and the map from V on p-adic tests to D ↦ V(D/𝔡).
-/

section CrystallineClasses

open CategoryTheory ObjectProperty TensorProduct Ideal Function Functor Period Submodule LinearEquiv
  IsDiscreteValuationRing MvPolynomial Comparison H Module Abelian Flat LinearMap Quotient Envelope

variable {p : ℕ} [ThePrime p]
  {S R : Type} [CommRing S] [CommRing R]
  {r : R →+* S ⧸ pdIdeal S} {X : CommAlg R ⥤ Type 1} (V : Subfunctor X)

/-- Flat base change for the maps from an S/𝔡(S)-algebra to reductions modulo divided powers. Here
𝔡 is the ideal `New.Variety.pdIdeal` of the x with n! ∣ x^n for all n, and G is a commutative
S/𝔡(S)-algebra. The free abelian group on the functor B ↦ Hom(G, B/𝔡(B)), on p-torsion-free
p-complete S-algebras B, has flat base change (`New.Variety.HasFlatBaseChange`): its cohomology
commutes with tensoring by flat modules. -/
lemma HasFlatBaseChange.pdReduction_reprBy (G : CommAlg (S ⧸ pdIdeal S)) :
    HasFlatBaseChange (freeAb.obj (pdReduction (RingHom.id (S ⧸ pdIdeal S)) ⋙ reprBy G)) := by
  -- Čech descent along the cover `q : L ⟶ Hom (G, – / 𝔡)`, where a point of `L B` is a map
  -- `G ⟶ B / 𝔡` together with a lift to `B` of the image of each element of `G`.
  let ρ : CrysTest S ⥤ CommAlg (S ⧸ pdIdeal S) := pdReduction (.id (S ⧸ pdIdeal S))
  let L : CrysTest S ⥤ Type 1 := .mk
    (fun B ↦ {x : ULift (G ⟶ ρ.obj B) × (G → B) // ∀ g, (x.2 g : B ⧸ pdIdeal B) = x.1.1 g})
    fun f ↦ ↾fun x ↦ ⟨(⟨x.1.1.1 ≫ ρ.map f⟩, f.1 ∘ x.1.2), fun g ↦ congr(ρ.map f $(x.2 g))⟩
  let q : L ⟶ ρ ⋙ reprBy G := .mk fun B ↦ ↾fun x ↦ x.1.1
  -- Lifts can always be chosen, so the image of `q` is everything.
  have h_onto (B : CrysTest S) : Bijective ((Subfunctor.range q).ι.app B) := by
    refine (Equiv.subtypeUnivEquiv fun y ↦ ?_).bijective
    let lifts : G → B := fun g ↦ Quot.out (y.down.hom g)
    exact ⟨⟨(y, lifts), fun g ↦ Quot.out_eq (y.down.hom g)⟩, rfl⟩
  refine isClosedClass.freeAb_of_bijective _ h_onto fun S' T M ↦
    fun Φ ↦ HasBaseChange.devissage.allBijective_freeAb_range_of_cech q fun m ↦ ?_
  -- The `(m + 1)`-fold fibre power of `q` is represented by the envelope `E` of the polynomial
  -- ring on `m + 1` copies of `G` along the kernel of `π : X (i, g) ↦ g`.
  let π : MvPolynomial (Fin (m + 1) × G) S →+* G :=
    eval₂Hom ((algebraMap (S ⧸ pdIdeal S) G).comp (pdQuotientMk S)) Prod.snd
  have hπ : Surjective π := fun g ↦ ⟨X (0, g), by simp [π]⟩
  let E : CrysTest S := Envelope S {f | π f = 0}
  -- The kernel of `π` lands in `𝔡 E`, so `π` induces `y : G → E / 𝔡`.
  have h_ker_le : RingHom.ker π ≤
      RingHom.ker ((pdQuotientMk E).comp (algebraMap (MvPolynomial (Fin (m + 1) × G) S) E)) :=
    fun f hf ↦ eq_zero_iff_mem.2 (algebraMap_mem_pdIdeal S _ hf)
  obtain ⟨y, hy⟩ : ∃ y : G →+* E ⧸ pdIdeal E, ∀ x : MvPolynomial (Fin (m + 1) × G) S,
      y (π x) = Ideal.Quotient.mk (pdIdeal E) (algebraMap (MvPolynomial (Fin (m + 1) × G) S) E x) :=
    ⟨π.liftOfSurjective hπ ⟨_, h_ker_le⟩, π.liftOfSurjective_comp_apply hπ ⟨_, h_ker_le⟩⟩
  -- `y` is a map of `S / 𝔡`-algebras: on the class of `s : S` both sides are the class of `s`.
  have hy_algebraMap (c : S ⧸ pdIdeal S) :
      y (algebraMap (S ⧸ pdIdeal S) G c) = algebraMap (S ⧸ pdIdeal S) (ρ.obj E) c := by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [show algebraMap (S ⧸ pdIdeal S) G (Ideal.Quotient.mk _ s) = π (C s) by simp [π], hy]
    exact congrArg (Ideal.Quotient.mk (pdIdeal E))
      (IsScalarTower.algebraMap_apply S (MvPolynomial (Fin (m + 1) × G) S) E s).symm
  let y' : G ⟶ ρ.obj E := CommAlg.homOfRingHom y hy_algebraMap
  -- The variable `X (i, g)` of the envelope lifts `y g`.
  have hy_X (i : Fin (m + 1)) (g : G) :
      Ideal.Quotient.mk (pdIdeal E) (algebraMap (MvPolynomial (Fin (m + 1) × G) S) E (X (i, g))) =
        y g := by
    simp [← hy, π]
  -- The universal point: `y` with the lifts `g ↦ X (i, g)`.
  let z : (cech q m).obj E :=
    ⟨fun i ↦ ⟨(⟨y'⟩, fun g ↦ algebraMap (MvPolynomial _ S) E (X (i, g))), hy_X i⟩, fun _ _ ↦ rfl⟩
  -- Representable functors have base change, so it remains to see that `z` is universal.
  refine HasBaseChange.devissage.isClosedClass.freeAb_of_bijective (pointMap z)
    (fun B ↦ (bijective_iff_existsUnique _).2 fun e ↦ ?_)
        (HasBaseChange.baseChangeMap_bijective_freeAb_reprBy E)
  -- A point `e` over `B` gives `k : X (i, g) ↦` (the `i`-th lift of `g`). It sends the kernel
  -- of `π` into `𝔡 B`, because modulo `𝔡 B` it is the common map `G ⟶ B / 𝔡` composed with `π`.
  let k : MvPolynomial (Fin (m + 1) × G) S →ₐ[S] B := aeval fun (i, g) ↦ (e.val i).val.2 g
  -- All points of `e` have the same map `φ : G → B / 𝔡`, and each lift reduces to it.
  let φ : G →+* B ⧸ pdIdeal B := (e.val 0).val.1.down.hom.toRingHom
  have h_lift (i : Fin (m + 1)) (g : G) :
      Ideal.Quotient.mk (pdIdeal B) ((e.val i).val.2 g) = φ g := by
    rw [(e.val i).property g, show (e.val i).val.1 = (e.val 0).val.1 from e.property i 0]
    rfl
  have h_k_mod (f) : Ideal.Quotient.mk (pdIdeal B) (k f) = φ (π f) := by
    induction f using MvPolynomial.induction_on with
    | C s =>
      have h_commutes : φ (algebraMap (S ⧸ pdIdeal S) G (pdQuotientMk S s)) =
          algebraMap S (B ⧸ pdIdeal B) s :=
        (e.val 0).val.1.down.hom.commutes _
      simp [k, π, h_commutes]
    | add a b ha hb => simp [ha, hb]
    | mul_X a v ha => simp [k, π, ha, h_lift]
  have hk (f : MvPolynomial (Fin (m + 1) × G) S) (hf : π f = 0) : k f ∈ pdIdeal B := by
    rw [← eq_zero_iff_mem, h_k_mod, hf, map_zero]
  -- A map out of `E` is the same as a map out of the polynomial ring sending the kernel into `𝔡 B`.
  refine (Equiv.ulift.existsUnique_congr fun g ↦ ?_).2 (existsUnique_lift _ _ k hk)
  -- A map `g : E ⟶ B` sends `z` to `e` exactly when it extends `k`, since a point of `L B` is
  -- determined by its lifts: its map to `B / 𝔡` sends each element to the class of its lift.
  have h_inj : Injective fun a : L.obj B ↦ a.val.2 := by
    rintro ⟨⟨⟨φa⟩, la⟩, ha⟩ ⟨⟨⟨φb⟩, lb⟩, hb⟩ (rfl : la = lb)
    obtain rfl : φa = φb := CommAlgCat.hom_ext (AlgHom.ext fun g ↦ (ha g).symm.trans (hb g))
    rfl
  -- The `b`-lift of the `i`-th point of `g · z` is the image under `g` of the variable `X (i, b)`.
  have h_lift_pointMap (i : Fin (m + 1)) (b : G) :
      (((pointMap z).app B g).val i).val.2 b =
        g.down.hom.hom (algebraMap (MvPolynomial (Fin (m + 1) × G) S)
          (PrincipalCompletion (preEnvelope {f | π f = 0}) p) (X (i, b))) :=
    rfl
  -- Both sides say that for each `i` and `b`, `g` sends `X (i, b)` to the `b`-lift of the
  -- `i`-th point of `e`.
  refine Subtype.ext_iff.trans ?_
  simp [← h_inj.eq_iff, _root_.funext_iff, MvPolynomial.algHom_ext_iff, k, h_lift_pointMap]

/-- Flat base change for the points of V modulo divided powers. Suppose that V satisfies
`New.Variety.IsCharting` (V covers X and is built from charts étale over tori). Then the free
abelian group on D ↦ V(D/𝔡(D)), on p-torsion-free p-complete S-algebras D, has flat base change
(`New.Variety.HasFlatBaseChange`). Here D/𝔡(D) is an R-algebra through r : R → S/𝔡(S). -/
lemma hasFlatBaseChange_freeAb_pdReduction_of_isCharting (hV : IsCharting V) :
    HasFlatBaseChange (freeAb.obj (pdReduction r ⋙ V.toFunctor)) := by
  algebraize [r]
  -- It holds on each chart by `New.Variety.HasFlatBaseChange.pdReduction_reprBy`.
  obtain ⟨-, h_charts⟩ := hV
  exact h_charts _ (HasFlatBaseChange.isClosedClass.comap (restrictAlong _)) fun b _ ↦
    ((HasFlatBaseChange.isClosedClass.comap
      (restrictAlong (@pdReduction p _ S ..))).freeAb_of_bijective
      _ (pointMap_algBaseChange_unit_bijective b.coordRing) (.pdReduction_reprBy _) :)

section

variable {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
  {A K : Type} [CommRing A] [CommRing K] {L : C' ⥤ C} {U : C ⥤ C'} (adj : L ⊣ U) (φ : C'' ⥤ C)
  (Θ : C ⥤ CommAlg A)

/-- For an adjunction L ⊣ U, a functor φ into the source of U and a functor Θ to A-algebras, the
map of A-modules Θ(L(U(φ c))) → Θ(φ c) induced by the counit, natural in c. -/
private def counitCoeff :
    (φ ⋙ U) ⋙ (L ⋙ Θ) ⋙ asModules (𝟭 (CommAlg A)) ⟶ asModules (φ ⋙ Θ) :=
  φ.whiskerLeft (whiskerRight adj.counit (asModules Θ))

/-- Let L ⊣ U. If restriction along φ, via v : Y'' ⟶ Y ∘ U ∘ φ, is bijective on the cohomology of Y
∘ U with coefficients G ∘ Θ, then the comparison along U ∘ φ given by the counit is bijective on the
cohomology of Y with coefficients G ∘ Θ ∘ L. -/
private lemma coeffCompBijective_counitCoeff (G : ModuleCat A ⥤ ModuleCat K) {Y : C' ⥤ Type 1}
    {Y'' : C'' ⥤ Type 1} (v : Y'' ⟶ (φ ⋙ U) ⋙ Y)
    (hv : (Comparison.restrict φ (moduleCoeff (asModules Θ ⋙ G))).IsBijective
      (freeAbMap (Y := U ⋙ Y) v)) :
    CoeffCompBijective (counitCoeff adj φ Θ) (freeAbMap v) G := by
  refine (isBijective_of_adj (F := moduleCoeff (asModules Θ ⋙ G)) adj).trans hv ?_
  exact freeAb.hom_ext fun _ _ ↦ rfl

end

variable [h : CrysPeriodAlgebra] [Algebra R OC] [Algebra S Amax]
  (i : pdReduction integersToPdQuotient ⋙ restrictAlg R OC ⟶ CrysTest.restrictScalars S ⋙
    pdReduction r)

/-- The comparison (a functor from p-adic tests with a map of coefficient functors) along the
functor sending a p-adic test c to D = completed A_max ⊗ W(c^♭), viewed over S, from coefficients D
to B_max ⊗ D by x ↦ 1 ⊗ x. -/
abbrev crysComparison :
    Comparison (moduleCoeff (asModules (ι fun (A : CommAlg S) ↦ IsCompleteTorsionFree A)))
      (moduleCoeff (asModules (crysThickening ⋙
        ι fun (A : CommAlg Amax) ↦ IsCompleteTorsionFree A) ⋙ tensorWith Bmax Bmax)) :=
  Comparison.of (F := moduleCoeff (asModules (ι _))) (crysThickening ⋙ CrysTest.restrictScalars S :)
    (tensorWith.mk Bmax (1 : Bmax) (asModules (crysThickening ⋙ ι _)))

/-- The natural map V(c) → V(D/𝔡(D)) on p-adic tests c induced by `New.Variety.testToPdReduction`
followed by i, which passes from the R-structure through O_C to the one through r, D the completion
of A_max ⊗ W(c^♭) viewed over S. -/
def toCrysPoints :
    PadicTest.algFunctor ⋙ restrictAlg R OC ⋙ V.toFunctor ⟶
      (crysThickening ⋙ CrysTest.restrictScalars S) ⋙ pdReduction r ⋙ V.toFunctor :=
  -- Apply `V` to `testToPdReduction`, read over `R`, followed by the comparison `i` at the ring
  -- given by `crysThickening`.
  (whiskerRight (whiskerRight testToPdReduction (restrictAlg R OC) ≫ crysThickening.whiskerLeft i)
    V.toFunctor :)

/-- Completed base change along S → A_max: the functor sending a p-torsion-free p-complete
S-algebra D to the p-adic completion of A_max ⊗_S D. As A_max is flat over S, this completion is
again p-torsion-free. -/
private def crysBaseChange [Module.Flat S Amax] : CrysTest S ⥤ CrysTest Amax :=
  lift (fun B ↦ IsCompleteTorsionFree B.1) (ι _ ⋙ algBaseChange Amax ⋙ algCompletion Amax p)
    fun D ↦
      isCompleteTorsionFree_completion fun _ _ h_smul ↦
        D.property.isSMulRegular_natCast.lTensor _ (mod_cast h_smul)

/-- The map from A_max ⊗_S D to its p-adic completion (`crysBaseChange` of D), natural in the
p-torsion-free p-complete S-algebra D. -/
private def toCrysBaseChange [Module.Flat S Amax] :
    ((ι _ ⋙ algBaseChange Amax) ⋙ 𝟭 (CommAlg Amax) : CrysTest S ⥤ CommAlg Amax) ⟶
      crysBaseChange ⋙ ι _ :=
  (ι _ ⋙ algBaseChange _).whiskerLeft (algCompletion.of ..)

/-- Completed base change along S → A_max (`crysBaseChange`) is left adjoint to restriction of
scalars, between p-torsion-free p-complete S-algebras and A_max-algebras. -/
private def crysBaseChangeAdj [Module.Flat S Amax] :
    crysBaseChange (S := S) ⊣ CrysTest.restrictScalars S := by
  -- Maps from the completion of `Amax ⊗ A` to the complete algebra `B` are maps from `Amax ⊗ A`.
  have bij_cpl (A : CrysTest S) (B : CrysTest Amax) :
      Bijective fun g : (crysBaseChange.obj A).obj ⟶ B.obj ↦ toCrysBaseChange.app A ≫ g :=
    (isCompletionBijective_completion (B := (algBaseChange Amax).obj A.obj)).comp_bijective
      (toCrysBaseChange.app A) B.property.complete
  let homEquiv (A : CrysTest S) (B : CrysTest Amax) :
      (crysBaseChange.obj A ⟶ B) ≃ (A ⟶ (CrysTest.restrictScalars S).obj B) :=
    -- Forget the subcategory, restrict along the map to the completion (`B` is complete), and use
    -- the adjunction of base change.
    .trans (.mk _ .mk) <| .trans (.ofBijective _ (bij_cpl A B)) <|
      (algBaseChangeAdj.homEquiv ..).trans (.mk (fun f ↦ ⟨f⟩) fun f ↦ f.hom)
  refine .mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := fun f ↦ (homEquiv ..).surjective.forall.2 fun g ↦ ?_
      homEquiv_naturality_right := fun _ _ ↦ rfl }
  -- Naturality in `A`: both sides restrict `g` along `f` and the map to the completion.
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_eq]
  ext
  exact congrArg _ (toCrysBaseChange.naturality_apply f (1 ⊗ₜ _))

attribute [-instance] addCommGroupH in
/-- Completing the coefficients is bijective on cohomology, under a finiteness condition. Let S be a
p-torsion-free p-complete discrete valuation ring with uniformiser p, over which A_max is a flat
algebra. Let N be a functor to abelian groups on p-torsion-free p-complete S-algebras D that has
flat base change (`New.Variety.HasFlatBaseChange`). Let L D be the p-adic completion of A_max ⊗_S D
(`crysBaseChange`). Suppose that B_max ⊗ H^m(N, L D) is a finite B_max-module in every degree m.
Then the map H^n(N, A_max ⊗_S D) → H^n(N, L D) induced by the completion is bijective. -/
private lemma bijective_pullₗ_toCrysBaseChange [IsDomain S] [IsDiscreteValuationRing S]
    [Module.Flat S Amax] (hS : IsCompleteTorsionFree S) (hp : Irreducible (p : S))
    {N : CrysTest S ⥤ Ab} (hN : HasFlatBaseChange N)
    (h_fin : ∀ m : ℕ, Module.Finite Bmax
      (Bmax ⊗[Amax] H N (moduleCoeff ((crysBaseChange ⋙ ι _) ⋙ asModules (𝟭 (CommAlg Amax)))) m))
    (n : ℕ) :
    Bijective (pullₗ (φ := 𝟭 (CrysTest S)) (Φ := asModules (ι _) ⋙ tensorWith Amax Amax)
      (Φ' := asModules (crysBaseChange ⋙ ι _)) (N := N)
      (whiskerRight toCrysBaseChange (asModules (𝟭 (CommAlg Amax)))) (𝟙 N) n) := by
  -- By flat base change and reduction mod `p`, it suffices that `H^m(N, D)` have finite rank
  -- over `S` whenever the kernel of the map is `p`-divisible. We show that independent families
  -- stay independent in `Bmax ⊗ H^m(N, L D)`, which is finite.
  -- A topological basis of `Amax` over `S`, given by its coordinate functionals. `h_max` and
  -- `h_complete` are the instances that `Amax.nonempty_adicBasis` needs.
  have h_max : (Ideal.span {(p : S)}).IsMaximal := hp.prime.isMaximal_span_singleton
  have h_complete : IsAdicComplete (Ideal.span {(p : S)}) S := hS.complete
  obtain ⟨coord⟩ := Amax.nonempty_adicBasis S (rfl : Ideal.span {(p : S)} = _)
  -- `flatEquiv m` is flat base change, and `complMap m` passes from the coefficients `Amax ⊗ D` to
  -- their completion.
  let flatEquiv (m : ℕ) : Amax ⊗[S] H N (moduleCoeff (asModules (ι _))) m ≃ₗ[Amax]
      H N (moduleCoeff (asModules (ι _) ⋙ tensorWith Amax Amax)) m :=
    ofBijective _ (hN S Amax Amax (asModules (ι _)) m)
  -- `toCompl` is the map of coefficients to the completion, typed as
  -- `isBijective_of_isReductionMod` states it.
  let toCompl : 𝟭 (CrysTest S) ⋙ asModules (ι _) ⋙ tensorWith Amax Amax ⟶
      asModules (crysBaseChange ⋙ ι _) :=
    whiskerRight toCrysBaseChange (asModules (𝟭 (CommAlg Amax)))
  let complMap (m : ℕ) : H N (moduleCoeff (asModules (ι _) ⋙ tensorWith Amax Amax)) m →ₗ[Amax]
      H N (moduleCoeff (asModules (crysBaseChange ⋙ ι _))) m :=
    pullₗ toCompl (𝟙 N) m
  -- If the kernel of `complMap m` is `p`-divisible, `z ↦ complMap m (flatEquiv m (1 ⊗ z))` keeps
  -- independence.
  have h_indep (m : ℕ)
      (h_div : ∀ x : (complMap m).ker, ∃ y : (complMap m).ker, (p : Amax) • y = x)
      (s : Set (H N (moduleCoeff (asModules (ι _))) m)) (hs : LinearIndepOn S id s) :
      LinearIndependent Amax fun z : s ↦ complMap m (flatEquiv m (1 ⊗ₜ z.val)) := by
    -- A coefficient `a d` vanishes if all its coordinates `coord.coord i (a d)` do, and these are
    -- the coefficients of a relation over `S`.
    rw [linearIndependent_iff']
    intro w a h_sum d hd
    refine coord.eq_zero_of_coord fun i ↦ linearIndependent_iff'.1 hs w (coord.coord i ∘ a) ?_ d hd
    -- The coordinate `ω = coord.coord i ⊗ 1` maps the kernel to a `p`-divisible subset of a
    -- derived `p`-complete module, and such a subset is zero.
    let ω (x : (complMap m).ker) : H N (moduleCoeff (asModules (ι _))) m :=
      lift (.lsmul S _ ∘ₗ coord.coord i) ((flatEquiv m).symm x)
    have h_approx (x : (complMap m).ker) : ∃ (c : S) (y : (complMap m).ker),
        ω x = (0 : S →ₗ[S] H N (moduleCoeff (asModules (ι _))) m) c + (p : S) • ω y := by
      obtain ⟨y, hy⟩ := h_div x
      exact ⟨0, y, by simp [ω, ← hy, Nat.cast_smul_eq_nsmul]⟩
    have hω (x : (complMap m).ker) : ω x = 0 := by
      obtain ⟨c, hc⟩ :=
        (IsDerivedComplete.cohomology (fun D ↦ D.property.isDerivedComplete)
          ..).exists_apply_eq_of_approx
          hS.isDerivedComplete 0 ω h_approx x
      rw [← hc, LinearMap.zero_apply]
    have h_sum_ker : ∑ d ∈ w, a d • flatEquiv m (1 ⊗ₜ d.val) ∈ (complMap m).ker := by
      simpa using h_sum
    -- Applying `ω` to the relation gives the relation between the coordinates.
    simpa [ω, smul_tmul'] using hω ⟨_, h_sum_ker⟩
  refine hN.isBijective_of_isReductionMod hS h.isCompleteTorsionFree (fun D ↦ D.property) hp toCompl
    (fun m h_div ↦ ?_) (fun D ↦ (crysBaseChange.obj D).property)
    (fun _ _ _ _ ↦ .comp_algebraMap) n
  -- An independent family of `H^m(N, D)` of the size of its rank stays independent in the finite
  -- module `Bmax ⊗ H^m(N, L D)`, so the rank is finite.
  obtain ⟨s, hs_rank, hs⟩ := exists_set_linearIndependent S (H N (moduleCoeff (asModules (ι _))) m)
  -- The instance that `lt_aleph0_of_finite` needs.
  have h_fin_m : Module.Finite Bmax
      (Bmax ⊗[Amax] H N (moduleCoeff (asModules (crysBaseChange ⋙ ι _))) m) := h_fin m
  exact hs_rank.ge.trans_lt
    (linearIndependent_one_tmul (S := Bmax) (h_indep m h_div s hs)).lt_aleph0_of_finite

attribute [-instance] addCommGroupH in
/-- Let S be a p-torsion-free p-complete discrete valuation ring with uniformiser p, and 𝔡(D) the
ideal of x with n! ∣ xⁿ for all n. On p-torsion-free p-complete A_max-algebras D, let `i` be an
isomorphism of R-algebras from D/𝔡(D), reduced along O_C → A_max/𝔡(A_max), to D viewed over S and
reduced along `r`. Let `V` be a subfunctor of the functor `X` on R-algebras with `IsCharting V`.
Suppose that for every degree, the cohomology of V on p-adic tests c (products of cells with a map
from O_C) is a finite B_max-module, with coefficients B_max ⊗ D, where D is the completed
A_max ⊗ W(c^♭). Then in each degree n it is spanned over B_max by the classes pulled back along
`New.Variety.crysComparison` from H^n of D ↦ V(D/𝔡(D)). -/
lemma span_range_crysComparison_pull_eq_top (hi_iso : IsIso i) [IsDomain S]
    [IsDiscreteValuationRing S] (hS : IsCompleteTorsionFree S) (hV : IsCharting V)
    (hp : Irreducible (p : S))
    (h_fin : ∀ n : ℕ,
      Module.Finite Bmax
        (H (freeAb.obj (PadicTest.algFunctor ⋙ restrictAlg R OC ⋙ V.toFunctor))
          (moduleCoeff (asModules (crysThickening ⋙ ι _) ⋙ tensorWith Bmax Bmax)) n))
    (n : ℕ) :
    Submodule.span Bmax
      (Set.range (crysComparison.pull (freeAbMap (toCrysPoints V i)) n)) = ⊤ := by
  -- Work on `p`-torsion-free complete `S`-algebras `D`, with `N` the free abelian group on the
  -- points of `V` in `D / 𝔡`. We identify the period cohomology with `Bmax ⊗ Amax ⊗ H^n(N, D)`, so
  -- that the elements `1 ⊗ 1 ⊗ z` go to crystalline classes. Flat base change applies because
  -- `Amax` is torsion-free over the discrete valuation ring `S`.
  have h_torsionFree : IsTorsionFree S Amax := by
    -- `p` is regular on `Amax`, and every nonzero element of `S` divides a power of `p`.
    refine isTorsionFree_of_dvd_pow h.isSMulRegular_natCast fun ht ↦ ?_
    obtain ⟨k, hk⟩ := associated_pow_irreducible ht hp
    exact ⟨k, hk.dvd⟩
  algebraize [r, (algebraMap Amax Bmax).comp (algebraMap S Amax)]
  let N : CrysTest S ⥤ Ab := freeAb.obj (pdReduction r ⋙ V.toFunctor)
  -- Completed base change `L` along `S → Amax` is left adjoint to restriction of scalars.
  let L : CrysTest S ⥤ CrysTest Amax := crysBaseChange
  let adj : L ⊣ CrysTest.restrictScalars S := crysBaseChangeAdj
  -- Flat base change and the crystalline comparison hold on charts, hence on `V`.
  have hN : HasFlatBaseChange N := hasFlatBaseChange_freeAb_pdReduction_of_isCharting V hV
  obtain ⟨-, h_charts⟩ := hV
  -- The comparison: `H^n(N, Bmax ⊗ L D)` is the period cohomology of `V` on `p`-adic tests.
  -- By `adj` one may pass from `S`-algebras to `Amax`-algebras, where it holds on charts.
  have h_cmp :
      CoeffCompBijective (counitCoeff adj crysThickening (ι _)) (freeAbMap (toCrysPoints V i))
        (tensorWith Bmax Bmax) := by
    have h_toCrysPoints : 𝟙 _ ≫ toCrysPoints V i =
        whiskerRight testToPdReduction _ ≫ crysThickening.whiskerLeft (whiskerRight i _) := by
      rw [Category.id_comp, toCrysPoints, whiskerRight_comp]
      rfl
    refine coeffCompBijective_counitCoeff adj crysThickening (ι _) (tensorWith Bmax Bmax) _
      (((Comparison.restrict ..).isBijective_congr h_toCrysPoints (.of_isIso _) (.of_isIso _)).2 ?_)
    exact h_charts _ ((isClosedClass (.restrict ..) testToPdReduction).comap (restrictAlong _))
      fun b ↦ hasCrysComparison_chart _ b.etale
  -- `θ n` goes from `Bmax ⊗ H'`, where `H'` has the completed coefficients `L D`, to the period
  -- cohomology: flat base change, then the comparison.
  let θ (n : ℕ) :
      Bmax ⊗[Amax] H N (moduleCoeff ((L ⋙ ι _) ⋙ asModules (𝟭 (CommAlg Amax)))) n ≃ₗ[Bmax]
        H (freeAb.obj (PadicTest.algFunctor ⋙ restrictAlg R OC ⋙ V.toFunctor))
          (moduleCoeff (asModules (crysThickening ⋙ ι _) ⋙ tensorWith Bmax Bmax)) n :=
    ofBijective _ (hN Amax Bmax Bmax _ n) ≪≫ₗ ofBijective (pullₗ ..) (h_cmp n)
  -- `flatEquiv` is flat base change, and `complMap` passes from the coefficients `Amax ⊗ D` to
  -- their completion `L D`.
  let flatEquiv : Amax ⊗[S] H N (moduleCoeff (asModules (ι _))) n ≃ₗ[Amax]
      H N (moduleCoeff (asModules (ι _) ⋙ tensorWith Amax Amax)) n :=
    ofBijective _ (hN S Amax Amax (asModules (ι _)) n)
  let complMap : H N (moduleCoeff (asModules (ι _) ⋙ tensorWith Amax Amax)) n →ₗ[Amax]
      H N (moduleCoeff (asModules (L ⋙ ι _))) n :=
    pullₗ (φ := 𝟭 _) (whiskerRight toCrysBaseChange (asModules (𝟭 _))) (𝟙 N) n
  -- Completion of the coefficients is bijective on cohomology, as `Bmax ⊗ H^m(N, L D)` is finite.
  have hu : Bijective complMap :=
    bijective_pullₗ_toCrysBaseChange hS hp hN (fun m ↦ (h_fin m).equiv (θ m).symm) n
  let e :
      Bmax ⊗[Amax] (Amax ⊗[S] H N (moduleCoeff (asModules (ι _))) n) ≃ₗ[Bmax]
        H (freeAb.obj (PadicTest.algFunctor ⋙ restrictAlg R OC ⋙ V.toFunctor))
          (moduleCoeff (asModules (crysThickening ⋙ ι _) ⋙ tensorWith Bmax Bmax)) n :=
    (flatEquiv ≪≫ₗ ofBijective complMap hu).baseChange Amax Bmax _ _ ≪≫ₗ θ n
  -- For `z` in `H^n(N, D)`, `e (1 ⊗ 1 ⊗ z)` is the crystalline class of `z`: both are images of `z`
  -- under maps of coefficients, which agree by the triangle identity of `adj`.
  have h_pull_push (z : H N (moduleCoeff (asModules (ι _))) n) :
      (ofModuleHom (crysThickening ⋙ CrysTest.restrictScalars S)
          (whiskerRight (counitCoeff adj crysThickening (ι _))
            (tensorWith Bmax Bmax))).pull (freeAbMap (toCrysPoints V i)) n
        (push N (tensorWith.mk Amax 1 (asModules (ι _)) ≫
            coeffMap (whiskerRight toCrysBaseChange (asModules (𝟭 (CommAlg Amax)))) ≫
              tensorWith.mk Bmax 1 ((L ⋙ ι _) ⋙ asModules (𝟭 (CommAlg Amax)))) n z) =
        crysComparison.pull (freeAbMap (toCrysPoints V i)) n z := by
    refine (crysComparison.pull_push _ _ _ ?_ ..).trans (Ext.comp_mk₀_id _)
    ext c x
    exact congr(⟨_ ⊗ₜ $(adj.right_triangle_components (crysThickening.obj c)) _⟩)
  -- The elements `1 ⊗ 1 ⊗ z` span the source of `e`, so it is enough that `e` send each of them
  -- to a crystalline class.
  -- That is, the quotient by the span, precomposed with `e`, is zero on all `1 ⊗ 1 ⊗ z`.
  refine (orderIsoMapComap e).symm.injective ((ker_mkQ _).symm.trans (ker_eq_top.2 ?_))
  ext z
  refine (Quotient.mk_eq_zero _).2 (subset_span ⟨z, .symm ?_⟩)
  -- Unfolding `e` on `1 ⊗ 1 ⊗ z` gives the left side of `h_pull_push z`.
  simpa [e, complMap, flatEquiv, θ, ← push_comp, pullₗ, pull_id_eq_push] using h_pull_push z

end CrystallineClasses

end New.Variety

end
