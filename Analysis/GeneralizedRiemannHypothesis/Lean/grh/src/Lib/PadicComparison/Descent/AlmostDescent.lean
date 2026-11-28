import Lib.Cohomology.Etale.RelativeChains
import Lib.General.Algebra.PerfectAlgebras

/-!
# Almost coefficients, v-descent for perfect algebras and acyclicity of tilt points

The tilt O♭ (`New.Period.OFlat`) has maximal ideal 𝔪 (`New.Variety.MaxIdealFlat`) and contains p♭
(`New.Variety.pFlat`); N is an O♭-module killed by p♭. The coefficient functor
`New.Variety.almostCoeff N` sends an O♭-algebra b to b ⊗ N ⊗ 𝔪, a case of
`New.Variety.tensorCoeff`.
For these coefficients, a map of perfect O♭-algebras that is onto on points in tilts of tests is a
cover. By Čech descent, the points of a perfect algebra in tilts are acyclic. Auxiliary results
treat 𝔪² = 𝔪 and Witt vectors of O♭-algebras.

## Main definitions and results

* `New.Variety.isCover_of_points`: if p^♭ kills N, a map b → b' of perfect O^♭-algebras that is onto
  on points with values in tilts of tests is a cover (`New.Variety.IsCover`) for the coefficients
  D ↦ D ⊗ N ⊗ 𝔪.
* `New.Variety.isAcyclicAt_perfectTilt`: for N killed by p♭, the points of a perfect O♭-algebra in
  tilts of tests are acyclic (`New.Variety.IsAcyclicAt`) for the coefficients b ↦ b ⊗ N ⊗ 𝔪. This
  holds on the category of perfect O♭-algebras.
* `New.Variety.isAcyclicOnPerfect_almostCoeff`: the same on all O♭-algebras, for b perfect.

Notions from other files:
* `New.Period.OFlat`: The ring O^♭, the inverse limit of O_C/p along x ↦ x^p, where O_C is the ring
  of integers of C_p.
* `New.Variety.moduleCoeff`, `New.Variety.tensorWith`: A functor Φ to S-modules regarded as
  coefficients for cohomology, and M ⊗_S Φ for an S-module M.
* `New.Variety.pFlat`: The element p^♭ = ξ mod p of O^♭ = A_inf/p, the zeroth Witt coefficient of
  the generator ξ of the kernel of θ.
* `New.Variety.PadicTest`: A non-empty family of cells (`New.Variety.IsCell`) with a ring map from
  O_C = `New.OC` to their product; `TiltRing` is the tilt of the product.

## Relation to the literature

Known result: Almost acyclicity of the structure sheaf for the v-topology. The statement holds for
any perfect algebra over the tilt of O_C, as cohomology on products of complete absolutely
integrally closed valuation rings modulo p♭, with the maximal ideal put into the coefficients so
that the result is exact. The proof passes to a valuation ring. Source: P. Scholze, Étale cohomology
of diamonds, arXiv 1709.07343 (2017), Theorem 8.7, Proposition 8.8; for perfect rings B. Bhatt, P.
Scholze, Projectivity of the Witt vector affine Grassmannian, Invent. Math. 209 (2017), Theorem 4.1;
points argument O. Gabber, S. Kelly, Points in algebraic geometry, J. Pure Appl. Algebra 219 (2015),
Theorem 2.3.
-/

noncomputable section

namespace New.Variety

/-!
## Almost coefficient functors and idempotence of 𝔪

`New.Variety.MaxIdealFlat.exists_smul_eq` is a sharp form of 𝔪² = 𝔪: every element of 𝔪 is s • k
with k in 𝔪 and s nilpotent modulo a given t ≠ 0.
-/

section AlmostCoefficients

open CategoryTheory TensorProduct Period

variable {p : ℕ} [ThePrime p]

/-- For an O^♭-module M, the functor B ↦ B ⊗_{O^♭} M from commutative O^♭-algebras to
O^♭-modules. -/
noncomputable abbrev tensorCoeff (M : ModuleCat OFlat) : CommAlg OFlat ⥤ ModuleCat OFlat :=
  asModules (𝟭 (CommAlg OFlat)) ⋙ MonoidalCategory.tensorRight M

/-- For an O^♭-module N, the functor b ↦ b ⊗ N ⊗ 𝔪 from commutative O^♭-algebras to O^♭-modules,
𝔪 the maximal ideal of O^♭ and tensor products over O^♭. -/
noncomputable abbrev almostCoeff (N : Type) [AddCommGroup N] [Module OFlat N] :
    CommAlg OFlat ⥤ ModuleCat OFlat :=
  tensorCoeff (ModuleCat.of OFlat (N ⊗[OFlat] MaxIdealFlat))

/-- For m in the maximal ideal 𝔪 of O^♭ and t ≠ 0 in O^♭, one can write m = s·k with k in 𝔪 and
s in O^♭ such that t divides a power of s. -/
lemma MaxIdealFlat.exists_smul_eq (m : MaxIdealFlat) {t : OFlat} (ht_ne : t ≠ 0) :
    ∃ (s : OFlat) (k : MaxIdealFlat), s • k = m ∧ ∃ n : ℕ, t ∣ s ^ n := by
  -- Take `s = k` a square root of `m`; it is not a unit, and every `t ≠ 0` divides a power of a
  -- non-unit (`OFlat.exists_dvd_pow`).
  obtain ⟨s, hs_sq⟩ : ∃ s : OFlat, s ^ 2 = m := OFlat.isAbsIntegrallyClosed.exists_pow_eq 2 m
  have hs_nonunit : ¬IsUnit s := fun hs_unit ↦
    (IsLocalRing.mem_maximalIdeal _).mp m.property (by simpa only [hs_sq] using hs_unit.pow 2)
  exact ⟨s, ⟨s, hs_nonunit⟩, Subtype.ext ((sq s).symm.trans hs_sq),
    OFlat.exists_dvd_pow hs_nonunit ht_ne⟩

end AlmostCoefficients

/-!
## The zeroth Witt coefficient and p-torsion-freeness

An O^♭-algebra b is an algebra over A_inf = W(O^♭) through the zeroth Witt coefficient.
-/

section WittTensorRegular

open TensorProduct Period WittVector

variable {p : ℕ} [ThePrime p] (b : CommAlg OFlat)

noncomputable instance : Algebra Ainf b := .compHom _ constantCoeff

instance : IsScalarTower Ainf OFlat b := .of_compHom ..

/-- For an O^♭-algebra b, the A_inf-linear map W(b) → b sending a Witt vector to its zeroth
coefficient. -/
noncomputable def wittConstCoeff : wittFunctor.obj b →ₗ[Ainf] b :=
  AlgHom.toLinearMap { toRingHom := constantCoeff, commutes' _ := rfl }

/-- If the A_inf-module 𝒜 has no p-torsion and the O^♭-algebra b is perfect without p♭-torsion
(`New.Variety.IsPerfectTorsionFree`), then 𝒜 ⊗ W(b), over A_inf, has no p-torsion. -/
lemma isSMulRegular_tensor_witt {𝒜 : Type} [AddCommGroup 𝒜] [Module Ainf 𝒜]
    (h𝒜_reg : IsSMulRegular 𝒜 p) {b : CommAlg OFlat} (hb : IsPerfectTorsionFree b) :
    IsSMulRegular (𝒜 ⊗[Ainf] wittFunctor.obj b) p := by
  obtain ⟨hb_perf, hb_reg⟩ : PerfectRing b p ∧ IsSMulRegular b pFlat := hb
  -- Every nonzero element of the valuation ring `OFlat` divides a power of the non-unit `pFlat`, so
  -- `b`, which has no `pFlat`-torsion, is torsion-free and hence flat over `OFlat`.
  have hb_torsionFree : Module.IsTorsionFree OFlat b :=
    isTorsionFree_of_dvd_pow hb_reg (OFlat.exists_dvd_pow not_isUnit_pFlat)
  -- `OFlat = Ainf / p` and `b = W(b) / p`, and `W(b)` has no `p`-torsion.
  have hO_mod : IsReductionMod p (constantCoeff : WittVector p OFlat →+* OFlat) :=
    (isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat OFlat).left
  have hb_mod : IsReductionMod p (wittConstCoeff b) :=
    (isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat b).left
  have hW_reg : IsSMulRegular (WittVector p b) p :=
    (isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat b).right.left.regular
  -- So `W(b) / p` is flat over `Ainf / p`; this keeps `p` regular on the tensor product.
  exact isSMulRegular_tensor_of_flat_mod (wittConstCoeff b) hO_mod hb_mod hW_reg h𝒜_reg

end WittTensorRegular

/-!
## v-descent for almost coefficients

* Suppose a relative class z with coefficients E ⊗ D ⊗ N ⊗ 𝔪 is nonzero, of least degree. It is
  pushed along maps E → E' (`New.Variety.tensorPush`) and stays nonzero up to a valuation ring V
  (`New.Variety.exists_maximal_tensorPush_ne_zero`,
  `New.Variety.exists_perfect_valuationRing_factor`);
* `New.Variety.exists_faithfullyFlat_padicTest`, `New.Variety.tensorPush_quotient_ne_zero`: to a
  quotient of V over which the tilt of a test is faithfully flat;
* `New.Variety.faithfullyFlat_descent`: there it vanishes, as this point of b lifts to b'.

`New.Variety.PerfectAlg` S is the category of perfect S-algebras, `New.Variety.H` K F n is Ext^n(K,
F) for functors to abelian groups, and `New.Variety.relFreeAb` U = ℤ[Y]/ℤ[U], for a subfunctor U of
Y, gives relative cohomology. For an object X, h_X = Hom(X, −).
-/

section VDescent

open RingHom hiding mk
open LinearMap hiding lTensor rTensor mk ker rTensor_tensor
open TensorProduct Ideal Quotient Function Period ValuationRing Module NeZero Algebra ULift
  IsLocalRing CategoryTheory Limits Functor AlgebraTensorModule ConcreteCategory ObjectProperty H
  Comparison HasBaseChange Filter Localization MonoidalCategory Flat WittVector AlgHom
open ModuleCat hiding ofHom

variable {p : ℕ} [ThePrime p] {S M : Type}
  {M' M'' V A : Type _} [CommRing S] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [CommRing V] [CommRing A]
  (N : Type) [AddCommGroup N] [Module OFlat N] [Algebra OFlat S] [Module S M] [Module S M']
  [Module S M''] {a b d : PerfectAlg S} (φ : b ⟶ d) {C : Type 1} [Category C]
  {K : AbFunctor C} {n : ℕ} {Φ : C ⥤ ModuleCat S} {z : H K (moduleCoeff (Φ ⋙ tensorWith S M)) n}
  {f : M →ₗ[S] M'} {g : M' →ₗ[S] M''}

/-! ### Two facts of commutative algebra over O^♭ -/

/-- For a reduced commutative O^♭-algebra S, the O^♭-module 𝔪 ⊗_{O^♭} S is torsion-free, where
𝔪 is the maximal ideal of O^♭. -/
instance MaxIdealTensor.isTorsionFree_of_isReduced [IsReduced S] :
    IsTorsionFree OFlat (MaxIdealFlat ⊗[OFlat] S) := by
  refine ⟨fun t ht ↦ ?_⟩
  -- `m ⊗ x = 0` for `t`-torsion `x`: write `m = s • k` with `k ∈ 𝔪` and `t ∣ s ^ n`; then `s • x`
  -- is nilpotent, so zero.
  have h_ker :
      LinearMap.lTensor MaxIdealFlat (LinearMap.ker (LinearMap.lsmul OFlat S t)).subtype = 0 := by
    refine ext' fun m ⟨x, (htx : t • x = 0)⟩ ↦ ?_
    obtain ⟨s, k, rfl, n, d, hd : s ^ n = t * d⟩ := m.exists_smul_eq ht.ne_zero
    have h_nilpotent : (s • x) ^ (n + 1) = 0 := by grind [smul_pow, Algebra.smul_def]
    have hsx : s • x = 0 := IsReduced.eq_zero _ ⟨n + 1, h_nilpotent⟩
    rw [LinearMap.lTensor_tmul, Submodule.subtype_apply, smul_tmul, hsx, tmul_zero,
      LinearMap.zero_apply]
  -- As `𝔪` is flat, the kernel of `t` on `𝔪 ⊗ S` is the image of the map in `h_ker`.
  have h_inj :
      Function.Injective (LinearMap.lTensor MaxIdealFlat (DistribSMul.toLinearMap OFlat S t)) :=
    (injective_iff_eq_zero_of_exact
      (lTensor_exact MaxIdealFlat (lsmul OFlat S t).exact_subtype_ker_map)).mpr h_ker
  rwa [lTensor_smul_action] at h_inj

/-- Let V be a perfect O^♭-algebra that is a valuation domain, in which p^♭ is neither zero nor a
unit. Then there are a p-adic test c and an O^♭-algebra map φ from V to the tilt `c.TiltRing` of c
such that the induced map V / ker φ → `c.TiltRing` is faithfully flat and p^♭ divides every element
of the kernel of φ. Here a p-adic test is a non-empty family of cells together with a ring map from
O_C to their product. -/
lemma exists_faithfullyFlat_padicTest (V : CommAlg OFlat) [IsDomain V] [ValuationRing V]
    [PerfectRing V p] (h_ne : algebraMap OFlat V pFlat ≠ 0)
    (h_nonunit : ¬IsUnit (algebraMap OFlat V pFlat)) :
    ∃ (c : PadicTest) (φ : V →ₐ[OFlat] c.TiltRing),
      φ.kerLift.FaithfullyFlat ∧
      ∀ v : V, φ v = 0 → algebraMap OFlat V pFlat ∣ v := by
  -- Take a map `ρ` from `OC ⊗ W(V)` to a cell `W` that sends the kernel of the map `π` to the
  -- residue field of `V` to nonunits; `φ` is the corresponding map from `V` to the tilt of `W`.
  -- `π` is defined because the kernel of `theta` is generated by `xi`, which reduces to `pFlat`,
  -- a nonunit of `V`.
  have h_theta (a : Ainf) (ha : theta a = 0) : algebraMap Ainf (ResidueField V) a = 0 := by
    have h_dvd : algebraMap OFlat V pFlat ∣ algebraMap Ainf V a :=
      map_dvd (algebraMap OFlat V) (map_dvd constantCoeff (theta_eq_zero_iff_xi_dvd.mp ha))
    exact eq_zero_iff_mem.mpr fun h_unit ↦ h_nonunit (isUnit_of_dvd_unit h_dvd h_unit)
  let π : OC ⊗[Ainf] wittFunctor.obj V →ₐ[Ainf] ResidueField V :=
    TensorProduct.productMap
      (.liftOfSurjective (ofId Ainf OC) theta_surjective (ofId Ainf (ResidueField V)) h_theta)
      ⟨.comp (residue V) constantCoeff, fun _ ↦ rfl⟩
  -- The ring `OC ⊗ W(V)` has no `p`-torsion, as `pFlat` is regular on the domain `V`, and `ker π`
  -- is a prime ideal that contains `p`.
  have hp_reg : IsSMulRegular (OC ⊗[Ainf] wittFunctor.obj V) p :=
    isSMulRegular_tensor_witt (.of_ne_zero (NeZero.ne p))
      ⟨inferInstance, (isSMulRegular_algebraMap_iff _).mp (.of_ne_zero h_ne)⟩
  have hp_mem : (p : OC ⊗[Ainf] wittFunctor.obj V) ∈ ker π := by
    simp [natCast_eq_zero_of_algebra_oFlat]
  obtain ⟨W, hW_ring, hW_cell, ρ, hρ⟩ : ∃ (W : Type) (_ : CommRing W) (_ : IsCell p W)
      (ρ : OC ⊗[Ainf] wittFunctor.obj V →+* W), ∀ x ∈ ker π, ¬IsUnit (ρ x) :=
    exists_cell_over (ker_isPrime π) hp_reg hp_mem
  -- `c.fst` is the test with the one cell `W` and `c.snd` the point `ρ`. By `homTiltIso` this
  -- point is induced by `θ ∘ W(φ)` for an algebra map `φ` from `V` to the tilt.
  let c : Sigma (PadicTest.algFunctor ⋙ reprBy ((wittFunctor ⋙ algBaseChange OC).obj V)) :=
    cellPoint ((wittFunctor ⋙ algBaseChange OC).obj V) fun _ : Unit ↦ ρ
  obtain ⟨⟨φ : V →+* c.fst.TiltRing, hφ_alg⟩, hφ⟩ :=
    surjective_of_epi (homTiltIso.hom c.fst) c.snd
  -- The ring `c.fst.ProdRing ≃ W` of the test is a valuation ring, hence so is its tilt
  -- `c.fst.TiltRing`. The image of `V` in the tilt is a valuation ring too, so the inclusion is
  -- flat.
  have e_prod : c.fst.ProdRing ≃+* W := .piUnique fun () ↦ W
  have h_prod_domain : IsDomain c.fst.ProdRing := e_prod.injective.isDomain
  have h_prod_valuationRing : ValuationRing c.fst.ProdRing :=
    e_prod.symm.surjective.valuationRing e_prod.symm.toRingHom
  have h_ker_prime : (ker φ).IsPrime := ker_isPrime φ
  have h_quot_valuationRing : ValuationRing (V ⧸ ker φ) := (mkₐ_surjective V (ker φ)).valuationRing
  algebraize [φ.kerLift]
  have h_torsionFree : IsTorsionFree (V ⧸ ker φ) c.fst.TiltRing :=
    isTorsionFree_iff_algebraMap_injective.mpr φ.kerLift_injective
  -- `φ` is local: if `φ v` is a unit then so is `ρ (1 ⊗ [v])`, its untilt, and by `hρ` the element
  -- `1 ⊗ [v]` is not in the kernel of `π`.
  have h_local (v : V) (hv : IsUnit (φ v)) : IsUnit v := by
    by_contra hv_nonunit
    have h_mem : (1 ⊗ₜ teichmuller p v : OC ⊗[Ainf] wittFunctor.obj V) ∈ ker π :=
      eq_zero_iff_mem.mpr (mul_mem_left _ _ hv_nonunit)
    apply hρ (1 ⊗ₜ teichmuller p v) h_mem
    -- The equation `hφ` of points, evaluated at `1 ⊗ [v]`.
    have h_point : PadicTest.thetaIso.hom c.fst (1 ⊗ₜ WittVector.map φ (teichmuller p v)) =
        fun _ ↦ ρ (1 ⊗ₜ teichmuller p v) :=
      congrArg (fun q ↦ q.down.hom (1 ⊗ₜ teichmuller p v)) hφ
    have h_untilt :
        (teichmuller p (φ v)).fontaineTheta c.fst.ProdRing p () = ρ (1 ⊗ₜ teichmuller p v) := by
      rw [← map_teichmuller]
      exact congrFun ((c.fst.thetaIso_hom_one_tmul _).symm.trans h_point) ()
    rw [← h_untilt]
    exact ((hv.map (teichmuller p)).map (fontaineTheta c.fst.ProdRing p)).apply ()
  have h_kerLift_local : IsLocalHom φ.kerLift :=
    ⟨Quot.ind fun v hv ↦ (h_local v hv).map (mkₐ V _)⟩
  refine ⟨c.fst, ⟨φ, hφ_alg⟩, .of_flat_of_isLocalHom, fun v (hφv : φ v = 0) ↦ ?_⟩
  -- If `v` divided `pFlat`, then `pFlat` would vanish in the tilt, where it is regular.
  have h_tilt_ne : algebraMap OFlat c.fst.TiltRing pFlat ≠ 0 :=
    IsLeftRegular.ne_zero (R := c.fst.TiltRing) c.fst.isPerfectTorsionFree_tilt.right
  rcases dvd_total (algebraMap OFlat V pFlat) v with h_dvd | h_dvd
  · exact h_dvd
  · have h_img_dvd : φ v ∣ φ (algebraMap OFlat V pFlat) := map_dvd φ h_dvd
    rw [hφv, zero_dvd_iff] at h_img_dvd
    exact absurd ((hφ_alg pFlat).symm.trans h_img_dvd) h_tilt_ne

local instance : IsScalarTower S S M := inferInstance

/-- For a functor Φ from C to S-modules, a functor K from C to abelian groups and a degree n: the
additive map that sends an S-linear map f: M → M' to the induced homomorphism
H^n(K, M ⊗_S Φ) → H^n(K, M' ⊗_S Φ). -/
def tensorPush :
    (M →ₗ[S] M') →+ H K (moduleCoeff (Φ ⋙ tensorWith S M)) n →+
      H K (moduleCoeff (Φ ⋙ tensorWith S M')) n :=
  (pushHom K (moduleCoeff (Φ ⋙ tensorWith S M)) (moduleCoeff (Φ ⋙ tensorWith S M')) n).comp <|
    AddMonoidHom.mk'
      (fun f ↦ coeffMap (Φ.whiskerLeft ((curriedTensor (ModuleCat S)).map (↟f)) :
        Φ ⋙ tensorWith S M ⟶ Φ ⋙ tensorWith S M'))
      (by aesop)

/-- The coefficient map of a composite of natural maps is the composite of the coefficient maps. -/
private lemma coeffMap_comp {Ψ Θ : C ⥤ ModuleCat S} (β : Φ ⟶ Ψ) (β' : Ψ ⟶ Θ) :
    coeffMap (β ≫ β') = coeffMap β ≫ coeffMap β' :=
  rfl

private lemma coeffMap_id : coeffMap (𝟙 Φ) = 𝟙 (moduleCoeff Φ) :=
  rfl

/-- For a functor Φ to S-modules, the natural map M ⊗ Φ → M' ⊗ Φ induced by an S-linear map
f: M → M'. -/
private def tensorCoeffMap (Φ : C ⥤ ModuleCat S) (f : M →ₗ[S] M') :
    Φ ⋙ tensorWith S M ⟶ Φ ⋙ tensorWith S M' :=
  Φ.whiskerLeft ((curriedTensor (ModuleCat S)).map (↟f))

private lemma tensorCoeffMap_comp :
    tensorCoeffMap Φ (g ∘ₗ f) = tensorCoeffMap Φ f ≫ tensorCoeffMap Φ g :=
  congrArg Φ.whiskerLeft ((curriedTensor (ModuleCat S)).map_comp (↟f) (↟g))

private lemma tensorCoeffMap_id :
    tensorCoeffMap Φ (LinearMap.id : M →ₗ[S] M) = 𝟙 (Φ ⋙ tensorWith S M) :=
  congrArg Φ.whiskerLeft ((curriedTensor (ModuleCat S)).map_id (ModuleCat.of S M))

/-- `tensorPush f` is the push-forward along the map of coefficients M ⊗ Φ → M' ⊗ Φ induced by f. -/
lemma tensorPush_apply (f : M →ₗ[S] M') (x : H K (moduleCoeff (Φ ⋙ tensorWith S M)) n) :
    tensorPush f x = push K (coeffMap (tensorCoeffMap Φ f)) n x :=
  rfl

@[simp]
lemma tensorPush_comp : tensorPush (g ∘ₗ f) z = tensorPush g (tensorPush f z) := by
  simp only [tensorPush_apply, tensorCoeffMap_comp, coeffMap_comp, push_comp]

/-- Let M → M' → M'' → 0 be exact via f, g, with f ⊗ Φ(A) injective for every object A of C. If
H^m(K, M'' ⊗ Φ) = 0 for all m < n, then classes z and y in H^n(K, M ⊗ Φ) with the same image under
`tensorPush f` are equal. -/
lemma eq_of_tensorPush_eq {y : H K (moduleCoeff (Φ ⋙ tensorWith S M)) n} (h_exact : Exact f g)
    (h_surj : Surjective g) (h_inj : ∀ A : C, Function.Injective (f.rTensor (Φ A)))
    (h_vanish : ∀ m < n, Subsingleton (H K (moduleCoeff (Φ ⋙ tensorWith S M'')) m)) :
    tensorPush f z = tensorPush f y → z = y := by
  -- The sequence of coefficients `0 → M ⊗ Φ → M' ⊗ Φ → M'' ⊗ Φ → 0` is short exact.
  obtain ⟨_, h_short⟩ := shortExact_of_app
    (α := whiskerRight (tensorCoeffMap Φ f) (forget₂ (ModuleCat S) Ab))
    (g := whiskerRight (tensorCoeffMap Φ g) (forget₂ (ModuleCat S) Ab)) h_inj
    (fun A ↦ rTensor_exact (Φ.obj A) h_exact h_surj) fun A ↦ rTensor_surjective (Φ.obj A) h_surj
  -- In its long exact sequence the third terms vanish below degree `n`, so the first map is
  -- injective in degree `n`.
  intro h_eq
  exact (LongExactSeq.covariant
      (h_short.map_of_exact ((whiskeringRight C _ _).obj AddCommGrpCat.uliftFunctor))
      K).f_injective_of_g_surjective (fun m hm x ↦ ⟨0, (h_vanish m hm).elim _ x⟩) h_eq

open WidePushout in
/-- Let S be an O^♭-algebra and φ: b → d a map of perfect S-algebras. On perfect S-algebras, the
(m+1)-fold fibre power of h_d over h_b (`New.Variety.cech`) is representable: there are a perfect
S-algebra D and a point z of the fibre power at D such that, for every A, the map h_D(A) → fibre
power at A induced by z is bijective. -/
lemma exists_repr_cech (m : ℕ) :
    ∃ (D : PerfectAlg S) (z : cech (reprMap φ) m D),
      AllBijective fun A : PerfectAlg S ↦ pointMap z A := by
  -- The representing object is the wide pushout `d ⊗_b ⋯ ⊗_b d` of `m + 1` copies of `φ`, which
  -- exists among perfect algebras; the universal point is the family of its coprojections.
  have h_closed (J : Type) :
      IsClosedUnderColimitsOfShape (fun A : CommAlg S ↦ PerfectRing A p) (WidePushoutShape J) :=
    PerfectAlg.isClosedUnderColimitsOfShape_widePushoutShape (S := S)
      natCast_eq_zero_of_algebra_oFlat J
  have : HasColimitsOfShape (WidePushoutShape (Fin (m + 1))) (PerfectAlg S) := inferInstance
  refine ⟨widePushout b (fun _ : Fin (m + 1) ↦ d) fun _ ↦ φ, ⟨fun i ↦ ⟨ι (fun _ ↦ φ) i⟩, ?_⟩,
    fun A ↦ bijective_iff_has_inverse.mpr ?_⟩
  · simp [reprMap, reprFunctor, DFunLike.coe, arrow_ι fun _ ↦ φ]
  -- The inverse glues `m + 1` maps `d ⟶ A` that agree on `b` to one map out of the pushout.
  refine ⟨fun e ↦ ⟨desc (φ ≫ (e.val 0).down) (fun i ↦ (e.val i).down)
      fun i ↦ congrArg ULift.down (e.property i 0)⟩, fun g ↦ ?_, fun e ↦ ?_⟩
  · -- A map out of the pushout is determined by its composites with the coprojections.
    refine ULift.down_injective (.symm ?_)
    apply eq_desc_of_comp_eq
    exacts [fun _ ↦ rfl, (arrow_ι_assoc _ 0 g.down).symm]
  · -- The glued map, composed with the `i`-th coprojection, is the `i`-th map.
    exact Subtype.ext (funext fun i ↦ ULift.down_injective (ι_desc (fun _ ↦ φ) ..))

/-- For a map φ: b → d of perfect S-algebras, the functor D ↦ ℤ[Hom(b,D)]/ℤ[maps that factor
through φ] from perfect S-algebras to abelian groups. -/
abbrev relFreeAbOfHom : PerfectAlg S ⥤ Ab := relFreeAb (Subfunctor.range (reprMap φ))

/-- Let S be an O^♭-algebra, φ: b → d a map of perfect S-algebras, and Q the functor
D ↦ ℤ[Hom(b,D)]/ℤ[maps factoring through φ] (`New.Variety.relFreeAbOfHom φ`). Let Φ be a functor
from perfect S-algebras to S-modules, and V → A a map of S-algebras with A flat over V. If x in
H^n(Q, V ⊗_S Φ) maps to zero in H^n(Q, A ⊗_S Φ) under the map induced by V → A (`tensorPush`), then
1 ⊗ x = 0 in A ⊗_V H^n(Q, V ⊗_S Φ). -/
lemma one_tmul_eq_zero_of_tensorPush {Φ : PerfectAlg S ⥤ ModuleCat S} [Algebra S V] [Algebra V A]
    [Algebra S A] [IsScalarTower S V A] [Flat V A]
    (x : H (relFreeAbOfHom φ) (moduleCoeff (Φ ⋙ tensorWith V V)) n)
    (hx : tensorPush (algHom S V A).toLinearMap x = 0) :
    (1 : A) ⊗ₜ[V] x = 0 := by
  -- The maps `A ⊗_V H^n(K, F) → H^n(K, A ⊗_V F)` are bijective for the representable fibre
  -- powers of `φ`, so, as `A` is flat, by Čech descent for the image of `φ`, and then for the
  -- quotient by the five lemma.
  have h_cech (m : ℕ) : AllBijective fun n ↦
      baseChangeMap A A (freeAb (cech (reprMap φ) m)) (Φ ⋙ tensorWith V V) n := by
    obtain ⟨D, z_D, hD⟩ := exists_repr_cech φ m
    exact devissage.isClosedClass.freeAb_of_bijective _ hD (baseChangeMap_bijective_freeAb_reprBy D)
  have h_rel : AllBijective fun n ↦ baseChangeMap A A (relFreeAbOfHom φ) (Φ ⋙ tensorWith V V) n :=
    -- the five lemma for `0 → ℤ[im h_d] → ℤ[h_b] → Q → 0`
    (devissage.isClosedClass.right _ (relFreeAb.shortExact _).2
      (devissage.allBijective_freeAb_range_of_cech _ h_cech)).mp
        (baseChangeMap_bijective_freeAb_reprBy b)
  -- The image of `1 ⊗ x` is the push-forward of `x` along `V ⊗ Φ → A ⊗ Φ ≅ A ⊗ (V ⊗ Φ)`.
  let r (D : PerfectAlg S) := (cancelBaseChange S V V A (Φ.obj D)).symm.toLinearMap
  let ρ : Φ ⋙ tensorWith V A ⟶ Φ ⋙ tensorWith V V ⋙ tensorWith V A :=
    { app D := ↟(r D)
      naturality := by
        delta tensorWith
        aesop }
  have h_factor (D : PerfectAlg S) :
      mk V A (V ⊗[S] Φ.obj D) 1 = r D ∘ₗ rTensor _ _ (Algebra.linearMap V A) := by
    ext
    simp [r]
  -- On coefficients, `y ↦ 1 ⊗ y` is the map induced by `V → A`, followed by `ρ`. The coefficients
  -- over `S` and over `V` are the same abelian groups but not the same module functors, so this
  -- equation of coefficient maps is proved inside the `congr` term.
  have h_push : baseChangeMap A A _ (Φ ⋙ tensorWith V V) n (1 ⊗ₜ x) =
      push _ (coeffMap ρ) n (tensorPush (algHom S V A).toLinearMap x) :=
    congr(x.push _ $(by
      ext D ⟨y⟩
      congrm ⟨$(h_factor D) y⟩) n).trans (push_comp ..)
  rw [hx] at h_push
  exact (map_eq_zero_iff _ (h_rel n).injective).mp (h_push.trans (map_zero _))

instance (priority := low) [Algebra V S] : Algebra V a.obj := .compHom _ (algebraMap V S)

instance [Algebra V S] : IsScalarTower V S a.obj := .of_compHom ..

/-- The functor sending a perfect S-algebra D to D ⊗ N ⊗ 𝔪, tensor products over O^♭ with 𝔪 its
maximal ideal, regarded as an S-module. -/
def perfectAlmostCoeff : PerfectAlg S ⥤ ModuleCat S where
  obj D := ModuleCat.of S (D.1 ⊗[OFlat] (N ⊗[OFlat] MaxIdealFlat))
  map f := ↟(rTensor OFlat (N ⊗[OFlat] MaxIdealFlat) f.1.1.toLinearMap)

variable {N} {z : H (relFreeAbOfHom φ) (moduleCoeff (perfectAlmostCoeff N ⋙ tensorWith S a.obj)) n}

/-! ### Reduction to valuation rings -/

/-- Let z be a class in H^n(Q, D ↦ a ⊗_S D ⊗ N ⊗ 𝔪), Q = `New.Variety.relFreeAbOfHom φ`, and c a
non-empty chain of relations on a, each t in c of the form f, g ↦ ψ_t(f) ∣ ψ_t(g) for a map
ψ_t: a → B_t of perfect S-algebras whose push-forward keeps z nonzero. Then some map χ: a → L of
perfect S-algebras keeps z nonzero, and every relation in c implies χ(f) ∣ χ(g). -/
private lemma exists_tensorPush_ne_zero_of_isChain {c : Set (a.obj → a.obj → Prop)}
    (hc_chain : IsChain (· ≤ ·) c) (hc_nonempty : c.Nonempty) {B : c → PerfectAlg S}
    {ψ : ∀ t : c, a.obj →ₐ[S] (B t).obj} (h_ne : ∀ t : c, tensorPush (ψ t).toLinearMap z ≠ 0)
    (h_eq : ∀ t : c, (t : a.obj → a.obj → Prop) = fun f g : a.obj ↦ ψ t f ∣ ψ t g) :
    ∃ (L : PerfectAlg S) (χ : a.obj →ₐ[S] L.obj),
      tensorPush χ.toLinearMap z ≠ 0 ∧ ∀ s ∈ c, s ≤ fun f g : a.obj ↦ χ f ∣ χ g := by
  classical
  -- `L` is the localisation of `∏ B t` at the families that are eventually one.
  let M : Submonoid (∀ t, (B t).obj) :=
    { carrier := {y | ∀ᶠ t in atTop, y t = 1}
      mul_mem' hx hy := hx.mp (hy.mono (by simp +contextual))
      one_mem' := by simp }
  have h_frob : Bijective fun y : ∀ t, (B t).obj ↦ y ^ p :=
    Bijective.piMap fun t ↦ (B t).property.bijective_frobenius
  -- It is perfect, as the `p`-th root of an element of `M` is again eventually one.
  have h_perf : PerfectRing (Localization M) p := by
    have h_reduced : IsReduced (∀ t, (B t).obj) := isReduced_of_perfectRing ⟨h_frob⟩
    refine perfectRing_of_pow_surjective natCast_eq_zero_of_algebra_oFlat fun x ↦ x.ind ?_
    rintro ⟨y, s, hs⟩
    obtain ⟨y, rfl⟩ : ∃ r : ∀ t, (B t).obj, r ^ p = y := h_frob.surjective y
    obtain ⟨s, rfl⟩ : ∃ r : ∀ t, (B t).obj, r ^ p = s := h_frob.surjective s
    have hs_mem : s ∈ M := hs.mono fun t ↦ (powMulEquiv (B t).obj p).map_eq_one_iff.mp
    exact ⟨.mk y ⟨s, hs_mem⟩, mk_pow ..⟩
  let Ψ : a.obj →ₐ[S] ∀ t, (B t).obj := .pi ψ
  refine ⟨⟨.of S (Localization M), h_perf⟩, (algHom S _ (Localization M)).comp Ψ,
    fun h_zero ↦ ?_, fun s hs f g hfg ↦ ?_⟩
  · -- If `z` died, then by flat base change some `s ∈ M` would kill its image over the product;
    -- project to a factor where `s t = 1`.
    obtain ⟨s, hs : tensorPush (mulLeft S s.val) (tensorPush Ψ.toLinearMap z) = 0⟩ :=
      (IsLocalizedModule.eq_zero_iff M (TensorProduct.mk (∀ t, (B t).obj) (Localization M) _ 1)).mp
        (one_tmul_eq_zero_of_tensorPush φ (tensorPush Ψ.toLinearMap z)
          (tensorPush_comp.symm.trans h_zero))
    have h_neBot : (atTop : Filter c).NeBot :=
      atTop_neBot_iff.mpr ⟨hc_nonempty.to_subtype, hc_chain.directedOn.isDirectedOrder⟩
    obtain ⟨t, ht : s.val t = 1⟩ := h_neBot.nonempty_of_mem s.property
    have h_factor : (ψ t).toLinearMap = proj t ∘ₗ mulLeft S s.val ∘ₗ Ψ.toLinearMap := by
      ext x
      simp [Ψ, ht]
    apply h_ne t
    rw [h_factor, tensorPush_comp, tensorPush_comp, hs, map_zero]
  · -- As `ψ t f ∣ ψ t g` for `t ≥ s`, the indicator `e` of the `t` where this holds lies in `M`.
    have h_large (t : c) (ht : s ≤ t) : ψ t f ∣ ψ t g := by
      rw [h_eq t] at ht
      exact ht f g hfg
    let e : ∀ t, (B t).obj := fun t ↦ if ψ t f ∣ ψ t g then 1 else 0
    have he : e ∈ M := (eventually_ge_atTop ⟨s, hs⟩).mono fun t ht ↦ ite_eq_left (h_large t ht)
    have h_dvd : Ψ f ∣ e * Ψ g := pi_dvd_iff.mpr fun t ↦ by simp [Ψ, e, apply_ite (ψ t f ∣ ·)]
    exact (monoidOf M).map_dvd_map.mpr ⟨e, he, h_dvd⟩

/-- Let φ: b → d be a map of perfect S-algebras, a a perfect S-algebra, N an O^♭-module,
Q = ℤ[h_b]/ℤ[im h_d] (`New.Variety.relFreeAbOfHom φ`) and z ≠ 0 a class in H^n(Q, D ↦ a ⊗_S
D ⊗ N ⊗ 𝔪). Consider the relations f, g ↦ ψ(f) ∣ ψ(g) on a, for the maps ψ: a → B of S-algebras, B
perfect, whose push-forward (`New.Variety.tensorPush`) keeps z nonzero. Among them there is a
maximal one m, for the order of implication between relations. -/
lemma exists_maximal_tensorPush_ne_zero (hz : z ≠ 0) :
    ∃ m : a.obj → a.obj → Prop,
      Maximal
        (fun s : a.obj → a.obj → Prop ↦
          ∃ (B : PerfectAlg S) (ψ : a.obj →ₐ[S] B.obj),
            tensorPush ψ.toLinearMap z ≠ 0 ∧ s = fun x y : a.obj ↦ ψ x ∣ ψ y)
        m := by
  -- Zorn's lemma for the relations `ψ f ∣ ψ g` on `a`, over all `ψ` along which `z` survives.
  let good : Set (a.obj → a.obj → Prop) := {s | ∃ (B : PerfectAlg S) (ψ : a.obj →ₐ[S] B.obj),
    tensorPush ψ.toLinearMap z ≠ 0 ∧ s = fun f g ↦ ψ f ∣ ψ g}
  have h_chain (c : Set (a.obj → a.obj → Prop)) (hc : c ⊆ good) (hc_chain : IsChain (· ≤ ·) c)
      (s₀ : a.obj → a.obj → Prop) (hs₀ : s₀ ∈ c) : ∃ ub ∈ good, ∀ s ∈ c, s ≤ ub := by
    choose B ψ h_ne h_eq using fun t : c ↦ hc t.property
    obtain ⟨L, χ, hχ_ne, hχ_ub⟩ :=
      exists_tensorPush_ne_zero_of_isChain φ hc_chain ⟨s₀, hs₀⟩ h_ne h_eq
    exact ⟨fun f g ↦ χ f ∣ χ g, ⟨L, χ, hχ_ne, rfl⟩, hχ_ub⟩
  -- The identity of `a` gives a first member of `good`.
  have h_id : tensorPush (AlgHom.id S a.obj).toLinearMap z = z := by
    rw [tensorPush_apply, AlgHom.toLinearMap_id, tensorCoeffMap_id, coeffMap_id]
    exact z.comp_mk₀_id
  obtain ⟨m, -, h_max⟩ :=
    zorn_le_nonempty₀ good h_chain _ ⟨a, AlgHom.id S a.obj, h_id.trans_ne hz, rfl⟩
  exact ⟨m, h_max⟩

/-- Let S be an O^♭-algebra, and ψ: a → d, k: d → b be maps of perfect S-algebras with k ≠ 0,
such that for any two elements of a one of their images under ψ divides the other, and likewise
for k on d. Then kψ factors, by S-linear maps α: a → V and β: V → b, through a perfect S-algebra
V that is a valuation domain. -/
lemma exists_perfect_valuationRing_factor {ψ : a.obj →ₐ[S] d.obj} {k : d.obj →ₐ[S] b.obj}
    (hk : k.toLinearMap ≠ 0) (hψ_total : ∀ x y : a.obj, ψ x ∣ ψ y ∨ ψ y ∣ ψ x)
    (hk_total : ∀ x y : d.obj, k x ∣ k y ∨ k y ∣ k x) :
    ∃ (V : PerfectAlg S) (α : a.obj →ₗ[S] V.obj) (β : V.obj →ₗ[S] b.obj),
      (k.comp ψ).toLinearMap = β ∘ₗ α ∧ ∃ _ : IsDomain V.obj, ValuationRing V.obj := by
  -- `d ⧸ ker k` is a perfect domain. Inside it, `V` is the saturation of the image of `a`: the
  -- `y` with `v * y` in the image for some `v ≠ 0` in the image.
  have hb_reduced : IsReduced b.obj := isReduced_of_perfectRing b.property
  have h_prime : (ker k).IsPrime := by
    refine ⟨fun h_top ↦ hk (LinearMap.ext fun x ↦ (eq_top_iff.mp h_top trivial : x ∈ ker k)),
      fun {x y} hxy ↦ ?_⟩
    -- If `k (x * y) = 0` and `k y ∣ k x`, then `k x ^ 2 = 0`; and symmetrically.
    have h_mul : k x * k y = 0 := by simpa using hxy
    rcases hk_total y x with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact .inl (IsReduced.eq_zero (k x) ⟨2, by grind⟩)
    · exact .inr (IsReduced.eq_zero (k y) ⟨2, by grind⟩)
  have h_perf : PerfectRing (d.obj ⧸ ker k) p := by
    refine perfectRing_of_pow_surjective natCast_eq_zero_of_algebra_oFlat fun y ↦ ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, rfl⟩ := d.property.bijective_frobenius.surjective y
    exact ⟨mkₐ S _ x, rfl⟩
  let f : a.obj →ₐ[S] d.obj ⧸ ker k := (mkₐ S (ker k)).comp ψ
  let V : Subalgebra S (d.obj ⧸ ker k) :=
    f.range.saturation (f.range.toSubmonoid ⊓ nonZeroDivisors _) inf_le_left
  -- `V` is perfect: if `v * y ^ p` is in the image, so is `(v * y) ^ p`, say `f x ^ p`; then
  -- `v * y = f x`.
  have hV_perf : PerfectRing V p := by
    refine perfectRing_of_pow_surjective natCast_eq_zero_of_algebra_oFlat fun ⟨y, hy⟩ ↦ ?_
    obtain ⟨y, rfl⟩ := h_perf.bijective_frobenius.surjective y
    obtain ⟨v, ⟨hv_range, hv_nzd⟩, hvy⟩ := hy
    obtain ⟨x, hx : f x = v ^ (p - 1) * (v * y ^ p)⟩ := mul_mem (pow_mem hv_range (p - 1)) hvy
    obtain ⟨x, rfl⟩ : ∃ r : a.obj, r ^ p = x := a.property.bijective_frobenius.surjective x
    have h_pow : f x ^ p = (v * y) ^ p := by
      rw [← map_pow, hx, ← mul_assoc, pow_sub_one_mul out, mul_pow]
    exact ⟨⟨y, v, ⟨hv_range, hv_nzd⟩, x, h_perf.bijective_frobenius.injective h_pow⟩, rfl⟩
  -- Divisibility in the domain passes to `V`: a quotient of two elements of `V` lies in `V`.
  have h_dvd {y z : V} (h_yz : (y : d.obj ⧸ ker k) ∣ z) : y ∣ z := by
    obtain ⟨w, hw⟩ := h_yz
    obtain rfl | hy := eq_or_ne y 0
    · exact ⟨0, Subtype.ext (by simpa using hw)⟩
    obtain ⟨v, ⟨hv_range, hv_nzd⟩, hvy⟩ := y.property
    have h_mem : v * y * w ∈ V := by
      rw [mul_assoc, ← hw]
      exact mul_mem (f.range.le_saturation hv_range) z.property
    have hw_mem : w ∈ V := f.range.mem_saturation_of_mul_mem_left h_mem
      ⟨hvy, mul_mem hv_nzd (mem_nonZeroDivisors_of_ne_zero (by simpa using hy))⟩
    exact ⟨⟨w, hw_mem⟩, Subtype.ext hw⟩
  -- If `f u = v' * v * y` and `f u' = v * v' * z` with `v' * v` a nonzerodivisor, then `ψ u ∣ ψ u'`
  -- gives `f u ∣ f u'` in `d ⧸ ker k`, hence `y ∣ z` after cancelling `v' * v`.
  have h_dvd_of_image {y z v v' : d.obj ⧸ ker k} {u u' : a.obj}
      (h_nzd : v' * v ∈ nonZeroDivisors _) (hu : f u = v' * (v * y)) (hu' : f u' = v * (v' * z))
      (huu' : ψ u ∣ ψ u') : y ∣ z := by
    have h_image : f u ∣ f u' := map_dvd (mkₐ S (ker k)) huu'
    rwa [hu, hu', ← mul_assoc, ← mul_assoc, mul_comm v v',
      dvd_cancel_left_mem_nonZeroDivisors h_nzd] at h_image
  -- Given `y, z ∈ V`, the multiples `v' * v * y` and `v * v' * z` are images of `u`, `u'` in `a`,
  -- and one of `ψ u`, `ψ u'` divides the other.
  have hV_total : Std.Total fun y z : V ↦ y ∣ z := by
    refine ⟨fun ⟨y, v, ⟨hv, hv_nzd⟩, hy⟩ ⟨z, v', ⟨hv', hv'_nzd⟩, hz⟩ ↦ ?_⟩
    obtain ⟨u, hu⟩ := mul_mem hv' hy
    obtain ⟨u', hu'⟩ := mul_mem hv hz
    exact (hψ_total u u').imp
      (fun huu' ↦ h_dvd (h_dvd_of_image (mul_mem hv'_nzd hv_nzd) hu hu' huu'))
      fun huu' ↦ h_dvd (h_dvd_of_image (mul_mem hv_nzd hv'_nzd) hu' hu huu')
  -- `α` is `f` with values in `V`, and `β` is `k` on `V`; `k ∘ ψ = β ∘ α` by definition.
  let α : a.obj →ₐ[S] V := f.codRestrict V fun x ↦ f.range.le_saturation ⟨x, rfl⟩
  let β : V →ₐ[S] b.obj := (kerLiftAlg k).comp V.val
  exact ⟨⟨.of S V, hV_perf⟩, α.toLinearMap, β.toLinearMap, rfl, inferInstance,
    iff_dvd_total.mpr hV_total⟩

/-- Let φ: b → d be a map of perfect S-algebras, a a perfect S-algebra, and let p^♭ kill the
O^♭-module N. Let I be an ideal of a such that the image of p^♭ in a divides every element of I,
or is radical in a. Then a nonzero class z in H^n(ℤ[h_b]/ℤ[im h_d], D ↦ a ⊗ D ⊗ N ⊗ 𝔪) stays
nonzero when pushed along a → a/I. Here h_b = Hom(b, –) and im h_d is the set of maps that
factor through φ. -/
lemma tensorPush_quotient_ne_zero (hN : ∀ x : N, pFlat • x = 0) (hz : z ≠ 0) (I : Ideal a.obj)
    (hI : (∀ y ∈ I, algebraMap OFlat a.obj pFlat ∣ y) ∨ IsRadical (algebraMap OFlat a.obj pFlat)) :
    tensorPush (mkₐ S I).toLinearMap z ≠ 0 := by
  -- It is enough that `I ⊗ D ⊗ N ⊗ 𝔪 → a ⊗ D ⊗ N ⊗ 𝔪` is zero: then the coefficients for `a` and
  -- for `a ⧸ I` are isomorphic.
  have h_zero (D : PerfectAlg S) :
      (I.restrictScalars S).subtype.rTensor (D.obj ⊗[OFlat] (N ⊗[OFlat] MaxIdealFlat)) = 0 := by
    ext y w x m
    -- Write `m = s • c` with `pFlat ∣ s ^ j`; then `pFlat` divides `s * y` in both cases of `hI`.
    obtain ⟨s, c, rfl, j, hj : pFlat ∣ s ^ j⟩ := m.exists_smul_eq pFlat_ne_zero
    obtain ⟨y', hy'⟩ : algebraMap OFlat a.obj pFlat ∣ algebraMap OFlat a.obj s * y := by
      rcases hI with h_dvd | h_rad
      · exact (h_dvd y y.property).mul_left _
      · refine (h_rad j _ ?_).mul_right _
        simpa only [map_pow] using map_dvd (algebraMap OFlat a.obj) hj
    -- Move `s` from `m` to `y`, and `pFlat` back to `x`, which it kills by `hN`.
    calc (y : a.obj) ⊗ₜ[S] (w ⊗ₜ[OFlat] (x ⊗ₜ[OFlat] (s • c)))
      _ = (algebraMap OFlat a.obj s * y) ⊗ₜ[S] (w ⊗ₜ[OFlat] (x ⊗ₜ[OFlat] c)) := by
        rw [tmul_smul, tmul_smul, ← smul_tmul, Algebra.smul_def]
      _ = y' ⊗ₜ[S] (w ⊗ₜ[OFlat] ((pFlat • x) ⊗ₜ[OFlat] c)) := by
        rw [hy', ← Algebra.smul_def, smul_tmul, ← tmul_smul, smul_tmul']
      _ = 0 := by simp [hN]
  have h_bij (D : PerfectAlg S) :
      Bijective ((I.restrictScalars S).mkQ.rTensor (D.obj ⊗[OFlat] (N ⊗[OFlat] MaxIdealFlat))) :=
    ⟨ker_eq_bot.mp (by rw [rTensor_mkQ, h_zero, range_zero]),
      rTensor_surjective _ (Submodule.mkQ_surjective _)⟩
  refine (map_ne_zero_iff _ (Bijective.injective ?_)).mpr hz
  exact push_bijective_of_isIso
    (isoOfAppBijective _ fun D ↦ map_bijective.mpr (h_bij D)).isIso_hom n

/-- Let S be a perfect O^♭-algebra, i: S → d and k: d → a maps of perfect S-algebras, ρ: V → a a
faithfully flat map of S-algebras, and N an O^♭-module. Then every class x in
H^n(ℤ[h_S]/ℤ[im h_d], D ↦ V ⊗_S D ⊗ N ⊗ 𝔪) is zero; here h_S = Hom(S, –) and im h_d is the set
of maps that factor through i. -/
lemma faithfullyFlat_descent [hS : PerfectRing S p] [Algebra S V] (ρ : V →ₐ[S] a.obj)
    (h_flat : ρ.FaithfullyFlat) (i : { obj := CommAlgCat.of S S, property := hS } ⟶ d) (k : d ⟶ a)
    (x : H (relFreeAbOfHom i) (moduleCoeff (perfectAlmostCoeff N ⋙ tensorWith V V)) n) :
    x = 0 := by
  -- By faithful flatness and flat base change it is enough that `x` dies with coefficients in `a`.
  -- That map of coefficients factors through `η D : D ⟶ a ⊗ D`, and `η` induces zero on the
  -- relative object, because every `a ⊗ D` receives a map from `d`.
  algebraize [ρ.toRingHom]
  refine (h_flat.one_tmul_eq_zero_iff ..).mp (one_tmul_eq_zero_of_tensorPush i x ?_)
  let E : PerfectAlg S ⥤ PerfectAlg S :=
    lift _ (ι _ ⋙ tensorLeft a.obj) (perfectRing_tensor natCast_eq_zero_of_algebra_oFlat a)
  let η : 𝟭 _ ⟶ E := { app _ := ⟨ofHom TensorProduct.includeRight⟩ }
  -- A push-forward along `whiskerRight η F ≫ β` is a pull-back along `whiskerRight η K`, so it
  -- vanishes when that map is zero.
  have h_push {K F G : AbFunctor (PerfectAlg S)} {y : H K F n} {γ : F ⟶ G} (β : E ⋙ F ⟶ G)
      (hK : whiskerRight η K = 0) (hγ : γ = whiskerRight η F ≫ β) : push K γ n y = 0 := by
    rw [hγ, ← pull_id_eq_push, pull_whiskerRight]
    simp [pull, H.map, hK]
  -- After `η`, every point `S ⟶ D` becomes the point `S ⟶ d ⟶ a ⟶ a ⊗ D`, which factors
  -- through `i`: two maps of `S`-algebras out of `S` agree.
  have h_rel : whiskerRight η (relFreeAbOfHom i) = 0 := by
    refine relFreeAb.hom_ext fun D g ↦
      relFreeAb.mk_eq_zero ⟨⟨k ≫ ⟨ofHom TensorProduct.includeLeft⟩⟩, ?_⟩
    refine ULift.down_injective (ObjectProperty.hom_ext _ ?_)
    ext
  -- The multiplication map `V ⊗ (a ⊗ D) ⊗ N ⊗ 𝔪 → a ⊗ D ⊗ N ⊗ 𝔪`, natural in `D`.
  let r (D : PerfectAlg S) :=
    liftBaseChange V (assoc OFlat S S a.obj D.obj (N ⊗[OFlat] MaxIdealFlat)).toLinearMap
  let β : E ⋙ perfectAlmostCoeff N ⋙ tensorWith V V ⟶ perfectAlmostCoeff N ⋙ tensorWith V a.obj :=
    { app D := ↟(r D)
      naturality D D' _ := by
        refine ModuleCat.hom_ext ?_
        show r D' ∘ₗ _ = _ ∘ₗ r D
        ext
        rfl }
  have h_factor (D : PerfectAlg S) : rTensor S _ (Algebra.linearMap V a.obj) =
      r D ∘ₗ lTensor V V (rTensor OFlat _ (TensorProduct.mk S a.obj D.obj 1)) := by
    ext
    simp [r]
  refine h_push (coeffMap β) h_rel ?_
  ext D ⟨y⟩
  exact congrArg _ (LinearMap.congr_fun (h_factor D) y)

/-- For a map φ: b → d of perfect S-algebras, the ring d regarded as a perfect b-algebra through
φ. -/
def perfectAlgAlong {b d : PerfectAlg S} (φ : b ⟶ d) : PerfectAlg b.obj :=
  letI : Algebra b.obj d.obj := φ.hom.hom.toRingHom.toAlgebra
  ⟨CommAlgCat.of b.obj d.obj, d.property⟩

/-- Let S be a perfect O^♭-algebra, φ: b → d a map of perfect S-algebras, a a perfect
S-algebra, and z ≠ 0 a class in H^n(ℤ[h_b]/ℤ[im h_d], D ↦ a ⊗_S D ⊗ N ⊗ 𝔪)
(`New.Variety.relFreeAbOfHom φ`). Suppose that these groups vanish in every degree m < n for every
perfect S-algebra E in place of a. Then z stays nonzero (`New.Variety.tensorPush`) along some map
ψ: a → B of S-algebras, B perfect, such that of any two images under ψ one divides the other. -/
lemma exists_tensorPush_ne_zero_and_dvd_total [PerfectRing S p]
    (h_below : ∀ m < n, ∀ E : PerfectAlg S,
      Subsingleton
        (H (relFreeAbOfHom φ) (moduleCoeff (perfectAlmostCoeff N ⋙ tensorWith S E.obj)) m))
    (hz : z ≠ 0) :
    ∃ (B : PerfectAlg S) (ψ : a.obj →ₐ[S] B.obj),
      tensorPush ψ.toLinearMap z ≠ 0 ∧ ∀ f g : a.obj, ψ f ∣ ψ g ∨ ψ g ∣ ψ f := by
  -- Take `ψ` with a maximal divisibility relation. The class survives on one of the two charts
  -- on which `ψ g ∣ ψ f`, resp. `ψ f ∣ ψ g`, so by maximality that relation holds in `B`.
  obtain ⟨_, ⟨B, ψ, hψ, rfl⟩, h_maximal⟩ := exists_maximal_tensorPush_ne_zero φ hz
  have h_max {E : PerfectAlg S} (i : B.obj →ₐ[S] E.obj) {f g : a.obj}
      (hi : tensorPush (i.comp ψ).toLinearMap z ≠ 0) : i (ψ f) ∣ i (ψ g) → ψ f ∣ ψ g :=
    h_maximal ⟨E, i.comp ψ, hi, rfl⟩ (fun _ _ ↦ map_dvd i) f g
  refine ⟨B, ψ, hψ, fun f g ↦ ?_⟩
  -- The perfected charts `i₁ : B → B₁`, `i₂ : B → B₂` of the blow-up of `(ψ f, ψ g)`: the sequence
  -- `B → B₁ × B₂ → B₀ → 0` is exact, and injective on the left after tensoring with any `D`.
  obtain ⟨B₁, B₂, B₀, i₁, i₂, j, h₁ : i₁ (ψ g) ∣ i₁ (ψ f), h₂ : i₂ (ψ f) ∣ i₂ (ψ g), h_surj,
    h_exact, h_inj⟩ := exists_perfect_blowup_charts natCast_eq_zero_of_algebra_oFlat B (ψ f) (ψ g)
  let k : B.obj →ₗ[S] B₁.obj × B₂.obj := i₁.toLinearMap.prod i₂.toLinearMap
  -- `k` stays injective on the coefficients `D ⊗ N ⊗ 𝔪`. Tensoring with `D` and the flat module
  -- `𝔪` gives a short exact sequence whose last term `𝔪 ⊗ B₀ ⊗ D` is torsion-free, so flat, as
  -- `B₀ ⊗ D` is reduced; so it stays exact on the left after tensoring with `N`.
  have h_coeff (D : PerfectAlg S) : Function.Injective (k.rTensor (perfectAlmostCoeff N D)) := by
    have hB₀D_reduced : IsReduced (B₀.obj ⊗[S] D.obj) :=
      isReduced_of_perfectRing (perfectRing_tensor natCast_eq_zero_of_algebra_oFlat B₀ D)
    have h_flat : Module.Flat OFlat (MaxIdealFlat ⊗[OFlat] (B₀.obj ⊗[S] D.obj)) :=
      flat_iff_torsion_eq_bot_of_isBezout.2 (Submodule.isTorsionFree_iff_torsion_eq_bot.1
        MaxIdealTensor.isTorsionFree_of_isReduced)
    let kD : B.obj ⊗[S] D.obj →ₗ[OFlat] (B₁.obj × B₂.obj) ⊗[S] D.obj :=
      (k.rTensor D.obj).restrictScalars OFlat
    let jD : (B₁.obj × B₂.obj) ⊗[S] D.obj →ₗ[OFlat] B₀.obj ⊗[S] D.obj :=
      (j.rTensor D.obj).restrictScalars OFlat
    -- `0 → 𝔪 ⊗ (B ⊗ D) → 𝔪 ⊗ ((B₁ × B₂) ⊗ D) → 𝔪 ⊗ (B₀ ⊗ D) → 0` is exact, with a flat last term.
    have h_surj_D : Function.Surjective (jD.lTensor MaxIdealFlat) :=
      lTensor_surjective MaxIdealFlat (rTensor_surjective _ h_surj)
    have h_inj_D : Function.Injective (kD.lTensor MaxIdealFlat) :=
      lTensor_preserves_injective_linearMap kD (h_inj D)
    have h_exact_D : Exact (kD.lTensor MaxIdealFlat) (jD.lTensor MaxIdealFlat) :=
      lTensor_exact _ (rTensor_exact (f := k) D.obj h_exact h_surj :)
    have h_ten_N : Function.Injective ((kD.lTensor MaxIdealFlat).lTensor N) :=
      lTensor_injective_of_exact_of_flat _ h_surj_D _ h_inj_D h_exact_D N
    have h_ten : Function.Injective (kD.rTensor (N ⊗[OFlat] MaxIdealFlat)) := by
      simpa [lTensor_tensor, ← lTensor_inj_iff_rTensor_inj] using h_ten_N
    change Function.Injective (k.rTensor (D.obj ⊗[OFlat] (N ⊗[OFlat] MaxIdealFlat)))
    rw [rTensor_tensor]
    exact (assoc ..).injective.comp (h_ten.comp (assoc ..).symm.injective)
  -- If the class died on both charts, it would die in `B₁ × B₂`, hence in `B` by
  -- `eq_of_tensorPush_eq`.
  have h_chart :
      tensorPush (i₂.comp ψ).toLinearMap z ≠ 0 ∨ tensorPush (i₁.comp ψ).toLinearMap z ≠ 0 := by
    refine not_and_or.mp fun ⟨h₂_zero, h₁_zero⟩ ↦
      hψ (eq_of_tensorPush_eq (f := k) h_exact h_surj h_coeff (fun m hm ↦ h_below m hm B₀) ?_)
    have hk : k ∘ₗ ψ.toLinearMap = inl S B₁.obj B₂.obj ∘ₗ (i₁.comp ψ).toLinearMap +
        inr S B₁.obj B₂.obj ∘ₗ (i₂.comp ψ).toLinearMap := by ext <;> simp [k]
    rw [← tensorPush_comp, hk]
    simp [h₁_zero, h₂_zero, -comp_toLinearMap]
  exact h_chart.imp (fun h ↦ h_max i₂ h h₂) fun h ↦ h_max i₁ h h₁

/-- Let y: b → b' be a map of perfect O^♭-algebras, regarded also as a map of perfect b-algebras (b'
a b-algebra through y; `structureMap` is the map from b, seen as a b-algebra over itself, to b').
Suppose that for every n and every perfect b-algebra E the relative cohomology H^n(ℤ[h_b]/ℤ[im
h_{b'}], D ↦ E ⊗_b D ⊗ N ⊗ 𝔪) of this map of b-algebras vanishes. Then h_{b'} → h_b is a cover
(`New.Variety.IsCover`) for the coefficients D ↦ D ⊗ N ⊗ 𝔪 on perfect O^♭-algebras. -/
private lemma isCover_reprMap_of_forall_subsingleton {b b' : PerfectAlg OFlat} (y : b ⟶ b')
    (h_van : ∀ (n : ℕ) (E : PerfectAlg b.obj),
      Subsingleton
        (H (relFreeAbOfHom (⟨structureMap⟩ : perfectAlgAlong (𝟙 b) ⟶ perfectAlgAlong y))
          (moduleCoeff (perfectAlmostCoeff N ⋙ tensorWith b.obj E.obj)) n)) :
    IsCover (ι _ ⋙ moduleCoeff (almostCoeff N)) (reprMap y) := by
  -- Universal points carry the statement from `OFlat`-algebras to `b`-algebras, where it is the
  -- vanishing of the relative cohomology for `E = b`. `R` restricts scalars from `b` to `OFlat`,
  -- and `u w` is the identity of `A`, seen as a `b`-algebra through `w`.
  let R : PerfectAlg b.obj ⥤ PerfectAlg OFlat := lift _ (ι _ ⋙ restrictAlg ..) fun A ↦ A.property
  let u {A : PerfectAlg OFlat} (w : b ⟶ A) : A ⟶ R.obj (perfectAlgAlong w) :=
    ⟨ofHom ⟨.id _, fun s ↦ (w.hom.hom.commutes s).symm⟩⟩
  -- Over a point `w : b ⟶ A` the universal point is `A` with the `b`-algebra structure `w`.
  have h_univ : HasUniversalPoints (F := ι _ ⋙ moduleCoeff (almostCoeff N))
      ⟨R, tensorWith.mk b.obj (1 : b.obj) (perfectAlmostCoeff N)⟩
      (pointMap (Y := R ⋙ reprBy b) ⟨u (𝟙 b)⟩) := by
    intro A w
    refine ⟨perfectAlgAlong w.down, ⟨⟨structureMap⟩⟩, u w.down, rfl, fun B x f hf ↦ ?_, ?_⟩
    · -- `f` is a map of `b`-algebras, and the only one over `f`
      have hf_comm (s : b.obj) : f.hom.hom (w.down.hom.hom s) = algebraMap b.obj B.obj s :=
        (congrArg (fun v ↦ v.down.hom.hom s) hf).symm.trans (x.down.hom.hom.commutes s)
      refine ⟨⟨ofHom ⟨f.hom.hom.toRingHom, hf_comm⟩⟩, ⟨?_, rfl⟩, ?_⟩
      · -- two maps of `b`-algebras out of `b` agree
        refine ULift.down_injective (ObjectProperty.hom_ext _ ?_)
        ext
      · rintro g' ⟨-, rfl⟩
        rfl
    · -- `x ↦ 1 ⊗ x` is bijective onto `b ⊗[b] –`
      let e_lid := TensorProduct.lid b.obj (perfectAlmostCoeff N (perfectAlgAlong w.down))
      exact map_bijective.mpr (e_lid.symm.bijective.comp (map_bijective bijective_id bijective_id))
  refine (h_univ.isCohomEquiv_incl_iff _ ?_).mpr
    ((relFreeAb.isCohomEquiv_iff_subsingleton_rel _).mpr fun n ↦ h_van n (perfectAlgAlong (𝟙 b)))
  -- a point of a `b`-algebra factors through `⟨structureMap⟩` if and only if it factors through `y`
  ext B g
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨⟨u y ≫ R.map w.down⟩, rfl⟩
  · -- `w` is a map of `b`-algebras, by `hw`
    rintro ⟨w, hw⟩
    have hw_comm (s : b.obj) : w.down.hom.hom (y.hom.hom s) = algebraMap b.obj B.obj s :=
      (congrArg (fun v ↦ v.down.hom.hom s) hw).trans (g.down.hom.hom.commutes s)
    -- two maps of `b`-algebras out of `b` agree
    refine ⟨⟨⟨ofHom ⟨w.down.hom.hom.toRingHom, hw_comm⟩⟩⟩,
      ULift.down_injective (ObjectProperty.hom_ext _ ?_)⟩
    ext

/-- Let p^♭ kill N and let y : b → b' be a map of perfect O^♭-algebras such that every
map from b to the tilt of a test (`New.Variety.PadicTest`) factors through y. Then h_{b'} → h_b is a
cover (`New.Variety.IsCover`) for the coefficients D ↦ D ⊗ N ⊗ 𝔪; here h_b = Hom(b, –) on perfect
O^♭-algebras, and ι includes them into all O^♭-algebras. This is v-descent for these
coefficients. -/
lemma isCover_of_points (hN : ∀ x : N, pFlat • x = 0) {b b' : PerfectAlg OFlat} (y : b ⟶ b')
    (hy : IsPointwiseSurjective (PadicTest.perfectTilt.whiskerLeft (reprMap y))) :
    IsCover (ι _ ⋙ moduleCoeff (almostCoeff N)) (reprMap y) := by
  -- Work over `b` and suppose `z ≠ 0` is a relative class of least degree. Push it to a valuation
  -- ring `V`, then to a quotient of `V` over which the tilt of a test is faithfully flat. That
  -- point of `b` lifts to `b'`, so the class vanishes there by descent.
  refine isCover_reprMap_of_forall_subsingleton y fun n ↦ ?_
  let i : perfectAlgAlong (𝟙 b) ⟶ perfectAlgAlong y := ⟨structureMap⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    refine fun E ↦ subsingleton_of_forall_eq 0 fun z ↦ by_contra fun hz ↦ ?_
    -- Two steps make the images of `E` in `B` and of `B` in `B'` totally ordered by divisibility;
    -- then `E → B'` factors as `β ∘ α` through a perfect valuation ring `V`.
    obtain ⟨B, ψ, hψ, hψ_total⟩ := exists_tensorPush_ne_zero_and_dvd_total i ih hz
    obtain ⟨B', k, hk, hk_total⟩ := exists_tensorPush_ne_zero_and_dvd_total i ih hψ
    obtain ⟨V, α, β, h_fac : (k.comp ψ).toLinearMap = β ∘ₗ α, hV_domain, hV_valuation⟩ :=
      exists_perfect_valuationRing_factor (fun hk_zero ↦ hk (by simp [hk_zero])) hψ_total hk_total
    -- `k ∘ ψ = β ∘ α`, so if `α` killed `z` then so would `k ∘ ψ`.
    have hα : tensorPush α z ≠ 0 := fun hα_zero ↦ hk <| by
      rw [← tensorPush_comp, ← comp_toLinearMap, h_fac, tensorPush_comp, hα_zero, map_zero]
    -- If `p^♭` were radical in `V` (say zero or a unit), the class would survive in the zero ring,
    -- which is absurd.
    have h_rad : ¬IsRadical (algebraMap OFlat V.obj pFlat) := fun h_radical ↦
      tensorPush_quotient_ne_zero i hN hα ⊤ (.inr h_radical)
        (by simp [Subsingleton.eq_zero (toLinearMap _)])
    have h_ne : algebraMap OFlat V.obj pFlat ≠ 0 := fun h_zero ↦
      h_rad (by rw [h_zero, zero_isRadical_iff]; infer_instance)
    -- a test `c` and `φ : V → c.TiltRing`, faithfully flat over `V ⧸ ker φ`, with `ker φ ⊆ p^♭ V`
    obtain ⟨c, φ, hφ_flat, hφ_ker⟩ := exists_faithfullyFlat_padicTest (CommAlgCat.of OFlat V.obj)
      h_ne fun h_unit ↦ h_rad h_unit.squarefree.isRadical
    -- The point `b → V → c.TiltRing` lifts to `g : b' → c.TiltRing`. The class survives in
    -- `V ⧸ ker φ`, and it vanishes there by descent along the faithfully flat map
    -- `V ⧸ ker φ → c.TiltRing`, where `c.TiltRing` is a `b`-algebra through `y ≫ g`.
    obtain ⟨⟨g⟩, hg⟩ := hy c ⟨⟨ofHom (φ.comp (algHom ..))⟩⟩
    refine tensorPush_quotient_ne_zero i hN hα (ker φ) (.inl hφ_ker) ?_
    -- `φ` on `V ⧸ ker φ`, and `g` on `b'`, as maps of `b`-algebras
    exact faithfullyFlat_descent (a := perfectAlgAlong (y ≫ g))
      ⟨φ.kerLift, fun s ↦ congr($(hg.symm).down.hom s)⟩ hφ_flat i
      ⟨ofHom ⟨g.hom.hom.toRingHom, fun s ↦ rfl⟩⟩ _

end VDescent

/-!
## Acyclicity of points in tilts

`New.Variety.IsAcyclicAt φ F B` says that the functor Hom(B, φ –) with coefficients F∘φ has
cohomology F(B), in degree 0. `New.Variety.IsAcyclicOnPerfect F` says this for the tilt functor and
every perfect O♭-algebra B.
-/

section AlmostAcyclic

open CategoryTheory ObjectProperty TensorProduct Function Period Comparison freeAb Category
  PadicTest IsCohomEquiv Eqv

variable {C C' D : Type 1} [Category C] [Category C'] [Category D]
  {F : AbFunctor C} {F' : AbFunctor C'} {G : AbFunctor D} {p : ℕ} [ThePrime p]
  {N : Type} [AddCommGroup N] [Module OFlat N]

/-- Let `c` and `c'` compare the coefficients `F` on `C` and `F'` on `C'` with the same coefficients
`G` on `D`, and let `u` and `v` map a functor `Y` on `D` to the points of `B` and of `B'`. A point
`y` of `Y A` gives maps `F B → G A` and `F' B' → G A`; suppose that they agree through a bijection
`γ : F B → F' B'`. If `c` is bijective along `u`, then `c'` is bijective along `v`. -/
lemma Comparison.IsBijective.transfer {Y : D ⥤ Type 1} {B : C} {B' : C'}
    {c : Comparison F G} {c' : Comparison F' G}
    {u : Y ⟶ c.functor ⋙ reprBy B} {v : Y ⟶ c'.functor ⋙ reprBy B'}
    (hc : c.IsBijective (freeAbMap u)) {γ : F.obj B → F'.obj B'} (hγ : Bijective γ)
    (h_compat : ∀ (A : D) (y : Y.obj A) (x : F.obj B),
      c.coeffHom A (F.map (u A y).down x) = c'.coeffHom A (F'.map (v A y).down (γ x))) :
    c'.IsBijective (freeAbMap v) := by
  -- By `isBijective_reprBy_iff` each side says that the higher cohomology of `Y` in `G` vanishes
  -- and that the map `homOfValue` from the value of the functor to the sections is bijective.
  have h_sec : ⇑(c.homOfValue u) = c'.homOfValue v ∘ γ :=
    funext fun x ↦ hom_ext (by simp [homOfValue_app, h_compat])
  rwa [isBijective_reprBy_iff, h_sec, hγ.of_comp_iff, ← isBijective_reprBy_iff] at hc

/-- For every perfect O^♭-algebra b, the functor S ↦ Hom(b, S^♭) on p-adic tests, with coefficients
S ↦ F(S^♭), has cohomology F(b), in degree 0. -/
abbrev IsAcyclicOnPerfect (F : AbFunctor (CommAlg OFlat)) : Prop :=
  ∀ (b : CommAlg OFlat) [PerfectRing b p], IsAcyclicAt tilt F b

/-- Every perfect O^♭-algebra b has a map y: b → b' of perfect O^♭-algebras that is onto on points
in tilts of p-adic tests, such that the points of b' in tilts of tests are acyclic for the
coefficients D ↦ D ⊗ N ⊗ 𝔪. The proof takes b' to be the tilt of one test through which all points
of b factor, or the zero ring if b has no point. -/
private lemma exists_isPointwiseSurjective_and_isAcyclicAt (b : PerfectAlg OFlat) :
    ∃ (b' : PerfectAlg OFlat) (y : b ⟶ b'),
      IsPointwiseSurjective (perfectTilt.whiskerLeft (reprMap y)) ∧
      IsAcyclicAt perfectTilt (ι _ ⋙ moduleCoeff (almostCoeff N)) b' := by
  by_cases! h_point : ∃ c : PadicTest, Nonempty (b ⟶ perfectTilt.obj c)
  · -- b has a point. By `homTiltIso` the points of b in tilts are those of the ring O_C ⊗ W(b) in
    -- tests; all of them factor through one test c (`HasCoveringPoints.exists_surjective_point`);
    -- b' is its tilt.
    obtain ⟨c₀, ⟨f₀⟩⟩ := h_point
    let e := homTiltIso (b := b.obj)
    obtain ⟨c, y, hy⟩ := HasCoveringPoints.exists_surjective_point _ (e.hom.app c₀ ⟨f₀.hom⟩)
    refine ⟨perfectTilt.obj c, ⟨(e.inv.app c y).down⟩, fun d f ↦ ?_, ?_⟩
    · obtain ⟨g, hg⟩ := (e.symm.app d).toEquiv.surjective.comp (hy d) ⟨f.down.hom⟩
      exact ⟨⟨perfectTilt.map g.down⟩, congr(⟨⟨$((e.inv.naturality_apply ..).symm.trans hg).down⟩⟩)⟩
    · -- tilting is fully faithful, so c represents the points of its tilt
      exact isBijective_of_repr _ (pointMap_id_bijective_of_fullyFaithful (lift ..) _)
        (ConcreteCategory.bijective_of_isIso ((moduleCoeff _).map (𝟙 _)))
  · -- b has no point: b' is the zero ring, and both sides of the comparison vanish
    let zero : PerfectAlg OFlat := ⟨.of OFlat Unit, ⟨by simp⟩⟩
    let y : b ⟶ zero := ⟨CommAlgCat.ofHom default⟩
    have h_zero {A : AbFunctor PadicTest} (u v : freeAb.obj (perfectTilt ⋙ reprBy zero) ⟶ A) :
        u = v :=
      hom_ext fun d f ↦ (h_point d).elim (y ≫ f.down)
    refine ⟨zero, y, fun d f ↦ (h_point d).elim f.down, isBijective_reprBy_iff.mpr ⟨?_, ?_⟩⟩
    · -- the map from the value at the zero ring to the sections is bijective
      refine ⟨?_, fun s ↦ ⟨0, h_zero ..⟩⟩
      apply injective_of_subsingleton (α := ULift (Unit ⊗ _))
    · -- the higher cohomology vanishes, as the identity of `freeAb.obj (perfectTilt ⋙ reprBy zero)`
      -- is zero
      intro m
      exact H.subsingleton_of_id_eq_zero (h_zero ..) ..

/-- Almost descent. Let N be an O^♭-module killed by p^♭, and 𝔪 the maximal ideal of O^♭. For b
perfect over O^♭, S ↦ Hom(b, S^♭) on p-adic tests with coefficients S^♭ ⊗ N ⊗ 𝔪 has cohomology
b ⊗ N ⊗ 𝔪, in degree 0. -/
lemma isAcyclicAt_perfectTilt (hN : ∀ x : N, pFlat • x = 0) (b : PerfectAlg OFlat) :
    IsAcyclicAt perfectTilt (ObjectProperty.ι _ ⋙ moduleCoeff (almostCoeff N)) b := by
  -- Every b has a cover b → b' (onto on points in tests) with the claim known for b'
  -- (`exists_isPointwiseSurjective_and_isAcyclicAt`). Čech descent (`bijectiveUpTo_of_cech_pred`)
  -- then gives one more step of `BijectiveUpTo` for b from the fibre powers of b'.
  refine allBijective_iff_forall_bijectiveUpTo.mpr fun r ↦ ?_
  induction r generalizing b with
  | zero => tauto
  | succ r ih =>
    obtain ⟨b', y, hy, hb'⟩ := exists_isPointwiseSurjective_and_isAcyclicAt (N := N) b
    -- v-descent (`isCover_of_points`): a map that is onto on points in tests is a cover for these
    -- coefficients; this is where `hN` is used
    refine bijectiveUpTo_of_cech_pred rfl (isCover_of_points hN y hy) hy.isCover hb' fun m ↦ ?_
    -- the fibre powers are represented by perfect algebras D, to which induction applies
    obtain ⟨D, z, hz⟩ := exists_repr_cech y m
    exact (bijectiveUpTo_congr (comp_id _) (of_bijective hz)
      (of_bijective fun c ↦ hz (perfectTilt.obj c))).mpr (ih D)

/-- Let `N` be an `OFlat`-module killed by `pFlat`. For every perfect `OFlat`-algebra `b`, the
cohomology of the points of `b` in the tilts of tests, with coefficients `almostCoeff N`, is the
value of the coefficients at `b`, placed in degree zero. -/
lemma isAcyclicOnPerfect_almostCoeff (hN : ∀ x : N, pFlat • x = 0) :
    IsAcyclicOnPerfect (moduleCoeff (almostCoeff N)) := by
  -- Maps of perfect algebras from `b` to a tilt are just maps of algebras; the coefficients agree.
  intro b hb
  let e : tilt ⋙ reprBy b ⟶ perfectTilt ⋙ reprBy ⟨b, hb⟩ := { app _ := ↾fun f ↦ ⟨⟨f.down⟩⟩ }
  have he (c : PadicTest) : Bijective (e.app c) := (Equiv.mk _ fun f ↦ ⟨f.down.hom⟩).bijective
  exact ((isAcyclicAt_perfectTilt hN ⟨b, hb⟩).precomp_of_bijective e rfl he).transfer bijective_id
    fun _ _ _ ↦ rfl

end AlmostAcyclic

end New.Variety

end
