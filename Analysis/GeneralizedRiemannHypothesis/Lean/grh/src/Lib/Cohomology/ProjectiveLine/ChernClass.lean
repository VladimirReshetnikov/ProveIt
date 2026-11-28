import Lib.Cohomology.TorsionTheories

/-!
# Tate module, Kummer sequence and the first Chern class of O(1) on the projective line

Let `g` be a functor from `C` to tests over a ring `A`, and let `ℓ` be a prime. The Tate module `𝕋`
of `G_m` along `g` sits in the Kummer sequence. When `A` is local and absolutely integrally closed
and `ℓ` is invertible in `A`, a section `ε` of `𝕋` makes `𝕋` act on every coefficient `M`
(`New.Variety.TorsionCoeff`: killed by `ℓ`, with Zariski descent). On the projective line `ℙ¹`, the
cocycle of `O(1)` and the Kummer class give the first Chern class `η ∈ H²(ℙ¹, 𝕋)`, and the
projective line formula `H(ℙ¹ × S) = H(S) ⊕ η H(S)` is stated as a property of a coefficient.

## Main definitions and results

* `New.Variety.shortExact_kummerSeq`: the Kummer sequence 0 → 𝕋 → Hom(ℚ, G_m) → G_m → 0 is exact.
* `New.Variety.tateGen`, `New.Variety.isCohomEquiv_tensorPoint_tateGen`: a section ε of 𝕋 such that
  S → S ⊗ 𝕋, x ↦ x ⊗ ε, is bijective on Ext(−, F) for S killed by ℓ and F with Zariski descent. Here
  A is local and absolutely integrally closed, and the prime ℓ is invertible in A
  (`New.Variety.InvertsPrime`).
* `New.Variety.TorsionCoeff.tateAction`: the class in Ext⁰(M ⊗ 𝕋, M) inverse to x ↦ x ⊗ ε; it
  commutes with all classes between coefficients (`New.Variety.TorsionCoeff.tateAction_comm`).
* `New.Variety.TorsionCoeff.mulClass`: the product y · ξ of a class y in M with a class ξ in 𝕋,
  natural in M.
* `New.Variety.etaClass`: the class `η ∈ H²(ℙ¹, 𝕋)`, the cocycle class times the Kummer class.
* `New.Variety.TorsionCoeff.etaAt`, `New.Variety.TorsionCoeff.HasLineFormula`: product with `η`;
  `H(ℙ¹ × S) = H(S) ⊕ η H(S)`.

Notions from other files:
* `New.Variety.IsTest`: a test ring A is reduced and absolutely integrally closed, and any a, b ∈ A
  admit an idempotent e with a ∣ eb and b ∣ (1 − e)a.
* `New.Variety.TestOver`: The category of tests over A: the full subcategory of commutative
  A-algebras whose underlying rings are test rings.
* `New.Variety.H`: The group Ext^n(N,F) in the category of functors from C to abelian groups.
* `New.Variety.Cocycle`: A 1-cocycle from F to G: homomorphisms D(f): F(c) → G(d) for f: c → d with
  D(gf) = G(g)D(f) + D(g)F(f). It defines an extension of F by G.

## Relation to the literature

Known; see `Lib.Cohomology.ProjectiveLine.ConstantLineFormula` and
`Lib.PadicComparison.Duality.GoodPairs` for sources.
-/

noncomputable section

/-- For an additive map χ from ℚ and a nonzero natural number n, n times the map x ↦ χ(x / n) is
χ. -/
theorem AddMonoidHom.nsmul_comp_mulRight_inv_natCast {G : Type*} [AddCommGroup G] (χ : ℚ →+ G)
    (n : ℕ) [NeZero n] : n • χ.comp (AddMonoidHom.mulRight (n : ℚ)⁻¹) = χ := by
  ext
  simp [← map_nsmul, mul_left_comm]

namespace New.Variety

/-!
## Kummer sequence, Tate module and its action on torsion coefficients

`New.Variety.TotalH N F` is total Ext(N, F), `New.Variety.TotalH.comp` the Yoneda product in diagram
order, and `New.Variety.abTensor` the pointwise tensor product over ℤ.
-/

section TateModule

open CategoryTheory AddCommGrpCat Polynomial Module TotalH Function TensorProduct NeZero
  AddCommGroup

set_option backward.isDefEq.respectTransparency false

variable {C C' : Type _} [Category C] [Category C'] {ℓ : ℕ} {A : Type} [CommRing A]
  (g : C ⥤ TestOver A)

/-! ### The Kummer sequence and the Tate module -/

/-- The Kummer short complex 𝕋 → Hom(ℚ, G_m) → G_m of functors along g, formed by evaluation at
1 and its kernel 𝕋, the Tate module. -/
abbrev kummerSeq : ShortComplex (AbFunctor C) :=
  -- the kernel sequence of evaluation at 1 on homomorphisms from `ℚ` to the units
  kerComplex
    (M :=
      CategoryTheory.Functor.mk (fun c ↦ of (ℚ →+ (ringOf g ⋙ Gm) c)) fun f ↦
        ofHom (AddMonoidHom.compHom ((ringOf g ⋙ Gm).map f).hom))
    (G := ringOf g ⋙ Gm) {app _ := ofHom (AddMonoidHom.eval 1)}

/-- The Tate module 𝕋 of the multiplicative group along g: its value at c is the group of
homomorphisms χ from ℚ to the units of g(c) with χ(1) = 1. It is the first term `X₁` of the
Kummer complex `New.Variety.kummerSeq`, that is, the kernel of evaluation at 1,
Hom(ℚ, G_m) → G_m. A member χ is a compatible system χ(1/n) of n-th roots of unity for all
n ≥ 1, so all primes are included, not only ℓ. -/
abbrev tateModule : AbFunctor C := (kummerSeq g).X₁

instance : HasFlatValues (tateModule g) where
  flat c := by
    -- Homomorphisms from `ℚ` form a `ℚ`-vector space, so their subgroups are torsion-free.
    let : Module ℚᵐᵒᵖ (ℚ →+ (ringOf g ⋙ Gm) c) := AddMonoidHom.instDomMulActModule
    have : HasUniqueDiv (ℚ →+ (ringOf g ⋙ Gm).obj c) :=
      HasUniqueDiv.of_isTorsionFree ℚᵐᵒᵖ (ℚ →+ (ringOf g ⋙ Gm) c)
    exact inferInstanceAs (Flat ℤ (AddMonoidHom.ker _))

/-- Along a functor g to tests over A, the Kummer sequence 0 → 𝕋 → Hom(ℚ, G_m) → G_m → 0, with
last map evaluation at 1, is short exact. -/
lemma shortExact_kummerSeq : (kummerSeq g).ShortExact := by
  -- Evaluation at 1 is onto: g(c) is absolutely integrally closed, so every unit has a compatible
  -- system of roots.
  refine kerComplex_shortExact fun (c : C) (y : (ringOf g ⋙ Gm).obj c) ↦ ?_
  obtain ⟨χ, hχ⟩ :=
    exists_compatible_roots (h := (g c).property.toIsAbsIntegrallyClosed) (.ofMul y.down)
  let up : Additive ((ringOf g).obj c)ˣ →+ (ringOf g ⋙ Gm).obj c := .mk' ULift.up fun _ _ ↦ rfl
  exact ⟨up.comp χ, congrArg ULift.up hχ⟩

variable [u : InvertsPrime A ℓ]

/-! ### A generator of the Tate module modulo ℓ -/

/-- For a prime ℓ invertible in a local, absolutely integrally closed ring A, there is a
homomorphism χ from ℚ to A^× with χ(1) = 1 such that χ(1/ℓ) is a root of the ℓ-th cyclotomic
polynomial. -/
def compatibleRootsOfUnity :
    {χ : Multiplicative ℚ →* Aˣ //
      χ (Multiplicative.ofAdd 1) = 1 ∧
      (cyclotomic ℓ A).IsRoot (χ (Multiplicative.ofAdd (1 / ℓ)))} :=
  Nonempty.some <| by
    -- Take a root ζ of the cyclotomic polynomial; it is a unit with ζ ^ ℓ = 1. Choose a compatible
    -- system of roots χ of ζ, with χ 1 = ζ, and rescale it to s ↦ χ (ℓ * s).
    obtain ⟨ζ, hζ⟩ : ∃ ζ : A, (cyclotomic ℓ A).IsRoot ζ :=
      IsAbsIntegrallyClosed.exists_root _ (cyclotomic.monic ℓ A)
        (by simp [natDegree_cyclotomic, pos])
    have hζ_pow : ζ ^ ℓ = 1 := isRoot_of_unity_of_root_cyclotomic (by aesop) hζ
    obtain ⟨χ, hχ⟩ :
        ∃ χ : ℚ →+ Additive Aˣ, χ 1 = Additive.ofMul (Units.ofPowEqOne ζ ℓ hζ_pow (ne ℓ)) :=
      exists_compatible_roots _
    exact ⟨(ℓ • χ).toMultiplicativeLeft, by simp [hχ], by simpa [← map_nsmul, hχ] using hζ⟩

lemma compatibleRootsOfUnity_ofAdd_one :
    (compatibleRootsOfUnity (A := A) (ℓ := ℓ)).val (Multiplicative.ofAdd 1) = 1 :=
  compatibleRootsOfUnity.property.left

lemma isRoot_cyclotomic_compatibleRootsOfUnity :
    (cyclotomic ℓ A).IsRoot
      ((compatibleRootsOfUnity (A := A) (ℓ := ℓ)).val (Multiplicative.ofAdd (1 / ℓ))) :=
  compatibleRootsOfUnity.property.right

/-- The section ε of the Tate module `New.Variety.tateModule` along g, as a map from the constant
functor ℤ (the free abelian group on the one-point functor). At c it is the homomorphism
`New.Variety.compatibleRootsOfUnity` χ: ℚ → Aˣ, with χ(1) = 1 and χ(1/ℓ) a root of the ℓ-th
cyclotomic polynomial, followed by the structure map A → g(c). -/
def tateGen : freeAb (onePointFunctor C) ⟶ tateModule g :=
  -- at `c`, the image of `compatibleRootsOfUnity` under the structure map of `g c`, which still
  -- sends 1 to 1
  freeAb.desc
    (fun c _ ↦
      ⟨AddMonoidHom.comp (AddMonoidHom.mk' ULift.up fun _ _ ↦ rfl)
          ((Units.map (algebraMap A (g c).1).1).comp compatibleRootsOfUnity.1).toAdditiveRight,
        Gm.ext.2 ((congrArg (fun x : Aˣ ↦ algebraMap A (g c).1 x)
          compatibleRootsOfUnity_ofAdd_one).trans (map_one _))⟩)
    (by
      intros
      congr
      ext
      exact Gm.ext.2 ((g.map _).1.hom.2 _).symm)

end TateModule

section TateAction

open CategoryTheory AddCommGrpCat Polynomial Module TotalH Function TensorProduct NeZero
  AddCommGroup

set_option backward.isDefEq.respectTransparency false

variable {C C' : Type _} [Category C] [Category C'] {ℓ : ℕ} {A : Type} [CommRing A]
  {g : C ⥤ TestOver A} [u : InvertsPrime A ℓ] {S S' P F : AbFunctor C}

/-- For t in the Tate module at c, the value t(1/ℓ) is an ℓ-th root of unity of the ring g(c):
ℓ • t(1/ℓ) = t(1), which is the unit 1 (written 0, as the group of units is written additively). -/
private lemma tateModule_apply_inv_mem_rootsOfUnity {c : C} (t : tateModule g c) :
    (t.val (1 / ℓ)).down ∈ rootsOfUnity ℓ ((ringOf g).obj c) := by
  have h_pow : ℓ • t.val (1 / ℓ) = 0 := by
    calc ℓ • t.val (1 / ℓ) = (ℓ • t.val.comp (.mulRight (ℓ : ℚ)⁻¹)) 1 := by simp
      _ = t.val 1 := by rw [AddMonoidHom.nsmul_comp_mulRight_inv_natCast]
      _ = 0 := t.property
  exact congrArg ULift.down h_pow

/-- For a ring map ψ from g(c) to K, the additive map t ↦ ψ(t(1/ℓ)) from the Tate module at c to
the ℓ-th roots of unity of K, written additively. -/
private def tateRoot {c : C} {K : Type} [CommRing K] (ψ : (ringOf g).obj c →+* K) :
    tateModule g c →+ Additive (rootsOfUnity ℓ K) :=
  (restrictRootsOfUnity ψ ℓ).toAdditive.comp
    (.mk' (fun t ↦ ⟨(t.val (1 / ℓ)).down, tateModule_apply_inv_mem_rootsOfUnity t⟩) fun _ _ ↦ rfl)

/-- For a ring map ψ from g(c) to a domain K, the image ψ(ε(1/ℓ)) of the section
ε = `New.Variety.tateGen` is a primitive ℓ-th root of unity. -/
private lemma isPrimitiveRoot_tateRoot_tateGen {c : C} {K : Type} [CommRing K] [IsDomain K]
    (ψ : (ringOf g).obj c →+* K) :
    IsPrimitiveRoot (tateRoot ψ (tateGen g c (.of ⟨⟩))).val ℓ := by
  -- ψ(ε(1/ℓ)) is the image of a root of the ℓ-th cyclotomic polynomial, and ℓ ≠ 0 in K
  let φ : A →+* K := ψ.comp (algebraMap A (g c).obj)
  have h_unit : IsUnit (ℓ : K) := by simpa using (InvertsPrime.isUnit_prime (A := A)).map φ
  have h_ne_zero : NeZero (ℓ : K) := ⟨h_unit.ne_zero⟩
  have h_val : ((tateRoot ψ (tateGen g c (.of ⟨⟩))).val : K) =
      φ ((compatibleRootsOfUnity (A := A)).val (.ofAdd (1 / ℓ))) := by
    simp only [tateRoot, tateGen, freeAb.desc_of]
    rfl
  have h_root : (cyclotomic ℓ K).IsRoot ((tateRoot ψ (tateGen g c (.of ⟨⟩))).val : K) := by
    rw [h_val, ← map_cyclotomic ℓ φ]
    exact isRoot_cyclotomic_compatibleRootsOfUnity.map
  exact IsPrimitiveRoot.coe_units_iff.mp (isRoot_cyclotomic_iff.mp h_root)

/-- Let A be local and absolutely integrally closed, with the prime ℓ invertible in A. If ℓ kills
every value of S and F satisfies Zariski descent along g (a subfunctor that contains everything near
each maximal ideal of the rings g(c) is dense for F), then the map S → S ⊗ 𝕋, x ↦ x ⊗ ε, induces
bijections on all Ext^n(−, F). Here 𝕋 is the Tate module and ε = `New.Variety.tateGen`. -/
lemma isCohomEquiv_tensorPoint_tateGen (hS : ∀ (c : C) (x : S c), ℓ • x = 0)
    (hF : HasZariskiDescent (ringOf g) F) :
    IsCohomEquiv F (tensorPoint (tateGen g) S) := by
  -- The map is locally bijective. In the localization at a maximal ideal, a domain, ζ = ε (1 / ℓ)
  -- is a primitive ℓ-th root of unity. So s ⊗ ε = 0 forces s = 0; and every t in the Tate module
  -- is i • ε plus an element t' that is locally divisible by ℓ, so that s ⊗ t' is locally zero.
  let ε {c : C} : tateModule g c := tateGen g c (.of ⟨⟩)
  -- The localization at a maximal ideal is a local domain, absolutely integrally closed.
  have h_local {d : C} (m : Ideal ((ringOf g).obj d)) [m.IsPrime] :
      IsAbsIntegrallyClosedLocal (Localization.AtPrime m) :=
    (IsTest.exists_valuationSubring_atPrime (g d).property m).left
  -- It suffices that kernel and cokernel are locally zero; by Zariski descent this is tested near
  -- each maximal ideal m, along each map f from c.
  have h_prim {c d : C} (f : c ⟶ d) (m : Ideal ((ringOf g).obj d)) [m.IsPrime] :
      IsPrimitiveRoot (tateRoot ((algebraMap _ (Localization.AtPrime m)).comp
        ((ringOf g).map f).hom) (ε (c := c))).val ℓ :=
    isPrimitiveRoot_tateRoot_tateGen _
  refine LocalIso.isCohomEquiv ⟨?_, ?_⟩
  · -- Kernel: the discrete logarithm l to the base ζ turns s ⊗ ε = 0 into l ζ • s = 0.
    rintro c (s : S c) hs
    refine hF fun d f m hm ↦ ?_
    let ψ : (ringOf g).obj c →+* Localization.AtPrime m :=
      (algebraMap _ (Localization.AtPrime m)).comp ((ringOf g).map f.down).hom
    have hζ : IsPrimitiveRoot (tateRoot ψ ε).val ℓ := h_prim f.down m
    have h_zmod : Module (ZMod ℓ) (S c) := zmodModule (hS c)
    let l : Additive (rootsOfUnity ℓ (Localization.AtPrime m)) ≃+ ZMod ℓ :=
      (hζ.zmodEquivZPowers.trans (MulEquiv.toAdditive (MulEquiv.subgroupCongr hζ.zpowers_eq))).symm
    have hl : l (tateRoot ψ ε) ≠ 0 :=
      l.map_ne_zero_iff.mpr fun h ↦ hζ.ne_one Fact.out (congrArg Subtype.val h)
    -- pair s ⊗ t with l (tateRoot ψ t) ∈ ZMod ℓ, which acts on S c
    let pairing : S c →ₗ[ℤ] tateModule g c →ₗ[ℤ] S c :=
      ((l.toAddMonoidHom.comp (tateRoot ψ)).toIntLinearMap.smulRight 1).flip
    have h_tmul : s ⊗ₜ[ℤ] ε = 0 := hs
    have h_smul : l (tateRoot ψ ε) • s = 0 := by
      simpa [pairing] using congrArg (lift pairing) h_tmul
    obtain rfl : s = 0 := (smul_eq_zero_iff_right hl).mp h_smul
    exact ⟨1, m.one_notMem, fun b f' _ ↦ map_zero (S.map _).hom⟩
  · -- Cokernel: t (1 / ℓ) = ζ ^ i at m, so y = t' (1 / ℓ) is 1 at m for t' = t - i • ε.
    intro c t
    refine t.inductionOn (fun s t ↦ hF fun d f m hm ↦ ?_) fun _ _ ↦ add_mem
    let ψ : (ringOf g).obj c →+* Localization.AtPrime m :=
      (algebraMap _ (Localization.AtPrime m)).comp ((ringOf g).map f.down).hom
    have hζ : IsPrimitiveRoot (tateRoot ψ ε).val ℓ := h_prim f.down m
    obtain ⟨i, hi : (tateRoot ψ ε).val ^ i = (tateRoot ψ t).val⟩ :=
      hζ.zpowers_eq.ge (tateRoot ψ t).property
    let t' : tateModule g c := t - i • ε
    let y : (ringOf g).obj c := (t'.val (1 / ℓ)).down.val
    have h_ker : tateRoot ψ t' = 0 := by
      rw [map_sub, map_zsmul, show i • tateRoot ψ ε = tateRoot ψ t from Subtype.ext hi, sub_self]
    -- read in the localization, ψ(t'(1/ℓ)) = 1
    have hy : ψ y = 1 :=
      congrArg (fun r : Additive (rootsOfUnity ℓ (Localization.AtPrime m)) ↦
        ((r.val : (Localization.AtPrime m)ˣ) : Localization.AtPrime m)) h_ker
    -- Hence a y = a for some a outside m, and where a is a unit, y = 1.
    obtain ⟨a, ha⟩ :
        ∃ a : m.primeCompl, (a : (ringOf g).obj d) * (ringOf g).map f.down y = a * 1 :=
      Localization.isLocalization.exists_of_eq (hy.trans (map_one _).symm)
    refine ⟨a, a.property, fun b f' h_unit ↦ ?_⟩
    have hy_map : (ringOf g).map (f.down ≫ f') y = 1 := by
      rw [(ringOf g).map_comp_apply, ← h_unit.mul_eq_left, ← map_mul, ha, mul_one]
    -- There, for the image τ of t', τ (· / ℓ) lies in the Tate module, so τ is divisible by ℓ,
    -- which kills S.
    let τ : tateModule g b := (tateModule g).map (f.down ≫ f') t'
    let τ' : tateModule g b := ⟨τ.val.comp (.mulRight (ℓ : ℚ)⁻¹), Gm.ext.mpr hy_map⟩
    have hτ : τ = ℓ • τ' := Subtype.ext (AddMonoidHom.nsmul_comp_mulRight_inv_natCast τ.val ℓ).symm
    have h_zero : S.map (f.down ≫ f') s ⊗ₜ[ℤ] τ = 0 := by rw [hτ, ← smul_tmul, hS, zero_tmul]
    -- In the cokernel s ⊗ t and s ⊗ t' agree, as they differ by (i • s) ⊗ ε.
    have h_sub : (i • s) ⊗ₜ[ℤ] ε = s ⊗ₜ[ℤ] t - s ⊗ₜ[ℤ] t' := by simp [t', tmul_sub, smul_tmul]
    have h_class : (abCoker.π ((tensorPoint (tateGen g)).app S)).app c (s ⊗ₜ[ℤ] t) =
        (abCoker.π ((tensorPoint (tateGen g)).app S)).app c (s ⊗ₜ[ℤ] t') :=
      QuotientAddGroup.eq_iff_sub_mem.mpr ⟨i • s, h_sub⟩
    calc _ = (abCoker ((tensorPoint (tateGen g)).app S)).map (f.down ≫ f')
          ((abCoker.π ((tensorPoint (tateGen g)).app S)).app c (s ⊗ₜ[ℤ] t')) :=
        congrArg ((abCoker ((tensorPoint (tateGen g)).app S)).map (f.down ≫ f')) h_class
      _ = 0 := congrArg _ h_zero

/-! ### The action on coefficients and the product with a class -/

variable (M K : TorsionCoeff g) (φ : C' ⥤ C) (M' : TorsionCoeff (φ ⋙ g))
  (T : TotalH (φ ⋙ K.functor) M'.functor)

/-- The action of the Tate module 𝕋 on a coefficient M: the class in Ext⁰(M ⊗ 𝕋, M) whose
pull-back along x ↦ x ⊗ ε, ε = `New.Variety.tateGen`, is the identity. -/
def TorsionCoeff.tateAction : H ((abTensor.flip.obj (tateModule g)).obj M.functor) M.functor 0 :=
  surjInv (isCohomEquiv_tensorPoint_tateGen M.prime_smul_eq_zero M.zariski_descent 0).2
    (Abelian.Ext.mk₀ (𝟙 ((𝟭 (AbFunctor C)).obj M.functor)))

/-- The class `New.Variety.TorsionCoeff.tateAction` of M pulls back along x ↦ x ⊗ ε to the identity
class of M (ε = `New.Variety.tateGen`). -/
lemma TorsionCoeff.pullbackAlong_tensorPoint_tateAction :
    pullbackAlong (tensorPoint (tateGen g) M.functor) M.tateAction.toTotalH = homClass
      (𝟙 M.functor) := by
  -- `M.tateAction` is defined as a preimage of the identity class under this pull-back
  rw [pullbackAlong_of, show H.map M.functor (tensorPoint (tateGen g) M.functor) 0 M.tateAction =
    Abelian.Ext.mk₀ (𝟙 M.functor) from
      surjInv_eq (isCohomEquiv_tensorPoint_tateGen M.prime_smul_eq_zero M.zariski_descent 0).2 _]
  rfl

/-- The generator ε acts as the identity: for a class y in total Ext(S, M), the Yoneda composite of
x ↦ x ⊗ ε, y ⊗ 𝕋 and `New.Variety.TorsionCoeff.tateAction` of M is y (𝕋 the Tate module,
ε = `New.Variety.tateGen`). -/
lemma TorsionCoeff.pullbackAlong_tensorPoint_comp_tateAction (y : TotalH S M.functor) :
    pullbackAlong (tensorPoint (tateGen g) S)
      (TotalH.comp (TotalH.map (abTensor.flip.obj (tateModule g)) y)
        M.tateAction.toTotalH) = y := by
  -- By naturality x ↦ x ⊗ ε moves past `y`; and `M.tateAction` pulls back along this map to the
  -- identity class.
  calc _ = TotalH.comp (TotalH.map (𝟭 (AbFunctor C)) y)
          (pullbackAlong (tensorPoint (tateGen g) M.functor) M.tateAction.toTotalH) :=
        TotalH.comp_assoc_of_sq (y.naturality (tensorPoint (tateGen g))).symm _
    _ = TotalH.comp y (homClass (𝟙 M.functor)) := by
        rw [M.pullbackAlong_tensorPoint_tateAction, TotalH.map_id]
        rfl
    _ = y := TotalH.comp_id

/-- For coefficients K along g and M' along g∘φ, every class T in total Ext(K∘φ, M') commutes
with the actions μ = `New.Variety.TorsionCoeff.tateAction` of the Tate module 𝕋: in diagram
order, μ_K restricted along φ and then T equals T ⊗ 𝕋 and then μ_{M'}. -/
lemma TorsionCoeff.tateAction_comm :
    mapThenComp (restrictAlong φ) T K.tateAction.toTotalH =
      TotalH.comp (TotalH.map (abTensor.flip.obj (tateModule (φ ⋙ g))) T)
        M'.tateAction.toTotalH := by
  -- Pull-back along x ↦ x ⊗ ε is injective on classes with values in `M'.functor`, and it sends
  -- both sides to `T`, because ε acts as the identity on both coefficients.
  apply (isCohomEquiv_tensorPoint_tateGen (S := φ ⋙ K.functor)
    (fun (c : C') ↦ K.prime_smul_eq_zero (φ.obj c))
    M'.zariski_descent).bijective_pullbackAlong.injective
  rw [M'.pullbackAlong_tensorPoint_comp_tateAction T]
  -- On the left, the action on K restricted along φ pulls back to the identity class as well.
  have h_restricted :
      pullbackAlong (tensorPoint (tateGen (φ ⋙ g)) (φ ⋙ K.functor))
        (TotalH.map (restrictAlong φ) K.tateAction.toTotalH) = homClass (𝟙 (φ ⋙ K.functor)) := by
    have h_mapped :
        TotalH.map (restrictAlong φ)
            (pullbackAlong (tensorPoint (tateGen g) K.functor) K.tateAction.toTotalH) =
          TotalH.map (restrictAlong φ) (homClass (𝟙 K.functor)) :=
      congrArg _ K.pullbackAlong_tensorPoint_tateAction
    rw [map_pullbackAlong, map_homClass, CategoryTheory.Functor.map_id] at h_mapped
    exact h_mapped
  calc _ = TotalH.comp (pullbackAlong (tensorPoint (tateGen (φ ⋙ g)) (φ ⋙ K.functor))
          (TotalH.map (restrictAlong φ) K.tateAction.toTotalH)) T :=
        (TotalH.comp_assoc _ _).symm
    _ = T := by
        rw [h_restricted]
        exact TotalH.pullbackAlong_id

/-- The product with a class ξ in total Ext(P, 𝕋), 𝕋 the Tate module `New.Variety.tateModule`. For
S with flat values it is the additive map y ↦ y · ξ from total Ext(S, M) to total Ext(S ⊗ P, M),
where y · ξ is the Yoneda composite S ⊗ P → S ⊗ 𝕋 → M ⊗ 𝕋 → M of S ⊗ ξ, y ⊗ 𝕋 and
`New.Variety.TorsionCoeff.tateAction`. -/
def TorsionCoeff.mulClass [HasFlatValues S] (ξ : TotalH P (tateModule g)) :
    TotalH S M.functor →+ TotalH ((abTensor.obj S).obj P) M.functor :=
  (ξ.map (abTensor S)).comp.comp (mapThenComp (abTensor.flip (tateModule g)) M.tateAction.toTotalH)

lemma TorsionCoeff.mulClass_apply [HasFlatValues S] (ξ : TotalH P (tateModule g))
    (y : TotalH S M.functor) :
    M.mulClass ξ y = TotalH.comp (TotalH.map (abTensor S) ξ)
      (mapThenComp (abTensor.flip (tateModule g)) M.tateAction.toTotalH y) :=
  rfl

/-- The product is natural in the coefficient. Let φ : C' ⥤ C, K a coefficient along g (an ℓ-torsion
functor with Zariski descent, `TorsionCoeff`) and M' one along φ ⋙ g, and let S have flat values.
Let y be a class in total Ext(S, K), ξ one in total Ext(P, 𝕋) (𝕋 the Tate module) and T one in total
Ext(K∘φ, M'). Restricting the product y · ξ ∈ total Ext(S ⊗ P, K) along φ and composing with T gives
the product of (y restricted, then T) with ξ restricted. -/
lemma TorsionCoeff.mulClass_naturality [HasFlatValues S] (ξ : TotalH P (tateModule g))
    (y : TotalH S K.functor) :
    mapThenComp (restrictAlong φ) T (K.mulClass ξ y) =
      M'.mulClass (S := φ ⋙ S) (P := φ ⋙ P) (TotalH.map (restrictAlong φ) ξ)
        (mapThenComp (restrictAlong φ) T y) := by
  -- Both sides expand to the product of S ⊗ ξ, y ⊗ 𝕋, `T` ⊗ 𝕋 and the action μ (𝕋 the Tate
  -- module): restriction along φ and tensoring with 𝕋 are multiplicative, and `T` commutes with μ.
  -- Restricting along φ and tensoring commute, as the two composite functors agree by definition.
  have h_ξ : TotalH.map (restrictAlong φ) (TotalH.map (abTensor.obj S) ξ) =
      TotalH.map (abTensor.obj (φ ⋙ S)) (TotalH.map (restrictAlong φ) ξ) := by
    rw [TotalH.map_map, TotalH.map_map]
    rfl
  have h_y : TotalH.map (restrictAlong φ) (TotalH.map (abTensor.flip.obj (tateModule g)) y) =
      TotalH.map (abTensor.flip.obj (tateModule (φ ⋙ g))) (TotalH.map (restrictAlong φ) y) := by
    rw [TotalH.map_map, TotalH.map_map]
    rfl
  calc mapThenComp (restrictAlong φ) T (K.mulClass ξ y)
      = TotalH.comp (TotalH.map (restrictAlong φ) (TotalH.map (abTensor.obj S) ξ))
          (TotalH.comp
            (TotalH.map (restrictAlong φ) (TotalH.map (abTensor.flip.obj (tateModule g)) y))
            (TotalH.comp (TotalH.map (restrictAlong φ) K.tateAction.toTotalH) T)) :=
        (map_comp_assoc (restrictAlong φ) T).trans
          (congrArg _ (map_comp_assoc (restrictAlong φ) T))
    _ = TotalH.comp (TotalH.map (abTensor.obj (φ ⋙ S)) (TotalH.map (restrictAlong φ) ξ))
          (TotalH.comp
            (TotalH.map (abTensor.flip.obj (tateModule (φ ⋙ g))) (TotalH.map (restrictAlong φ) y))
            (TotalH.comp (TotalH.map (abTensor.flip.obj (tateModule (φ ⋙ g))) T)
              M'.tateAction.toTotalH)) :=
        -- (a term: `rw` cannot match these sides, whose implicit objects differ by unfolding)
        congrArg₂ (fun a b ↦ TotalH.comp a b) h_ξ
          (congrArg₂ (fun a b ↦ TotalH.comp a b) h_y (K.tateAction_comm φ M' T))
    _ = M'.mulClass (S := φ ⋙ S) (P := φ ⋙ P) (TotalH.map (restrictAlong φ) ξ)
          (mapThenComp (restrictAlong φ) T y) :=
        congrArg _ (map_comp_assoc (abTensor.flip.obj (tateModule (φ ⋙ g))) _).symm

/-- Let Θ be a theory along g (an ℓ-torsion coefficient F = Θ.functor with Zariski descent that
behaves well on closed loci). Let J be a compatible family of ideals J_c of the rings g(c), and
U = `relFreeAb J.topLocus` (ℤ modulo ℤ[V], V the locus where J is the unit ideal). Let ξ be a class
in Ext²(U, 𝕋), 𝕋 the Tate module. If a, a' : S' → S, between functors with flat values, agree at
every c with J_c = 0, then (a^*y) · ξ = (a' ⊗ U)^*(y · ξ) for every class y in total Ext(S, F). Here
y · ξ in total Ext(S ⊗ U, F) is the Yoneda composite of S ⊗ ξ, y ⊗ 𝕋 and the action of 𝕋 on F. -/
lemma Theory.mulClass_congr_of_eq_on_zeros [HasFlatValues S] [HasFlatValues S'] (Θ : Theory g)
    (J : IdealFamily (ringOf g)) (ξ : H (relFreeAb J.topLocus) (tateModule g) 2)
    {a a' : S' ⟶ S} (h_agree : ∀ c : C, J.ideal c = ⊥ → a c = a' c) (y : TotalH S Θ.functor) :
    Θ.mulClass ξ.toTotalH (pullbackAlong a y) =
      pullbackAlong (abTensor.map a' (relFreeAb J.topLocus)) (Θ.mulClass ξ.toTotalH y) := by
  -- The product z · ξ is z ⊗ U, then F ⊗ U → F_J ⊗ U, then one class v that depends only on ξ; here
  -- F = `Θ.functor`, F_J = `J.zerosCoeff Θ.functor` and U = `relFreeAb J.topLocus`. So z · ξ
  -- depends only on the image of z with coefficients F_J, and there the pull-backs along a and a'
  -- agree.
  let Φ : AbFunctor C ⥤ AbFunctor C := abTensor.flip.obj (relFreeAb J.topLocus)
  -- By `exists_isTensorClass`, a class w from F ⊗ U to F ⊗ 𝕋 (𝕋 the Tate module) has
  -- z ∪ ξ = (z ⊗ U, then w).
  obtain ⟨w, hw⟩ :
      ∃ w : TotalH (Φ.obj Θ.functor) ((abTensor.flip.obj (tateModule g)).obj Θ.functor),
        ∀ (S : AbFunctor C) [HasFlatValues S] (z : TotalH S Θ.functor),
          TotalH.comp (.map Φ z) w = z.cup ξ.toTotalH := by
    obtain ⟨family, h_family⟩ := exists_isTensorClass ξ
    refine ⟨(family C (𝟭 C) Θ.functor).toTotalH, fun S _ z ↦ ?_⟩
    -- for S with flat values the class of the family is S ⊗ ξ
    have h_flat : (family C (𝟭 C) S).toTotalH = TotalH.map (abTensor.obj S) ξ.toTotalH :=
      (h_family.eq_of_flat C (𝟭 C) S).trans (congrArg _ TotalH.map_id)
    refine (h_family.comm C (𝟭 C) S Θ.functor z).trans ?_
    rw [h_flat]
    rfl
  -- The sections of ker (F → F_J) ⊗ U are locally zero: locally s dies, or J is the unit ideal
  -- and then U is zero.
  have h_loc (c : C) (t : Φ (kerComplex (J.toZerosCoeff Θ.functor)).X₁ c) :
      t ∈ locallyZero Θ.functor _ c := by
    refine t.inductionOn (fun s r ↦ ?_) fun x y hx hy ↦ add_mem hx hy
    refine (Θ.zariski_descent (Θ.isZariskiLocallyTop_ker_toZerosCoeff J)).of_preimage_le
      (pointMap s) fun b f hf ↦ ?_
    show (kerComplex (J.toZerosCoeff Θ.functor)).X₁.map f.down s ⊗ₜ[ℤ]
        (relFreeAb J.topLocus).map f.down r = 0
    rcases hf with (hs : (kerComplex (J.toZerosCoeff Θ.functor)).X₁.map f.down s = 0) | hb
    · -- s dies along f
      rw [hs, zero_tmul]
    · -- J is the unit ideal at b, where the relative chains U vanish
      have h_r : (relFreeAb J.topLocus).map f.down r = 0 :=
        AddSubgroup.mem_bot.mp (relFreeAb.mem_of_mk_mem ⊥ (fun _ ↦ relFreeAb.mk_eq_zero hb) _)
      simp [h_r]
  -- Hence F ⊗ U → F_J ⊗ U is an equivalence for F, and the class (w, then the action) lifts to v.
  have h_eqv : IsCohomEquiv Θ.functor ((kerComplex (J.toZerosCoeff Θ.functor)).map Φ).g :=
    isCohomEquiv_quotient_of_acyclic
      ((kerComplex_shortExact fun _ ↦ Quot.mk_surjective).map_of_exact Φ)
      (cohomology_eq_zero_of_locallyZero h_loc)
  obtain ⟨v, hv⟩ : ∃ v : TotalH (Φ.obj (J.zerosCoeff Θ.functor)) Θ.functor,
      pullbackAlong (Φ.map (J.toZerosCoeff Θ.functor)) v = w.comp Θ.tateAction.toTotalH :=
    h_eqv.bijective_pullbackAlong.surjective (w.comp Θ.tateAction.toTotalH)
  have h_dot (S : AbFunctor C) [HasFlatValues S] (z : TotalH S Θ.functor) :
      Θ.mulClass ξ.toTotalH z =
        TotalH.comp (.map Φ (z.comp (.homClass (J.toZerosCoeff Θ.functor)))) v := by
    rw [map_comp_assoc, map_homClass, hv]
    exact (TotalH.comp_assoc_of_sq (hw S z) _).symm
  -- The inclusion of ker (a - a') is bijective where J = 0, a dense locus for F_J, and it
  -- equalizes a and a'.
  have h_ker : IsCohomEquiv (J.zerosCoeff Θ.functor) (kerComplex (a - a')).f :=
    (Θ.isCohomDense_botLocus J).isCohomEquiv_of_bijective_on fun (c : C) (hc : J.ideal c = ⊥) ↦ by
      have h_mem (x : S' c) : x ∈ ((a - a').app c).hom.ker := by simp [h_agree c hc]
      exact ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, h_mem x⟩, rfl⟩⟩
  -- the inclusion ι of ker (a - a') has ι ≫ a = ι ≫ a'
  let ι : (kerComplex (a - a')).X₁ ⟶ S' := (kerComplex (a - a')).f
  have h_equalizes : ι ≫ a = ι ≫ a' :=
    sub_eq_zero.mp ((Preadditive.comp_sub ι a a').symm.trans (kerComplex (a - a')).zero)
  have h_classes :
      TotalH.comp (homClass ι) (homClass a) = TotalH.comp (homClass ι) (homClass a') := by
    rw [← homClass_comp, ← homClass_comp, h_equalizes]
  have h_pull (z : TotalH S (J.zerosCoeff Θ.functor)) : pullbackAlong a z = pullbackAlong a' z :=
    h_ker.bijective_pullbackAlong.injective (TotalH.comp_assoc_of_sq h_classes z)
  calc Θ.mulClass ξ.toTotalH (pullbackAlong a y)
      = TotalH.comp
          (TotalH.map Φ (pullbackAlong a (y.comp (homClass (J.toZerosCoeff Θ.functor))))) v := by
        rw [h_dot, TotalH.comp_assoc]
    _ = TotalH.comp
          (TotalH.map Φ (pullbackAlong a' (y.comp (homClass (J.toZerosCoeff Θ.functor))))) v := by
        rw [h_pull]
    _ = pullbackAlong (Φ.map a')
          (TotalH.comp (TotalH.map Φ (y.comp (homClass (J.toZerosCoeff Θ.functor)))) v) := by
        rw [map_comp_assoc, map_homClass]
    _ = pullbackAlong (abTensor.map a' (relFreeAb J.topLocus)) (Θ.mulClass ξ.toTotalH y) := by
        -- `Φ.map a'` is a' ⊗ U by definition; the two sides differ only in how this is written
        rw [← h_dot]
        rfl

end TateAction

/-!
## The projective line, the class η and the line formula

The projective line `New.Variety.projLine` sends a ring `B` to the points `(1 + u v : v)`. Along a
ring map the chosen rows change by units, and these units form a cocycle from `ℤ[ℙ¹]` to `𝔾_m`
(`New.Variety.projLine.cocycle`), the cocycle of `O(1)`. For a coefficient `M`, the product with `η`
at a point is `New.Variety.TorsionCoeff.etaAt`; the projective line formula
(`New.Variety.TorsionCoeff.HasLineFormula`) says that `1` and `η` are a basis over the cohomology of
every `S`.

Here `g : C ⥤ TestOver A` is a functor to tests over `A`, `New.Variety.ringOf g` gives the ring of
`g c`, `New.Variety.freeAb` is `Y ↦ ℤ[Y]`, and `New.Variety.H N F n` is `Extⁿ(N, F)` of functors
`C ⥤ Ab`.
-/

section LineChernClass

open CategoryTheory AddCommGrpCat Abelian TotalH FreeAbelianGroup Ideal

set_option backward.isDefEq.respectTransparency false

variable {C C' : Type _} [Category C] [Category C'] {ℓ : ℕ} {A : Type} [CommRing A]
  (g : C ⥤ TestOver A)

/-! ### The projective line and the cocycle of `O(1)` -/

/-- The relation on pairs `(u, v)` whose classes are the points of the projective line. The pair
`(u, v)` stands for the row `(1 + u v, v)`; two pairs are related if the determinant of their rows
is zero. This gives the points `(a : v)` with a representative such that `a ≡ 1 mod v`. -/
def projLineSetoid (B : Type) [CommRing.{0} B] : Setoid (B × B) where
  r (x y : B × B) := (1 + x.1 * x.2) * y.2 = x.2 * (1 + y.1 * y.2)
  iseqv := by grind [Equivalence.mk]

/-- The projective line as a functor (`PointFunctor`) from commutative rings (`CommRingCat`) to
`Type 1`: B goes to the set of points (1 + uv : v) with u, v in B, that is, pairs (u, v) modulo
`New.Variety.projLineSetoid`. -/
def projLine : PointFunctor where
  obj B := ULift (Quotient (projLineSetoid B))
  map f :=
    ↾fun q ↦ ⟨q.1.map (Prod.map f.hom f.hom) fun x y
      (h : (1 + x.1 * x.2) * y.2 = x.2 * (1 + y.1 * y.2)) ↦
        show (1 + f.hom x.1 * f.hom x.2) * f.hom y.2 = f.hom x.2 * (1 + f.hom y.1 * f.hom y.2) by
          simpa using congrArg f.hom h⟩
  map_id _ := by
    ext ⟨⟨⟩⟩
    rfl
  map_comp _ _ := by
    ext ⟨⟨⟩⟩
    rfl

/-- The product of copies of the projective line indexed by `ι`. -/
def projLinePow (ι : Type) : PointFunctor where
  obj B := ι → projLine B
  map f := ↾fun q i ↦ projLine.map f (q i)

/-- For a functor of points X, the projection (c, x) ↦ c from pairs of a test c over A and
x ∈ X(c) to tests over A. -/
abbrev testOfPoint (A : Type) [CommRing A] (X : CommRingCat ⥤ Type 1) :
    (ringOf (𝟭 (TestOver A)) ⋙ X).Elements ⥤ TestOver A :=
  elementsProj (ringOf (𝟭 (TestOver A)) ⋙ X) ⋙ 𝟭 (TestOver A)

/-- The projective line over the tests of `g`. -/
abbrev projLineAlong : C ⥤ Type 1 := ringOf g ⋙ projLine

namespace projLine

variable {B B' : CommRingCat} (f : B ⟶ B') (q : projLine B)

/-- The homogeneous coordinates `(1 + u v, v)` of a point, for a chosen representative `(u, v)`. -/
def unimodularRow : B × B := (1 + q.down.out.1 * q.down.out.2, q.down.out.2)

/-- The row `(1 + u v, v)` of a pair `x = (u, v)` is a unit times the row of its point. -/
lemma exists_unit_smul_unimodularRow (x : B × B) :
    ∃ ε : Bˣ, (1 + x.fst * x.snd, x.snd) = ε.val • unimodularRow ⟨⟦x⟧⟩ := by
  -- The chosen representative `y` of the class of `x` has a row of determinant zero with that of
  -- `x`. Writing `x = (u, v)` and `y = (u', v')`, the unit is `1 + (u - u') v`, with inverse
  -- `1 + (u' - u) v'`.
  let y : B × B := (⟦x⟧ : Quotient (projLineSetoid B)).out
  have h_det : (1 + y.fst * y.snd) * x.snd = y.snd * (1 + x.fst * x.snd) :=
    Quotient.mk_out (s := projLineSetoid B) x
  have h_mul_inv : (1 + (x.fst - y.fst) * x.snd) * (1 + (y.fst - x.fst) * y.snd) = 1 := by
    linear_combination (x.fst - y.fst) * h_det
  have h_fst : 1 + x.fst * x.snd = (1 + (x.fst - y.fst) * x.snd) * (1 + y.fst * y.snd) := by
    linear_combination y.fst * h_det
  have h_snd : x.snd = (1 + (x.fst - y.fst) * x.snd) * y.snd := by
    linear_combination h_det
  have h_row : unimodularRow (⟨⟦x⟧⟩ : projLine B) = (1 + y.fst * y.snd, y.snd) := rfl
  refine ⟨Units.mkOfMulEqOne _ _ h_mul_inv, ?_⟩
  simp [h_row, ← h_fst, ← h_snd]

/-- Unit multiples of chosen rows determine both the unit and the point. -/
lemma eq_and_eq_of_smul_unimodularRow_eq {q q' : projLine.obj B} {a b : Bˣ}
    (h_smul : a.val • unimodularRow (B := B) q = b.val • unimodularRow q') :
    a = b ∧ q = q' := by
  -- Compare the coordinates of the rows of the chosen representatives of `q` and `q'`.
  obtain ⟨h_fst, h_snd⟩ :
      a.val * (1 + q.down.out.fst * q.down.out.snd) =
          b.val * (1 + q'.down.out.fst * q'.down.out.snd) ∧
        a.val * q.down.out.snd = b.val * q'.down.out.snd := by
    simpa only [unimodularRow, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq] using h_smul
  -- Cross-multiplying the two coordinates gives `a` times the relation that defines the line.
  have h_rel : (1 + q.down.out.fst * q.down.out.snd) * q'.down.out.snd =
      q.down.out.snd * (1 + q'.down.out.fst * q'.down.out.snd) := by
    apply a.mul_right_inj.mp
    linear_combination q'.down.out.snd * h_fst - (1 + q'.down.out.fst * q'.down.out.snd) * h_snd
  obtain rfl : q = q' := ULift.down_injective (Quotient.out_equiv_out.mp h_rel)
  -- The coordinates `1 + u v` and `v` of the row of a representative `(u, v)` generate the unit
  -- ideal, so `a = b`.
  exact ⟨Units.ext (by linear_combination h_fst - q.down.out.fst * h_snd), rfl⟩

/-- The unit by which `f` rescales the row of a point (`unimodularRow_map`), extended additively
to the free abelian group on the points. -/
def rowUnit : FreeAbelianGroup (projLine B) →+ Gm B' :=
  lift fun q : projLine B ↦ ⟨(exists_unit_smul_unimodularRow (q.1.out.map f f)).choose⟩

/-- The image under `f` of a point `q` is the class of the image of its chosen representative. -/
lemma map_eq_mk_map_out (f : B ⟶ B') (q : projLine B) :
    projLine.map f q = ⟨⟦q.down.out.map f f⟧⟩ := by
  exact congrArg (projLine.map f) (congrArg ULift.up q.down.out_eq.symm : q = ⟨⟦q.down.out⟧⟩)

/-- The image under `f` of the chosen row of `q` is the unit `New.Variety.projLine.rowUnit` times
the chosen row of the image point of `q`. -/
lemma unimodularRow_map :
    (unimodularRow q).map f f =
      (rowUnit f (FreeAbelianGroup.of q)).down.toMul.val • unimodularRow (projLine.map f q) := by
  -- `rowUnit f q` is the unit chosen for the image of the representative of `q`.
  have h_unit : (rowUnit f (FreeAbelianGroup.of q)).down.toMul =
      (exists_unit_smul_unimodularRow (q.down.out.map f f)).choose :=
    congrArg (fun u : Gm B' ↦ u.down.toMul) (lift_apply_of _ q)
  rw [h_unit, map_eq_mk_map_out, ← (exists_unit_smul_unimodularRow _).choose_spec]
  simp [unimodularRow]

/-- If `f` maps `a` times the row of `q` to `b` times a row, then `b` is the product of `f a` and
the unit `rowUnit f q`. -/
lemma add_rowUnit_eq {q' : projLine B'} {a : Bˣ} {b : B'ˣ}
    (h_row : (a.val • unimodularRow q).map f f = b.val • unimodularRow q') :
    Gm.map f ⟨a⟩ + rowUnit f (FreeAbelianGroup.of q) = ⟨b⟩ := by
  -- Write the image of `a • unimodularRow q` in two ways as a unit times a row; the unit is unique.
  have h_smul : (Gm.map f ⟨a⟩ + rowUnit f (FreeAbelianGroup.of q)).down.toMul.val •
      unimodularRow (projLine.map f q) = b.val • unimodularRow q' := by
    change (f a.val * (rowUnit f (FreeAbelianGroup.of q)).down.toMul.val) •
      unimodularRow (projLine.map f q) = _
    rw [mul_smul, ← unimodularRow_map, ← h_row]
    ext <;> simp
  exact Gm.ext.mpr (congrArg Units.val (eq_and_eq_of_smul_unimodularRow_eq h_smul).left)

/-- The point (x : 1) of the projective line over B. -/
def affinePt (x : B) : projLine B := ⟨⟦(x - 1, 1)⟧⟩

lemma map_affinePt (x : B) : projLine.map f (affinePt x) = affinePt (f x) := by
  simp [affinePt, projLine]

/-- The first coordinate of the row of the point `(x : 1)` is a unit exactly when `x` is a unit. -/
lemma isUnit_unimodularRow_affinePt_iff {x : B} :
    IsUnit (unimodularRow (affinePt x)).fst ↔ IsUnit x := by
  obtain ⟨ε, h_ε⟩ := exists_unit_smul_unimodularRow (x - 1, 1)
  have h_fst : x = ε.val * (unimodularRow (affinePt x)).fst := by
    simpa [affinePt] using congrArg Prod.fst h_ε
  rw [← ε.isUnit_units_mul, ← h_fst]

lemma affinePt_injective : Function.Injective (affinePt (B := B)) := by
  intro x y
  simp [affinePt, projLine, projLineSetoid, Quotient.eq]

/-- If the image of the row of `q` is proportional to `(x, 1)`, then `q` maps to `(x : 1)`. -/
lemma affinePt_eq_map (x : B')
    (h_ratio : f (unimodularRow q).fst = f (unimodularRow q).snd * x) :
    affinePt x = projLine.map f q := by
  -- The pair `(x - 1, 1)` and the image of the representative of `q` have proportional rows.
  have h_rel : (projLineSetoid B').r (x - 1, 1) (q.down.out.map f f) := by
    simp only [unimodularRow, map_add, map_mul, map_one] at h_ratio
    change (1 + (x - 1) * 1) * f q.down.out.snd = 1 * (1 + f q.down.out.fst * f q.down.out.snd)
    linear_combination -h_ratio
  rw [map_eq_mk_map_out]
  exact congrArg ULift.up (Quotient.sound h_rel)

/-- If `f` sends the first coordinate of the row of `q` to a unit, then the row of the image point
also has a unit as first coordinate. -/
lemma isUnit_fst_unimodularRow_map (h_unit : IsUnit (f (unimodularRow q).fst)) :
    IsUnit (unimodularRow (projLine.map f q)).fst := by
  rw [show f (unimodularRow q).fst = (rowUnit f (FreeAbelianGroup.of q)).down.toMul.val *
      (unimodularRow (projLine.map f q)).fst from congrArg Prod.fst (unimodularRow_map f q)]
    at h_unit
  exact (IsUnit.mul_iff.mp h_unit).right

/-- The complement of `(0 : 1)`: the points whose row has a unit as first coordinate. -/
def affineChart : Subfunctor projLine where
  obj _ := {q | IsUnit (unimodularRow q).1}
  map f q h_unit := isUnit_fst_unimodularRow_map f q (IsUnit.map f.hom h_unit)

/-- The section of the projective line along g whose value at every object c is the base point
(1 : 1) over the ring g(c). -/
def basePt : (projLineAlong g).sections :=
  ⟨fun _ : C ↦ affinePt 1, fun {c d : C} (_ : c ⟶ d) ↦ by simp [map_affinePt]⟩

/-- The 1-cocycle from ℤ[P¹] to G_m along g sending a morphism f and a point q to the transition
unit `New.Variety.projLine.rowUnit` of the chosen rows. -/
def cocycle : Cocycle (freeAb (projLineAlong g)) (ringOf g ⋙ Gm) where
  component f := ofHom (rowUnit ((ringOf g).map f))
  cocycle_comp _ _ := by
    -- Both sides are the unit by which `unimodularRow` changes along the composite map.
    ext : 2
    symm
    apply add_rowUnit_eq
    erw [← unimodularRow_map, ← unimodularRow_map]
    aesop

/-- The determinant `a v' - v a'` of the rows `(a, v)` and `(a', v')` of two points `p`, `p'` of the
projective line. -/
private def rowDet (p p' : projLine B) : B :=
  (unimodularRow p).fst * (unimodularRow p').snd - (unimodularRow p).snd * (unimodularRow p').fst

/-- A ring map `f` sends the determinant of the rows of `p` and `p'` to the value of `rowUnit f` at
`p + p'` times the determinant of the rows of the image points. -/
private lemma map_rowDet (p p' : projLine B) :
    f (rowDet p p') = (rowUnit f (.of p + .of p')).down.toMul.val *
      rowDet (projLine.map f p) (projLine.map f p') := by
  have h_fst (r : projLine B) : f (unimodularRow r).fst =
      (rowUnit f (.of r)).down.toMul.val * (unimodularRow (projLine.map f r)).fst :=
    congrArg Prod.fst (unimodularRow_map f r)
  have h_snd (r : projLine B) : f (unimodularRow r).snd =
      (rowUnit f (.of r)).down.toMul.val * (unimodularRow (projLine.map f r)).snd :=
    congrArg Prod.snd (unimodularRow_map f r)
  -- The sum in `Gm` is the product of the units.
  have h_add : (rowUnit f (.of p + .of p')).down.toMul.val =
      (rowUnit f (.of p)).down.toMul.val * (rowUnit f (.of p')).down.toMul.val := by
    rw [map_add]
    rfl
  simp only [rowDet, map_sub, map_mul, h_fst, h_snd, h_add]
  ring

/-- Two points of the projective line are equal exactly when their rows have determinant zero. -/
lemma eq_iff_unimodularRow_fst_mul_snd_eq {p p' : projLine B} :
    p = p' ↔ (unimodularRow p).fst * (unimodularRow p').snd =
      (unimodularRow p).snd * (unimodularRow p').fst := by
  refine ⟨?_, fun h_det ↦ ULift.down_injective (Quotient.out_equiv_out.mp h_det)⟩
  rintro rfl
  exact mul_comm _ _

end projLine

open projLine

/-! ### The class `η` -/

/-- The class `η` in `Ext²(ℤ[ℙ¹], T)`, with `T` the Tate module: the product of the extension class
of the cocycle of `O(1)` and the extension class of the Kummer sequence. -/
@[irreducible]
def etaClass : H (freeAb (projLineAlong g)) (tateModule g) 2 :=
  (cocycle g).shortExact_extension.extClass.comp (shortExact_kummerSeq g).extClass rfl

/-! ### The product with `η` on a coefficient, and the line formula -/

/-- A family of classes in `Ext²(S ⊗ ℤ[ℙ¹], S ⊗ T)`, with `T` the Tate module, one for each functor
`φ` to tests over `A` and each functor `S` from `D` to abelian groups, not only torsion
coefficients. It is chosen by `exists_isTensorClass` for the class `η` on the category of all tests
over `A`. -/
abbrev TorsionCoeff.etaTensor (D : Type 1) [Category.{0} D] (φ : D ⥤ TestOver A) (S : AbFunctor D) :
    H (abTensor.flip (φ ⋙ freeAb (projLineAlong (𝟭 (TestOver A)))) S)
      (abTensor.flip (φ ⋙ tateModule (𝟭 (TestOver A))) S) 2 :=
  (exists_isTensorClass (etaClass (𝟭 (TestOver A)))).choose D φ S

/-- The family `etaTensor` tensors the class `η` on the category of all tests over `A` with every
coefficient. -/
lemma TorsionCoeff.isTensorClass_etaTensor :
    IsTensorClass (etaClass (𝟭 (TestOver A))) TorsionCoeff.etaTensor :=
  (exists_isTensorClass (etaClass (𝟭 (TestOver A)))).choose_spec

/-- The class `S ⊗ η` in `Ext²(S ⊗ ℤ[ℙ¹], S ⊗ T)`, defined for every coefficient `S`, flat or not.
It is used through `etaTensorClass_naturality`, `etaTensorClass_of_hasFlatValues` and
`map_restrictAlong_etaTensorClass`. -/
def etaTensorClass (S : AbFunctor C) :
    H (abTensor.flip (freeAb (projLineAlong g)) S) (abTensor.flip (tateModule g) S) 2 :=
  TorsionCoeff.etaTensor C g S

end LineChernClass

section EtaProduct

open CategoryTheory AddCommGrpCat Abelian TotalH FreeAbelianGroup Ideal projLine

set_option backward.isDefEq.respectTransparency false

variable {C C' : Type _} [Category C] [Category C'] {ℓ : ℕ} {A : Type} [CommRing A]
  {g : C ⥤ TestOver A} {S : AbFunctor C} {Y : C ⥤ Type 1} (φ : C' ⥤ C)

/-- The class `etaTensorClass g S` is natural in the coefficient `S`, for classes of every
degree. -/
lemma etaTensorClass_naturality {S' : AbFunctor C} (y : TotalH S S') :
    comp (map (abTensor.flip (freeAb (projLineAlong g))) y) (etaTensorClass g S').toTotalH =
      comp (etaTensorClass g S).toTotalH (map (abTensor.flip (tateModule g)) y) :=
  TorsionCoeff.isTensorClass_etaTensor.comm C g S S' y

/-- The class `etaTensorClass g S` is compatible with restriction along a functor `φ`. -/
lemma map_restrictAlong_etaTensorClass :
    map (restrictAlong φ) (etaTensorClass g S).toTotalH =
      (etaTensorClass (φ ⋙ g) (φ ⋙ S)).toTotalH :=
  TorsionCoeff.isTensorClass_etaTensor.restrict C g S C' φ

/-- A section `q` of `Y` as a map `ℤ[pt] ⟶ ℤ[Y]`. -/
abbrev freeAbSectionMap (q : Y.sections) : freeAb (onePointFunctor C) ⟶ freeAb Y :=
  freeAb.map (sectionMap q)

/-- The class `η` is compatible with restriction along a functor `φ`. -/
lemma map_restrictAlong_etaClass :
    map (restrictAlong φ) (etaClass g).toTotalH = (etaClass (φ ⋙ g)).toTotalH := by
  -- Restriction along `φ` is exact, so it maps the product of the extension classes of the cocycle
  -- and of the Kummer sequence to the product of the extension classes of the restricted sequences,
  -- which are the sequences along `φ ⋙ g`.
  rw [etaClass, etaClass, TotalH.map_of, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.mapExactFunctor_extClass]
  rfl

/-- If `S` has flat values, then `etaTensorClass g S` is the image of `η` under the exact functor
`S ⊗ -`. -/
lemma etaTensorClass_of_hasFlatValues [HasFlatValues S] :
    (etaTensorClass g S).toTotalH = map (abTensor S) (etaClass g).toTotalH := by
  have h_restrict : (etaTensorClass g S).toTotalH =
      map (abTensor S) (map (restrictAlong g) (etaClass (𝟭 (TestOver A))).toTotalH) :=
    TorsionCoeff.isTensorClass_etaTensor.eq_of_flat C g S
  rw [h_restrict, map_restrictAlong_etaClass]
  -- `g ⋙ 𝟭 _` is `g` by definition
  rfl

/-- If the cocycle of `O(1)`, pulled back along `b`, is the coboundary of a family of units `u`,
then `η` pulls back to zero along `b`. -/
lemma map_etaClass_eq_zero_of_coboundary (b : freeAb Y ⟶ freeAb (projLineAlong g))
    (u : ∀ c : C, Y c → (ringOf g ⋙ Gm) c)
    (h_coboundary : ∀ (c d : C) (f : c ⟶ d) (x : Y c), (ringOf g ⋙ Gm).map f (u c x) =
      (cocycle g).component f (b c (FreeAbelianGroup.of x)) + u d (Y.map f x)) :
    H.map (tateModule g) b 2 (etaClass g) = 0 := by
  -- The units `u` trivialize the cocycle along `b`, so `b` lifts to the middle term of the
  -- extension `(cocycle g).extension`, and the extension class dies on the middle term.
  let s (c : C) (x : Y c) : (cocycle g).extension.X₂ c := (-u c x, b c (.of x))
  have h_nat (c d : C) (f : c ⟶ d) (x : Y c) :
      s d (Y.map f x) = (cocycle g).extension.X₂.map f (s c x) := by
    refine Prod.ext ?_ (b.naturality_apply f (.of x))
    simpa [s, Cocycle.extension, eq_neg_add_iff_add_eq, add_neg_eq_iff_eq_add] using
      h_coboundary c d f x
  let b' : freeAb Y ⟶ (cocycle g).extension.X₂ := freeAb.desc s h_nat
  -- the second coordinate of `b'` is `b`
  have h_lift : b = b' ≫ (cocycle g).extension.g := freeAb.hom_ext fun c x ↦ by aesop
  -- `etaClass` starts with the extension class of the cocycle, which dies on the middle term.
  have h_middle : H.map (tateModule g) (cocycle g).extension.g 2 (etaClass g) = 0 := by
    simp [etaClass, H.map, ShortComplex.ShortExact.comp_extClass_assoc]
  rw [h_lift, H.map_comp]
  exact (congrArg (H.map (tateModule g) b' 2) h_middle).trans (map_zero _)

/-- The class `η` pulls back to zero along a map `b` into the affine chart, where the first
coordinate of the row is a unit. -/
lemma pullbackAlong_etaClass_eq_zero_of_isUnit (b : Y ⟶ projLineAlong g)
    (h_unit : ∀ (c : C) (x : Y c), IsUnit (unimodularRow (b c x)).fst) :
    pullbackAlong (freeAb.map b) (etaClass g).toTotalH = 0 := by
  -- The first coordinate of the row trivializes the cocycle.
  have h_zero : H.map (tateModule g) (freeAb.map b) 2 (etaClass g) = 0 := by
    refine map_etaClass_eq_zero_of_coboundary _ (fun c x ↦ ⟨(h_unit c x).unit⟩)
      fun c d f x ↦ Gm.ext.mpr ?_
    show (ringOf g).map f (unimodularRow (b c x)).fst =
      (rowUnit ((ringOf g).map f) (.of (b c x))).down.toMul.val *
        (unimodularRow (b d (Y.map f x))).fst
    rw [b.naturality_apply f x]
    exact congrArg Prod.fst (unimodularRow_map ((ringOf g).map f) (b c x))
  rw [pullbackAlong_of, h_zero, map_zero]

/-- For sections `q`, `q'` of the projective line along `g`, the pullback of `η ∈ Ext²(ℤ[ℙ¹], T)`
(`T` the Tate module) along `q + q'` is supported where `q = q'`. That is, there is a family of
ideals `J` such that `q` and `q'` agree where `J` is zero, and the class comes from a class `ξ`
relative to the locus where `J` is the unit ideal. -/
lemma exists_etaClass_supported_diagonal (q q' : (projLineAlong g).sections) :
    ∃ J : IdealFamily (ringOf g), (∀ c : C, J.ideal c = ⊥ → q.val c = q'.val c) ∧
      ∃ ξ : H (relFreeAb J.topLocus) (tateModule g) 2,
        pullbackAlong (relFreeAb.π J.topLocus) ξ.toTotalH =
          pullbackAlong (freeAbSectionMap q + freeAbSectionMap q') (etaClass g).toTotalH := by
  -- Let `J c` be generated by the determinant of the rows of `q c` and `q' c`. Where it is a unit,
  -- it trivializes the cocycle along `q + q'`, so the class dies there and is a relative class.
  -- A ring map `f` sends the determinant at `c` to a unit times the determinant at `d`.
  have h_gen {c d : C} (f : c ⟶ d) : ((ringOf g).map f).hom (rowDet (q.val c) (q'.val c)) =
      (rowUnit ((ringOf g).map f) (.of (q.val c) + .of (q'.val c))).down.toMul.val *
        rowDet (q.val d) (q'.val d) := by
    rw [← q.property f, ← q'.property f]
    exact map_rowDet ((ringOf g).map f) (q.val c) (q'.val c)
  let J : IdealFamily (ringOf g) := ⟨fun c ↦ span {rowDet (q.val c) (q'.val c)}, fun f ↦ by
    rw [map_span, Set.image_singleton, h_gen f, span_singleton_mul_left_unit (Units.isUnit _)]⟩
  refine ⟨J, fun c h_bot ↦
    -- Where `J c` is zero the determinant is zero, so the points agree.
    eq_iff_unimodularRow_fst_mul_snd_eq.mpr (sub_eq_zero.mp (span_singleton_eq_bot.mp h_bot)), ?_⟩
  have h_dies : H.map (tateModule g)
      (freeAb.map J.topLocus.ι ≫ (freeAbSectionMap q + freeAbSectionMap q')) 2
      (etaClass g) = 0 :=
    -- The unit at `c` is the determinant, and `f` rescales it by the cocycle (`map_rowDet`).
    map_etaClass_eq_zero_of_coboundary _ (fun c x ↦ ⟨(span_singleton_eq_top.mp x.property).unit⟩)
      fun c d f x ↦ Gm.ext.mpr (h_gen f)
  rw [H.map_comp] at h_dies
  -- Exactness at `H² (ℤ[pt], T)` of the sequence of the pair `(pt, J.topLocus)`.
  obtain ⟨_, h_exact : ShortComplex.ShortExact _⟩ := relFreeAb.shortExact J.topLocus
  obtain ⟨ξ, hξ⟩ : ∃ ξ : H (relFreeAb J.topLocus) (tateModule g) 2,
      H.map (tateModule g) (relFreeAb.π J.topLocus) 2 ξ =
        H.map (tateModule g) (freeAbSectionMap q + freeAbSectionMap q') 2 (etaClass g) :=
    Ext.contravariant_sequence_exact₂ h_exact _ _ h_dies
  exact ⟨ξ, by rw [pullbackAlong_of, pullbackAlong_of, hξ]⟩

/-- `mapThenComp Φ u x` is `Φ x` followed by `u`. -/
private lemma mapThenComp_eq_comp_map {E E' : Type 1} [Category E] [Category E']
    (Φ : AbFunctor E ⥤ AbFunctor E') [IsExactFunctor Φ] {N F : AbFunctor E} {K : AbFunctor E'}
    (u : TotalH (Φ.obj F) K) (x : TotalH N F) :
    mapThenComp Φ u x = comp (map Φ x) u :=
  rfl

namespace TorsionCoeff

variable [InvertsPrime A ℓ]
  (M K : TorsionCoeff g) (M' : TorsionCoeff (φ ⋙ g)) (T : TotalH (φ ⋙ K.functor) M'.functor)

/-- The product with `η` at `b : ℤ[pt] ⟶ ℤ[ℙ¹]`, an additive map in `b`: the class in `Ext²(M, M)`
of the composite `M → M ⊗ ℤ[ℙ¹] → (M ⊗ T)[2] → M[2]` of `x ↦ x ⊗ b` (`tensorPoint b`), of `M ⊗ η`
(`etaTensorClass`) and of the action `M.tateAction` of the Tate module `T`. -/
@[irreducible]
def etaAt : (freeAb (onePointFunctor C) ⟶ freeAb (projLineAlong g)) →+ H M.functor M.functor 2 :=
  AddMonoidHom.mk'
    (fun b ↦ H.map M.functor (tensorPoint b M.functor) 2
      ((etaTensorClass g M.functor).comp M.tateAction rfl))
    fun a b ↦ by
      have h_add : tensorPoint (a + b) M.functor = tensorPoint a M.functor + tensorPoint b
        M.functor := by
        ext
        apply TensorProduct.tmul_add
      simp [H.map, h_add, Ext.mk₀_add]

/-- As a total class, `M.etaAt b` is the pullback along `x ↦ x ⊗ b` of the product of `M ⊗ η` and
`M.tateAction`. -/
lemma toTotalH_etaAt (b : freeAb (onePointFunctor C) ⟶ freeAb (projLineAlong g)) :
    (M.etaAt b).toTotalH = pullbackAlong (tensorPoint b M.functor)
      (comp (etaTensorClass g M.functor).toTotalH M.tateAction.toTotalH) := by
  rw [comp_of (h := rfl), pullbackAlong_of, etaAt, AddMonoidHom.mk'_apply]
  -- the degrees `2` and `2 + 0` agree by definition
  rfl

/-- The product of a class `y` from `S` to `M` with `M.etaAt b` is the composite of `x ↦ x ⊗ b`,
`S ⊗ η`, `y ⊗ T` and the action `M.tateAction`. -/
lemma comp_etaAt (b : freeAb (onePointFunctor C) ⟶ freeAb (projLineAlong g))
    (y : TotalH S M.functor) :
    comp y (M.etaAt b).toTotalH = pullbackAlong (tensorPoint b S)
      (comp (etaTensorClass g S).toTotalH
        (mapThenComp (abTensor.flip (tateModule g)) M.tateAction.toTotalH y)) := by
  -- Both `tensorPoint b` and `etaTensorClass g` are natural in the coefficient: move `y` past them.
  have h_point : comp y (homClass (tensorPoint b M.functor)) =
      pullbackAlong (tensorPoint b S) (map (abTensor.flip (freeAb (projLineAlong g))) y) := by
    nth_rw 1 [← TotalH.map_id (x := y)]
    exact y.naturality (tensorPoint b)
  calc comp y (M.etaAt b).toTotalH
      = comp y (comp (homClass (tensorPoint b M.functor))
          (comp (etaTensorClass g M.functor).toTotalH M.tateAction.toTotalH)) :=
        congrArg (comp y) (toTotalH_etaAt M b)
    _ = comp (homClass (tensorPoint b S)) (comp (map (abTensor.flip (freeAb (projLineAlong g))) y)
          (comp (etaTensorClass g M.functor).toTotalH M.tateAction.toTotalH)) :=
        TotalH.comp_assoc_of_sq h_point _
    _ = comp (homClass (tensorPoint b S)) (comp (etaTensorClass g S).toTotalH
          (comp (map (abTensor.flip (tateModule g)) y) M.tateAction.toTotalH)) :=
        congrArg (comp (homClass (tensorPoint b S)))
          (TotalH.comp_assoc_of_sq (etaTensorClass_naturality y) _)

/-- Let `K` be a coefficient along `g`, `M'` one along `φ ⋙ g`, and `T` (not the Tate module) a
class of any degree in total Ext from `K` restricted along `φ` to `M'`. Then `T` commutes with the
product with `η` at `b`: restricting `K.etaAt b` along `φ` and composing with `T` is `T` followed by
`M'.etaAt` at `b` restricted. -/
lemma etaAt_naturality (b : freeAb (onePointFunctor C) ⟶ freeAb (projLineAlong g)) :
    mapThenComp (restrictAlong φ) T (K.etaAt b).toTotalH =
      comp T (M'.etaAt (φ.whiskerLeft b)).toTotalH := by
  -- `T` commutes with `tateAction`, and `etaTensorClass` is compatible with restriction along `φ`.
  calc mapThenComp (restrictAlong φ) T (K.etaAt b).toTotalH
      = comp (map (restrictAlong φ) (comp (homClass (tensorPoint b K.functor))
          (comp (etaTensorClass g K.functor).toTotalH K.tateAction.toTotalH))) T :=
        congrArg (fun x ↦ comp (map (restrictAlong φ) x) T) (toTotalH_etaAt K b)
    _ = comp (homClass (tensorPoint (φ.whiskerLeft b) (φ ⋙ K.functor)))
          (comp (etaTensorClass (φ ⋙ g) (φ ⋙ K.functor)).toTotalH
            (mapThenComp (restrictAlong φ) T K.tateAction.toTotalH)) := by
        rw [map_comp_assoc, map_comp_assoc, mapThenComp_eq_comp_map, map_homClass,
          map_restrictAlong_etaTensorClass]
        -- the sides differ only in implicit objects, `(restrictAlong φ).obj F` against `φ ⋙ F`
        rfl
    _ = comp (homClass (tensorPoint (φ.whiskerLeft b) (φ ⋙ K.functor)))
          (comp (etaTensorClass (φ ⋙ g) (φ ⋙ K.functor)).toTotalH
            (comp (map (abTensor.flip (tateModule (φ ⋙ g))) T) M'.tateAction.toTotalH)) := by
        rw [K.tateAction_comm φ M' T]
    _ = comp T (M'.etaAt (φ.whiskerLeft b)).toTotalH := (comp_etaAt M' (φ.whiskerLeft b) T).symm

/-- Pulling `M.mulClass ζ y` back along `x ↦ x ⊗ σ` equals pulling `M.mulClass (σ^* ζ) y` back along
`x ↦ x ⊗ 1`, where `σ^* ζ` is `ζ` pulled back along `σ`. -/
private lemma pullbackAlong_tensorPoint_mulClass {S : AbFunctor C} [HasFlatValues S]
    {Q : AbFunctor C} (σ : freeAb (onePointFunctor C) ⟶ Q) (ζ : TotalH Q (tateModule g))
    (y : TotalH S M.functor) :
    pullbackAlong (tensorPoint σ S) (M.mulClass ζ y) =
      pullbackAlong (tensorPoint (𝟙 (freeAb (onePointFunctor C))) S)
        (M.mulClass (pullbackAlong σ ζ) y) := by
  -- `x ↦ x ⊗ σ` is `x ↦ x ⊗ 1` followed by `S ⊗ σ`, by definition
  have h_tp : tensorPoint σ S =
      tensorPoint (𝟙 (freeAb (onePointFunctor C))) S ≫ (abTensor S).map σ := rfl
  have h_map : map (abTensor S) (pullbackAlong σ ζ) =
      pullbackAlong ((abTensor S).map σ) (map (abTensor S) ζ) :=
    map_pullbackAlong
  rw [h_tp, ← pullbackAlong_pullbackAlong, mulClass_apply, mulClass_apply, h_map, comp_assoc]
  rfl -- `pullbackAlong` is composition with `homClass`

/-- Let `S` have flat values. If `ξ` pulled back along `ρ` is `η` pulled back along `b`, then the
product `M.mulClass ξ y` of `y` with `ξ`, pulled back along `x ↦ x ⊗ ρ`, is the product of `y`
with `M.etaAt b`. -/
lemma mulClass_eq_comp_etaAt [HasFlatValues S] {P : AbFunctor C} (ξ : TotalH P (tateModule g))
    (ρ : freeAb (onePointFunctor C) ⟶ P) {b : freeAb (onePointFunctor C) ⟶ freeAb (projLineAlong g)}
    (hξ : pullbackAlong ρ ξ = pullbackAlong b (etaClass g).toTotalH) (y : TotalH S M.functor) :
    pullbackAlong (tensorPoint ρ S) (M.mulClass ξ y) = comp y (M.etaAt b).toTotalH := by
  -- For flat `S` the class `etaTensorClass g S` is `S ⊗ η`, so the right side is the product of `y`
  -- with `η` pulled back along `x ↦ x ⊗ b`. Move both pullbacks to `x ↦ x ⊗ 1` and use `hξ`.
  have h_right : comp y (M.etaAt b).toTotalH =
      pullbackAlong (tensorPoint b S) (M.mulClass (etaClass g).toTotalH y) := by
    rw [comp_etaAt, etaTensorClass_of_hasFlatValues, mulClass_apply]
    rfl -- the sides differ only in implicit objects
  rw [h_right, pullbackAlong_tensorPoint_mulClass M ρ ξ y,
    pullbackAlong_tensorPoint_mulClass M b (etaClass g).toTotalH y, hξ]

/-- For `S` with flat values, the product of every class `y` from `S` to `M` with `η` at the base
point of the line is zero. -/
lemma comp_etaAt_basePt [HasFlatValues S] (y : TotalH S M.functor) :
    comp y (M.etaAt (freeAbSectionMap (basePt g))).toTotalH = 0 := by
  -- The row of the base point has a unit as first coordinate, so `η` pulls back to zero.
  have h_zero : pullbackAlong (freeAbSectionMap (basePt g)) (etaClass g).toTotalH = 0 :=
    pullbackAlong_etaClass_eq_zero_of_isUnit (sectionMap (basePt g)) fun _ _ ↦
      isUnit_unimodularRow_affinePt_iff.mpr isUnit_one
  have h_mul_zero : M.mulClass (0 : TotalH (freeAb (onePointFunctor C)) (tateModule g)) y = 0 := by
    simp [mulClass]
  -- With `ρ = 𝟙`, the product with `η` at the base point is the product with `0`.
  rw [← M.mulClass_eq_comp_etaAt
      (pullbackAlong (freeAbSectionMap (basePt g)) (etaClass g).toTotalH)
      (𝟙 (freeAb (onePointFunctor C))) pullbackAlong_id y,
    h_zero, h_mul_zero, map_zero]

/-- The product with `η` on the category of points of the line: `etaAt` at the tautological
point. -/
abbrev cupClass :
    H (M.onElements (X := projLineAlong g)).functor (M.onElements (X := projLineAlong g)).functor
      2 :=
  M.onElements.etaAt (freeAb.map (tautologicalSection (X := projLineAlong g)))

/-- The degrees of the classes `1` (index `true`) and `η` (index `false`). -/
abbrev lineDegree : Bool → ℕ
  | true => 0
  | false => 2

/-- The two classes `1` (index `true`, degree 0) and `η` (index `false`, degree 2) on the category
of points of the line. -/
def lineBasis : ∀ i : Bool, H (restrictAlong (elementsProj (projLineAlong g)) M.functor)
    (elementsProj (projLineAlong g) ⋙ M.functor) (lineDegree i)
  | true => Ext.mk₀ (𝟙 (elementsProj (projLineAlong g) ⋙ M.functor))
  | false => M.cupClass

lemma lineBasis_true :
    M.lineBasis true = Ext.mk₀ (𝟙 (elementsProj (projLineAlong g) ⋙ M.functor)) := rfl

lemma lineBasis_false : M.lineBasis false = M.cupClass := rfl

/-- The projective line formula `H(ℙ¹ × S) = H(S) ⊕ η H(S)`: the classes `1` and `η` are a basis
over the cohomology of every `S`. -/
def HasLineFormula : Prop := ∀ S : AbFunctor C, IsLerayHirschBasis M.lineBasis S

/-- Restricting `M.etaAt b` to the category of points of `X` gives `etaAt` of the restrictions. -/
lemma map_etaAt_onElements (X : C ⥤ Type 1)
    (b : freeAb (onePointFunctor C) ⟶ freeAb (projLineAlong g)) :
    map (restrictAlong (elementsProj X)) (M.etaAt b).toTotalH =
      (M.onElements.etaAt ((elementsProj X).whiskerLeft b)).toTotalH := by
  -- `etaAt_naturality` for the identity class of `M` restricted to the points of `X`
  exact comp_id.symm.trans ((etaAt_naturality (elementsProj X) M M.onElements
    (homClass (𝟙 (elementsProj X ⋙ M.functor))) b).trans pullbackAlong_id)

end TorsionCoeff

end EtaProduct

end New.Variety

end
