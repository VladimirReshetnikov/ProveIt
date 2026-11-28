import Lib.PadicComparison.Completion
import Lib.PadicComparison.ToricTower

/-!
# Divided power envelopes, lifts modulo divided powers, and one divided power variable

For a prime `p` (fixed by the class `New.ThePrime p`) and a `p`-torsion-free, `p`-adically
complete ring `S` (`New.Variety.IsCompleteTorsionFree`), `New.Variety.pdIdeal S` is the ideal of the
`x` with `n ! ∣ x ^ n` for all `n`. The file proves lifting results along `S → S ⧸ pdIdeal S`. It
then constructs the divided power envelope of a subset `J` of `T` and proves its universal property.
Finally it treats one divided power variable `z = t - v`.

## Main definitions and results

* `New.Variety.IsCompleteTorsionFree.monoidHom_lift_bijective`,
  `New.Variety.IsCompleteTorsionFree.existsUnique_witt_lift`: multiplicative maps from a perfect
  monoid, and ring maps from a perfect ring via its Witt vectors, lift uniquely from `S ⧸ pdIdeal S`
  to `S`.
* `New.Variety.IsCompletionBijective.comp_bijective`: maps to a `p`-complete ring extend uniquely
  along a map that is bijective modulo every power of `p` (`New.Variety.IsCompletionBijective`).
* `New.Variety.preEnvelope`, `New.Variety.Envelope`: adjoin the `x ^ n / n !`, `x ∈ J`, inside
  `T ⊗ ℚ`, then complete; `New.Variety.Envelope.existsUnique_lift` is the universal property.
* `New.Variety.exists_preEnvelope_basis`: if `T` has the `B`-basis `u a * v ^ n`, the uncompleted
  envelope of `z = t - v` has the basis `u a * z ^ n / n !`.
* `New.Variety.koszulExact_pd_line`: take an endomorphism `γ` that scales the unit `v` by `1 + q`
  with `p ^ 3 ∣ q`. It must also scale each `u a` with `a ≠ 0` by `1 + η` with `p * η ∣ q`, and
  `u 0 = 1`. Then the sequence `0 → B → E → E → 0` given by `γ - 1` is exact after a base change
  that inverts `q`. The proof uses a shift `S` of the basis such that `(γ - 1) S` is `q * v` times
  `1 - p W` for an endomorphism `W`.

Notions from other files:
* `New.Variety.CrysTest`: the category of `p`-torsion-free, `p`-adically complete `S`-algebras
  (`New.Variety.IsCompleteTorsionFree`); an object `E` is read as its underlying ring.
* `New.Variety.KoszulExact`: for a map `i` and an endomorphism `g`, the map `i` is injective, every
  fixed point of `g` lies in the image of `i`, and `z ↦ g z - z` is onto.

## Relation to the literature

Known; see `Lib.PadicComparison.Crystalline.ComparisonMap` for sources.
-/

noncomputable section

/-! ## Lifts modulo divided powers and the divided power envelope -/

section DividedPowerEnvelope

open CategoryTheory CommAlgCat Ideal Quotient Nat Function Algebra TensorProduct Perfection
  WittVector IsScalarTower nonZeroDivisors AlgHom DFunLike

namespace New.Variety

variable {p : ℕ} [hp : ThePrime p] {S : Type}
  {T : Type _} [CommRing S] [CommRing T] [Algebra S T] {x : T}
  {M : Type*} [CommMonoid M] [PerfectRing M p] (E : CrysTest S)

/-! ### Lifting modulo the divided power ideal -/

/-- For p not a unit in S, the ring homomorphism S/𝔡(S) → S/p induced by x ↦ x^p, where 𝔡(S) is
the ideal of elements with divided powers. -/
def frobModPd [Fact ¬IsUnit (p : S)] : S ⧸ pdIdeal S →+* ModP S p :=
  -- The `p`-th power of `x ∈ pdIdeal S` vanishes modulo `p`, because `p ∣ p ! ∣ x ^ p`.
  Ideal.Quotient.lift (pdIdeal S) ((frobenius _ p).comp (mk _)) fun _ hx ↦
    (eq_zero_iff_dvd ..).2 ((dvd_factorial Fin.pos' le_rfl).natCast.trans (hx p))

/-- In a `p`-torsion-free, `p`-complete ring `S`, `p` has divided powers: `n !` divides `p ^ n`. -/
lemma IsCompleteTorsionFree.p_mem_pdIdeal (h : IsCompleteTorsionFree S) : ↑p ∈ pdIdeal S := by
  -- Write `n! = p ^ v * m` with `m` prime to `p`. Then `m` is a unit, since `p` lies in the
  -- Jacobson radical of the `p`-complete ring `S`, and `v ≤ n`.
  intro n
  obtain ⟨a, b, hab⟩ := (coprime_ordCompl hp.out n.factorial_ne_zero).cast (R := S)
  have h_unit : IsUnit ((p : S) * -a + 1) :=
    mem_jacobson_bot.mp (h.complete.le_jacobson_bot _ (subset_span rfl)) (-a)
  have h_fact : (n ! : S) ∣ p ^ padicValNat p n ! := by
    refine h_unit.dvd_mul_right.mp ⟨b, ?_⟩
    -- multiply `a * p + b * m = 1` by `p ^ v` and use `p ^ v * m = n !`
    have h_split : ((p ^ (n !).factorization p * (n ! / p ^ (n !).factorization p) : ℕ) : S) =
        (n ! : S) :=
      congrArg (Nat.cast : ℕ → S) (ordProj_mul_ordCompl_eq_self n ! p)
    grind [factorization_def, hp.out]
  exact h_fact.trans (pow_dvd_pow _ (padicValNat_factorial_le p n))

/-- If `S` is `p`-torsion-free and `p`-complete, the quotient map `S → S ⧸ pdIdeal S` is a local
homomorphism: an element whose class is a unit is a unit. -/
lemma IsCompleteTorsionFree.isLocalHom_pdQuotientMk (h : IsCompleteTorsionFree S) :
    IsLocalHom (pdQuotientMk S) := by
  -- If `x ∈ pdIdeal S` then `p ∣ p ! ∣ x ^ p`, so `x ^ p` lies in the Jacobson radical, which is a
  -- radical ideal.
  refine isLocalHom_of_le_jacobson_bot _ fun x hx ↦
    isRadical_jacobson _ ⟨p, h.complete.le_jacobson_bot _ ?_⟩
  grw [mem_span_singleton, ← hx p, ← dvd_factorial Fin.pos' le_rfl]

/-- Let `S` be `p`-torsion-free and `p`-complete, and `M` a commutative monoid on which `x ↦ x ^ p`
is bijective. Composition with the quotient map `S → S ⧸ pdIdeal S` is a bijection from `M →* S`
to `M →* S ⧸ pdIdeal S`. -/
lemma IsCompleteTorsionFree.monoidHom_lift_bijective (h : IsCompleteTorsionFree S) :
    Bijective ((pdQuotientMk S).toMonoidHom.comp : (M →* S) → (M →* S ⧸ pdIdeal S)) := by
  -- Reduction factors as `S → S / p → S / pdIdeal S`; both steps are bijective on maps from `M`.
  have h_complete : IsAdicComplete (span {(p : S)}) S := h.complete
  nontriviality S using bijective_iff_existsUnique, ExistsUnique, ext_iff
  -- `S → S / p`: maps from `M` lift uniquely to the perfections, which agree for `S` and `S / p`.
  let modP : (M →* Perfection S p) ≃ (M →* S ⧸ span {(p : S)}) :=
    (quotientMulEquiv p (span {(p : S)})).monoidHomCongrRightEquiv.trans
      (liftMonoidHom p M (S ⧸ span {(p : S)})).toEquiv.symm
  -- `S / p → S / pdIdeal S`: the inverse sends `x` to `m ↦ frobModPd (x (m ^ (1 / p)))`.
  have h_span_le : span {(p : S)} ≤ pdIdeal S := by simpa using h.p_mem_pdIdeal
  let red : S ⧸ span {(p : S)} →+* S ⧸ pdIdeal S := factor h_span_le
  -- On representatives both composites are `x ↦ x ^ p`.
  have h_left : ∀ y : S ⧸ span {(p : S)}, frobModPd (red y) = y ^ p := Quot.ind fun _ ↦ rfl
  have h_right : ∀ y : S ⧸ pdIdeal S, red (frobModPd y) = y ^ p := Quot.ind fun _ ↦ rfl
  have h_root_pow {N : Type} [Monoid N] (x : M →* N) (m : M) :
      x ((powMulEquiv M p).symm m) ^ p = x m := by simp [← map_pow x]
  let modDp : (M →* S ⧸ span {(p : S)}) ≃ (M →* S ⧸ pdIdeal S) :=
    { toFun := red.toMonoidHom.comp
      invFun x := frobModPd.toMonoidHom.comp (x.comp (powMulEquiv M p).symm)
      left_inv x := MonoidHom.ext fun m ↦ (h_left _).trans (h_root_pow x m)
      right_inv x := MonoidHom.ext fun m ↦ (h_right _).trans (h_root_pow x m) }
  exact ((liftMonoidHom p M S).symm.bijective.of_comp_iff _).mp (modP.trans modDp).bijective

/-- Let `S` be `p`-torsion-free and `p`-complete, and `b` a perfect ring with `p = 0`. Each ring
map `f : b → S ⧸ pdIdeal S` has a unique lift `g : W(b) → S`: the class of `g x` modulo
`pdIdeal S` is `f` of the zeroth Witt coefficient of `x`, for every Witt vector `x`. -/
lemma IsCompleteTorsionFree.existsUnique_witt_lift (h : IsCompleteTorsionFree S) {b : Type*}
    [CommRing b] [PerfectRing b p] (hp_zero : (p : b) = 0) (f : b →+* S ⧸ pdIdeal S) :
    ∃! g : WittVector p b →+* S, ∀ x : WittVector p b, pdQuotientMk S (g x) = f (x.coeff 0) := by
  have h_complete : IsAdicComplete (span {(p : S)}) S := h.complete
  have h_span_le : span {(p : S)} ≤ pdIdeal S := by simpa using h.p_mem_pdIdeal
  by_cases! h_sub : Subsingleton S
  · -- Over the zero ring the constant map is the only ring map.
    use .mk' 1 ?_
    · simp [nontriviality, RingHom.ext_iff]
    · simp [nontriviality]
  have h_nontrivial : Nontrivial b := (frobModPd.comp f).domain_nontrivial
  have h_charP : CharP b p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hp_zero
  -- `frobModPd ∘ f : b → S / p` lifts to the tilt of `S`. Undo the Frobenius in `frobModPd` by a
  -- `p`-th root, pass to Witt vectors and apply Fontaine's `θ`.
  let toTilt : b →+* PreTilt S p :=
    (pthRoot (ModP S p) p).comp (lift p b (ModP S p) (frobModPd.comp f))
  refine existsUnique_of_exists_of_unique
    ⟨(fontaineTheta S p).comp (WittVector.map toTilt), fun x ↦ ?_⟩ fun g g' hg hg' ↦ ?_
  · let red : S ⧸ span {(p : S)} →+* S ⧸ pdIdeal S := factor h_span_le
    have h_frob : ∀ y : S ⧸ pdIdeal S, red (frobModPd y) = y ^ p := Quot.ind fun _ ↦ rfl
    -- Modulo `p`, `θ` reads the zeroth coefficient, here `frobModPd (f r)` for the `p`-th root `r`
    -- of `x₀`; and `f r ^ p = f x₀`.
    let r : b := (frobeniusEquiv b p).symm (x.coeff 0)
    calc pdQuotientMk S ((fontaineTheta S p).comp (WittVector.map toTilt) x)
        = red (PreTilt.coeff 0 ((WittVector.map toTilt x).coeff 0)) :=
          congrArg red (mk_fontaineTheta (WittVector.map toTilt x))
      _ = red (frobModPd (f r)) := rfl
      _ = f r ^ p := h_frob (f r)
      _ = f (x.coeff 0) := by simp [r, ← f.map_pow]
  · -- Two lifts agree on Teichmüller representatives, which determine a ring map on Witt vectors
    -- since `S` is `p`-adically separated.
    have h_teich : g.toMonoidHom.comp (teichmuller p) = g'.toMonoidHom.comp (teichmuller p) :=
      h.monoidHom_lift_bijective.injective (by ext; simp [hg, hg'])
    exact wittVector_ringHom_ext_of_teichmuller fun x ↦ DFunLike.congr_fun h_teich x

omit [ThePrime p] in
/-- If a map κ: C → W of S-algebras is bijective modulo every power of p and the S-algebra X is
p-adically complete, then composition with κ is a bijection Hom(W, X) → Hom(C, X). -/
lemma IsCompletionBijective.comp_bijective {C W X : CommAlg S} (κ : C ⟶ W)
    (hκ : IsCompletionBijective p κ.hom.toLinearMap) (hX : IsAdicComplete (span {(p : X)}) X) :
    Bijective (fun g : W ⟶ X ↦ κ ≫ g : (W ⟶ X) → (C ⟶ X)) := by
  -- Linear maps extend uniquely (`IsCompletionBijective.linearMap_comp_bijective`); uniqueness
  -- makes the extension multiplicative.
  have hX_base : IsAdicComplete (span {(p : S)}) X := isAdicComplete_over_base (S := S) hX
  obtain ⟨h_inj, h_surj⟩ := hκ.linearMap_comp_bijective (Y := X)
  refine ⟨fun f g hfg ↦ hom_ext (AlgHom.toLinearMap_injective (h_inj ?_)), fun f ↦ ?_⟩
  · exact congrArg (fun u : C ⟶ X ↦ u.hom.toLinearMap) hfg
  obtain ⟨G, hG⟩ := h_surj f.hom.toLinearMap
  have hGκ (t : C) : G (κ t) = f t := LinearMap.congr_fun hG t
  -- `y ↦ G (x * y)` and `y ↦ G x * G y` are linear, so agree if they do on the image of `κ`.
  have h_mul_of_image (x : W) (hx : ∀ t : C, G (x * κ t) = G x * G (κ t)) (y : W) :
      G (x * y) = G x * G y :=
    have h_lin : G ∘ₗ .mulLeft S x = .mulLeft S (G x) ∘ₗ G := h_inj (LinearMap.ext hx)
    LinearMap.congr_fun h_lin y
  -- Use this twice: first for a left factor in the image of `κ`, then for any left factor.
  have h_image (t u : C) : G (κ t * κ u) = G (κ t) * G (κ u) := by simp only [← map_mul, hGκ]
  have hG_mul_left (t : C) : ∀ y : W, G (κ t * y) = G (κ t) * G y :=
    h_mul_of_image (κ t) (h_image t)
  have h_right (x : W) (t : C) : G (x * κ t) = G x * G (κ t) := by
    rw [mul_comm, hG_mul_left, mul_comm]
  have hG_mul (x y : W) : G (x * y) = G x * G y := h_mul_of_image x (h_right x) y
  have hG_one : G 1 = 1 := by simpa using hGκ 1
  exact ⟨ofHom (.ofLinearMap G hG_one hG_mul), hom_ext (AlgHom.ext hGκ)⟩

/-- A test object is read as its underlying type. -/
instance : CoeSort (CrysTest S) Type := ⟨(·.obj)⟩

/-- A `p`-torsion-free `p`-complete algebra has no additive torsion: `n` divides `p ^ n` there. -/
instance : HasUniqueDiv E where
  nsmul_right_injective n hn x y hxy := by
    -- `n ∣ n ! ∣ p ^ n`, and `p ^ n` can be cancelled.
    obtain ⟨c, hc⟩ : (n ! : E) ∣ p ^ n := E.property.p_mem_pdIdeal n
    have h_fact : ((n * (n - 1) ! : ℕ) : E) = (n ! : E) :=
      congrArg (Nat.cast : ℕ → E) (mul_factorial_pred hn)
    refine E.property.regular.pow n ?_
    grind

/-- In a `p`-torsion-free `p`-complete algebra `E`, `p` vanishes modulo `pdIdeal E`. -/
lemma CrysTest.p_eq_zero_mod_pdIdeal : (p : E ⧸ pdIdeal E) = 0 :=
  eq_zero_iff_mem.mpr E.property.p_mem_pdIdeal

variable (S) (J : Set T)

/-! ### The divided power envelope -/

/-- For a subset J of T, the T-subalgebra of T ⊗_ℤ ℚ generated by the divided powers x^n/n! with
x in J and n ≥ 0. -/
def preEnvelope : Subalgebra T (T ⊗[ℤ] ℚ) := adjoin T {(x ^ n) ⊗ₜ[ℤ] (n ! : ℚ)⁻¹ | (x ∈ J) (n : ℕ)}

/-- The divided power envelope of T along J: the p-adic completion of `New.Variety.preEnvelope`, as
a p-torsion-free p-complete S-algebra. -/
abbrev Envelope : CrysTest S where
  obj := CommAlgCat.of S (PrincipalCompletion (preEnvelope J) p)
  property := isCompleteTorsionFree_completion fun x y hxy ↦ by
    -- `preEnvelope J` has no `p`-torsion because `p` is a unit of `T ⊗ ℚ`.
    have h_unit : IsUnit (includeRight (p : ℚ) : T ⊗[ℤ] ℚ) :=
      (isUnit_of_invertible _).map includeRight
    exact Subtype.ext (h_unit.mul_left_cancel (by simpa using congrArg Subtype.val hxy))

/-- Universal property of the envelope: an S-algebra map h from T to a p-torsion-free p-complete
S-algebra B that sends J into the elements with divided powers factors uniquely through the
canonical map from T to the envelope of J. -/
lemma Envelope.existsUnique_lift {B : CrysTest S} (h : T →ₐ[S] B.obj)
    (hJ : ∀ x ∈ J, h x ∈ pdIdeal B.obj) :
    ∃! g : Envelope S J ⟶ B, g.hom.hom.comp (toAlgHom S T (Envelope S J).obj) = h := by
  let algebra_T_B : Algebra T B.obj := h.toRingHom.toAlgebra
  -- In `B ⊗ ℚ` the generators `x ^ n / n!` of `preEnvelope J` land in `B`, as `n! ∣ h x ^ n`.
  have h_range : preEnvelope J ≤ .comap (rTensor ℚ (ofId T B.obj)) includeLeft.range := by
    refine adjoin_le fun y ⟨x, hx, n, hy⟩ ↦ (hJ x hx n).imp fun c hc ↦ ?_
    -- `h x ^ n ⊗ (n!)⁻¹ = (n! • c) ⊗ (n!)⁻¹ = c ⊗ (n! • (n!)⁻¹) = c ⊗ 1`
    have h_tmul : (n ! • c) ⊗ₜ[ℤ] (n ! : ℚ)⁻¹ = c ⊗ₜ[ℤ] (n ! • (n ! : ℚ)⁻¹) := smul_tmul n ! c _
    have h_alg : algebraMap T B.obj x = h x := rfl
    simpa [← hy, ← hc, factorial_ne_zero, h_alg] using h_tmul.symm
  -- `B` is torsion-free, so it is isomorphic to its image in `B ⊗ ℚ`; as `preEnvelope J` maps
  -- into that image, we get a map `F : preEnvelope J → B`.
  let e_B : B.obj ≃ₐ[T] (includeLeft : B.obj →ₐ[T] B.obj ⊗[ℤ] ℚ).range :=
    AlgEquiv.ofInjective _ (includeLeft_injective Int.cast_injective)
  let F_range : preEnvelope J →ₐ[T] (includeLeft : B.obj →ₐ[T] B.obj ⊗[ℤ] ℚ).range :=
    ((rTensor ℚ (ofId T B.obj)).comp (preEnvelope J).val).codRestrict _ fun x ↦ h_range x.property
  let F : preEnvelope J →ₐ[T] B.obj := e_B.symm.toAlgHom.comp F_range
  -- `F` extends uniquely to the completion, since `B` is `p`-complete: `hG` says that `G` extends
  -- `F`, and `h_uniq` that every extension is `G`.
  obtain ⟨G, hG, h_uniq⟩ :=
    (isCompletionBijective_completion.comp_bijective (ofHom _) B.property.complete).existsUnique
      (ofHom (F.restrictScalars S))
  refine ⟨⟨G⟩, AlgHom.ext fun t ↦ ?_, ?_⟩
  · -- `G` restricts to `F`, which is a `T`-algebra map
    have hG_apply : ∀ y : preEnvelope J,
        G (algebraMap (preEnvelope J) (Envelope S J).obj y) = F y := ConcreteCategory.congr_hom hG
    exact (hG_apply (algebraMap T (preEnvelope J) t)).trans (F.commutes t)
  · -- Uniqueness: `G'` restricts to `F` as well, since a nonzero integer multiple of any element
    -- of `preEnvelope J` comes from `T` and `B` is torsion-free.
    rintro ⟨G'⟩ hG'
    refine congrArg _ (h_uniq G' (hom_ext (AlgHom.ext fun x ↦ ?_)))
    obtain ⟨⟨t, n⟩, hx⟩ := IsLocalizedModule.surj ℤ⁰ (toAlgHom ℤ T (T ⊗[ℤ] ℚ)).toLinearMap x.val
    have hx' : (n : ℤ) • x = ofId T _ t := Subtype.ext hx
    refine zsmul_right_injective (coe_ne_zero n) ?_
    have hG'_t : G' (algebraMap T (Envelope S J).obj t) = h t := DFunLike.congr_fun hG' t
    simp only [← AlgHom.map_smul_of_tower, hx']
    -- `using!` unfolds the algebra maps of the envelope.
    simpa using! hG'_t

/-- For a subset J of the S-algebra T and x in J, the image of x in the envelope E of T along J
lies in the ideal 𝔡(E) = `New.Variety.pdIdeal` E: n! divides its n-th power for every n. -/
lemma Envelope.algebraMap_mem_pdIdeal (hx : x ∈ J) :
    algebraMap T (Envelope S J) x ∈ pdIdeal (Envelope S J) := by
  -- Already in `preEnvelope J` the factorial `n!` divides `x ^ n`: the quotient is a generator.
  refine pdIdeal_le_comap (algebraMap (preEnvelope J) _) fun n ↦ ?_
  refine ⟨⟨(x ^ n) ⊗ₜ (n ! : ℚ)⁻¹, subset_adjoin ⟨x, hx, n, rfl⟩⟩, ?_⟩
  ext
  simp [natCast_def', factorial_ne_zero]

end New.Variety

end DividedPowerEnvelope

/-! ## A basis of the envelope of one element and exactness of γ − 1 -/

section DividedPowerLine

open Module Submodule Nat Polynomial Function Set Algebra LinearMap TensorProduct algebraMap

namespace New.Variety

variable {p : ℕ} [ThePrime p] {A : Type} [CommRing A] (B : CrysTest A)
  {T I : Type*} [CommRing T] [Algebra B T]

/-- Let B be a p-torsion-free, p-adically complete A-algebra (`New.Variety.CrysTest`), T a
B-algebra with a B-basis b indexed by I × ℕ with b(a, n) = u a * v ^ n, and z = t − v with t in B.
Then the subalgebra `New.Variety.preEnvelope {z}` of T ⊗ ℚ, generated over T by the z ^ n / n!,
contains elements y n with z ^ n = n! * y n, and the u a * y n form a B-basis c of it. -/
lemma exists_preEnvelope_basis (z : T) (b : Basis (I × ℕ) B T) (u : I → T) {v : T} {t : B}
    (hb : ∀ (a : I) (n : ℕ), b (a, n) = u a * v ^ n) (hz : t - v = z) :
    ∃ (y : ℕ → preEnvelope {z}) (c : Basis (I × ℕ) B (preEnvelope {z})),
      -- (a) the basis consists of the `u a * y n`
      (∀ (a : I) (n : ℕ), c (a, n) = u a * y n) ∧
      -- (b) the `y n` are the divided powers of `z`
      ∀ n : ℕ, z ^ n = n ! * y n := by
  classical
  -- First pass from the basis `u a * v ^ n` of `T` to the basis `b'` of the `u a * z ^ n`: the
  -- substitution `F : v ↦ t - v` is an involution.
  let F : T →ₗ[B] T := b.constr B fun j ↦ u j.fst * z ^ j.snd
  have hF : F * F = 1 := by
    refine b.ext fun (a, n) ↦ ?_
    -- `u a * (t - w) ^ n` expanded by the binomial formula
    have h_expand (w : T) : u a * (algebraMap B T t - w) ^ n =
        ∑ i ∈ .range (((C t - X) ^ n).natDegree + 1), ((C t - X) ^ n).coeff i • (u a * w ^ i) := by
      -- `(… :)`: with the polynomial ring written out, `simp` leaves `aeval` unsimplified.
      simpa using congrArg (mulLeft B (u a)) (((C t - X) ^ n :).aeval_eq_sum_range w)
    simp [F, h_expand, ← hb, ← h_expand, ← hz]
  let b' : Basis (I × ℕ) B T := b.map (.ofInvolutive F fun x ↦ LinearMap.congr_fun hF x)
  have hb' (j : I × ℕ) : u j.fst * z ^ j.snd = b' j :=
    (b.constr_basis B (fun j ↦ u j.fst * z ^ j.snd) j).symm
  -- The divided powers `y n = z ^ n / n !`.
  let y (n : ℕ) : preEnvelope {z} := ⟨(z ^ n) ⊗ₜ (n ! : ℚ)⁻¹, subset_adjoin ⟨z, rfl, n, rfl⟩⟩
  have hy (n : ℕ) : algebraMap T _ z ^ n = n ! * y n :=
    Subtype.ext (by simp [y, natCast_def', factorial_ne_zero])
  have hy_mul (n m : ℕ) : y n * y m = (n + m).choose n * y (n + m) := by
    ext
    simp only [MulMemClass.coe_mul, tmul_mul_tmul, pow_add, SubringClass.coe_natCast, natCast_def',
        cast_add_choose, one_mul, y]
    field_simp
  let w (j : I × ℕ) : preEnvelope {z} := algebraMap T _ (u j.fst) * y j.snd
  -- Independence: apply the coordinate `i` of `b'` to a relation in `T ⊗ ℚ`, multiply by `i.snd !`,
  -- and use that `B → B ⊗ ℚ` is injective.
  have h_indep : LinearIndependent B w := by
    refine linearIndependent_iff'.mpr fun s g hg i hi ↦ ?_
    apply includeLeft_injective (S := ℤ) (Int.cast_injective (α := ℚ))
    have h_val : ∑ j ∈ s, g j • (w j).val = 0 := by simpa using congrArg Subtype.val hg
    simpa [w, y, hb', Finsupp.single_apply, ite_tmul, hi, natCast_def', smul_tmul',
      factorial_ne_zero] using
      congrArg (fun e : T ⊗[ℤ] ℚ ↦ AlgebraTensorModule.rTensor ℤ ℚ (b'.coord i) e * i.snd !) h_val
  -- Spanning.
  have h_span : span B (Set.range w) = ⊤ := by
    refine top_unique ?_
    -- Over `B`, the envelope is spanned by the `b' i • x` with `x` a product of generators
    -- `z ^ n / n!`; so it suffices that these lie in the span of the `w`.
    suffices h_gen : ∀ (i : I × ℕ), ∀ x ∈ Submonoid.closure ((Subtype.val : preEnvelope {z} → _) ⁻¹'
        {(z' ^ n) ⊗ₜ[ℤ] (n ! : ℚ)⁻¹ | (z' ∈ ({z} : Set T)) (n : ℕ)}),
          b' i • x ∈ span B (Set.range w) by
      -- `erw`: `preEnvelope {z}` is `adjoin T _` only after unfolding its definition, and
      -- `adjoin_adjoin_coe_preimage` is stated for `adjoin`.
      erw [← restrictScalars_top _ T, ← top_toSubmodule, ← adjoin_adjoin_coe_preimage,
        adjoin_eq_span, ← span_smul_of_span_eq_top b'.span_eq, span_le, Set.smul_subset_iff,
        Set.forall_mem_range]
      exact h_gen
    rintro ⟨a, k⟩ x hx
    suffices key : ∀ n c : ℕ, algebraMap T _ (u a) * (c * y n) * x ∈ span B (Set.range w) by
      simpa [← hb', smul_def', hy] using key k k !
    -- Induction on the product `x`: a factor `y m` is absorbed into `c * y n` by `hy_mul`.
    induction hx using Submonoid.closure_induction_left with
    | one => simp [w, ← nsmul_eq_mul, nsmul_mem, mem_span_of_mem]
    | mul_left x hx x' _ ih =>
      intro n c
      obtain ⟨_, rfl, m, hm⟩ := hx
      obtain rfl : y m = x := Subtype.ext hm
      have h_eq : algebraMap T _ (u a) * (c * y n) * (y m * x') =
          algebraMap T _ (u a) * ((c * (n + m).choose n : ℕ) * y (n + m)) * x' := by
        push_cast
        linear_combination algebraMap T _ (u a) * c * x' * hy_mul n m
      rw [h_eq]
      exact ih (n + m) (c * (n + m).choose n)
  exact ⟨y, .mk h_indep h_span.ge, fun a n ↦ Basis.mk_apply h_indep h_span.ge (a, n), hy⟩

/-- Taylor's formula for divided powers in a `p`-torsion-free, `p`-complete algebra `E`: if
`y n = x ^ n / n !` and `γ x = x + p ^ 3 * z`, then
`γ (y (n + 1)) ≡ y (n + 1) + p ^ 3 * z * y n` modulo `p ^ 4 * z`. -/
lemma exists_map_dividedPow_succ (E : CrysTest A) (γ : E →+* E) {x z : E} {y : ℕ → E}
    (hy : ∀ n : ℕ, x ^ n = n ! * y n) (hγ : γ x = x + p ^ 3 * z) (n : ℕ) :
    ∃ w : E, γ (y (n + 1)) = y (n + 1) + p ^ 3 * z * (y n + p * w) := by
  -- `x` and `p` have divided powers, so `P = (x + p X) ^ (n + 1) / (n + 1)!` is a polynomial.
  have h_mem_pd : C x + X • C (p : E) ∈ pdIdeal E[X] :=
    (pdIdeal _).add_mem (pdIdeal_le_comap C fun n ↦ ⟨_, hy n⟩)
      (smul_mem _ X (pdIdeal_le_comap C E.property.p_mem_pdIdeal))
  obtain ⟨P, hP⟩ : ((n + 1)! : E[X]) ∣ (C x + X * C (p : E)) ^ (n + 1) := h_mem_pd (n + 1)
  -- Each value is checked after multiplying by `(n + 1)!`, which is regular in `E`.
  have h_reg : Function.Injective fun a : E.obj ↦ (n + 1)! • a :=
    nsmul_right_injective (M := E) (n + 1).factorial_ne_zero
  have h_eval_zero : P.eval 0 = y (n + 1) := by
    apply h_reg
    simpa [hy] using (congrArg (Polynomial.eval 0) hP).symm
  have h_deriv_zero : (derivative P).eval 0 = p * y n := by
    -- the derivative of `(x + p X) ^ (n + 1)` at `0` is `(n + 1) x ^ n p = (n + 1)! * y n * p`
    have h_deriv : (n + 1) * (n ! * y n) * p = (n + 1)! * (derivative P).eval 0 := by
      simpa [derivative_pow, hy] using congrArg (fun Q : E[X] ↦ (derivative Q).eval 0) hP
    apply h_reg
    push_cast [nsmul_eq_mul, factorial_succ] at h_deriv ⊢
    linear_combination -h_deriv
  have h_eval_pt : P.eval (p ^ 2 * z) = γ (y (n + 1)) := by
    have h₁ : (x + p ^ 2 * z * p) ^ (n + 1) = (n + 1)! * P.eval (p ^ 2 * z) := by
      simpa using congrArg (Polynomial.eval (p ^ 2 * z)) hP
    have h₂ : (x + p ^ 3 * z) ^ (n + 1) = (n + 1)! * γ (y (n + 1)) := by
      simpa [hγ] using congrArg γ (hy (n + 1))
    apply h_reg
    linear_combination h₂ - h₁
  -- Expand `P` at `0`: the remainder at `p ^ 2 * z` is a multiple of `p ^ 4 * z ^ 2`.
  obtain ⟨k, hk⟩ := P.binomExpansion 0 (p ^ 2 * z)
  rw [zero_add, h_eval_pt, h_eval_zero, h_deriv_zero] at hk
  refine ⟨z * k, ?_⟩
  linear_combination hk

/-- If the B-algebra E is p-torsion-free and p-adically complete, then 1 − p • W is bijective for
every B-linear endomorphism W of E. -/
lemma IsCompleteTorsionFree.bijective_one_sub_smul {E : Type} [CommRing E] [Algebra B E]
    (hE : IsCompleteTorsionFree E) (W : End B E) :
    Bijective (1 - (p : B) • W : End B E) := by
  refine ⟨fun x z hxz ↦ ?_, fun x ↦ ?_⟩
  · -- the sequences `W ^ i x` and `W ^ i z` have the same image under the injective map
    -- `shiftDiff E p : (x i) ↦ (x i - p • x (i + 1))`
    have h_shift :
        shiftDiff E (p : B) (fun i ↦ W^[i] x) = shiftDiff E (p : B) (fun i ↦ W^[i] z) := by
      funext i
      simpa [shiftDiff, ← End.pow_apply, pow_add] using congrArg (W^[i]) hxz
    exact congrFun (hE.isDerivedComplete.injective h_shift) 0
  · -- every `x` is in the image modulo `p`: `x = (1 - p W) x + p W x`
    exact hE.isDerivedComplete.exists_apply_eq_of_approx hE.isDerivedComplete (1 - (p : B) • W)
      (fun x ↦ x) (fun x ↦ ⟨x, W x, by simp⟩) x

/-- Let `m : N → M` be a split injection (`κ ∘ m = id`) whose image `γ` fixes pointwise. Suppose
that `γ S - S` is bijective for an endomorphism `S` and that `m ∘ κ' - V = S ∘ G` for a bijection
`V`, an endomorphism `G` and a map `κ' : M → N`. Then `m` and `γ` are Koszul-exact
(`New.Variety.KoszulExact`): `m` is injective, every fixed point of `γ` lies in the image of `m`,
and `γ - 1` is onto. -/
lemma koszulExact_of_bijective_sub {K M N : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {m : N →ₗ[K] M} {κ κ' : M →ₗ[K] N} {γ S G V : End K M}
    (hκ : κ ∘ₗ m = LinearMap.id) (hγ : γ ∘ₗ m = m) (hS : Bijective (γ ∘ₗ S - S : End K M))
    (hV : Bijective V) (hG : m ∘ₗ κ' - V = S ∘ₗ G) :
    KoszulExact m γ := by
  refine ⟨LeftInverse.injective (g := κ) fun x ↦ LinearMap.congr_fun hκ x, fun z hz ↦ ?_,
    fun z ↦ ?_⟩
  · -- Write `z = V x = m (κ' x) - S (G x)`. Then `γ` fixes `S (G x)`, so `G x = 0`.
    obtain ⟨x, rfl⟩ := hV.surjective z
    have hx : S (G x) = m (κ' x) - V x := (LinearMap.congr_fun hG x).symm
    have hm : γ (m (κ' x)) = m (κ' x) := LinearMap.congr_fun hγ (κ' x)
    have h_fix : (γ ∘ₗ S - S) (G x) = (γ ∘ₗ S - S) 0 := by simp [hx, hm, hz.eq]
    have hG_zero : G x = 0 := hS.injective h_fix
    exact ⟨κ' x, sub_eq_zero.mp (by simpa [hG_zero] using hx.symm)⟩
  · obtain ⟨x, hx⟩ := hS.surjective z
    exact ⟨S x, hx⟩

/-- Let `B → E` be `p`-torsion-free, `p`-complete `A`-algebras, `K` an `A`-algebra in which `q` is a
unit, `v` a unit of `E`, `t ∈ B`, and `γ` a `B`-algebra endomorphism of `E` fixing the image of the
inclusion `m : B → E`. Let `κ : E → B` be a `B`-linear left inverse of `m`, and let `S`, `G`, `W` be
`B`-linear endomorphisms of `E` with `γ ∘ S - S = q v (1 - p W)` and `m ∘ (q t κ) - q v = S ∘ G`,
where `v` acts by multiplication. Then after base change to `K` the map `m ⊗ K` is injective, every
fixed point of `γ ⊗ K` lies in its image, and `z ↦ (γ ⊗ K)(z) - z` is onto
(`New.Variety.KoszulExact`); `ULift` only moves the modules to universe `1`. -/
lemma koszulExact_baseChange_of_sub_comp_eq_smul {K : Type} [CommRing K] [Algebra A K]
    (E : CrysTest A) [Algebra B E] [IsScalarTower A B E] {v : E.obj} {t : B.obj} {q : A}
    (hv_unit : IsUnit v) (hq_unit : IsUnit (algebraMap A K q)) (γ : E →ₐ[B] E)
    {κ : E →ₗ[B] B} {S G W : End B E}
    (hκ_comp : κ ∘ₗ Algebra.linearMap B E = .id)
    (hγ_comp : γ.toLinearMap ∘ₗ Algebra.linearMap B E = Algebra.linearMap B E)
    (hS : γ.toLinearMap ∘ₗ S - S = q • v • (1 - (p : B) • W))
    (hG : Algebra.linearMap B E ∘ₗ (q • t • κ) - q • v • (1 : End B E) = S ∘ₗ G) :
    KoszulExact (ULift.map.{0, _, 1, 1} (((Algebra.linearMap B E).restrictScalars A).baseChange K))
      (ULift.map ((γ.toLinearMap.restrictScalars A).baseChange K)) := by
  -- After the base change `bc` to `K`, where `q` is a unit, the maps `q v (1 - p W')` are
  -- bijective, and `koszulExact_of_bijective_sub` applies with the bijection `q v`.
  let bc {M N : Type} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
      [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] (f : M →ₗ[B] N) :
      K ⊗[A] M →ₗ[K] K ⊗[A] N :=
    (f.restrictScalars A).baseChange K
  have h_bij (W' : End B E) : Bijective (bc (q • v • (1 - (p : B) • W'))) := by
    have h_bij_v : Bijective (bc (v • (1 - (p : B) • W'))) :=
      TensorProduct.map_bijective (f := 1) bijective_id
        (hv_unit.smul_bijective.comp (E.property.bijective_one_sub_smul B W'))
    have h_comp_eq : ⇑(bc (q • v • (1 - (p : B) • W'))) =
        (algebraMap A K q • ·) ∘ ⇑(bc (v • (1 - (p : B) • W'))) :=
      funext fun x ↦ by simp [bc]
    rw [h_comp_eq]
    exact hq_unit.smul_bijective.comp h_bij_v
  have h_koszul : KoszulExact (bc (Algebra.linearMap B E)) (bc γ.toLinearMap) := by
    refine koszulExact_of_bijective_sub (κ := bc κ) (κ' := bc (q • t • κ)) (S := bc S) (G := bc G)
      (V := bc (q • v • (1 : End B E))) ?_ ?_ ?_ (by simpa using h_bij 0) ?_
    · simpa [bc, baseChange_comp] using congrArg bc hκ_comp
    · simpa [bc, baseChange_comp] using congrArg bc hγ_comp
    · have h_bij_S : Bijective (bc (γ.toLinearMap ∘ₗ S - S)) := by simpa [hS] using h_bij W
      simpa [bc, baseChange_comp, sub_eq_add_neg] using h_bij_S
    · simpa [bc, baseChange_comp, sub_eq_add_neg] using congrArg bc hG
  -- `ULift.map` only changes the universe.
  simpa [bc, KoszulExact, subset_def, IsFixedPt, Function.Injective, Surjective,
    ← ULift.down_inj] using h_koszul

/-- Let `B → E` be `p`-torsion-free, `p`-complete `A`-algebras, where `E` has the topological
`B`-basis `u a * y n` (via `j`), `y n = (t - v) ^ n / n !`, `v` a unit, `u 0 = 1`. Let `p ^ 3 ∣ q`
with `q` a unit in `K`, and let `γ` scale `v` by `q + 1` and each `u a` (`a ≠ 0`) by `η + 1` with
`p η ∣ q`. Then `K ⊗ B → K ⊗ E` and `γ` are Koszul-exact: injective, fixed points in the image,
`γ - 1` onto. `ULift` only moves the modules to universe `1`. -/
lemma koszulExact_pd_line {K : Type} [CommRing K] [Algebra A K] (E : CrysTest A) [Algebra B E]
    [IsScalarTower A B E] [Zero I] {b : Basis (I × ℕ) B T} {j : T →ₗ[B] E}
    (hj : IsCompletionBijective p j) {u : I → E} {y : ℕ → E} {v : E.obj} {t : B.obj} {q : A}
    (hb : ∀ (a : I) (n : ℕ), j (b (a, n)) = u a * y n)
    (hy : ∀ n : ℕ, (algebraMap B E t - v) ^ n = n ! * y n) (hv_unit : IsUnit v) (hu_zero : u 0 = 1)
    (hq_dvd : (p : A) ^ 3 ∣ q) (hq_unit : IsUnit (algebraMap A K q)) (γ : E →ₐ[B] E)
    (hγv : γ v = (q + 1) • v)
    (hγu : ∀ a : I, a ≠ 0 → ∃ η : A, γ (u a) = (η + 1) • u a ∧ p * η ∣ q) :
    KoszulExact (ULift.map.{0, _, 1, 1} (((Algebra.linearMap B E).restrictScalars A).baseChange K))
      (ULift.map ((γ.toLinearMap.restrictScalars A).baseChange K)) := by
  classical
  -- A shift `S` of the topological basis makes `(γ - 1) S = q v (1 - p W)`, which is bijective
  -- on `K ⊗ E`; and `q v x` lies in `B` plus the image of `S` for every `x`.
  -- For `a ≠ 0`: `γ (u a) = (η a + 1) * u a` and `q = p * η a * c a`.
  choose! η hγu c hη using hγu
  obtain ⟨d, hd⟩ := hq_dvd
  -- the completeness instances that `hj.linearMap_comp_bijective` needs below
  have hE_complete : IsAdicComplete (Ideal.span {(p : B)}) E :=
    isAdicComplete_over_base E.property.complete
  have hB_complete : IsAdicComplete (Ideal.span {(p : B)}) B := B.property.complete
  have hy_zero : y 0 = 1 := by simpa using (hy 0).symm
  -- `γ` moves `t - v` by `-q • v`, a multiple of `p ^ 3`
  have h_taylor (n : ℕ) : ∃ w : E, γ (y n.succ) = y n.succ - q • v * (y n + p • w) := by
    have hγ : γ (algebraMap B E t - v) = algebraMap B E t - v + p ^ 3 * -d • v := by
      simp [hγv, hd, smul_def']
      ring
    simpa [hd, smul_def', mul_assoc, sub_eq_add_neg]
      using exists_map_dividedPow_succ E γ.toRingHom hy hγ n
  choose w hw using h_taylor
  -- Linear maps from `T` to a complete module extend uniquely along `j`. `F g` is the endomorphism
  -- of `E` with the values `g` on the basis; `κ` is the coefficient of `u 0 * y 0 = 1`.
  have h_extend (g : I × ℕ → E) : ∃ f : E →ₗ[B] E, ∀ x, f (j x) = b.constr B g x := by
    simpa [LinearMap.ext_iff] using hj.linearMap_comp_bijective.surjective (b.constr B g)
  choose F hF using h_extend
  obtain ⟨κ, hκ⟩ : ∃ κ : E →ₗ[B] B, ∀ x, κ (j x) = b.repr x (0, 0) := by
    simpa [LinearMap.ext_iff] using hj.linearMap_comp_bijective.surjective (b.coord (0, 0))
  let m : B →ₗ[B] E := Algebra.linearMap B E
  -- `S` sends `y n` to `-y (n + 1)` and multiplies `u a * y n` by `(q / η a) * v` for `a ≠ 0`.
  let S : End B E := F fun (a, n) ↦ if a = 0 then -y n.succ else p * c a • v * j (b (a, n))
  -- `W` and `G` are read off from the identities `hS` and `hG` below.
  let W : End B E := -F fun (a, n) ↦
    if a = 0 then w n
    else
      c a • γ (u a) * (y n - γ v * match n with
        | 0 => 0
        | k + 1 => y k + p • w k)
  let G : End B E := F fun (a, n) ↦
    if a = 0 then
      -q • j ((n + 1 : B) • b (a, n) - match n with
        | 0 => 0
        | k + 1 => t • b (a, k))
    else -η a • j (b (a, n))
  have hγ_comp : γ.toLinearMap ∘ₗ m = m := by simp [m, LinearMap.ext_ring_iff]
  have hκ_comp : κ ∘ₗ m = .id := by
    simpa [hb, hu_zero, hy_zero, m, LinearMap.ext_ring_iff] using hκ (b (0, 0))
  -- Both identities below are checked on the basis. The first uses `hw`, and
  -- `q = p * η a * c a` for `a ≠ 0`.
  have hS : γ.toLinearMap ∘ₗ S - S = q • v • (1 - (p : B) • W) := by
    refine hj.linearMap_comp_bijective.injective (b.ext fun (a, n) ↦ ?_)
    -- four cases, `n = 0` or not and `a = 0` or not, each an identity in the ring `E`
    rcases n with _ | n <;> simp +zetaDelta [hF] <;> split_ifs with ha
    · simp [smul_def', hw, hd, hy_zero, ha, hb, hu_zero]
      ring
    · simp [smul_def', hη a, hb, hy_zero, hγv, ha, hγu]
      ring
    · simp [smul_def', hw, hd, ha, hb, hu_zero]
      ring
    · simp [smul_def', hη a, hb, hγv, ha, hγu, hw]
      ring
  -- For `a = 0` the second rests on `v * y n = t * y n - (n + 1) * y (n + 1)`, which `hy` gives
  -- after multiplying by `n !`; for `n = 0` the term `t` is supplied by `m` instead of `S`.
  have hG : m ∘ₗ (q • t • κ) - q • v • (1 : End B E) = S ∘ₗ G := by
    refine hj.linearMap_comp_bijective.injective
      (b.ext fun (a, n) ↦ nsmul_right_injective n.factorial_ne_zero ?_)
    have hy_succ : (algebraMap B E t - v) ^ (n + 1) = (n + 1) * n ! * y (n + 1) := by
      simpa [factorial] using hy n.succ
    -- for `a = 0` the identity uses `hy` and `hy_succ`; for `a ≠ 0` it is a ring identity
    rcases n with _ | n <;> simp +zetaDelta [hF, hκ, apply_ite (F _)] <;> split_ifs with ha
    · simp [smul_def', hd, ha, hb, hu_zero, hy_zero]
      grind
    · simp [smul_def', hη a, ha, hb, hy_zero]
      ring
    · simp [smul_def', hd, ha, hb, hu_zero]
      grind
    · simp [smul_def', hη a, ha, hb]
      ring
  exact koszulExact_baseChange_of_sub_comp_eq_smul B E hv_unit hq_unit γ hκ_comp hγ_comp hS hG

end New.Variety

end DividedPowerLine

end
