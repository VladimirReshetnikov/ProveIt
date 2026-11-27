import Lib.Cohomology.Etale.EllAdicCohomology
import Lib.PadicComparison.Primitive.PeriodCoefficients

/-!
# The primitive comparison with period coefficients

The primitive comparison, passed from coefficients modulo `p` to period coefficients. For a `p`-adic
test `c` with ring `R`, let `L` be the ring of locally constant `𝔽_p`-valued functions on
`Spec R[1/p]` (for a test ring `A`, the same ring on `Spec A`; a `p`-adic test gives `A = R[1/p]`).
`New.Variety.primitiveMap` is the natural map of `O♭`-algebras from `O♭ ⊗ L` to the tilt `R♭`; on
`1 ⊗ L` it restricts to `locConstToTilt : L → R♭`, `ℓ ↦ primitiveMap (1 ⊗ ℓ)`. Let `S` be an
`A_inf`-algebra and `K` an `S`-algebra, and let `Ψ` be isomorphic (by `θ`) to the period
coefficients `c ↦ K ⊗ (S ⊗ W(R♭))^`, where `^` is `p`-adic completion.

* `New.Variety.primitivePeriodMap`: the natural map `K ⊗ W(L) → Ψ` induced by
  `New.Variety.primitiveMap`.
* `New.Variety.primitivePeriodMap_isBijective`: this map is bijective on cohomology under several
  conditions. `S` and `K` form a period ring pair, and `K` is flat over `S`. `N` and `N'` have flat
  base change. The cohomology of `N` with coefficients `ℤ_p` is finite over `ℤ_[p]`. The map that
  `New.Variety.primitiveMap` induces on the coefficients `b ↦ b ⊗ (O♭ ⊗ S) ⊗ 𝔪` is bijective on
  cohomology.
* `New.Variety.exists_primitive_period_comparison`: the same, in existential form.

Notions from other files:
* `New.Variety.CoeffCompBijective β α F`: the comparison of cohomology groups along `β` and `α` is
  bijective in every degree for the coefficients `F`.
* `New.Variety.HasFlatBaseChange N`: the cohomology of `N` commutes with flat extension of the
  coefficients.
* `New.Variety.IsPeriodRingPair`: `S` is `p`-torsion-free and `p`-complete, `p` divides the image of
  `ξ` in `S`, and `τ` is a unit in `K`.
* `New.Variety.almostCoeff`: for an `O♭`-module `N`, the functor `b ↦ b ⊗ N ⊗ 𝔪` on `O♭`-algebras,
  `𝔪` the maximal ideal of `O♭`.
* `New.Variety.oFlatLocConst`: the functor from test rings to `O♭`-algebras sending `A` to
  `O♭ ⊗_{𝔽_p} LC(A)`, `LC(A)` the locally constant functions `Spec A → 𝔽_p`.
* `New.Variety.ellAdicCoeff`: the coefficient `ℤ_ℓ` (here `ℓ = p`): a test ring `A` goes to the Witt
  vectors of the ring of locally constant functions `Spec A → 𝔽_ℓ`.

## Relation to the literature

Known; see `Lib.PadicComparison.HodgeTate.PeriodMap` for sources.
-/

namespace New.Variety

open CategoryTheory TensorProduct Functor Period PadicTest AlgebraTensorModule WittVector PadicInt
  ZMod Comparison

variable {p : ℕ} [ThePrime p] {S : Type} [CommRing S] [Algebra Ainf S] [Algebra ℤ_[p] S]
  [IsScalarTower ℤ_[p] Ainf S] (b : Type*) [CommRing b] [Algebra (ZMod p) b]
  (K : Type) [CommRing K] [Algebra S K] [Module.Flat S K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] S K] {Ψ : PadicTest ⥤ ModuleCat K}
  (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ)

/-- An `𝔽_p`-algebra `b` is a `ℤ_[p]`-algebra through reduction modulo `p`. -/
noncomputable local instance : Algebra ℤ_[p] b := .compHom _ (constantCoeff.comp (fromPadicInt p))

local instance : IsScalarTower ℤ_[p] (ZMod p) b := .of_compHom ..

/-- Let `q` and `π` be additive maps on `X` with kernel the multiples of `m`, and `q` onto. If
`π ∘ j` is a reduction modulo `m` (onto, with kernel the multiples of `m`), then so is `q ∘ j`. -/
lemma IsReductionMod.comp_of_exact_of_comp {W X Y Z : Type*} [SMul ℕ W] [AddCommGroup X]
    [AddCommGroup Y] [AddCommGroup Z] {m : ℕ} {q : X →+ Y} {π : X →+ Z} {j : W → X}
    (hq : IsReductionMod m q) (hπ : Function.Exact (fun x : X ↦ m • x) π)
    (hj : IsReductionMod m (π ∘ j)) :
    IsReductionMod m (q ∘ j) := by
  obtain ⟨hq_surj, hq_ker⟩ := hq
  obtain ⟨hj_surj, hj_ker⟩ := hj
  -- `q` and `π` have the same kernel, the multiples of `m`.
  have h_ker (x : X) : q x = 0 ↔ π x = 0 := (hq_ker x).trans (hπ x).symm
  refine ⟨fun y ↦ ?_, fun w ↦ (h_ker (j w)).trans (hj_ker w)⟩
  -- Write `y = q x`. Some `w` has `π (j w) = π x`, so `q` kills `j w - x` too.
  obtain ⟨x, rfl⟩ := hq_surj y
  obtain ⟨w, hw : π (j w) = π x⟩ := hj_surj (π x)
  have h_diff : q (j w - x) = 0 := (h_ker _).mpr (by simp [hw])
  exact ⟨w, by simpa [sub_eq_zero] using h_diff⟩

variable (p) in
/-- The functor from test rings to `ℤ_[p]`-algebras sending `A` to `W(L)`, where `L` is the ring
of locally constant functions `Spec A → 𝔽_p`. -/
noncomputable abbrev wittLocConst : TestRing ⥤ CommAlg ℤ_[p] :=
  (testIncl ⋙ locConstAlg) ⋙ wittFunctor ℤ_[p]

variable (S) in
/-- For a test ring `A`, with `L` the ring of locally constant functions `Spec A → 𝔽_p`, the
`ℤ_[p]`-algebra map `W(L) → W(O♭ ⊗ L) → S ⊗_{A_inf} W(O♭ ⊗ L)`, `w ↦ 1 ⊗ W(1 ⊗ –)(w)`. -/
noncomputable def wittIncludeRight (A : TestRing) :
    (wittLocConst p).obj A →ₐ[ℤ_[p]]
      (oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S ⋙ restrictAlg ℤ_[p] S).obj A := by
  open Algebra.TensorProduct in
    refine ⟨includeRight.toRingHom.comp (map includeRight.toRingHom), fun z ↦ ?_⟩
    -- Compare Witt coordinates, which come from `ZMod p`.
    have h_coord :
        WittVector.map includeRight.toRingHom (algebraMap ℤ_[p] ((wittLocConst p).obj A) z) =
          algebraMap Ainf ((oFlatLocConst ⋙ wittFunctor).obj A) (algebraMap ℤ_[p] Ainf z) :=
      WittVector.ext fun _ ↦ (includeRight.commutes _).trans (congrArg _ (cast_id p _))
    refine .trans (congrArg (tmul _ 1) h_coord) ?_
    -- `z` reaches `S` through `A_inf`.
    exact (includeRight.commutes _).trans
      (congrArg (fun s : S ↦ s ⊗ₜ 1) (IsScalarTower.algebraMap_apply ℤ_[p] Ainf S z)).symm

variable (S) in
/-- The `S`-algebra map `S ⊗_{ℤ_p} W(L) → S ⊗_{A_inf} W(O♭ ⊗ L)`, natural in the test ring: the
extension of `wittIncludeRight` to `S`-algebras, its transpose under base change to `S`. -/
noncomputable def wittLocConstBaseChange :
    wittLocConst p ⋙ algBaseChange S ⟶ oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S :=
  (baseChangeTranspose (wittLocConst p) (oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S)).symm
    (.mk fun A ↦ ConcreteCategory.ofHom (wittIncludeRight S A))

variable (S) in
/-- The map `S ⊗_{ℤ_p} W(L) → (S ⊗_{A_inf} W(O♭ ⊗ L))^` of `S`-modules, where `^` is the `p`-adic
completion: `wittLocConstBaseChange` followed by the map to the completion. -/
noncomputable def wittLocConstToPeriodAlg :
    asModules (wittLocConst p) ⋙ tensorWith S S ⟶ asModules (oFlatLocConst ⋙ periodAlg S) :=
  whiskerRight
    (wittLocConstBaseChange S ≫
      whiskerLeft (oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S) (algCompletion.of S p))
    (asModules (𝟭 (CommAlg S)))

variable (p S) in
/-- The isomorphism `K ⊗_{ℤ_p} W(L) ≅ K ⊗_S (S ⊗_{ℤ_p} W(L))`, natural in the test ring. -/
noncomputable def wittLocConstCancelIso :
    asModules (wittLocConst p) ⋙ tensorWith K K ≅
      (asModules (wittLocConst p) ⋙ tensorWith S S) ⋙ tensorWith K K :=
  NatIso.ofComponents
    (fun A ↦ (cancelBaseChange ℤ_[p] S K K ((wittLocConst p).obj A)).symm.toModuleIso)
    fun _ ↦ ModuleCat.hom_ext (tmul_ext fun _ _ ↦ rfl)

variable (S) in
/-- The image `1 ⊗ w` of a Witt vector `w ∈ W(B)` in the `p`-adic completion of `S ⊗ W(B)`. -/
noncomputable abbrev wittToPeriodAlg (B : CommAlg OFlat) (w : WittVector p B) :
    (periodAlg S).obj B :=
  AdicCompletion.of (Ideal.span {(p : S ⊗[Ainf] wittFunctor.obj B)}) (S ⊗[Ainf] wittFunctor.obj B)
    (1 ⊗ₜ w)

/-- Let `θ` be an isomorphism from the functor `c ↦ K ⊗ (S ⊗ W(R♭))^` to `Ψ`, where `R` is the ring
of the test `c` and `^` is the `p`-adic completion. This is the natural map from `K ⊗ W(L)` to `Ψ`,
where `L` is the ring of locally constant `𝔽_p`-valued functions on `Spec R[1/p]`. It is the
composite `K ⊗ W(L) ≅ K ⊗ (S ⊗ W(L)) → K ⊗ (S ⊗ W(O♭ ⊗ L))^ → K ⊗ (S ⊗ W(R♭))^ ≅ Ψ c`, the
third map induced by `primitiveMap`. -/
noncomputable def primitivePeriodMap :
    genericTest ⋙ asModules (wittLocConst p) ⋙ tensorWith K K ⟶ Ψ :=
  whiskerLeft genericTest
      ((wittLocConstCancelIso p S K).hom ≫
        whiskerRight (wittLocConstToPeriodAlg S) (tensorWith K K)) ≫
    whiskerRight primitiveMap (asModules (periodAlg S) ⋙ tensorWith K K) ≫ θ.hom

omit [Module.Flat S K] in
/-- `primitivePeriodMap K θ` sends `a ⊗ x` to `θ (a ⊗ 1 ⊗ x')`, where `x'` is the image of `x`
under the map of Witt vectors induced by `locConstToTilt`, and `1 ⊗ x'` is taken in the completion
(`wittToPeriodAlg`). -/
lemma primitivePeriodMap_app_tmul (c : PadicTest) (a : K)
    (x : (wittLocConst p).obj (genericTest.obj c)) :
    (primitivePeriodMap K θ).app c (a ⊗ₜ x) =
      θ.hom.app c (a ⊗ₜ wittToPeriodAlg S (tilt.obj c)
        (WittVector.map (locConstToTilt.app c).hom.toRingHom x)) := by
  refine congrArg (fun y ↦ θ.hom.app c (a ⊗ₜ y)) ((adicMap_algebraMap ..).trans (congrArg _ ?_))
  exact congrArg₂ (tmul _) (mul_one 1) (ext fun _ ↦ one_smul OFlat _)

/-- For every test ring `A`, the `O♭`-algebra `O♭ ⊗_{𝔽_p} LC(A)` is perfect, and `pFlat` (the class
of `ξ` modulo `p`) is a non-zero-divisor on it. -/
lemma isPerfectTorsionFree_oFlatLocConst (A : TestRing) :
    IsPerfectTorsionFree (oFlatLocConst.obj A) := by
  -- A tensor product over `𝔽_p` of the perfect rings `O♭` and `LC(A)` is perfect.
  refine ⟨perfectRing_tensor (ZMod.natCast_self p) ⟨.of _ OFlat, inferInstance⟩
    ⟨_, perfectRing_locConstAlg _⟩, ?_⟩
  -- `O♭ ⊗ LC(A)` is torsion-free over the domain `O♭`, and `pFlat ≠ 0`.
  exact .of_ne_zero (M := _ ⊗ _) pFlat_ne_zero

/-- Let `S` be an `A_inf`-algebra, `A` a test ring and `L` the ring of locally constant functions
`Spec A → 𝔽_p`. The map `S ⊗ W(L) → S ⊗ W(O♭ ⊗ L)` (`wittLocConstBaseChange`) is bijective
modulo `p`: followed by a reduction `q` modulo `p` of the target (`IsReductionMod p q`: `q` onto,
with kernel the multiples of `p`), it is a reduction modulo `p` of the source. -/
lemma IsReductionMod.comp_wittLocConstBaseChange {p : ℕ} [ThePrime p] {S : Type} [CommRing S]
    [Algebra Ainf S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] Ainf S] (A : TestRing)
    {Y : Type} [AddCommGroup Y]
    {q : (oFlatLocConst ⋙ wittFunctor ⋙ algBaseChange S).obj A →+ Y} (hq : IsReductionMod p q) :
    IsReductionMod p (q ∘ (wittLocConstBaseChange S).app A) := by
  -- The zeroth Witt coordinates reduce the source to `S ⊗ B` and the target to `S ⊗ (O♭ ⊗ B)`,
  -- where `B` is the ring of locally constant functions; the isomorphism `E` identifies the two.
  have h_perfect : PerfectRing (oFlatLocConst.obj A) p :=
    (isPerfectTorsionFree_oFlatLocConst A).1
  let B : CommAlg (ZMod p) := locConstAlg.obj A.obj
  -- `g` takes the zeroth Witt coordinate.
  let g : (wittLocConst p).obj A →ₐ[ℤ_[p]] B :=
    ⟨constantCoeff, fun _ ↦ congrArg (algebraMap _ _) (cast_id p _)⟩
  let f : Ainf →ₗ[Ainf] OFlat := Algebra.linearMap Ainf OFlat
  have h_tower : IsScalarTower ℤ_[p] Ainf OFlat := .of_compHom ..
  have h_compatible : CompatibleSMul ℤ_[p] (ZMod p) OFlat B :=
    .of_algebraMap_surjective _ _ (ringHom_surjective _)
  have h_source : IsReductionMod p (g.toLinearMap.lTensor S) :=
    (isReductionMod_constantCoeff_and_isCompleteTorsionFree (ZMod p) _).left.lTensor
  have h_target : IsReductionMod p ((wittConstCoeff (oFlatLocConst.obj A)).lTensor S) :=
    (isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat _).left.lTensor
  -- `A_inf ⊗ B = O♭ ⊗ B` over `ℤ_[p]`, because `p` kills `B` and `f` is reduction modulo `p`.
  have hf_bij : Function.Bijective (rTensor ℤ_[p] B f) :=
    (isReductionMod_constantCoeff_and_isCompleteTorsionFree OFlat _).left.bijective_rTensor
      (f.restrictScalars ℤ_[p])
      (ZModModule.char_nsmul_eq_zero p)
  let E : S ⊗[ℤ_[p]] B ≃ₗ[S] S ⊗[Ainf] (OFlat ⊗[ZMod p] B) :=
    (cancelBaseChange ℤ_[p] Ainf S S B).symm ≪≫ₗ congr (.refl S S)
      (.ofBijective (rTensor ℤ_[p] B f) hf_bij ≪≫ₗ
        equivOfCompatibleSMul (ZMod p) ℤ_[p] Ainf OFlat B)
  -- The map followed by the reduction of the target is the reduction of the source followed by `E`.
  have h_square :
      (wittConstCoeff (oFlatLocConst.obj A)).baseChange S ∘ₗ
          ((wittLocConstBaseChange S).app A).hom.toLinearMap =
        E.toLinearMap ∘ₗ g.toLinearMap.baseChange S := by
    refine ext fun a x ↦ ?_
    -- On `a ⊗ x` both sides are pure tensors `s ⊗ (t ⊗ u)`; compare the factors.
    change _ ⊗ₜ (_ ⊗ₜ _) = _ ⊗ₜ (_ ⊗ₜ _)
    congr 1
    · simp
    · congr 1
      simp [f]
  -- `baseChange S` and `lTensor S` are the same function.
  have h_comp :
      (wittConstCoeff (oFlatLocConst.obj A)).lTensor S ∘ (wittLocConstBaseChange S).app A =
        E ∘ g.toLinearMap.lTensor S :=
    congrArg DFunLike.coe h_square
  exact hq.comp_of_exact_of_comp
    (π := ((wittConstCoeff (oFlatLocConst.obj A)).lTensor S).toAddMonoidHom) h_target.right
    (by
      rw [LinearMap.toAddMonoidHom_coe, h_comp]
      exact ⟨E.surjective.comp h_source.left, fun x ↦ E.map_eq_zero_iff.trans (h_source.right x)⟩)

/-- The primitive comparison with period coefficients. Let `p` be a prime, `(S, K)` a period ring
pair (`S` an `A_inf`-algebra, `K` a flat `S`-algebra), `θ` an isomorphism from
`c ↦ K ⊗ (S ⊗ W(R♭))^` to `Ψ : PadicTest ⥤ ModuleCat K`, and `α : N' ⟶ genericTest ⋙ N` the map that
compares cohomology over `p`-adic tests with cohomology over test rings. Suppose that `N` and `N'`
have flat base change, that each `H N ellAdicCoeff n` (the `n`-th cohomology of `N` with
coefficients `ℤ_p`) is finite over `ℤ_[p]`, and that `primitiveMap` is bijective on cohomology along
`α` for the coefficients `almostCoeff (O♭ ⊗ S)` (`CoeffCompBijective`). Then
`primitivePeriodMap K θ`, viewed by `ofModuleHom genericTest` as a map of coefficients, is bijective
on cohomology along `α`, in every degree. -/
lemma primitivePeriodMap_isBijective {p : ℕ} [ThePrime p] {S : Type} [CommRing S] [Algebra Ainf S]
    [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] Ainf S] (K : Type) [CommRing K] [Algebra S K]
    [Module.Flat S K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] S K] {Ψ : PadicTest ⥤ ModuleCat K}
    (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ) (hS : IsPeriodRingPair p S K)
    {N : AbFunctor TestRing} {N' : AbFunctor PadicTest} {α : N' ⟶ genericTest ⋙ N}
    (hN : HasFlatBaseChange N) (hN' : HasFlatBaseChange N')
    (h_finite : ∀ n : ℕ, Module.Finite ℤ_[p] (H N ellAdicCoeff n))
    (h_primitive : CoeffCompBijective primitiveMap α (almostCoeff (OFlat ⊗[Ainf] S))) :
    (ofModuleHom genericTest (primitivePeriodMap K θ)).IsBijective α := by
  -- The map is the composite of the isomorphism `wittLocConstCancelIso`, of
  -- `wittLocConstToPeriodAlg`, of the map induced by `primitiveMap`, and of `θ`. The second is
  -- bijective on cohomology because it is bijective modulo `p` and the cohomology is finite, the
  -- third by the hypothesis on `primitiveMap`.
  -- `S` is torsion-free over `ℤ_[p]`: a nonzero `t = u p ^ v` divides a power of `p`.
  have h_dvd_pow {t : ℤ_[p]} (ht : t ≠ 0) : t ∣ (p : ℤ_[p]) ^ t.valuation :=
    (unitCoeff_spec ht).dvd.trans (Units.mul_left_dvd.mpr dvd_rfl)
  have h_torsionFree : Module.IsTorsionFree ℤ_[p] S :=
    isTorsionFree_of_dvd_pow hS.isSMulRegular_natCast fun ht ↦ ⟨_, h_dvd_pow ht⟩
  have h_padic : IsCompleteTorsionFree ℤ_[p] :=
    { regular := .of_ne_zero NeZero.out
      complete := by
        rw [← maximalIdeal_eq_span_p]
        infer_instance }
  have h_witt (A : TestRing) : IsCompleteTorsionFree ((wittLocConst p).obj A) :=
    isCompleteTorsionFree_wittVector (ZMod p) (locConstAlg.obj A.obj)
  have h_period (A : TestRing) : IsCompleteTorsionFree ((oFlatLocConst ⋙ periodAlg S).obj A) :=
    isCompleteTorsionFree_completion
      (isSMulRegular_tensor_witt hS.regular (isPerfectTorsionFree_oFlatLocConst A))
  have h_mod (A : TestRing) {Y : Type} [AddCommGroup Y]
      (q : (asModules (oFlatLocConst ⋙ periodAlg S)).obj A →+ Y) (hq : IsReductionMod p q) :
      IsReductionMod p (q ∘ (wittLocConstToPeriodAlg S).app A) :=
    (IsReductionMod.comp_algebraMap hq).comp_wittLocConstBaseChange A
  -- The cohomology with coefficients `ℤ_p` has finite rank, by `h_finite`.
  have h_rank (n : ℕ) : Module.rank ℤ_[p] (H N ellAdicCoeff n) < Cardinal.aleph0 :=
    have : Module.Finite ℤ_[p] (H N ellAdicCoeff n) := h_finite n
    Module.rank_lt_aleph0 ℤ_[p] (H N ellAdicCoeff n)
  have h_completion :
      (ofModuleHom (Φ := asModules (wittLocConst p) ⋙ tensorWith S S) (𝟭 TestRing)
        (wittLocConstToPeriodAlg S)).IsBijective (𝟙 N) :=
    hN.isBijective_of_isReductionMod (Θ := wittLocConst p) h_padic hS.isCompleteTorsionFree h_witt
      irreducible_p (X := oFlatLocConst ⋙ periodAlg S) (wittLocConstToPeriodAlg S)
      (fun n _ ↦ h_rank n) h_period h_mod
  have h_completion_tensor :
      CoeffCompBijective (Ψ := asModules (wittLocConst p) ⋙ tensorWith S S) (φ := 𝟭 TestRing)
        (wittLocConstToPeriodAlg S) (𝟙 N) (tensorWith K K) :=
    (h_completion.baseChangeMap_bijective_iff hN).mp
      (hN S K K (asModules (oFlatLocConst ⋙ periodAlg S)))
  have h_primitive_tensor :
      CoeffCompBijective primitiveMap α (asModules (periodAlg S) ⋙ tensorWith K K) :=
    h_primitive.periodAlg_of_almostCoeff hN hS (fun G ↦ hN' S K K (tilt ⋙ G))
      isPerfectTorsionFree_oFlatLocConst isPerfectTorsionFree_tilt
  have h_composite :
      (ofModuleHom (Φ := (asModules (wittLocConst p) ⋙ tensorWith S S) ⋙ tensorWith K K) genericTest
        (whiskerLeft genericTest (whiskerRight (wittLocConstToPeriodAlg S) (tensorWith K K)) ≫
          whiskerRight primitiveMap (asModules (periodAlg S) ⋙ tensorWith K K))).IsBijective α :=
    -- `(… :)`: the composite of the two comparisons is this one only after unfolding.
    (h_completion_tensor.trans h_primitive_tensor rfl :)
  -- The isomorphisms `wittLocConstCancelIso` and `θ` do not affect bijectivity; the square
  -- commutes by the definition of `primitivePeriodMap`.
  refine (isBijective_iff_of_coeff_iso
    (whiskerRight (wittLocConstCancelIso p S K).hom (moduleCoeff (𝟭 (ModuleCat K))))
    (isoWhiskerRight θ (moduleCoeff (𝟭 (ModuleCat K)))).inv ?_).mpr h_composite
  exact (isoWhiskerRight θ (moduleCoeff (𝟭 (ModuleCat K)))).eq_comp_inv.mpr rfl

/-- The primitive comparison in existential form. For a period ring pair `(S, K)` and an isomorphism
`θ` from `c ↦ K ⊗ (S ⊗ W(R♭))^` to `Ψ : PadicTest ⥤ ModuleCat K` (`R` the ring of the test `c`),
there is a natural map `γ : K ⊗ W(L) → Ψ` (`L`: locally constant `Spec R[1/p] → 𝔽_p`) with
`γ (a ⊗ x) = θ (a ⊗ (1 ⊗ x'))`, `x'` the image of `x` under the Witt vector map of `locConstToTilt`;
`γ` is bijective on cohomology under the conditions of `primitivePeriodMap_isBijective`. -/
lemma exists_primitive_period_comparison {p : ℕ} [ThePrime p] {S : Type} [CommRing S]
    [Algebra Ainf S] [Algebra ℤ_[p] S] [IsScalarTower ℤ_[p] Ainf S] (K : Type) [CommRing K]
    [Algebra S K] [Module.Flat S K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] S K]
    {Ψ : PadicTest ⥤ ModuleCat K} (θ : asModules (tilt ⋙ periodAlg S) ⋙ tensorWith K K ≅ Ψ)
    (hS : IsPeriodRingPair p S K) :
    ∃ γ : genericTest ⋙ asModules (wittLocConst p) ⋙ tensorWith K K ⟶ Ψ,
      (∀ (c : PadicTest) (a : K) (x : (wittLocConst p).obj (genericTest.obj c)),
        γ.app c (a ⊗ₜ x) =
          θ.hom.app c (a ⊗ₜ wittToPeriodAlg S (tilt.obj c)
            (WittVector.map (locConstToTilt.app c).hom.toRingHom x))) ∧
      ∀ {N : AbFunctor TestRing} {N' : AbFunctor PadicTest} {α : N' ⟶ genericTest ⋙ N},
        HasFlatBaseChange N → HasFlatBaseChange N' →
        (∀ n : ℕ, Module.Finite ℤ_[p] (H N ellAdicCoeff n)) →
        CoeffCompBijective primitiveMap α (almostCoeff (OFlat ⊗[Ainf] S)) →
        (ofModuleHom genericTest γ).IsBijective α :=
  ⟨primitivePeriodMap K θ, primitivePeriodMap_app_tmul K θ, primitivePeriodMap_isBijective K θ hS⟩

end New.Variety
