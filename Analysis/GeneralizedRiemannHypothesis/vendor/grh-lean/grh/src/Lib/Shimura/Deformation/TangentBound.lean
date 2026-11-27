import Lib.General.Geometry.SerreTheorem
import Lib.Shimura.Deformation.TangentCount

/-!
# Drinfeld lifting over k[ε] and a bound on the tangent space of the moduli scheme

In the first two sections, `x` and `x'` are first-order deformations over `k[ε]` of one object `x₀`
over a field `k`, in a family `New.ThetaFamily` of abelian schemes. In the third section, `x` is a
first-order deformation of `x₀` over `k ⊕ M*`. `New.Variety.sqZeroReduction k k` is
`Spec k ⟶ Spec k[ε]`, and `New.ThetaObject.IsPullbackAlong b x₀ x` exhibits `x₀` as the pull-back of
`x` along `b`. In the second section, `k` is algebraically closed of prime characteristic. There,
`f : x.groupScheme ⟶ x'.groupScheme` is a homomorphism that reduces to multiplication by `a` on
`x₀.groupScheme`. If `a ≠ 0`, a homomorphism `F` that reduces to `c * a` and kills the kernel of `f`
yields a homomorphism out of `x'.groupScheme` that reduces to `c`. These tools give the tangent
bound for deformations without constant directions.

## Main definitions and results

* `New.Variety.AgreeModEps`: points of `x.groupScheme` and `x'.groupScheme` with the same reduction
  modulo `ε`. The points that agree with `0` are those that vanish modulo `ε`.
  `New.Variety.AgreeModEps.ringChar_smul_and_smul_eq_zero` gives elements that kill them.
* `New.Variety.drinfeld_lift`: if `c` kills the points of `x'.groupScheme` that vanish modulo `ε`,
  then multiplication by `c` on `x₀.groupScheme` lifts to a homomorphism
  `x.groupScheme ⟶ x'.groupScheme`.
* `New.Variety.isLinear_and_pairing_eq_of_reduction`: such an `f` is linear, and `a` kills its
  kernel modulo `ε`. The lemma also describes its effect on the pairing.
* `New.Variety.finrank_tangent_le_card_index_sub_one`: under the hypotheses stated in its docstring,
  if a first-order deformation `x` over `k ⊕ M*` of `x₀` has no constant direction in `M`, then
  `finrank k M ≤ Fintype.card D.Index - 1`.

Notions from other files:
* `New.ThetaObject`: An object of the family X over a scheme T: a morphism from T to the base of X.
* `New.ThetaObject.groupScheme`: The group scheme with O_E-action of an object x over S: the
  pull-back of the abelian scheme of the family along x : S → base.
* `New.Pic.pairing`: For c in Pic A and T-points x, y of A, the class ⟨x,
  y⟩ = (x + y)^*c − x^*c − y^*c + 0^*c in Pic T (`New.Pic.atPoint` is x ↦ x^*c).
* `New.IsGroupBaseChange.pointEquiv`: For an O-compatible base change p : A' → A and an S'-scheme T,
  the O-linear bijection x ↦ p∘x from T-points of A' over S' to T-points of A over S.

## Relation to the literature

Known result: Deformations of the PEL object have at most n - 1 parameters, where n is the size of
the index set `D.Index`. Only the upper bound for first-order deformations is proved here, at every
good place, working on the finite group scheme of w-torsion with Drinfeld's lifting lemma and
without p-divisible groups or crystals. Source: N. Katz, Serre–Tate local moduli, LNM 868 (1981), §1
(Drinfeld's lemma); J. Lubin, J. Tate, Formal moduli for one-parameter formal Lie groups, Bull. SMF
94 (1966); M. Harris, R. Taylor, The Geometry and Cohomology of Some Simple Shimura Varieties
(2001), III.4.1.
-/

noncomputable section

namespace New.Variety

/-! ## Drinfeld's lifting lemma for homomorphisms of deformations over k[ε] -/

section DrinfeldLifting

open CategoryTheory AlgebraicGeometry CommRingCat Over Spec Ideal.Quotient Scheme DualNumber
  NumberField ThetaObject Obj IsGroupBaseChange

variable {E k : Type} [Field E] [CMBase E] {D : PEL E} [Field k]
  {Z : Scheme} {σ : Z ⟶ Spec (of (𝓞 E))} {Y : ThetaFamily D Z σ} {x₀ : ThetaObject Y (Spec (of k))}
  {x x' : ThetaObject Y (Spec (of (TrivSqZeroExt k k)))}
  (hq : IsPullbackAlong (sqZeroReduction k k) x₀ x)
  (hq' : IsPullbackAlong (sqZeroReduction k k) x₀ x')

/-- The T-points y of `x.groupScheme` and y' of `x'.groupScheme` agree modulo ε: on every affine
k-scheme Spec B mapping to T through the closed point of `Spec k[ε]`, their restrictions are the
same point of the abelian scheme of the family. The arguments `hq` and `hq'` fix the two
deformations `x` and `x'` of `x₀`; `pointEquiv` sends a point of `x.groupScheme` to the
corresponding point of the abelian scheme of the family. -/
@[local simp]
def AgreeModEps (T : Over (Spec (of (TrivSqZeroExt k k)))) (y : T ⟶ x.groupScheme)
    (y' : T ⟶ x'.groupScheme) : Prop :=
  ∀ (B : CommRingCat) (b : Spec B ⟶ Spec (of k))
      (t : Over.map (sqZeroReduction k k) (Over.mk b) ⟶ T),
    x.isGroupBaseChange.pointEquiv (t ≫ y) =
      homMk (𝟙 (Spec B)) ≫ x'.isGroupBaseChange.pointEquiv (t ≫ y')

/-- `ψ : C ⟶ B`, with `b : Spec B ⟶ Spec k`, is the reduction modulo `ε` of the affine scheme
`s : Spec C ⟶ Spec k[ε]`. Here `preimage s : k[ε] ⟶ C` is the ring map of which `s` is the
spectrum. -/
structure IsReductionModEps {C B : CommRingCat} (s : Spec C ⟶ Spec (of (TrivSqZeroExt k k)))
    (ψ : C ⟶ B) (b : Spec B ⟶ Spec (of k)) : Prop where
  /-- `Spec B` lies over the closed point of `Spec k[ε]`. -/
  comp_eq : Spec.map ψ ≫ s = b ≫ sqZeroReduction k k
  /-- `ψ` is onto, and the product of any two elements of its kernel is zero. -/
  isSqZeroExt : IsSqZeroExt ψ
  /-- The kernel of `ψ` is generated by the image of `ε`. -/
  eq_zero_iff_dvd : ∀ a : C, ψ a = 0 ↔ preimage s ε ∣ a
  /-- Every affine point over the closed point factors through `Spec B`. -/
  exists_factor : ∀ {B' : CommRingCat} {t : Spec B' ⟶ Spec C} {b' : Spec B' ⟶ Spec (of k)},
    t ≫ s = b' ≫ sqZeroReduction k k → ∃ l : Spec B' ⟶ Spec B, l ≫ Spec.map ψ = t

/-- Every affine scheme `s : Spec C ⟶ Spec k[ε]` has a reduction modulo `ε`
(`New.Variety.IsReductionModEps`). -/
lemma exists_isReductionModEps {C : CommRingCat} (s : Spec C ⟶ Spec (of (TrivSqZeroExt k k))) :
    ∃ (B : CommRingCat) (ψ : C ⟶ B) (b : Spec B ⟶ Spec (of k)), IsReductionModEps s ψ b := by
  -- `B` is `C` modulo the image of `ε`, and `π` is the quotient map.
  let π := ofHom (mk (Ideal.span {preimage s ε}))
  have h_sq : IsSqZeroExt π := by
    refine ⟨mk_surjective, ?_⟩
    -- A product of two multiples of `ε` is a multiple of `ε * ε = 0`.
    simp +contextual [π, eq_zero_iff_dvd, dvd_def, mul_mul_mul_comm _ _ (preimage s ε), ← map_mul]
  refine ⟨_, π, map (ofHom (algebraMap k _) ≫ preimage s ≫ π), ?_, h_sq, eq_zero_iff_dvd _,
    fun {B' t b'} h_t ↦ ?_⟩
  · -- Compare the two ring maps out of `k[ε]`.
    apply homEquiv.injective
    aesop
  · -- A point `t` that lies over `sqZeroReduction k k` kills `ε`, so it factors through the
    -- quotient.
    have h_eps : preimage t (preimage s ε) = 0 :=
      calc preimage t (preimage s ε)
          _ = preimage (t ≫ s) ε := by simp
          _ = preimage (b' ≫ sqZeroReduction k k) ε := by rw [h_t]
          _ = 0 := by simp
    rw [← map_preimage t]
    exact le_ker_iff_factors.mp ((Ideal.span_singleton_le_iff_mem _).mpr h_eps)

/-- Let `x` deform `x₀` over `k[ε]` (`hq`) and let y be a T-point of `x.groupScheme` that vanishes
modulo ε. Then y is killed by the characteristic of k. Suppose further that the base homomorphism
`x.baseHom : 𝓞 E →+* k[ε]` factors as some ψ : k → k[ε] after `x₀.baseHom`. Then y is also killed
by (β* − b)·c, for every integer b and every c in 𝓞 E such that β − b and c both map to 0 under
`x₀.baseHom`; here `D.β` is the integer β of `E` that the PEL datum `D` carries. -/
lemma AgreeModEps.ringChar_smul_and_smul_eq_zero (hq : IsPullbackAlong (sqZeroReduction k k) x₀ x)
    {T : Over (Spec (of (TrivSqZeroExt k k)))}
    {y : T ⟶ x.groupScheme} (h_agree : AgreeModEps hq hq T y 0) :
    ringChar k • y = 0 ∧
    ∀ {ψ : k →+* TrivSqZeroExt k k},
      x.baseHom = RingHom.comp ψ x₀.baseHom →
      ∀ ⦃b : ℤ⦄ ⦃c : 𝓞 E⦄, x₀.baseHom (D.β - b) = 0 → x₀.baseHom c = 0 →
        ((Star.star D.β - b) * c) • y = 0 := by
  -- Vanishing is tested on affine points `τ` of `T`, and on those `y` is infinitesimal for the
  -- reduction modulo `ε`.
  have h_test {y' : T ⟶ x.groupScheme}
      (hy' : ∀ {C B : CommRingCat} (s : Spec C ⟶ Spec (of (TrivSqZeroExt k k))) (ψ : C ⟶ B)
        [IsSqZeroExt ψ] (τ : mk s ⟶ T), IsInfinitesimal ψ (τ ≫ y) → τ ≫ y' = 0) :
      y' = 0 := by
    refine OverMorphism.ext (hom_ext_of_cover .one fun _ A t _ ↦ ?_)
    obtain ⟨B, ψ, b, h_over, h_sq, -⟩ := exists_isReductionModEps (t ≫ T.hom)
    let τ : mk (t ≫ T.hom) ⟶ T := homMk t
    have h_tiny : IsInfinitesimal ψ (τ ≫ y) := by
      simpa [IsInfinitesimal, eq_zero_iff_factors_zero_section] using
        h_agree B b (homMk _ h_over ≫ τ)
    show (τ ≫ y').left = (τ ≫ 0).left
    rw [hy' _ ψ τ h_tiny, AddMonObj.comp_zero]
  constructor
  · refine h_test fun {C B} s ψ _ τ h_tiny ↦ ?_
    -- On a smooth group scheme, an integer that is zero in the ring of an infinitesimal point
    -- kills the point; the characteristic of `k` is such an integer.
    have h_char : ((ringChar k : ℕ) : C) = 0 :=
      natCast_eq_zero_of_over_charP (s ≫ (specOver k _).hom)
    simpa [comp_nsmul] using
      h_tiny.nsmul_eq_zero x.smoothOfRelativeDimension (mkIdTerminal.from _) h_char
  · intro ρ hρ b c hb hc
    refine h_test fun s ψ _ τ h_tiny ↦ ?_
    -- On infinitesimal points the logarithm `ω` of `exists_isTangentLog` turns `c •` into
    -- multiplication by `x.baseHom c = 0`, and the points with `ω = 0` are killed by
    -- `star D.β - b`.
    obtain ⟨ω, hω⟩ := x.exists_isTangentLog (b := b) (by simp [hρ, hb])
    have h_log : ω (c • (τ ≫ y)) = 0 := by simp [(hω h_tiny).map_smul, hρ, hc]
    simpa [mul_smul] using (hω (h_tiny.smul c)).smul_eq_zero_of_eq_zero h_log

/-- Drinfeld's lifting lemma. Let `x`, `x'` deform `x₀` over `k[ε]`, and let `c` in `𝓞 E` kill all
points of `x'.groupScheme` that vanish modulo `ε`. Then some homomorphism
`F : x.groupScheme ⟶ x'.groupScheme` reduces to multiplication by `c`: composed with the inclusion
`hq.schemeMap` of the reduction `x₀.groupScheme` into `x.groupScheme`, it is `c` times the
inclusion `hq'.schemeMap`. Also `y ≫ F = c • y'` whenever `y` and `y'` agree modulo `ε`. -/
lemma drinfeld_lift (hq : IsPullbackAlong (sqZeroReduction k k) x₀ x)
    (hq' : IsPullbackAlong (sqZeroReduction k k) x₀ x') {c : 𝓞 E}
    (hc : ∀ (T : Over (Spec (of (TrivSqZeroExt k k)))) (y : T ⟶ x'.groupScheme),
      AgreeModEps hq' hq' T y 0 → c • y = 0) :
    ∃ F : x.groupScheme ⟶ x'.groupScheme,
      IsAdditive F ∧
      hq.schemeMap ≫ F = c • hq'.schemeMap ∧
      ∀ (T : Over (Spec (of (TrivSqZeroExt k k)))) (y' : T ⟶ x'.groupScheme)
        (y : T ⟶ x.groupScheme),
        AgreeModEps hq' hq T y' y → y ≫ F = c • y' := by
  -- Descend multiplication by `c` along the relation `AgreeModEps`. The relation is additive, `c`
  -- kills the points related to `0`, and it is locally total because points of a smooth scheme lift
  -- along `ε`. Cover `x.groupScheme` by affine opens `j a`, each mapping into an étale chart of the
  -- family.
  have h_chart : ∀ a : Y.total.left, ∃ (V : Y.total.left.Opens)
      (z : Fin (abelianDim E D.Index) → Γ(Y.total.left, V)), a ∈ V ∧ IsEtaleChart Y.total.hom V z :=
    fun a ↦ exists_isEtaleChart a Y.relative_dim
  choose V z hV_mem hV using h_chart
  have h_affine : ∀ a : ((Over.map x).obj x.groupScheme).left, ∃ (C : CommRingCat)
      (j : Spec C ⟶ ((Over.map x).obj x.groupScheme).left), IsOpenImmersion j ∧
        a ∈ Set.range j ∧ Set.range j ⊆ ↑(x.toFamily.left ⁻¹ᵁ V (x.toFamily.left a)) :=
    fun a ↦ exists_affine_mem_range_and_range_subset (x := a)
      (U := x.toFamily.left ⁻¹ᵁ V _) (hV_mem _)
  choose C j hj_open hj_mem hj_sub using h_affine
  have h_local (a : x.groupScheme.left) : ∃ y' : mk (j a ≫ x.groupScheme.hom) ⟶ x'.groupScheme,
      AgreeModEps hq' hq _ y' ((mk (j a ≫ x.groupScheme.hom)).homMk (j a)) := by
    obtain ⟨B, ψ, b, h_sq, hψ, -, h_fac⟩ := exists_isReductionModEps (j a ≫ x.groupScheme.hom)
    -- Reduce `j a` modulo `ε` and lift the result in the chart to a point of the family over `x'`,
    -- with any lifts of its coordinates.
    have hψ_onto : Function.Surjective ψ := hψ.coe_surjective
    have h_base : (map ψ ≫ j a ≫ x.toFamily.left) ≫ Y.total.hom =
        Spec.map ψ ≫ (j a ≫ x.groupScheme.hom) ≫ x' := by
      simp [reassoc_of% h_sq, hq, hq']
    obtain ⟨y, ⟨hy_red, -⟩, -⟩ :=
      hV _ (t := (j a ≫ x.groupScheme.hom) ≫ x') (map ψ ≫ j a ≫ x.toFamily.left) _
        (fun _ _ ↦ hj_sub a ⟨_, rfl⟩) h_base (hψ_onto.comp_left _).choose_spec
    refine ⟨x'.isGroupBaseChange.pointEquiv.symm y, fun _ _ t ↦ ?_⟩
    obtain ⟨l, hl⟩ := h_fac t.w
    ext
    simp [pointEquiv, ← hl, hy_red]
  have h_sub {T : Over (Spec (of (TrivSqZeroExt k k)))} {y₁' : T ⟶ x'.groupScheme}
      {y₁ : T ⟶ x.groupScheme} {y₂' : T ⟶ x'.groupScheme} {y₂ : T ⟶ x.groupScheme}
      (h₁ : AgreeModEps hq' hq T y₁' y₁) (h₂ : AgreeModEps hq' hq T y₂' y₂) :
      AgreeModEps hq' hq T (y₁' - y₂') (y₁ - y₂) := by
    intro B b t
    simp [h₁ B b t, h₂ B b t, AddGrpObj.comp_sub]
  have h_ker {T : Over (Spec (of (TrivSqZeroExt k k)))} (y' : T ⟶ x'.groupScheme)
      (h_agree : AgreeModEps hq' hq T y' 0) : y' ≫ (c • 𝟙 x'.groupScheme) = 0 := by
    simpa [comp_nsmul] using hc T y' (by simpa using h_agree)
  -- `AgreeModEps` is stable under pull-back, and the affine opens `j a` cover `x.groupScheme`.
  have h_nat {T' T : Over (Spec (of (TrivSqZeroExt k k)))} {y' : T ⟶ x'.groupScheme}
      {y : T ⟶ x.groupScheme} (g : T' ⟶ T) (h_agree : AgreeModEps hq' hq T y' y) :
      AgreeModEps hq' hq T' (g ≫ y') (g ≫ y) :=
    fun B b t ↦ h_agree B b (t ≫ g)
  have h_cover : Presieve.ofArrows (fun a ↦ Spec (C a)) j ∈
      Scheme.fpqcPrecoverage x.groupScheme.left :=
    zariskiPrecoverage_le_fpqcPrecoverage _ (by aesop)
  obtain ⟨F, hF_add, hF⟩ := exists_hom_of_rel (c • 𝟙 _) (AgreeModEps hq' hq _) h_nat h_sub h_ker
    (.ofArrows _ j) h_cover fun _ _ ⟨a⟩ ↦ h_local a
  have h_val (T : Over (Spec (of (TrivSqZeroExt k k)))) (y' : T ⟶ x'.groupScheme)
      (y : T ⟶ x.groupScheme) (h_agree : AgreeModEps hq' hq T y' y) : y ≫ F = c • y' := by
    simpa using hF T y' y h_agree
  -- The two inclusions of the reduction `x₀.groupScheme` agree modulo `ε`.
  have h_incl : AgreeModEps hq' hq ((Over.map (sqZeroReduction k k)).obj x₀.groupScheme)
      hq'.schemeMap hq.schemeMap := by
    intro B b t
    ext
    simp [pointEquiv, IsPullbackAlong.comp_toFamily]
  exact ⟨F, hF_add, h_val _ hq'.schemeMap hq.schemeMap h_incl, h_val⟩

end DrinfeldLifting

/-! ## Homomorphisms of deformations that reduce to multiplication by `a` -/

section LiftedIsogenies

open CategoryTheory Over AlgebraicGeometry NumberField Category ThetaObject Obj Spec DualNumber
  IsGroupBaseChange Algebra MorphismProperty IsArtinianRing IsClosedImmersion

variable {E k : Type} [Field E] [CMBase E]
  {D : PEL E} [Field k] [IsAlgClosed k]
  {Z : Scheme} {σ : Z ⟶ Spec (CommRingCat.of (𝓞 E))} {Y : ThetaFamily D Z σ}
  {x₀ : ThetaObject Y (Spec (CommRingCat.of k))}
  {x x' : ThetaObject Y (Spec (CommRingCat.of (TrivSqZeroExt k k)))}
  {hq : IsPullbackAlong (sqZeroReduction k k) x₀ x}
  {hq' : IsPullbackAlong (sqZeroReduction k k) x₀ x'}
  (f : x.groupScheme ⟶ x'.groupScheme) [IsAdditive f] {a : 𝓞 E}
  (hf : hq.schemeMap ≫ f = a • hq'.schemeMap) [Fact (ringChar k).Prime]

/-- The dual numbers `k[ε] = k × k` are a finite `k`-module. -/
instance : Module.Finite k k[ε] := .prod

include hf

/-- Let `f : x.groupScheme ⟶ x'.groupScheme` be a homomorphism of deformations of `x₀.groupScheme`
over `k[ε]`, `k` algebraically closed of prime characteristic, that reduces to multiplication by `a`
(`hf : hq.schemeMap ≫ f = a • hq'.schemeMap`). Then (a) `f` is linear over `𝓞 E`; (b) if `f` kills
`y`, then `a y` agrees with `0` modulo `ε`; (c) if `x` is a pull-back of `x₀`, then
`⟨f y, f z⟩ = ⟨a y, a z⟩` for the pairings (`New.Pic.pairing`) of the Pic classes
`lineBundle.picClass` of the line bundles of `x'` and `x`. -/
lemma isLinear_and_pairing_eq_of_reduction :
    IsLinear f ∧
    (∀ {T : Over (Spec (CommRingCat.of (TrivSqZeroExt k k)))} (y : T ⟶ x.groupScheme),
      y ≫ f = 0 → AgreeModEps hq hq T (a • y) 0) ∧
    ∀ {s : Spec (CommRingCat.of (TrivSqZeroExt k k)) ⟶ Spec (CommRingCat.of k)},
      x.IsPullbackAlong s x₀ →
      ∀ ⦃T : Over (Spec (CommRingCat.of (TrivSqZeroExt k k)))⦄ (y z : T ⟶ x.groupScheme),
      x'.lineBundle.picClass.pairing (y ≫ f) (z ≫ f) =
        x.lineBundle.picClass.pairing (y ≫ (a • 𝟙 x.groupScheme)) (z ≫ (a • 𝟙 x.groupScheme)) := by
  -- On points whose base lies in `ε = 0`, the map `f` is multiplication by `a` on `x₀.groupScheme`.
  have h_red {T : Over (Spec (CommRingCat.of k))}
      (v : (map (sqZeroReduction k k)).obj T ⟶ x.groupScheme) :
      v ≫ f = hq'.isGroupBaseChange.pointEquiv (hq.isGroupBaseChange.pointEquiv.symm (a • v)) ∧
      x'.lineBundle.picClass.atPoint (v ≫ f) = x.lineBundle.picClass.atPoint (a • v) := by
    obtain ⟨w, rfl⟩ := hq.isGroupBaseChange.pointEquiv.surjective v
    rw [← map_smul, LinearEquiv.symm_apply_apply]
    simp [pointEquiv_apply, ← (IsPullbackAlong.isGroupBaseChange _).linear.map_smul, Pic.atPoint,
      ← IsPullbackAlong.lineBundle_eq_pull, hf]
  have h_isog_char : IsIsogeny (ringChar k • 𝟙 x.groupScheme) :=
    mod_cast x.isIsogeny_smul_id (a := ringChar k) NeZero.out
  -- For the pairing, `pairing_eq_of_fpqc_cover` lets us assume that the first point is a multiple
  -- of `ringChar k`, since multiplication by it is a flat cover of `x.groupScheme`.
  refine ⟨⟨fun c ↦ ?_⟩, fun y hy B b t ↦ ?_, fun hs ↦ ?_⟩
  · -- The defect of linearity vanishes modulo `ε`, so `ringChar k` kills it; cancel this isogeny.
    have h_agree : AgreeModEps hq' hq' x.groupScheme ((c • 𝟙 x.groupScheme) ≫ f - c • f) 0 := by
      simp [AgreeModEps, ← assoc, h_red, smul_comm c, AddGrpObj.comp_sub]
    obtain ⟨h_char_kills, -⟩ := h_agree.ringChar_smul_and_smul_eq_zero hq'
    refine (epi_of_epi_left (ringChar k • 𝟙 _)).left_cancellation _ _ (eq_of_sub_eq_zero ?_)
    simpa [← smul_sub, nsmul_comp] using h_char_kills
  · -- `t` lies over `ε = 0`, where `h_red` turns `f` into `a`. `map_smul` is left out: with it
    -- `simp` moves `a` across `pointEquiv` and the fact no longer matches the goal.
    have h_zero : t ≫ y ≫ f = t ≫ 0 := t ≫= hy
    simpa [← assoc, h_red, -map_smul] using h_zero
  · refine pairing_eq_of_fpqc_cover hs.isGroupBaseChange.isPullback (ringChar k • 𝟙 _) f f _ _
      fun T y z ↦ ?_
    -- So we compare the pairings times `ringChar k`. That multiple of a class is its pull-back
    -- along the absolute Frobenius `Fr` of `T`, which factors through `ε = 0`, where `h_red`
    -- applies.
    let X : Over (Spec (CommRingCat.of k)) := Over.mk (T.hom ≫ (specOver k _).hom)
    let Fr :
        (map (sqZeroReduction k k)).obj
          (mk (X.hom ≫ specMap (frobPow (natCast_eq_zero_of_over_charP (𝟙 _)) 1))) ⟶ T :=
      homMk (absFrobenius 1 X) <| by
        rw [absFrobenius_comm 1 X (specOver ..), ← id_comp (absFrobenius ..), comp_absFrobenius]
        -- On `k[ε]` the Frobenius kills `ε`, so it factors through `k`.
        simpa [X] using _ ≫= homEquiv.injective (by aesop (add simp CharP.cast_eq_zero))
    have h_frob {x : ThetaObject Y _} (y : T ⟶ x.groupScheme) :
        ringChar k • x.lineBundle.picClass.atPoint y = x.lineBundle.picClass.atPoint (Fr ≫ y) := by
      have h_lin_sys : x.lineBundle.IsLinearSystem := x.isProjEmbedding.isLinearSystem
      have h_pull : ringChar k ^ 1 • (x.lineBundle.pull y.left).picClass =
          ((x.lineBundle.pull y.left).pull (absFrobenius 1 X)).picClass :=
        picClass_pull_absFrobenius 1 X (h_lin_sys.pull y.left)
      rw [pow_one] at h_pull
      -- Both sides are pull-backs of the line bundle of `x`; they match the lemma up to unfolding.
      exact h_pull
    suffices h_mul : ringChar k • x'.lineBundle.picClass.pairing (y ≫ f) (z ≫ f) =
        ringChar k • x.lineBundle.picClass.pairing (a • y) (a • z) by
      simpa [(ThetaObject.hasClassLaws _).1.pairing_nsmul_left, nsmul_comp, comp_nsmul] using h_mul
    simp [Pic.pairing, smul_sub, h_frob, ← add_comp, ← assoc, (h_red _).right, comp_add]

/-- Let `f : x.groupScheme ⟶ x'.groupScheme` and `F : x.groupScheme ⟶ x₁.groupScheme` be
homomorphisms of deformations of `x₀.groupScheme` over `k[ε]` (`k` algebraically closed of prime
characteristic) that reduce to multiplication by `a ≠ 0` (`hf`) and by `c a`. If `F` kills every
point `y` over a finite local noetherian `k[ε]`-algebra with `f y = 0` and `a² y = 0`, then some
homomorphism `x'.groupScheme ⟶ x₁.groupScheme` reduces to multiplication by `c`. -/
lemma exists_isAdditive_schemeMap_comp_eq_smul (ha : a ≠ 0)
    {x₁ : ThetaObject Y (Spec (CommRingCat.of (TrivSqZeroExt k k)))}
    (hq₁ : IsPullbackAlong (sqZeroReduction k k) x₀ x₁) (F : x.groupScheme ⟶ x₁.groupScheme)
    [IsAdditive F] (c : 𝓞 E) (hF : hq.schemeMap ≫ F = (c * a) • hq₁.schemeMap)
    (h_ker :
      ∀ (S : Type) [CommRing S] [IsLocalRing S] [Algebra k[ε] S] [Module.Finite k[ε] S]
          [IsNoetherianRing S] (y : specOver (TrivSqZeroExt k k) S ⟶ x.groupScheme),
        y ≫ f = 0 → a • a • y = 0 →
        y ≫ F = 0) :
    ∃ μ : x'.groupScheme ⟶ x₁.groupScheme,
      IsAdditive μ ∧ hq'.schemeMap ≫ μ = c • hq₁.schemeMap := by
  -- `f` is an isogeny whose kernel is killed by `a ^ 2`, so `F` factors as `f ≫ μ`; then `μ`
  -- reduces to `c` because `f` reduces to `a`.
  obtain ⟨h_lin, h_ker_agree, -⟩ := isLinear_and_pairing_eq_of_reduction f hf
  have h_artinian : IsArtinianRing k[ε] := of_finite k k[ε]
  have h_isog_a : IsIsogeny (a • 𝟙 x₀.groupScheme) := x₀.isIsogeny_smul_id ha
  -- The reductions do not change the underlying spaces, so `f` is quasi-finite and onto as `a` is.
  have h_surj : Surjective hq.schemeMap.left :=
    of_isPullback hq.isGroupBaseChange.isPullback.flip isSqZeroExt_fstHom.surjective_specMap
  have h_surj' : Surjective hq'.schemeMap.left :=
    of_isPullback hq'.isGroupBaseChange.isPullback.flip isSqZeroExt_fstHom.surjective_specMap
  have h_closed' : IsClosedImmersion hq'.schemeMap.left :=
    of_isPullback hq'.isGroupBaseChange.isPullback.flip
      (spec_of_surjective _ isSqZeroExt_fstHom.coe_surjective)
  -- Multiplication by `a` commutes with the inclusion of the reduction.
  have h_sq : (a • 𝟙 x₀.groupScheme).left ≫ hq'.schemeMap.left = hq.schemeMap.left ≫ f.left := by
    simpa [← hf] using
      congr_arg CommaMorphism.left (hq'.isGroupBaseChange.linear.map_smul a (𝟙 x₀.groupScheme))
  have h_quasi : LocallyQuasiFinite f.left := by
    refine .of_finite_preimage_singleton _ fun z ↦ ?_
    have h_fin := ((a • 𝟙 x₀.groupScheme).left ≫ hq'.schemeMap.left).finite_preimage_singleton z
    rw [h_sq] at h_fin
    exact .of_preimage h_fin h_surj.surj
  have h_surj_comp : Surjective (hq.schemeMap.left ≫ f.left) := by
    rw [← h_sq]
    infer_instance
  have h_isog : IsIsogeny f := isIsogeny_of_locallyQuasiFinite f h_quasi
    (.of_comp hq.schemeMap.left _)
  -- The kernel of `f` is killed by `a ^ 2`.
  have h_kill {T : Over (Spec (CommRingCat.of (TrivSqZeroExt k k)))} (y : T ⟶ x.groupScheme)
      (hy : y ≫ f = 0) : a • a • y = 0 := by
    -- The kernel of `f` is `Spec S`. On it, multiplication by `a` is a ring map `γ`, the zero
    -- section is `o`, and `γ ≡ o` modulo `ε` by `h_ker_agree`.
    obtain ⟨S, ι, -, -, hι_closed, hι, h_univ⟩ := exists_finite_kernel_ring h_isog.toIsFinite
    obtain ⟨z, rfl⟩ := h_univ y hy
    obtain ⟨γ, hγ⟩ : ∃ γ : S →ₐ[k[ε]] S, specOver.map γ ≫ ι = a • ι :=
      specOver.map_bijective.surjective.exists.mp (h_univ (a • ι) (by simp [hι]))
    obtain ⟨o, ho⟩ : ∃ o : S →ₐ[k[ε]] k[ε], specOver.map o ≫ ι = 0 :=
      specOver.map_bijective.surjective.exists.mp (h_univ 0 (by simp))
    -- `ψ` is the quotient map of `S` modulo `ε`, and `u` the closed immersion it defines.
    obtain ⟨B, ψ, b, hψ, -, hψ_ker, -⟩ := exists_isReductionModEps (specOver k[ε] S).hom
    let u : (map (sqZeroReduction k k)).obj (mk b) ⟶ specOver _ S := homMk _ hψ
    have hu : u ≫ specOver.map γ = u ≫ specOver.map (.comp (ofId ..) o) :=
      (mono_of_mono_left ι).right_cancellation _ _ <| by
        -- `map_smul` is left out: with it `simp` moves `a` out of `pointEquiv`, off the goal.
        simpa [← specOver.map_comp_assoc, -map_smul, hγ, ho] using h_ker_agree ι hι _ _ u
    have h_split (s : S) :
        ∃ d : S, γ s = preimage (specOver k[ε] S).hom ε * d + ofId _ S (o s) := by
      have h_eq : preimage (u ≫ specOver.map γ).left s =
          preimage (u ≫ specOver.map ((ofId _ S).comp o)).left s := by rw [hu]
      have h_dvd : preimage (specOver k[ε] S).hom ε ∣ γ s - ofId _ S (o s) :=
        (hψ_ker _).mp (by simpa [specOver.map, u, sub_eq_zero] using h_eq)
      exact Exists.imp (fun _ ↦ eq_add_of_sub_eq) h_dvd
    choose d hd using h_split
    -- With `γ s = ε * d s + o s` and `ε * ε = 0`, both sides below are `ε * o (d s) + o s`.
    -- On points: applying `a` twice factors through the zero section, so `a • a • ι = 0`.
    have hγγ : γ.comp γ = .comp (.comp (ofId ..) o) γ := by
      ext s
      simp [hd s, hd (d s), ← smul_def, smul_smul]
    have h_comp : z ≫ specOver.map (γ.comp γ) ≫ ι =
        z ≫ specOver.map (((ofId _ S).comp o).comp γ) ≫ ι := by rw [hγγ]
    simpa [← specOver.map_comp_assoc, hγ, ho] using h_comp
  -- Hence `F` kills the kernel of the isogeny `f`, and `F = f ≫ μ`.
  obtain ⟨μ, hμ_add, hμ⟩ := exists_isAdditive_comp_eq_of_isIsogeny f F
    fun S _ _ _ _ _ y hy ↦ h_ker S y hy (h_kill y hy)
  refine ⟨μ, hμ_add, ?_⟩
  -- Modulo `ε` this is the claim multiplied by `a`; cancel the isogeny `a` of `x₀.groupScheme`.
  have h_epi : Epi (a • 𝟙 x₀.groupScheme) := epi_of_epi_left _
  simp [← cancel_epi ((map (sqZeroReduction k k)).map (a • 𝟙 x₀.groupScheme)), ← assoc,
    (IsPullbackAlong.isGroupBaseChange _).linear.map_smul, smul_smul, ← hF, ← hμ, hf]

end LiftedIsogenies

end New.Variety

/-!
## The tangent bound for deformations with no constant direction

An object `x` has the abelian scheme `x.groupScheme` and the ring map `x.baseHom` from `𝓞 E`.

Idea: lift the `𝔭`-torsion points of `x₀.groupScheme` (`𝔭 = ker x₀.baseHom`) with values in a local
`k`-algebra `C` to points of `x.groupScheme` over `C ⊕ Hom(M, C)`, multiply by an element of `𝔭` and
take logarithms. These maps bound the dimension, and a direction that they all kill is constant.
-/

namespace New.Variety.TangentBound

open CategoryTheory AlgebraicGeometry TrivSqZeroExt ThetaObject Obj IsGroupBaseChange CommRingCat
  DualNumber Module Dual Spec Over OverMorphism RingHom Algebra

variable {E k M : Type} [Field E] [CMBase E] {D : PEL E} [Field k] {Z : Scheme}
  {σ : Z ⟶ Spec (of (NumberField.RingOfIntegers E))} [AddCommGroup M] [Module k M]
  {X : ThetaFamily D Z σ} {x₀ : ThetaObject X (Spec (of k))}
  {x : ThetaObject X (Spec (of (TrivSqZeroExt k (M →ₗ[k] k))))}
  (hp : IsPullbackAlong (sqZeroReduction k (M →ₗ[k] k)) x₀ x) ⦃C : Type⦄ {C' : Type _} [CommRing C]
  [Algebra k C] [CommRing C'] [Algebra k C'] (φ : C →ₐ[k] C')

instance : CommRing (TrivSqZeroExt C (M →ₗ[k] C)) := inferInstance

/-- `k ⊕ M*` is a local ring: an element is a unit exactly when its first component is not zero. -/
instance : IsLocalRing (TrivSqZeroExt k (M →ₗ[k] k)) :=
  .of_nonunits_add fun a b _ _ ↦ by simp_all [isUnit_iff_isUnit_fst]

/-! ### The rings `C ⊕ Hom(M, C)` and lifts of points -/

/-- For a k-algebra map φ: C → C', the ring homomorphism C ⊕ Hom_k(M,C) → C' ⊕ Hom_k(M,C') of
trivial square-zero extensions given by φ and composition with φ. -/
@[simps]
def sqZeroMap : TrivSqZeroExt C (M →ₗ[k] C) →+* TrivSqZeroExt C' (M →ₗ[k] C') where
  toFun x := inl (φ x.fst) + inr (φ ∘ₗ x.snd)
  map_one' := by aesop
  map_mul' := by aesop
  map_zero' := by aesop
  map_add' := by aesop

/-- The reduction `Spec C ⟶ Spec (C ⊕ Hom(M, C))` induced by the first projection, as a morphism
over `Spec (k ⊕ M*)`. -/
def toSqZeroSpec (C : Type) [CommRing C] [Algebra k C] :
    Over.map (sqZeroReduction k (M →ₗ[k] k)) (specOver k C) ⟶
      Over.mk (specMap (sqZeroMap (ofId k C))) :=
  homMk (sqZeroReduction C (M →ₗ[k] C)) <| by
    simp [← map_comp, ↓map_inj]
    cat_disch

/-- Every point `y` of `x₀.groupScheme` with values in a local `k`-algebra `C` lifts to a point `Z`
of `x.groupScheme` with values in `C ⊕ Hom(M, C)`: the reduction of `Z` is `y`, seen in
`x.groupScheme` through `hp.isGroupBaseChange.pointEquiv`. -/
lemma exists_point_lift [IsLocalRing C] (y : specOver k C ⟶ x₀.groupScheme) :
    ∃ Z : Over.mk (specMap (sqZeroMap (ofId k C))) ⟶ x.groupScheme,
      toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv y := by
  -- In a chart around the image of the closed point, lift the point along the square-zero
  -- extension, keeping its coordinates.
  let y' : Over.map (sqZeroReduction k (M →ₗ[k] k)) (specOver k C) ⟶ x.groupScheme :=
    hp.isGroupBaseChange.pointEquiv y
  obtain ⟨V, z, h_mem, h_chart⟩ :=
    exists_isEtaleChart (y'.left (IsLocalRing.closedPoint C)) x.smoothOfRelativeDimension
  obtain ⟨Z, ⟨hZ_red, -⟩, -⟩ := h_chart (t := specMap (sqZeroMap (ofId k C))) y'.left (inl ∘ _)
    (landsIn_iff_mem.2 h_mem) ((Over.w y').trans (toSqZeroSpec C).w.symm) rfl
  exact ⟨Z, ext hZ_red⟩

/-- For a k-algebra map φ: C → C', the induced morphism Spec(C' ⊕ Hom_k(M,C')) → Spec(C ⊕
Hom_k(M,C)) over Spec(k ⊕ M*), M* the dual of M. -/
def sqZeroSpecMap :
    Over.mk (specMap (sqZeroMap (ofId k C'))) ⟶ Over.mk (specMap (sqZeroMap (M := M) (ofId k C))) :=
  homMk (specMap (sqZeroMap φ)) <| by
    simp [← map_comp, ↓map_inj]
    cat_disch

/-- Lifts are natural in the algebra: if `Z` lifts the `C`-point `y`, then the image of `Z` along
`φ : C → C'` lifts the image of `y`. -/
lemma sqZeroSpecMap_point_lift {y : specOver k C ⟶ x₀.groupScheme}
    {Z : Over.mk (specMap (sqZeroMap (ofId k C))) ⟶ x.groupScheme}
    (hZ : toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv y) :
    toSqZeroSpec C' ≫ sqZeroSpecMap φ ≫ Z =
      hp.isGroupBaseChange.pointEquiv (specOver.map φ ≫ y) := by
  simp [pointEquiv_apply] at *
  ext
  simp [← hZ, toSqZeroSpec, sqZeroSpecMap, specOver.map, ← map_comp_assoc, ← ofHom_comp]
  -- on rings, `sqZeroMap φ` followed by the reduction `fstHom` is the reduction followed by `φ`
  congr 2
  aesop

/-- A point of `x.groupScheme` with values in `C ⊕ Hom(M, C)` whose reduction to `C` is zero is
infinitesimal for the first projection. -/
lemma isInfinitesimal_of_comp_eq_zero
    (Z : Over.mk (specMap (sqZeroMap (ofId k C))) ⟶ x.groupScheme) :
    toSqZeroSpec C ≫ Z = 0 → IsInfinitesimal (ofHom (fstHom C C (M →ₗ[k] C)).toRingHom) Z := by
  -- without `↓` this `simp` leaves a goal that `tauto` does not close
  simp [IsInfinitesimal, ↓eq_zero_iff_factors_zero_section]
  tauto

/-! ### The bound -/

open NumberField in
/-- Let `k` be an algebraically closed field of prime characteristic `p`, and let `x₀` be a rigid
(`HasSpanningCoords`) object of the family `X` over `k`. Let `z`, `z₀` be objects over `k[ε]` that
both reduce to `x₀`, with `z₀` the constant deformation (the pull-back of `x₀` along `k → k[ε]`) and
with `𝓞 E → k[ε]` for `z` factoring through `k`. Let `b : ℤ` satisfy: `D.β - b` (for the PEL integer
`D.β`) lies in `ker x₀.baseHom`; `D.β - b` and `star D.β - b` are coprime; and the ideal of the
level `D.level` together with `ker x₀.baseHom` times the ideal of `p` and `star D.β - b` is the unit
ideal. If an additive map `f` from the group scheme of `z₀` to that of `z` restricts over `x₀` to
`star D.β - b`, then `z₀ = z`. -/
lemma eq_of_lift_star_sub [IsAlgClosed k] [Fact (ringChar k).Prime] (h_rig : x₀.HasSpanningCoords)
    {z z₀ : ThetaObject X (Spec (of (TrivSqZeroExt k k)))}
    (hq : IsPullbackAlong (sqZeroReduction k k) x₀ z)
    (hq₀ : IsPullbackAlong (sqZeroReduction k k) x₀ z₀)
    (hz₀ : IsPullbackAlong (specMap (algebraMap k k[ε])) z₀ x₀)
    (hρ : z.baseHom = (algebraMap k k[ε]).comp x₀.baseHom) {b : ℤ} (hb : x₀.baseHom (D.β - b) = 0)
    (h_coprime : IsCoprime (D.β - b) (Star.star D.β - b))
    (h_level :
      Ideal.span {D.level} ⊔ ker x₀.baseHom * Ideal.span {↑(ringChar k), Star.star D.β - b} = ⊤)
    (f : z₀.groupScheme ⟶ z.groupScheme) [IsAdditive f]
    (hf : hq₀.schemeMap ≫ f = (Star.star D.β - b) • hq.schemeMap) :
    z₀ = z := by
  -- Divide twice to get a map `z₀.groupScheme ⟶ z.groupScheme` that reduces to the identity. It
  -- respects the pairing and the level points, so rigidity (`eq_and_comp_toFamily_eq_of_hom`)
  -- applies.
  obtain ⟨u, v, huv⟩ := h_coprime
  -- if `star D.β - b = 0`, then `huv` maps to `0 = 1` in `k`, as `x₀.baseHom (D.β - b) = 0`
  have h_ne : Star.star D.β - b ≠ 0 := fun h_zero ↦ by
    simpa [h_zero, hb] using congrArg x₀.baseHom huv
  -- The kernel of `f` is killed by `a = star β - b`, so `a • 𝟙` factors through `f`.
  obtain ⟨μ, _, hμ⟩ :
      ∃ μ : z.groupScheme ⟶ z₀.groupScheme,
        IsAdditive μ ∧ hq.schemeMap ≫ μ = (1 : 𝓞 E) • hq₀.schemeMap := by
    refine exists_isAdditive_schemeMap_comp_eq_smul f hf h_ne hq₀ ((star D.β - b) • 𝟙 _) 1 (by simp)
      fun S _ _ _ _ _ y hy hyy ↦ ?_
    -- `(β - b) a y` is killed by the characteristic and pairs to zero with every point, so it is
    -- zero by rigidity; the adjoint of `β - b` for the pairing is `a`
    have h_zero : (D.β - b) • (Star.star D.β - b) • y = 0 := by
      refine h_rig.eq_zero_of_pairing_eq_zero hz₀ _ 1 (𝟙 _) ?_ fun T t y' ↦ ?_
      · simp [smul_comm _ (D.β - _), AgreeModEps.ringChar_smul_and_smul_eq_zero hq₀,
          isLinear_and_pairing_eq_of_reduction f hf, hy]
      · calc
          z₀.lineBundle.picClass.pairing (t ≫ ((D.β - b) • (star D.β - b) • y)) y'
          _ = z₀.lineBundle.picClass.pairing ((star D.β - b) • t ≫ y) ((star D.β - b) • y') := by
            simpa using z₀.pairing_pow_smul_adjoint b 1 ((star D.β - b) • t ≫ y) y'
          _ = z.lineBundle.picClass.pairing ((t ≫ y) ≫ f) (y' ≫ f) := by
            obtain ⟨-, -, f_pair⟩ := isLinear_and_pairing_eq_of_reduction f hf
            simpa using (f_pair hz₀ (t ≫ y) y').symm
          _ = 0 := by simp [hy, Pic.pairing.eq_1 _ 0]
    -- now use `u (β - b) + v a = 1` and `a² y = 0`
    suffices (1 : 𝓞 E) • (Star.star D.β - b) • y = 0 by simpa using this
    simp [← huv, add_smul, h_zero, hyy, ← smul_smul]
  -- As `μ` reduces to `1`, the identity of `z.groupScheme` factors through it.
  obtain ⟨ν, _, hν⟩ :
      ∃ ν : z₀.groupScheme ⟶ z.groupScheme,
        IsAdditive ν ∧ hq₀.schemeMap ≫ ν = (1 : 𝓞 E) • hq.schemeMap :=
    exists_isAdditive_schemeMap_comp_eq_smul μ hμ one_ne_zero hq (𝟙 _) 1 (by simp) (by simp)
  obtain ⟨ν_lin, -, ν_pair⟩ := isLinear_and_pairing_eq_of_reduction ν hν
  have h_base : z₀.baseHom = z.baseHom := hz₀.baseHom_eq_comp.trans hρ.symm
  have h_pair : ∀ ⦃T : Over (Spec (of (TrivSqZeroExt k k)))⦄ (y y' : T ⟶ z₀.groupScheme),
      z₀.lineBundle.picClass.pairing y y' = z.lineBundle.picClass.pairing (y ≫ ν) (y' ≫ ν) := by
    simp [ν_pair hz₀]
  refine (h_rig.eq_and_comp_toFamily_eq_of_hom hz₀ h_base ν h_pair fun l ↦ ?_).1
  -- The difference `d` of the level points is killed by `𝔑`; being infinitesimal, it is also killed
  -- by the second ideal of `h_level`. The two ideals are coprime, so `d = 0`.
  set d := z₀.levelPoints l ≫ ν - z.levelPoints l
  have d_inf : AgreeModEps hq hq _ d 0 := by
    intro _ _ t
    -- `t.w` says that the test point lies over the closed point of `Spec k[ε]`
    have h_t := by simpa using t.w
    simp [d, hq.levelPoints_eq_pullSection, ← hq₀.levelPoints_eq_pullSection, hν,
      OverMorphism.ext_iff, h_t, ← hq.isGroupBaseChange.pullSection_comp,
      ← hq₀.isGroupBaseChange.pullSection_comp_assoc, ← comp_left _ _ _ hq₀.schemeMap,
      AddGrpObj.comp_sub, sub_eq_zero]
  have d_char : ringChar k • d = 0 := d_inf.ringChar_smul_and_smul_eq_zero.left
  have d_star {a : 𝓞 E} (ha : x₀.baseHom a = 0) : ((Star.star D.β - b) * a) • d = 0 :=
    d_inf.ringChar_smul_and_smul_eq_zero.right hρ hb ha
  have h_lev : Ideal.span {D.level} ≤ Ideal.torsionOf (𝓞 E) _ d := by
    have h_torsion : D.level • l = 0 := Subtype.ext l.prop
    simp [d, smul_sub, ← IsLinear.smul_comp, h_torsion, ← map_smul]
  have h_inf :
      ker x₀.baseHom * Ideal.span {↑(ringChar k), Star.star D.β - b} ≤
        Ideal.torsionOf (𝓞 E) _ d := by
    simpa [mul_comm, Ideal.span_insert, Ideal.sup_mul, Ideal.span_singleton_mul_le_iff,
      Nat.cast_smul_eq_nsmul, d_char, ← smul_smul] using fun _ ↦ d_star
  exact eq_of_sub_eq_zero ((Ideal.torsionOf_eq_top_iff ..).mp (eq_top_mono (sup_le h_lev h_inf)
    h_level))

open scoped Pointwise in
open NumberField in
/-- The data that the proof of the tangent bound fixes before its last step, for the lift `x` of
`x₀` given by `hp`, with `𝔭 = ker x₀.baseHom`: the elements `generator`, `localizer`, `residueInt`
with their conditions modulo `𝔭`, the `logarithm` of `New.ThetaObject.exists_tangent_log` (on points
`z` with `IsInfinitesimal ψ z`: `z` restricts to `0` over `Spec C'`, for `ψ : C ⟶ C'` onto with
square-zero kernel) with its properties, lifts `liftPoint y` of points of `x₀.groupScheme`
(`exists_point_lift`), and the fact that `logarithm (generator • Z)` does not depend on the lift `Z`
of a `𝔭`-torsion point. -/
private structure TangentBoundData where
  /-- An element of `𝔭` that generates it locally. -/
  generator : 𝓞 E
  /-- `generator` lies in `𝔭`. -/
  map_generator : x₀.baseHom generator = 0
  /-- `generator` is not zero. -/
  generator_ne_zero : generator ≠ 0
  /-- An element congruent to `1` modulo `𝔭` that multiplies `𝔭` into `(generator)`. -/
  localizer : 𝓞 E
  /-- `localizer ≡ 1` modulo `𝔭`. -/
  sub_one_mem : localizer - 1 ∈ ker x₀.baseHom
  /-- `localizer • 𝔭 ⊆ (generator)`. -/
  smul_ker_le_span : localizer • ker x₀.baseHom ≤ Ideal.span {generator}
  /-- An integer congruent to `D.β` modulo `𝔭`. -/
  residueInt : ℤ
  /-- `D.β - residueInt` lies in `𝔭`. -/
  map_β_sub_int : x₀.baseHom (D.β - residueInt) = 0
  /-- `D.β - residueInt` and `star D.β - residueInt` are coprime. -/
  isCoprime : IsCoprime (D.β - residueInt) (star D.β - residueInt)
  /-- The level condition: `(𝔑) + 𝔭 (p, star D.β - residueInt) = 𝓞 E`, `p` the characteristic
  of `k`. -/
  level_eq_top : Ideal.span {D.level} ⊔
    ker x₀.baseHom * Ideal.span {↑(ringChar k), star D.β - residueInt} = ⊤
  /-- The logarithm of a point of `x.groupScheme` with values in `C`. -/
  logarithm : ∀ ⦃C : CommRingCat⦄ ⦃s : Spec C ⟶ Spec (of (TrivSqZeroExt k (M →ₗ[k] k)))⦄,
    (Over.mk s ⟶ x.groupScheme) → C
  /-- On infinitesimal points, `a • z` has logarithm `x₀.baseHom a` times that of `z`. -/
  logarithm_smul : ∀ ⦃C C' : CommRingCat⦄ ⦃ψ : C ⟶ C'⦄ [IsSqZeroExt ψ]
      ⦃s : Spec C ⟶ Spec (of (TrivSqZeroExt k (M →ₗ[k] k)))⦄ ⦃z : Over.mk s ⟶ x.groupScheme⦄,
      IsInfinitesimal ψ z →
    ∀ a : 𝓞 E, logarithm (a • z) = preimage s (inl (x₀.baseHom a)) * logarithm z
  /-- An infinitesimal point with logarithm `0` is killed by `star D.β - residueInt`. -/
  smul_eq_zero_of_logarithm : ∀ ⦃C C' : CommRingCat⦄ ⦃ψ : C ⟶ C'⦄ [IsSqZeroExt ψ]
      ⦃s : Spec C ⟶ Spec (of (TrivSqZeroExt k (M →ₗ[k] k)))⦄ ⦃z : Over.mk s ⟶ x.groupScheme⦄,
      IsInfinitesimal ψ z →
    logarithm z = 0 → (star D.β - residueInt) • z = 0
  /-- The logarithm of an infinitesimal point lies in the kernel of `ψ`. -/
  map_logarithm_eq_zero : ∀ ⦃C C' : CommRingCat⦄ ⦃ψ : C ⟶ C'⦄ [IsSqZeroExt ψ]
      ⦃s : Spec C ⟶ Spec (of (TrivSqZeroExt k (M →ₗ[k] k)))⦄ ⦃z : Over.mk s ⟶ x.groupScheme⦄,
      IsInfinitesimal ψ z → ψ (logarithm z) = 0
  /-- On infinitesimal points, the logarithm is natural in the ring of values. -/
  logarithm_comp : ∀ ⦃C C' : CommRingCat⦄ ⦃ψ : C ⟶ C'⦄ [IsSqZeroExt ψ]
      ⦃s : Spec C ⟶ Spec (of (TrivSqZeroExt k (M →ₗ[k] k)))⦄ ⦃z : Over.mk s ⟶ x.groupScheme⦄,
      IsInfinitesimal ψ z →
    ∀ ⦃C₁ : CommRingCat⦄ ⦃χ : C ⟶ C₁⦄ ⦃s₁ : Spec C₁ ⟶ Spec (of (TrivSqZeroExt k (M →ₗ[k] k)))⦄
      (a : Over.mk s₁ ⟶ Over.mk s),
      a.left = Spec.map χ → logarithm (a ≫ z) = χ (logarithm z)
  /-- A lift of a point `y` of `x₀.groupScheme` to `x.groupScheme` over `C ⊕ Hom(M, C)`. -/
  liftPoint : ∀ ⦃C : Type⦄ [CommRing C] [Algebra k C] [IsLocalRing C],
    (specOver k C ⟶ x₀.groupScheme) →
      (Over.mk (specMap (sqZeroMap (ofId k C))) ⟶ x.groupScheme)
  /-- `liftPoint y` reduces to `y`. -/
  comp_liftPoint_eq : ∀ ⦃C : Type⦄ [CommRing C] [Algebra k C] [IsLocalRing C]
      (y : specOver k C ⟶ x₀.groupScheme),
    toSqZeroSpec C ≫ liftPoint y = hp.isGroupBaseChange.pointEquiv y
  /-- For a `𝔭`-torsion point `y`, `logarithm (generator • Z)` is the same for every lift `Z`
  of `y`. -/
  logarithm_smul_liftPoint_eq : ∀ {C : Type} [CommRing C] [Algebra k C] [IsLocalRing C]
      (y : placeTorsion x₀ C) (Z : Over.mk (specMap (sqZeroMap (ofId k C))) ⟶ x.groupScheme),
    toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv y →
      logarithm (generator • liftPoint y.val) = logarithm (generator • Z)

/-- The last step of the tangent bound. Let `k` be algebraically closed of prime characteristic,
`x₀` rigid (`h_rig`), `𝓞 E` map to `k ⊕ M*` through `k` (`hρ`), and let `l ∈ M` be `0` as soon as
the pull-back of `x` along `(a, φ) ↦ a + φ(l) ε` is constant (`h_const`). If for every `𝔭`-torsion
point `y` (`𝔭 = ker x₀.baseHom`) with values in a finite local `k`-algebra the logarithm of
`S.generator • S.liftPoint y` has second component `0` at `l`, then `l = 0`. -/
private lemma eq_zero_of_forall_snd_logarithm_eq_zero [IsAlgClosed k] [Fact (ringChar k).Prime]
    (h_rig : x₀.HasSpanningCoords)
    (hρ : x.baseHom = (algebraMap k (TrivSqZeroExt k (M →ₗ[k] k))).comp x₀.baseHom)
    (S : TangentBoundData hp) {l : M}
    (h_const : specMap (TrivSqZeroExt.map (Dual.eval k M l)).toRingHom ≫ x =
      specMap (algebraMap k (TrivSqZeroExt k k)) ≫ x₀ → l = 0)
    (hl : ∀ (C : Type) [CommRing C] [Algebra k C] [IsLocalRing C] [Module.Finite k C]
      (y : placeTorsion x₀ C), snd (S.logarithm (S.generator • S.liftPoint y.val)) l = 0) :
    l = 0 := by
  -- Write `c`, `t`, `b`, `ω`, `Y` for the generator, localizer, residue integer, logarithm and
  -- lifts of `S`.
  obtain ⟨c, hc, hc_ne, t, ht, hct, b, hb, h_coprime, h_level, ω, ω_smul, ω_ker, ω_red, ω_comp, Y,
    hY, ω_lift⟩ := S
  -- Let all `snd (ω (c • Y y))` kill `l` (`hl`). Compare the pull-back `z` of `x` along `l` with
  -- the constant deformation `z₀`, both over `k[ε]` and reducing to `x₀`.
  let m : Spec (of (TrivSqZeroExt k k)) ⟶ Spec (of (TrivSqZeroExt k (M →ₗ[k] k))) :=
    specMap (map (eval k M l)).toRingHom
  obtain ⟨z, hz⟩ := x.exists_isPullbackAlong m
  obtain ⟨z₀, hz₀⟩ := x₀.exists_isPullbackAlong (specMap (algebraMap k k[ε]))
  have hzρ : z.baseHom = (algebraMap k k[ε]).comp x₀.baseHom := by
    simpa [hρ, ← comp_assoc] using hz.baseHom_eq_comp
  have hq : IsPullbackAlong (sqZeroReduction k k) x₀ z := by
    -- `using!`: `hp` names the reduction `sqZeroReduction`, which the simplified goal unfolds
    simpa [m, ← hz, IsPullbackAlong, ← map_comp_assoc, ← ofHom_comp, ← AlgHom.comp_toRingHom]
      using! hp
  have hq₀ : IsPullbackAlong (sqZeroReduction k k) x₀ z₀ := by
    simp [← hz₀, IsPullbackAlong, ← map_comp_assoc, ← ofHom_comp]
  -- Put `β' = star D.β`. Drinfeld's lemma lifts `(β' - b) c` to
  -- `G : z₀.groupScheme ⟶ z.groupScheme`. If `G` kills the kernel of `c`, it can be divided by `c`.
  -- A lift of `β' - b` forces `z₀ = z`, so `l = 0`.
  obtain ⟨G, _, hG, G_agree⟩ := drinfeld_lift (c := (star D.β - b) * c) hq₀ hq
    fun _ _ h_inf ↦ (h_inf.ringChar_smul_and_smul_eq_zero).right hzρ hb hc
  suffices G_ker : ∀ (C : Type) [CommRing C] [IsLocalRing C] [Algebra k[ε] C] [Module.Finite k[ε] C]
      (y : specOver _ C ⟶ z₀.groupScheme), y ≫ (c • 𝟙 _) = 0 → y ≫ G = 0 by
    obtain ⟨g, _, hg⟩ := exists_isAdditive_schemeMap_comp_eq_smul (hq' := hq₀) (c • 𝟙 _) (by simp)
      hc_ne hq G _ hG fun C _ _ _ _ _ y hy _ ↦ G_ker C y hy
    have h_eq : z₀ = z := eq_of_lift_star_sub h_rig hq hq₀ hz₀ hzρ hb h_coprime h_level g hg
    exact h_const (hz.trans (h_eq.symm.trans hz₀.symm))
  intro C _ _ _ _ y hy
  -- View `y` as a point `v` of `x₀.groupScheme`, and pull `Y v` back along `(a, φ) ↦ a + ε φ(l)` to
  -- a point `y'` of `z.groupScheme`, which agrees with `y` modulo `ε`.
  algebraize [(algebraMap k[ε] C).comp (inlHom k k)]
  have : Module.Finite k C := .trans k[ε] C
  -- `θ` is the ring map `(a, φ) ↦ a + ε φ(l)` on `C ⊕ Hom(M, C)`, `d` the morphism of spectra.
  let θ := (liftEquivOfComm (A := C) ⟨(ε : k[ε]) • .applyₗ' (R := k) C l, by simp [smul_smul]⟩).1
  let d : (map m) (specOver _ C) ⟶ .mk (specMap (sqZeroMap (ofId k C))) :=
    homMk (specMap θ) (homEquiv.injective (by
      ext
      simp [m, θ, TrivSqZeroExt.map, smul_def, algebraMap_toAlgebra, mul_comm, ↓ lift_def,
        ↓ algebraMap_eq_inl']))
  let v : specOver k C ⟶ x₀.groupScheme :=
    homMk (V := (Over.map _).obj (specOver k[ε] C)) (𝟙 (Spec _))
      (by simp [← map_comp, ← ofHom_comp]) ≫ hz₀.isGroupBaseChange.pointEquiv y
  have hv : c • v = 0 := by simpa [map_smul] using congr(_ ≫ hz₀.isGroupBaseChange.pointEquiv $hy)
  let y' : specOver k[ε] C ⟶ z.groupScheme := hz.isGroupBaseChange.pointEquiv.symm (d ≫ Y v)
  obtain ⟨_, ψ, _, -, _, ψ_ker, ψ_univ⟩ := exists_isReductionModEps (specOver k[ε] C).hom
  have θ_red : ofHom θ ≫ ψ = ofHom (fstHom C C _).1 ≫ ψ := by
    ext
    simp [θ, smul_def, ψ_ker, -map_mul, ↓ lift_def]
  have h_agree : AgreeModEps hq hq₀ _ y' y := by
    intro _ _ s
    obtain ⟨s', hs'⟩ := ψ_univ s.w
    ext
    simpa [← hs', hp.comp_toFamily, hz₀.comp_toFamily, ← hz.comp_toFamily, y', d, v, toSqZeroSpec,
      θ_red, pointEquiv, ← map_comp_assoc, -map_comp] using
      s' ≫= map ψ ≫= congr($(hY v).1 ≫ x.toFamily.1)
  -- So `y ≫ G = (β' - b) c • y'`, which by `ω_ker` is zero once
  -- `ω (d ≫ c • Y v)`, which is `θ (ω (c • Y v))`, is zero.
  refine (G_agree _ y' y h_agree).trans (hz.isGroupBaseChange.pointEquiv.injective ?_)
  have v_tiny : IsInfinitesimal (ofHom (fstHom C C _).1) (c • Y v) :=
    isInfinitesimal_of_comp_eq_zero _ (by simp [hY, hv, ← map_smul])
  -- `t • v` is killed by `𝔭`, and `t ≡ 1` modulo `𝔭`, so `hl` for `t • v` computes `ω (c • Y v)`.
  have htv : t • v ∈ placeTorsion x₀ C := by
    simpa [← smul_smul] using fun a ha ↦
      (Ideal.torsionOf _ _ v).span_singleton_le_iff_mem.mpr hv (hct ⟨a, ha, mul_comm ..⟩)
  have h_snd : snd (ω (c • Y v)) l = 0 := by
    simpa [smul_comm c, ω_smul v_tiny, (sub_mem_ker_iff _).mp ht] using
      congr(snd $(ω_lift ⟨t • v, htv⟩ (t • Y v) (by simp [hY])) l).symm.trans (hl C _)
  -- the first component of `ω (c • Y v)` vanishes by `ω_red`, the second at `l` by `h_snd`
  have h_log : ω (d ≫ (c • Y v)) = 0 := by
    simpa [↓ω_comp v_tiny d rfl, h_snd, θ, ↓ lift_def] using ω_red v_tiny
  simpa [y', ← smul_smul] using ω_ker (v_tiny.precomp d rfl ψ θ_red) h_log

include hp in
/-- **Tangent bound.** Let `M` be a `k`-vector space over an algebraically closed field `k`, let
`x₀` be an object of the family `X` over `k`, and let `x` be an object over the square-zero
extension `k ⊕ M*`, where `M*` is the dual of `M`. Assume: (a) `D` is good at `ker x₀.baseHom`
(`PEL.IsGoodAt`, which via `ringChar_prime_and_exists_isCoprime_of_isGoodAt_ker` gives the
generator, localizer and residue integer of `TangentBoundData`); `x₀` is rigid
(`New.ThetaObject.HasSpanningCoords`) and is the fibre of an object `w` over a valuation subring of
`ℂ` that carries a `FullLevelStructure`; (b) `x` reduces to `x₀`, and `𝓞 E` maps to `k ⊕ M*` through
`k`;
(c) for `l ≠ 0` in `M`, the pull-back of `x` along `k ⊕ M* → k[ε]`, `(a, φ) ↦ a + φ(l) ε`, is not
the constant deformation of `x₀`. Then `finrank k M ≤ Fintype.card D.Index - 1`, where
`D.Index = Fin D.rank` indexes the coordinates, so the bound is `D.rank - 1`. -/
lemma _root_.New.Variety.finrank_tangent_le_card_index_sub_one [IsAlgClosed k]
    (hw : D.IsGoodAt (ker x₀.baseHom))
    {V : ValuationSubring ℂ} {w : ThetaObject X (Spec (of V))} (h_full : FullLevelStructure w)
    (h_rig : x₀.HasSpanningCoords) {χ : V →+* k} (h_spec : x₀.IsPullbackAlong (specMap χ) w)
    (hρ : x.baseHom = (algebraMap k (TrivSqZeroExt k (M →ₗ[k] k))).comp x₀.baseHom)
    (h_const : ∀ l : M,
      specMap (TrivSqZeroExt.map (Dual.eval k M l)).toRingHom ≫ x =
        specMap (algebraMap k (TrivSqZeroExt k k)) ≫ x₀ →
      l = 0) :
    Module.finrank k M ≤ Fintype.card D.Index - 1 := by
  -- For a point `y` of `x₀.groupScheme` killed by `𝔭 = ker x₀.baseHom` with values in a local
  -- algebra `C`, lift it to a point `Y y` of `x.groupScheme` over `C ⊕ Hom(M, C)`. Then `c • Y y`
  -- is infinitesimal for `c ∈ 𝔭`, and its logarithm `ω` gives maps `f C y : M → C`. By
  -- `finrank_le_of_placeTorsion` it is enough that they are natural in `C`, vanish on tangent
  -- vectors `y` and separate `M`.
  -- As `𝔭` is good, there are `c ≠ 0` in `𝔭` and `t ≡ 1` modulo `𝔭` with `t 𝔭 ⊆ (c)`, and an
  -- integer `b` with `D.β - b ∈ 𝔭` coprime to `star D.β - b`.
  obtain ⟨_, ⟨-, c, hc, hc_ne, t, ht, hct⟩, b, hb, h_coprime, h_level⟩ :=
    ringChar_prime_and_exists_isCoprime_of_isGoodAt_ker hw
  -- On points `y` infinitesimal for `ψ` the logarithm `ω` is additive and natural, takes values in
  -- the kernel of `ψ` (`ω_red`), turns the action of `a` into multiplication by
  -- `x₀.baseHom a` (`ω_smul`), and `ω y = 0` forces `(star D.β - b) • y = 0` (`ω_ker`).
  choose ω ω_smul ω_ker ω_add ω_red ω_comp using by
    simpa [hρ, ↓ algebraMap_eq_inl'] using x.exists_tangent_log (b := b) (by simp [hρ, hb])
  have h_lifts : ∀ ⦃C : Type⦄ [CommRing C] [Algebra k C] [IsLocalRing C]
      (y : specOver k C ⟶ x₀.groupScheme),
      ∃ Z : Over.mk (specMap (sqZeroMap (ofId k C))) ⟶ x.groupScheme,
        toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv y :=
    exists_point_lift hp
  choose Y hY using h_lifts
  have c_Y_infinitesimal {C : Type} [CommRing C] [Algebra k C] [IsLocalRing C]
      (y : placeTorsion x₀ C) : IsInfinitesimal (ofHom (fstHom C C _).1) (c • Y y.1) := by
    obtain ⟨y, hy⟩ := y
    have h_torsion : c • y = 0 := by simp_all
    exact isInfinitesimal_of_comp_eq_zero _ (by simp [hY, h_torsion, ← map_smul])
  -- `ω (c • Z)` is the same for all lifts `Z` of `y`: their difference is infinitesimal, and
  -- `x₀.baseHom c = 0`.
  have ω_lift {C : Type} [CommRing C] [Algebra k C] [IsLocalRing C] (y : placeTorsion x₀ C)
      (Z : Over.mk (specMap (sqZeroMap (ofId k C))) ⟶ x.groupScheme)
      (hZ : toSqZeroSpec C ≫ Z = hp.isGroupBaseChange.pointEquiv y) :
      ω (c • Y y.1) = ω (c • Z) := by
    have h_diff : IsInfinitesimal (ofHom (fstHom C C _).1) (Z - Y y.1) :=
      isInfinitesimal_of_comp_eq_zero _ (by simp [hY, hZ, AddGrpObj.comp_sub])
    simpa [← smul_add, ω_smul h_diff, hc] using
      (ω_add (h_diff.smul c) (c_Y_infinitesimal y)).symm
  let f (C : Type) [CommRing C] [Algebra k C] [IsLocalRing C] :
      placeTorsion x₀ C →ₛₗ[x₀.baseHom] M →ₗ[k] C :=
    { toFun y := snd (ω (c • Y y.1))
      map_add' y z := by
        simp [↓ω_lift (y + z) (Y y + Y z) (by simp [hY, comp_add]),
          ω_add (c_Y_infinitesimal y) (c_Y_infinitesimal z)]
      map_smul' a y := by
        simp [↓ω_lift (a • y) (a • Y y) (by simp [hY]), smul_comm c,
          ω_smul (c_Y_infinitesimal y)] }
  refine finrank_le_of_placeTorsion hw h_spec h_full f (fun φ y ↦ ?_) (fun y hy ↦ ?_) fun l hl ↦ ?_
  · -- Naturality: `sqZeroSpecMap φ ≫ Y y` is a lift of `placeTorsionMap φ y`.
    simp [f, ω_lift (placeTorsionMap φ y) _ (sqZeroSpecMap_point_lift hp φ (hY _)),
      ← ModuleObj.comp_smul, ω_comp (c_Y_infinitesimal y) (sqZeroSpecMap φ) rfl]
  · -- Tangent vectors: as `y` is `0` at `ε = 0`, the point `Z'` below also lifts `y`. It vanishes
    -- at `ε = 0`, so `ω (c • Z')` is `x₀.baseHom c = 0` times `ω Z'`.
    let Z' := Y y.1 - sqZeroSpecMap ((ofId k k[ε]).comp (fstHom k k k)) ≫ Y y.1
    have hZ' : toSqZeroSpec _ ≫ Z' = hp.isGroupBaseChange.pointEquiv y := by
      simp [Z', sqZeroSpecMap_point_lift hp, ← specOver.map_comp_assoc, hY, hy, AddGrpObj.comp_sub]
    have : IsSqZeroExt (ofHom (sqZeroMap (M := M) (fstHom k k k))) :=
      ⟨fun a ↦ ⟨sqZeroMap (ofId k k[ε]) a, by ext <;> simp⟩,
        by simp +contextual [TrivSqZeroExt.ext_iff, DFunLike.ext_iff]⟩
    have Z'_infinitesimal : IsInfinitesimal (ofHom (sqZeroMap (fstHom k k k))) Z' := by
      simp [Z', IsInfinitesimal, OverMorphism.ext_iff, sqZeroSpecMap, AddGrpObj.comp_sub,
        sub_eq_zero, ← map_comp_assoc, ← ofHom_comp]
      congr
      ext <;> simp
    simp [f, (ω_lift y Z' hZ').trans (ω_smul Z'_infinitesimal c), hc]
  -- Let all `f C y` kill `l`; then `l = 0` by the last step.
  exact eq_zero_of_forall_snd_logarithm_eq_zero hp h_rig hρ
    { generator := c, map_generator := hc, generator_ne_zero := hc_ne
      localizer := t, sub_one_mem := ht, smul_ker_le_span := hct
      residueInt := b, map_β_sub_int := hb, isCoprime := h_coprime, level_eq_top := h_level
      logarithm := ω, logarithm_smul := ω_smul, smul_eq_zero_of_logarithm := ω_ker
      map_logarithm_eq_zero := ω_red, logarithm_comp := ω_comp
      liftPoint := Y, comp_liftPoint_eq := hY, logarithm_smul_liftPoint_eq := ω_lift }
    (h_const l) hl

end New.Variety.TangentBound

end
