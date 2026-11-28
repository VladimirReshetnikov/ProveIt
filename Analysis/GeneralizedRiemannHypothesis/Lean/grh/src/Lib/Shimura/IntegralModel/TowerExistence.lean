import Lib.General.Combinatorics
import Lib.Shimura.CongruenceRelation.HeckeNeighbours
import Lib.Shimura.IntegralModel.BallImmersion

/-!
# Existence of the model: the tower of Kuga–Sato covers with its congruence relation

The end of the construction of the moduli tower. It goes from a universal family of PEL type
(`New.Variety.UniversalFamily`) to the structure `New.Variety.Model`, which is all that the point
counts use.

* `New.Variety.exists_model`: the model exists.
* `New.Variety.UniversalFamily.GraphClosure.congruenceRelation`,
  `New.Variety.UniversalFamily.GraphClosure.isTangentPoly_localTerm_of_translate`: the congruence
  relation and the tangent map at a fixed point, for the legs of a cover.

Notions from other files:
* `New.Variety.UniversalFamily`: a universal family of PEL type over `R`: a base scheme with an
  abelian scheme over it and its standing hypotheses. `New.Variety.UniversalFamily.GraphClosure` is
  the reduced closure of the graph of finitely many translations `a ↦ a·(g_j, 1)` of complex points;
  `C.proj j` projects it to the factor `j`, sending `C.point a` to `U.datumPoint 𝔪 (a.act g)`, the
  complex point of level `𝔪`, when `γ j = (𝔪, g)`.
* `New.Variety.Model`: the tower of Kuga–Sato varieties over `R`, given by a list of properties.
* `New.Variety.Cancels`: The integers `m i` add up to zero on every fibre of `v`, that is,
  `∑ m i • [v i] = 0` in the free abelian group on `V`.
* `New.Variety.IsSafe`: Safe places w of E: the place u of ℚ(√−d₀) below w satisfies
  `New.GaloisRep.IsSplitPrimeToDisc`, and 𝔑 lies neither in w nor in any place above ū.
* `New.Variety.IsNeat`: The level 𝔑 is neat: 𝔑 ≠ 0 and, whenever `x` is a signed frame with `ℓ` for
  some form (`New.Variety.IsSignedFrame`), every y in GL_n(E) with x⁻¹yx in `levelGU n 𝔑` (the
  subgroup of level 𝔑 of GL_n(𝔸f E), inside `GUPlus E n`, whose elements translate moduli points by
  `a.act`) that fixes ℓ under `New.Variety.ratConj` equals 1.

## Relation to the literature

Known result: Integral Kuga–Sato models for GU(1,n−1) with level covers and the congruence relation.
Here the smooth proper base is a closure of theta values with no moduli property. The covers are
reduced projective closures of tuples of isogenous points. The model asks for smoothness of the base
only, and of the covers that they are Galois on points in characteristic zero. The congruence
relation at good split places is part of the statement.
Source: Harris, Taylor, The geometry and cohomology of some simple Shimura varieties, 2001, III.4;
Kottwitz, Points on some Shimura varieties over finite fields, JAMS 5 (1992), §5.
-/

open NumberField CategoryTheory AlgebraicGeometry IsLocalRing CommRingCat New.Variety Spec
  ULift QuotientGroup Category Function ReducedClosure Finset IncidenceAlgebra Filter Algebra
  RingHom Over Finsupp ModuliPoint UniversalFamily

/-- The Möbius coefficients `(-1) ^ r * q ^ (r.choose 2)`, with `r = Module.finrank (ResField w) A`
the dimension of `A`, of the subspaces `A` of `k ^ n`, `k` the residue field of `w`, cancel along
every map that depends only on `A ⊔ W` for some `W ≠ ⊥`. -/
lemma New.Variety.cancels_moebius_of_factorsThrough_sup {E n : Type} {X : Type*} [Field E]
    [NumberField E] [Fintype n] {w : FinPlace E} {W : Submodule (ResField w) (n → ResField w)}
    (hW : W ≠ ⊥) {v : Submodule (ResField w) (n → ResField w) → X} (hv : v.FactorsThrough (· ⊔ W)) :
    Cancels
      (fun A : Submodule (ResField w) (n → ResField w) ↦
        (-1) ^ Module.finrank (ResField w) A * w.q ^ (Module.finrank (ResField w) A).choose 2)
      v := by
  classical
  let μ (A : Submodule (ResField w) (n → ResField w)) : ℤ :=
    (-1) ^ Module.finrank (ResField w) A * w.q ^ (Module.finrank (ResField w) A).choose 2
  let F (B : Submodule (ResField w) (n → ResField w)) : ℤ := ∑ A with A ⊔ W = B, μ A
  -- Summing `F` below `B` sums `μ` over the `A` with `A ⊔ W ≤ B`. This is empty unless `W ≤ B`;
  -- then it is the product in `q_binomial_submodule` at `X = 1`, whose first factor `1 - q ^ 0` is
  -- zero.
  let : LocallyFiniteOrder (Submodule (ResField w) (n → ResField w)) := Fintype.toLocallyFiniteOrder
  have sum_F (B : Submodule (ResField w) (n → ResField w)) : 0 = ∑ B' ∈ Finset.Iic B, F B' := by
    refine .trans ?_ (sum_fiberwise_eq_sum_filter ..).symm
    by_cases h : W ≤ B
    · simp [h, μ, ← Int.cast_inj (α := ℂ), prod_eq_zero (i := 0), q_binomial_submodule,
        ← card_ResField, zero_lt_iff, ne_bot_of_le_ne_bot hW]
    · simp [h]
  have F_eq_zero (B : Submodule (ResField w) (n → ResField w)) : F B = 0 := by
    simpa using moebius_inversion_bot F 0 sum_F B
  -- `F B` is the coefficient of `B` in the formal sum of the `μ A • [A ⊔ W]`
  refine .mono ((FreeAbelianGroup.equivFinsupp _).injective (ext fun B ↦ ?_)) hv
  simpa [sum_ite, single_apply, filter_filter, -zsmul_eq_mul] using F_eq_zero B

/-- Suppose `D.β` is the image of (1 + √−d₀)/2, and `c` sends the complex point of each `a` in the
closure `C` to `U.datumPoint 1 a`. Let `w` be a split finite place that is safe for `D.level` and at
which `D` is good, with residue field `k` of order `q = l ^ f`, and let `𝔭 ⊆ R` contain the image of
`w`. Let `u A`, for each subspace `A` of `k ^ n`, be maps from `C` to the base that translate the
complex points by the Hecke element `invHeckeIsogeny w A`. Then `u` satisfies the congruence
relation modulo `𝔭` (`New.Variety.CongruenceRelation`) with coefficients
`(-1) ^ r * q ^ (r.choose 2)` and `l`-power Frobenius exponents `(n - r) * f`, where `r` is the
dimension of `A`. -/
lemma New.Variety.UniversalFamily.GraphClosure.congruenceRelation {E : Type} [Field E] [CMBase E]
    {d₀ : ℕ} [HasQuadSubfield d₀ E] {R : Subalgebra (𝓞 E) E} {D : PEL E}
    {U : UniversalFamily D R} (hβ : D.β = algebraMap (𝓞 (QuadField d₀)) (𝓞 E) (QuadField.betaK d₀))
    {ν : ℕ} [NeZero ν] {J : Type} [Finite J] {γ : J → nonZeroDivisors (𝓞 E) × GUPlus E D.Index}
    (C : U.GraphClosure γ ν)
    {c : C.scheme ⟶ (Over.map U.base.hom).obj
      (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))}
    (hc : ∀ a : ModuliPoint E D.Index ν, C.point a ≫ c = U.datumPoint 1 a) {w : SplitFinPlace E}
    (hw : IsSafe D.level w.val) (hD : D.IsGoodAt w.val.asIdeal) {𝔭 : Set R}
    (h𝔭 : ∀ a ∈ w.val.asIdeal, algebraMap (𝓞 E) R a ∈ 𝔭)
    {u : Submodule (ResField (E := E) w) (D.Index → ResField (E := E) w) →
      (C.scheme ⟶ (Over.map U.base.hom).obj
        (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν)))}
    (hu : ∀ (A : Submodule (ResField (E := E) w) (D.Index → ResField (E := E) w))
        (a : ModuliPoint E D.Index ν),
      C.point a ≫ u A = U.datumPoint 1 (a.act
        ⟨invHeckeIsogeny w A, invHeckeIsogeny_mem_GUPlus w A⟩))
    {l f : ℕ} [Fact l.Prime] (hq : w.val.q = l ^ f) :
    let r (A : Submodule (ResField w.val) (D.Index → ResField w.val)) : ℕ :=
      Module.finrank (ResField w.val) A
    CongruenceRelation (fun A ↦ (-1) ^ r A * w.val.q ^ (r A).choose 2) 𝔭 l
      (fun A ↦ (Fintype.card D.Index - r A) * f) u := by
  intro r k h_field h_charP x hx
  -- `x` comes from the residue field of a point `z`, and `z` is the centre of an arc `α` over a
  -- valuation ring `V` of `ℂ`. By `along`, a map that sends the complex point of `b` to that of
  -- `a` sends `α` to the `V`-point of `a`.
  obtain ⟨z, ρ, rfl, -⟩ := exists_countable_residue_point C.scheme.hom x
  obtain ⟨V, α, b, ρ', centre, along⟩ := C.exists_arc z
  have hz_charP : CharP (C.scheme.left.residueField z) l := ρ.charP ρ.injective l
  have hV_charP : CharP (ResidueField V) l := charP_of_injective_ringHom ρ'.injective l
  -- the Frobenius twists of the reduced Hecke neighbours depend only on `A ⊔ W`, for some `W ≠ ⊥`
  let twist (A : Submodule (ResField w.val) (D.Index → ResField w.val)) :=
    specMap ((iterateFrobenius (ResidueField V) l ((Fintype.card D.Index - r A) * f)).comp
      (residue V)) ≫ α ≫ (u A).left
  obtain ⟨W, hW, reduction⟩ : ∃ W ≠ ⊥, FactorsThrough twist (· ⊔ W) := by
    -- the Frobenius exponents: `l ^ ((n - r A) * f) = q ^ (n - r A)`
    refine U.exists_ne_bot_factorsThrough_sup hβ (along (hc b)) residue_surjective rfl ?_ hD hw
      (fun A ↦ by simp [hq, pow_mul', r]) fun A ↦ along (hu A b)
    -- the centre of the arc lies above `w`
    refine w.val.isMaximal.eq_of_le (ker_ne_top _) fun a ha ↦ ?_
    -- `erw`: the goal `a ∈ ker (ThetaObject.baseHom …)` matches `hx` only after unfolding.
    erw [ThetaObject.baseHom, ← assoc, preimage_comp]
    simpa [← reassoc_of% centre, ← c.w] using hx _ (h𝔭 a ha)
  refine (cancels_moebius_of_factorsThrough_sup hW reduction).mono fun A B hAB ↦ ?_
  -- Frobenius commutes with `ρ` and `ρ'`, and `Spec` of a field embedding is an epimorphism: the
  -- equation descends from the residue field of `V` to that of `z` and goes up to `k`.
  simp [twist, specMap] at hAB
  -- both sides of `hAB` become the twists at `z`, followed by the field embedding `ρ'`
  simp [← reassoc_of% centre, ← map_comp_assoc, ← ofHom_comp, ← iterateFrobenius_comm] at hAB ⊢
  simpa [cancel_epi] using hAB


/-- The tangent map at a fixed point. Let `c` send the complex point of `a` in the closure `C` to
that of `a` in the base (`U.datumPoint 1 a`), and let `v` send it to that of the translate
`a.act g α`. Suppose `z` in GL_n(E) relates this translate to `a` at level `D.level` (`IsLevelIso`),
the characteristic polynomial of `z` is separable, and `a.reflection` is the marked reflection
`markedReflection z μ` for the index `μ`. Then `localTerm α z.val.charpoly μ` is
`det (1 - X (dc)⁻¹ dv)` on the tangent space at the point of `a`, which has dimension
`card D.Index - 1 + ν * abelianDim E D.Index`, up to a constant factor
(`New.Variety.IsTangentPoly`). -/
lemma New.Variety.UniversalFamily.GraphClosure.isTangentPoly_localTerm_of_translate
    {E : Type} [Field E] [CMBase E] {R : Subalgebra (𝓞 E) E}
    {D : PEL E} {U : UniversalFamily D R} {ν : ℕ} [NeZero ν] {J : Type} [Finite J]
    {γ : J → nonZeroDivisors (𝓞 E) × GUPlus E D.Index} (C : U.GraphClosure γ ν)
    {c v : C.scheme ⟶ (Over.map U.base.hom).obj
      (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))}
    (hc : ∀ a : ModuliPoint E D.Index ν, C.point a ≫ c = U.datumPoint 1 a) {g : GUPlus E D.Index}
    {α : Fin ν → 𝓞 E} (hv : ∀ a : ModuliPoint E D.Index ν,
      C.point a ≫ v = U.datumPoint 1 (a.act g α))
    {a : ModuliPoint E D.Index ν} {z : GL D.Index E} {μ : D.Index}
    (hz : z.val.charpoly.Separable) (h_reflection : a.reflection = markedReflection z μ)
    (hrel : (a.act g α).IsLevelIso (levelGU D.Index D.level) z a) :
    IsTangentPoly (Fintype.card D.Index - 1 + ν * abelianDim E D.Index)
      ((algPoints (ℂ) (of R)).map c) ((algPoints (ℂ) (of R)).map v) ⟨C.point a⟩
      (localTerm α z.val.charpoly μ) := by
  -- An analytic family `q ↦ f.ballPoint a.markedPoint q` passes through `a` at `q = 0`, and `z`
  -- acts on it near `0` by a linear map `K`. The tangent space is the parameter space, by the
  -- universal jet `σ`.
  obtain ⟨f, hf⟩ := exists_isBallFamily a
  obtain ⟨K, hK, hdet⟩ := hf.exists_linear_isLevelIso hz h_reflection hrel
  obtain ⟨σ, hσ⟩ := (C.holomorphicAt_point a.markedPoint 0 hf.zero_mem).exists_isJet .id
  -- `τ x` is the jet `σ` in the direction `x`
  let τ (x : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      Spec (of (TrivSqZeroExt ℂ ℂ)) ⟶ C.scheme.left :=
    specMap (TrivSqZeroExt.map (.applyₗ x)).toRingHom ≫ σ
  have jet (x : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      IsJet (fun q ↦ (C.point (f.ballPoint a.markedPoint q)).left) 0 (LinearMap.applyₗ x) (τ x) :=
    fun V s hV ↦ by
      simp [τ, PointFn.isRegularOn_ofSection _ _, hσ V s hV, LandsIn.comp]
  -- followed by `c`, it is the jet of the family in the base (`hc`)
  have jet_c (x : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      IsJet (fun q ↦ (U.datumPoint 1 (f.ballPoint a.markedPoint q)).left) 0 (LinearMap.applyₗ x)
        (τ x ≫ c.left) :=
    ((jet x).comp_hom c.left).congr
      (.of_forall fun q ↦ congrArg Hom.left (hc (f.ballPoint a.markedPoint q)))
  -- followed by `v`, it is the jet of the family moved by `K` (`hv`, and `z` near `0` by `hK`)
  have jet_v (x : BallBase D.Index × (Fin ν → BallFibre E D.Index)) :
      IsJet (fun q ↦ (U.datumPoint 1 (f.ballPoint a.markedPoint (K q))).left) 0 (LinearMap.applyₗ x)
        (τ x ≫ v.left) :=
    ((jet x).comp_hom v.left).congr <| hK.mono fun q hq ↦ by
      have h_pt : C.point (f.ballPoint a.markedPoint q) ≫ v = U.datumPoint 1
        (f.ballPoint a.markedPoint (K q)) :=
        (hv _).trans (datumPoint_eq_iff.mpr ⟨z, by simpa using hq⟩)
      exact congrArg Hom.left h_pt
  -- the tangent space at the point of `a` is the parameter space of the family, embedded by `σ`;
  -- it remains to check its dimension and its base point, that `dc` is injective, and `dv = dc K`
  refine ⟨.of ℂ _, ⟨homMk σ ((hσ.comp_base_eq fun _ ↦ w _).trans (map_comp ..).symm)⟩, K, ?_, ?_,
    fun x y hxy ↦ ?_, fun x ↦ up_inj.mpr (OverMorphism.ext ?_), hdet⟩
  · simp [(f.torus 0).isPeriodMap.finrank_eq_abelianDim, Module.finrank_pi_fintype]
  · -- the jet `σ` lies over the point of `f.ballPoint a.markedPoint 0 = a`
    refine congrArg ULift.up (OverMorphism.ext (hσ.fst_comp.trans ?_))
    rw [hf.ballPoint_zero]
  · -- Equal jets give equal derivatives, so the family is constant to first order in the
    -- direction `x - y`; it is immersed in the base.
    have same : τ x ≫ c.left = τ y ≫ c.left := congr($hxy.1.left)
    have imm : IsHolomorphicImmersionAt (fun q ↦
      (U.datumPoint 1 (f.ballPoint a.markedPoint q)).left) 0 :=
      U.isHolomorphicImmersionAt_datumPoint 0 hf.zero_mem
    refine sub_eq_zero.mp (imm.2 _ (isFirstOrderConst_iff.mpr fun V s hV ↦ ?_))
    have value_x := (jet_c x V s hV).2
    rw [same, (jet_c y V s hV).2] at value_x
    -- `using!`: the derivative parts match the goal only up to unfolding the maps of points.
    simpa [sub_eq_zero] using! congrArg TrivSqZeroExt.snd value_x.symm
  · -- By the chain rule, both sides are the jet of `q ↦ f.ballPoint a.markedPoint (K q)` in the
    -- direction `x`.
    have chain : IsJet (fun q ↦ (U.datumPoint 1 (f.ballPoint a.markedPoint (K q))).left) 0
        (LinearMap.applyₗ x) (τ (K x) ≫ c.left) :=
      (isJet_comp_iff (ContinuousLinearMap.mk K).hasFDerivAt
        (U.isHolomorphicImmersionAt_datumPoint _ (by simpa using hf.zero_mem)).1).mpr
        -- `using!`: `jet_c (K x)` matches this goal only up to unfolding
        (by simpa using! jet_c (K x))
    exact (jet_v x).unique chain

/-- Two moduli points `a` and `b` with the same complex point in the base (`hab`) have the same
complex point in the closure `C` after `a` is translated by `κ⁻¹` for some `κ` in
`levelGU D.Index D.level`. -/
lemma New.Variety.UniversalFamily.GraphClosure.exists_point_act_eq {E : Type} [Field E] [CMBase E]
    {R : Subalgebra (𝓞 E) E} {D : PEL E} {U : UniversalFamily D R} {ν : ℕ}
    [NeZero ν] {J : Type} [Finite J] {γ : J → nonZeroDivisors (𝓞 E) × GUPlus E D.Index}
    (C : U.GraphClosure γ ν) {a b : ModuliPoint E D.Index ν}
    (hab : U.datumPoint 1 a = U.datumPoint 1 b) :
    ∃ κ : levelGU D.Index D.level,
      C.point (a.act ⟨↑κ⁻¹, mem_GUPlus_of_mem_levelGU κ⁻¹.property⟩) = C.point b := by
  -- `z` is an isomorphism of level `D.level` from `a` to `b`. Its level condition gives `κ`; after
  -- translating `a` by `κ⁻¹`, `z` is an isomorphism of every level, in particular of the level
  -- `𝔫` at which the points of `C` are determined.
  obtain ⟨z, hz⟩ := datumPoint_eq_iff.mp hab
  obtain ⟨𝔫, h_point_eq⟩ := C.exists_level_point_eq
  exact ⟨⟨_, hz.mem_level.1⟩, h_point_eq
    { mem_level := by simp [act]
      reflection_eq := hz.reflection_eq
      sub_mem_lattice := by simpa [act] using hz.sub_mem_lattice }⟩

/-- A map `f` from the closure `C` to the base that translates the complex points by `g` is
determined by the coset of `g` modulo `levelGU D.Index D.level`: there is one map `u` on all cosets
with `f = u ⟦g⟧` for every such `f`. The map `c` serves only (the hypothesis `_hc` is unused) to
show that maps to the base exist. -/
lemma New.Variety.UniversalFamily.GraphClosure.exists_forall_eq_apply_mk_of_translate {E : Type}
    [Field E] [CMBase E] {R : Subalgebra (𝓞 E) E} {D : PEL E} {U : UniversalFamily D R} {ν : ℕ}
    [NeZero ν] {J : Type} [Finite J] {γ : J → nonZeroDivisors (𝓞 E) × GUPlus E D.Index}
    (C : U.GraphClosure γ ν)
    {c : C.scheme ⟶ (Over.map U.base.hom).obj
      (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))}
    (_hc : ∀ a : ModuliPoint E D.Index ν, C.point a ≫ c = U.datumPoint 1 a) :
    ∃ u : (GL D.Index (𝔸f E) ⧸ levelGU D.Index D.level) →
        (C.scheme ⟶ (Over.map U.base.hom).obj
          (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))),
      ∀ {g : GL D.Index (𝔸f E)}
        {f : C.scheme ⟶ (Over.map U.base.hom).obj
          (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))}
        (hg : g ∈ GUPlus E D.Index),
      (∀ a : ModuliPoint E D.Index ν, C.point a ≫ f = U.datumPoint 1 (a.act ⟨g, hg⟩)) →
      f = u ⟦g⟧ := by
  -- the legs: maps `f` that translate complex points by some `g`
  let Leg := Σ' (g : GUPlus E D.Index)
    (f : C.scheme ⟶ (Over.map U.base.hom).obj
      (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))),
    ∀ a : ModuliPoint E D.Index ν, C.point a ≫ f = U.datumPoint 1 (a.act g)
  -- two legs whose `g` have the same coset agree on all complex points, hence are equal
  have factors :
      FactorsThrough (fun p : Leg ↦ p.snd.fst) fun p : Leg ↦
        (p.fst.val : GL D.Index (𝔸f E) ⧸ levelGU D.Index D.level) := by
    rintro ⟨⟨g, hg⟩, f, hf⟩ ⟨⟨g', hg'⟩, f', hf'⟩ hpq
    refine C.isSeparatingFamily.hom_ext fun a ↦ ?_
    -- the isomorphism is `1`; its level condition is the equality of cosets `hpq`
    simpa [hf, hf', act, datumPoint_eq_iff, isLevelIso_iff, ratConj] using ⟨1, by
      simpa [QuotientGroup.eq] using hpq.symm⟩
  have h_nonempty : Nonempty (C.scheme ⟶ (Over.map U.base.hom).obj
      (ThetaFamily.fibrePower (NonzeroTorsion 1 D.Index ⊕ Fin ν))) := ⟨c⟩
  obtain ⟨u, hu⟩ := (factorsThrough_iff _).mp factors
  exact ⟨u, fun hg h ↦ congrFun hu ⟨⟨_, hg⟩, _, h⟩⟩

/-- Maps from a subring `R` of a number field that contains the integers to fields of
characteristic zero are injective, as `R` is algebraic over `ℤ`. -/
lemma New.Variety.injective_of_subalgebra_of_charZero {E : Type*} [Field E] [NumberField E]
    (R : Subalgebra (𝓞 E) E) (k : Type*) [Field k] [CharZero k] (f : R →+* k) :
    Function.Injective f := by
  -- `E` is algebraic over `ℤ` through `𝓞 E`, hence so is its subring `R`; a map from an algebraic
  -- `ℤ`-algebra to a field of characteristic zero is injective
  let algebra_R_k : Algebra R k := f.toAlgebra
  have h_alg_E : Algebra.IsAlgebraic ℤ E := IsAlgebraic.trans ℤ (𝓞 E) E
  have h_alg_R : Algebra.IsAlgebraic ℤ R := h_alg_E.tower_bot_of_injective Subtype.val_injective
  exact h_alg_R.injective_tower_top R Int.cast_injective

namespace New.Variety

section TowerHelpers

variable {E : Type} [Field E] [CMBase E] {R : Subalgebra (𝓞 E) E}
  {D : PEL E} {U : UniversalFamily D R} {ν : ℕ}

/-- The finite quotient of `levelGU D.Index D.level` by the normal core of its subgroup of level
`M`: the deck group of a cover of the tower in `New.Variety.exists_model`. -/
private abbrev TowerQuot (D : PEL E) (M : nonZeroDivisors (𝓞 E)) : Type :=
  levelGU D.Index D.level ⧸ ((levelGU D.Index (M : 𝓞 E)).subgroupOf
    (levelGU D.Index D.level)).normalCore

open scoped Classical in
/-- The pairs `(𝔪, κ * g)` that define the cover of level `i` in `New.Variety.exists_model`: `κ`
runs over `New.Variety.TowerQuot D M` (through the chosen representative `out`) and `(𝔪, g)` over
`i`, `(1, 1)` and `(M, 1)`. -/
private noncomputable abbrev towerPairs (D : PEL E) (M : nonZeroDivisors (𝓞 E))
    (i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E D.Index))
    (j : TowerQuot D M × ↥(insert (M, 1) (insert 1 i))) :
    nonZeroDivisors (𝓞 E) × GUPlus E D.Index :=
  (j.2.1.1, ⟨_, mem_GUPlus_of_mem_levelGU j.1.out.2⟩ * j.2.1.2)

open scoped Classical in
/-- On the cover `C` of level `i` with pairs `New.Variety.towerPairs D M i`, the factor `(⟦κ⟧, x)`
of the point of `a` may be computed with the representative `κ` instead of the chosen one: the two
differ by an element of level `M`, which `hM` conjugates into the level of every pair. -/
private lemma UniversalFamily.GraphClosure.point_comp_proj_towerPairs
    {M : nonZeroDivisors (𝓞 E)} {i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E D.Index)}
    (hM : ∀ x ∈ insert (M, 1) (insert 1 i), ∀ k ∈ levelGU D.Index (M : 𝓞 E),
      (x.2 : GL D.Index (𝔸f E))⁻¹ * k * x.2 ∈ levelGU D.Index D.level ⊓ levelGU D.Index x.1)
    (C : U.GraphClosure (towerPairs D M i) ν) {a : ModuliPoint E D.Index ν}
    (x : ↥(insert (M, 1) (insert 1 i))) (κ : levelGU D.Index D.level) :
    C.point a ≫ C.proj (⟦κ⟧, x) =
      U.datumPoint x.1.1 (a.act (⟨κ, mem_GUPlus_of_mem_levelGU κ.2⟩ * x.1.2)) := by
  -- `κ⁻¹` times the chosen representative of `⟦κ⟧` has level `M`
  have h_deep : (κ.1⁻¹ * (κ : TowerQuot D M).out) ∈ levelGU D.Index (M : 𝓞 E) := by
    simpa using! QuotientGroup.eq.1 (κ : TowerQuot D M).out_eq.symm 1
  rw [point_comp_proj]
  exact datumPoint_eq_iff.2 ⟨1, by
    simpa [towerPairs, act, isLevelIso_iff, mul_assoc, ratConj] using! hM _ x.2 _ h_deep⟩

open scoped Classical in
/-- The element `κ` of `levelGU D.Index D.level` acts on the cover `C` of level `i` by a map `p`
that permutes the factors, `(q, x) ↦ (κ⁻¹ q, x)`, and translates complex points by `κ⁻¹`. -/
private lemma UniversalFamily.GraphClosure.exists_deck_towerPairs
    {M : nonZeroDivisors (𝓞 E)} {i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E D.Index)}
    (hM : ∀ x ∈ insert (M, 1) (insert 1 i), ∀ k ∈ levelGU D.Index (M : 𝓞 E),
      (x.2 : GL D.Index (𝔸f E))⁻¹ * k * x.2 ∈ levelGU D.Index D.level ⊓ levelGU D.Index x.1)
    (C : U.GraphClosure (towerPairs D M i) ν) (κ : levelGU D.Index D.level) :
    ∃ p : C.scheme ⟶ C.scheme,
      (∀ j : TowerQuot D M × ↥(insert (M, 1) (insert 1 i)),
        p ≫ C.proj j = C.proj (κ⁻¹ * j.1, j.2)) ∧
        ∀ a : ModuliPoint E D.Index ν,
          C.point a ≫ p = C.point (a.act ⟨↑κ⁻¹, mem_GUPlus_of_mem_levelGU κ⁻¹.2⟩) :=
  C.exists_lift _ _ fun a j ↦ by
    rw [← j.1.out_eq]
    exact (C.point_comp_proj_towerPairs hM _ _).trans (by simp [towerPairs, act, mul_assoc])

open scoped Classical in
/-- The deck maps `p κ` act freely on complex points: if `p κ` and `p κ'` agree at the point of `x`,
then `κ` and `κ'` have the same class in `New.Variety.TowerQuot D M`. Compare the factors
`(⟦κ * q⁻¹⟧, (M, 1))`: the isomorphism between the two translates is an automorphism of level
`D.level`, hence trivial as the level is neat. -/
private lemma UniversalFamily.GraphClosure.eq_of_point_comp_deck_eq
    (hN : IsNeat D.Index D.level) {M : nonZeroDivisors (𝓞 E)}
    {i : Finset (nonZeroDivisors (𝓞 E) × GUPlus E D.Index)}
    (hM : ∀ x ∈ insert (M, 1) (insert 1 i), ∀ k ∈ levelGU D.Index (M : 𝓞 E),
      (x.2 : GL D.Index (𝔸f E))⁻¹ * k * x.2 ∈ levelGU D.Index D.level ⊓ levelGU D.Index x.1)
    (C : U.GraphClosure (towerPairs D M i) ν) {p : levelGU D.Index D.level → (C.scheme ⟶ C.scheme)}
    (hp : ∀ (κ : levelGU D.Index D.level) (a : ModuliPoint E D.Index ν),
      C.point a ≫ p κ = C.point (a.act ⟨↑κ⁻¹, mem_GUPlus_of_mem_levelGU κ⁻¹.2⟩))
    {x : ModuliPoint E D.Index ν} {κ κ' : levelGU D.Index D.level}
    (h_eq : C.point x ≫ p κ = C.point x ≫ p κ') :
    (κ : TowerQuot D M) = κ' := by
  refine QuotientGroup.eq.2 fun q ↦ ?_
  rw [hp, hp] at h_eq
  obtain ⟨z, hz⟩ := datumPoint_eq_iff.1
    (by simpa only [C.point_comp_proj_towerPairs hM] using
      h_eq =≫ C.proj ⟨⟦κ * q⁻¹⟧, _, mem_insert_self ..⟩)
  obtain ⟨h_level_𝔑, h_level_M⟩ := hz.mem_level
  have h_aut : x.frame⁻¹ * toFinGL z * x.frame ∈ levelGU D.Index D.level := by
    simpa [mul_mem_cancel_left, mul_assoc, act] using mul_mem h_level_𝔑 q.2
  obtain rfl : z = 1 := hN.eq_one_of_mem_levelGU x.isSignedFrame h_aut hz.reflection_eq
  simpa [mul_assoc, Subgroup.mem_subgroupOf, act] using h_level_M

end TowerHelpers

end New.Variety

/-- Let `U` be a universal family over `R` for the PEL data `D` (`New.Variety.UniversalFamily`),
where `E` contains ℚ(√−d₀) with d₀ ≡ 3 mod 4. Suppose that `D.level` is neat and that `D.β` is the
image of (1 + √−d₀)/2. Suppose also that `D` is good (`New.PEL.IsGoodAt`) at every finite place `w`
that is safe for `D.level`, meaning that the place of ℚ(√−d₀) below `w` is split and prime to the
discriminant, and that `D.level` lies neither in `w` nor in any place above its conjugate. Then for
every ν ≠ 0 there is a model `New.Variety.Model D.Index d₀ D.level ν R`, that is, a tower of
Kuga–Sato varieties over `R` with base `base`, schemes `cover i` and legs `leg` to the base, finite
deck groups `deckGroup i`, maps `mulMap` and complex points, satisfying the listed properties. -/
lemma New.Variety.exists_model {E : Type} [Field E] [CMBase E]
    {d₀ : ℕ} [HasQuadSubfield d₀ E] {R : Subalgebra (𝓞 E) E} {D : PEL E} (U : UniversalFamily D R)
    (hN : IsNeat D.Index D.level) (hβ : D.β = algebraMap (𝓞 (QuadField d₀)) (𝓞 E)
      (QuadField.betaK d₀))
    (hG : ∀ w : FinPlace E, IsSafe D.level w → D.IsGoodAt w.asIdeal) (ν : ℕ) [NeZero ν] :
    Nonempty (Model D.Index d₀ D.level ν R) := by
  classical
  -- The cover of level `i` is the closure `C i` of the tuples of complex points translated by
  -- `κ * g`, with `κ` in the finite quotient `New.Variety.TowerQuot D (M i)` of
  -- `levelGU D.Index D.level` and `(𝔪, g)` in `i` or equal to `(1, 1)` or `(M i, 1)`
  -- (`New.Variety.towerPairs`). All maps between covers are lifts of translations of points, and
  -- are determined by them. `M i` is chosen so that `g⁻¹ K(M i) g ⊆ K(𝔑) ∩ K(𝔪)` for all these
  -- `(𝔪, g)`.
  choose M hM using exists_level_conj_mem (n := D.Index) hN.ne_zero
  -- The base is the fibre power at level `1`: smooth, with dense complex points, and `m α`
  -- multiplies the marked points by `α`.
  obtain ⟨smooth, dense, m, hm⟩ := U.smooth_and_isDenseFamily_and_exists_comp_eq_act ν
  obtain ⟨C⟩ : Nonempty (∀ i, U.GraphClosure (towerPairs D (M i) i) ν) := inferInstance
  -- `κ` acts on `C i` by permuting the factors: this is the deck transformation `p κ`
  choose p p_proj pt_p using fun {i} ↦ (C i).exists_deck_towerPairs (hM i)
  -- the legs `u i`, and the set `s i` of the `g` for which `u i ⟦g⟧` translates points by `g`
  have pt_base (i) (a : ModuliPoint E D.Index ν) :
      (C i).point a ≫ (C i).proj ⟨⟦1⟧, 1, by simp⟩ = U.datumPoint 1 a := by
    simp [↓(C i).point_comp_proj_towerPairs (hM i), act]
  choose u eq_u using fun i ↦ (C i).exists_forall_eq_apply_mk_of_translate (pt_base i)
  let s i := {g | ∃ hg, ∀ a, (C i).point a ≫ u i ⟦g⟧ = U.datumPoint 1 (a.act ⟨g, hg⟩)}
  have mem_s {i g f} (hg : g ∈ GUPlus E D.Index)
      (h : ∀ a, (C i).point a ≫ f = U.datumPoint 1 (a.act ⟨g, hg⟩)) : g ∈ s i :=
    ⟨hg, by rwa [← eq_u i hg h]⟩
  have one_mem_s i : 1 ∈ s i := mem_s (one_mem _) (by simpa [act] using pt_base i)
  have pt_u_one {i} a : (C i).point a ≫ u i ⟦1⟧ = U.datumPoint 1 a := by
    simpa [act] using (one_mem_s i).2 a
  have comp_u {g hg i j f} (h : ∀ a, (C i).point a ≫ f = (C j).point (a.act ⟨g, hg⟩)) q
      (hq : q ∈ s j) : f ≫ u j ⟦q⟧ = u i ⟦g * q⟧ :=
    eq_u i (mul_mem hg hq.1) (by simp [reassoc_of% h, hq.2, act, mul_assoc])
  -- `p` is a homomorphism, trivial on the normal core, so the finite group `TowerQuot D (M i)` acts
  let deck i : TowerQuot D (M i) →* End (C i).scheme := QuotientGroup.lift _
    ⟨⟨fun κ ↦ .of (p κ), End.ext ((C i).isSeparatingFamily.hom_ext (by simp [pt_p, act]))⟩,
      fun _ _ ↦ End.ext
        ((C i).isSeparatingFamily.hom_ext (by simp [pt_p, ← assoc, act, mul_assoc]))⟩
    fun κ hκ ↦ End.ext <| ReducedClosure.hom_ext _ fun j ↦ by
      erw [p_proj, mul_eq_right.2]
      · simp
      · simpa
  exact ⟨{ base := _
           cover i := (C i).scheme
           legIndices := s
           leg := u
           one_mem := one_mem_s
           eventually_translate {g} j hg := by
             -- translation by `g` lifts once `i` contains the `g`-translates of all pairs
             refine (eventually_all.2 fun x ↦ eventually_finset_mem_atTop
                 ((towerPairs D (M j) j x).1, (⟨g, hg⟩ * (towerPairs D (M j) j x).2 :))).mono
               fun i hi ↦ ?_
             obtain ⟨f, -, hf⟩ :=
               (C j).exists_lift (C' := C i) (·.act ⟨g, hg⟩)
                 (fun x ↦ (C i).proj ⟨⟦1⟧, _, mem_insert_of_mem (mem_insert_of_mem (hi x))⟩)
                 (by simp [↓(C i).point_comp_proj_towerPairs (hM i), towerPairs, act, mul_assoc])
             exact ⟨mem_s (f := f ≫ u j ⟦1⟧) hg (by simp [← assoc, hf, pt_u_one]), f, comp_u hf⟩
           deckGroup i := .of (TowerQuot D (M i))
           deck := deck
           deck_comp_leg i := Quot.ind fun κ ↦ ⟨κ⁻¹, comp_u (pt_p κ)⟩
           mulMap := m
           point i := (C i).point
           point_surjective i := (C i).point_surjective pt_u_one
           point_eq_iff := by simp [pt_u_one, datumPoint_eq_iff]
           point_leg g α a h := by simp [reassoc_of% h.2, pt_u_one, hm]
           dimension := _
           smooth := smooth
           covering i := by
             refine isGaloisCovering_of_complex_points (injective_of_subalgebra_of_charZero R)
               (Quot.ind fun κ ↦ ?_) ?_ ?_
             · -- `u i ⟦1⟧` is invariant under the deck group
               exact (comp_u (pt_p κ) 1 (one_mem_s i)).trans (congrArg (u i) (by simp
                 [QuotientGroup.eq]))
             · -- its image is closed and contains the dense points `U.datumPoint 1 a`
               exact dense.surjective _ _ fun a ↦ congr($(pt_u_one a).1)
             · -- simply transitive on fibres; every complex point is some `(C i).point x`
               refine ((C i).point_surjective pt_u_one).forall₂.2 fun x y h ↦ ?_
               rw [pt_u_one, pt_u_one] at h
               obtain ⟨κ, hκ⟩ := (C i).exists_point_act_eq h
               rw [← pt_p] at hκ
               exact ⟨⟦κ⟧, hκ, Quot.ind fun κ' hκ' ↦
                 (C i).eq_of_point_comp_deck_eq hN (hM i) (fun κ a ↦ pt_p κ a) (hκ'.trans hκ.symm)⟩
           tangent i g α a z μ h :=
             (C i).isTangentPoly_localTerm_of_translate pt_u_one fun a ↦ by
               simp [reassoc_of% h.2, hm]
           congruence w hw i 𝔭 h𝔭 hs l f _ hq :=
             (C i).congruenceRelation hβ pt_u_one hw (hG _ hw) h𝔭 (fun A ↦ (hs A).2) hq }⟩
