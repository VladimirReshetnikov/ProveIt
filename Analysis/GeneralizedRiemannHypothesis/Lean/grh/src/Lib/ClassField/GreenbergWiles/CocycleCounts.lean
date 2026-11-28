import Lib.ClassField.GreenbergWiles.SplitPrimeReciprocity

/-!
# Counts of trivialised Galois cocycles for projective modules and central scalars

We count trivialised cocycles (`New.DiscreteModule.trivialisedCocycles`) of the absolute Galois
group `G` of a number field `K` (`IsProGalois G K Ω`: `G` acts on `Ω` as its Galois group over `K`)
in a finite module `V`. A trivialised cocycle vanishes on `I` and carries a trivialisation at each
place of `Ω` (the algebraic closure of `ℚ`) above `N` and infinity. Here
`New.IsLargeLevel.SplitPlaces` is the data of finitely many places not dividing `N`, indexed by `ι`,
with Frobenius elements `s.φ i` in `U`. The set `I` is the union of the inertia groups above the
other places not dividing `N`.

## Main definitions and results

* `New.IsLargeLevel.SplitPlaces.card_trivialised_of_isHigmanProjective`: for `V` killed by `l`,
  fixed by `U` and projective over `G ⧸ U` in Higman's sense, given `z`, `n` with `ρ(z) − n`
  injective on `V` and with `z • r − n • r` fixed by `U` for every unit `r` fixed by all `s.φ i`
  with `l • r` a `U`-fixed `N`-unit, at most `#V ^ (#ι + 1)` trivialised cocycles, with equality
  under further hypotheses.
* `New.IsLargeLevel.SplitPlaces.hasFewCocycles_of_central`: let `K` be totally complex and `r ≠ 0`.
  Suppose some `z`, central modulo `U` and with `l`-adic cyclotomic character `1`, satisfies
  `V.FiniteKilledFixedInj (l ^ r) U z 1`. Suppose also that the Frobenii of the split places detect
  roots. Then `V` has at most `#V ^ (#ι + 1)` trivialised cocycles.

Notions from other files:
* `New.DiscreteModule.IsHigmanProjective`: Higman's criterion relative to Q of finite index: some
  additive τ : A → A has ∑ gτg⁻¹ = 1, summed over chosen representatives g of G/Q.
* `New.DiscreteModule.FiniteKilledFixedInj`: The G-module A is finite and killed by n, Q acts
  trivially on it, and ρ(z) − m is injective on it.
* `New.IsLargeLevel.fixedSUnits`: The N-units of the fixed field of U: the N-units of Ω that are
  fixed by U.

## Relation to the literature

An upper bound of the kind the Greenberg–Wiles formula gives when the dual Selmer group vanishes;
the hypothesis on the Frobenii `s.φ i` takes the place of that vanishing. Only this bound is proved
(with a case of equality for projective modules), under the hypothesis that `ρ(z) − n` is injective
on `V`; for modules that are not projective, `n = 1` and `z` is central modulo `U`. No local duality
is used: the dual Selmer group is replaced by linear relations among the values of a cocycle on tame
inertia at the split places.

Source: H. Darmon, F. Diamond, R. Taylor, Fermat's Last Theorem (1995; revised 2007), Thm 2.18–2.19;
A. Wiles, Ann. of Math. 141 (1995), Prop. 1.6; J. S. Milne, Arithmetic Duality Theorems, I 4.10,
5.1; L. Washington, Galois cohomology (1997), Thm 2.
-/

/-!
## The count for a projective module

`New.IsLargeLevel.SplitPlaces.card_trivialised_of_isHigmanProjective` bounds the order of the group
of trivialised cocycles by `#V ^ (#ι + 1)`, with a case of equality, under further hypotheses on `V`
and `z` (`hV_fin`, `h_fix`).

The proof compares the group with the `G ⧸ U`-equivariant maps from (`N`-units) `× ℤ` to `V`. It
uses the reciprocity law `New.IsLargeLevel.SplitPlaces.power_residue_reciprocity` and the unit
theorem `New.IsLargeLevel.dirichlet_fixedSUnits`.
-/

section ProjectiveCount

open NumberField Nat NeZero Fintype AddSubgroup Finset Submodule AddMonoidHom

attribute [local instance low] Fintype.ofFinite

/-- Let `β : A → B` and `f : A → V` be additive maps, where `B` and `V` are vector spaces over
`ZMod l`. If `f` vanishes wherever `β` does, then `f = v ∘ β` for a `ZMod l`-linear map `v`. -/
lemma New.IsLargeLevel.exists_linearMap_factor_of_ker_le {l : ℕ} [Fact l.Prime] {A B V : Type}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup V] [Module (ZMod l) B] [Module (ZMod l) V]
    (β : A →+ B) (f : A →+ V) (h_ker_le : ∀ y : A, β y = 0 → f y = 0) :
    ∃ v : B →ₗ[ZMod l] V, ∀ y : A, v (β y) = f y := by
  -- `f` descends to the range of `β`, a subspace of `B`, and extends linearly from there.
  have h_vanish : β.rangeRestrict.ker ≤ f.ker := by
    simpa [ker_rangeRestrict, IsConcreteLE.le_iff] using h_ker_le
  let v₀ : β.range →+ V := liftOfSurjective _ β.rangeRestrict_surjective ⟨f, h_vanish⟩
  obtain ⟨v, hv⟩ := LinearMap.exists_extend (p := β.range.toZModSubmodule l) (v₀.toZModLinearMap l)
  refine ⟨v, fun y ↦ ?_⟩
  have h_eq : v (β y) = v₀ (β.rangeRestrict y) := LinearMap.congr_fun hv (β.rangeRestrict y)
  rw [h_eq]
  exact liftOfRightInverse_comp_apply ..

/-- Let `G` act on `Ω` (`New.Ω`, the algebraic closure of `ℚ`) as the Galois group over the number
field `K`. On a torsion element of (`N`-units of the fixed field of `U`) `× ℤ`, the element `z` acts
by a natural number that is congruent modulo `l` to the cyclotomic character of `z`. -/
lemma New.IsLargeLevel.exists_act_torsion_eq_nsmul {G : Type} [Group G] [TopologicalSpace G]
    [MulSemiringAction G Ω] {K : Type} [Field K] [EmbeddedNumberField K] [IsProGalois G K Ω] (l : ℕ)
    [NeZero l] {N : ℕ} {U : OpenNormalSubgroup G} (z : G) {y : fixedSUnits N U × ℤ}
    (hy : y ∈ torsion ℤ (fixedSUnits N U × ℤ)) :
    ∃ a : ℕ, (cyclotomicCharMod Ω l z).val = a ∧
      ((fixedSUnitsRep N U).prod (Representation.trivial ℤ (G ⧸ (U.toOpenSubgroup : Subgroup G)) ℤ))
        z y = a • y := by
  -- If `k • y = 0`, take the value of the cyclotomic character modulo `l * k`.
  obtain ⟨k, hk, hky⟩ := (torsion_int.le hy).exists_nsmul_eq_zero
  have hk_ne_zero : NeZero k := of_pos hk
  have hy₂ : y.2 = 0 := by simpa [hk.ne'] using congr_arg Prod.snd hky
  refine ⟨(cyclotomicCharMod Ω (l * k) z).val.val,
    cyclotomicCharMod_eq_of_dvd ⟨k, rfl⟩ zmod_eq_natCast_val, ?_⟩
  ext
  · -- The unit is a root of unity of order dividing `l * k`.
    refine smul_eq_pow_cyclotomicCharMod z ?_
    simpa [pow_mul'] using
      congr_arg (fun p : fixedSUnits N U × ℤ ↦ (p.1.val.toMul.val : Ω) ^ l) hky
  · simp [hy₂]

/-- Averaging with a Higman trace. Let `W` represent the finite group `Δ` on `V`, and let the
additive `τ : V → V` satisfy `∑ δ, δ (τ (δ⁻¹ a)) = a`. Let `F : X → V` on a `Δ`-set `X`, and let
`g (F x) = F (g • x) + c` for all `x`. Then `g` moves the average `∑ δ, δ (τ (δ⁻¹ (F (δ • x₀))))`
by `c`. -/
lemma Representation.apply_sum_trace_eq_add {Δ X V : Type} [Group Δ] [Fintype Δ] [MulAction Δ X]
    [AddCommGroup V] (W : Representation ℤ Δ V) (τ : V →+ V)
    (hτ : ∀ a : V, ∑ δ : Δ, W δ (τ (W δ⁻¹ a)) = a) (F : X → V) (x₀ : X) (g : Δ) (c : V)
    (hF : ∀ x : X, W g (F x) = F (g • x) + c) :
    W g (∑ δ : Δ, W δ (τ (W δ⁻¹ (F (δ • x₀))))) = ∑ δ : Δ, W δ (τ (W δ⁻¹ (F (δ • x₀)))) + c := by
  -- Reindex the sum by `δ ↦ g * δ`.
  have h_shift (δ : Δ) : W g (W δ (τ (W δ⁻¹ (F (δ • x₀))))) =
      W (g * δ) (τ (W (g * δ)⁻¹ (F ((g * δ) • x₀)))) + W (g * δ) (τ (W (g * δ)⁻¹ c)) := by
    simp [← map_add, ← hF, mul_smul]
  calc W g (∑ δ : Δ, W δ (τ (W δ⁻¹ (F (δ • x₀)))))
      = ∑ δ : Δ, W g (W δ (τ (W δ⁻¹ (F (δ • x₀))))) := map_sum ..
    _ = ∑ δ : Δ, (W δ (τ (W δ⁻¹ (F (δ • x₀)))) + W δ (τ (W δ⁻¹ c))) :=
      sum_equiv (.mulLeft g) _ _ h_shift
    _ = _ := by simp [sum_add_distrib, hτ]

section SymbolMaps

namespace New.IsLargeLevel

/-- Let `b y i` be the `l`-th power residue symbol of the `N`-unit `y` of the field of `U` at the
Frobenius `frob i`: `ζ ^ b y i = frob i r / r` whenever `r ^ l = y`, for the root of unity `ζ` of
`New.rootPowHom`. Let `U` fix `z r / r ^ n` whenever `r ^ l` is such an `N`-unit and every
`frob i` fixes `r` (written additively in `New.DiscreteUnits Ω`). If all symbols of
`y` vanish, then `z y / y ^ n` is the `l`-th power of an `N`-unit. -/
private lemma exists_act_sub_nsmul_eq_nsmul_of_symbol_eq_zero {G K : Type} [Group G]
    [TopologicalSpace G] [Field K] [EmbeddedNumberField K] [MulSemiringAction G Ω]
    [IsProGalois G K Ω] {l N : ℕ} [Fact l.Prime] {U : OpenNormalSubgroup G} {ι : Type}
    (frob : ι → G) (b : fixedSUnits N U →+ ι → ZMod l)
    (hb : ∀ (y : fixedSUnits N U) (r : DiscreteUnits Ω), l • r = ↑y → ∀ i : ι,
      (rootPowHom Ω l).val (b y i) = unitsRep (frob i) r - r)
    {z : G} {n : ℕ}
    (h_fix : ∀ r : DiscreteUnits Ω, l • r ∈ fixedSUnits N U → (∀ i : ι, unitsRep (frob i) r = r) →
      unitsRep z r - n • r ∈ (unitsModule U.toOpenSubgroup.toSubgroup).H0)
    (y : fixedSUnits N U) (hy : ∀ i : ι, b y i = 0) :
    ∃ c : fixedSUnits N U, fixedSUnitsRep N U z y - n • y = l • c := by
  obtain ⟨y, hyE⟩ := y
  obtain ⟨w, rfl⟩ := y.exists_nsmul (ne l)
  -- The `l`-th root `w` is fixed by every `frob i`, as the symbols vanish.
  have h_frob (i : ι) : unitsRep (frob i) w = w :=
    sub_eq_zero.mp (by simpa [hy i] using (hb ⟨l • w, hyE⟩ w rfl i).symm)
  -- So `c = z w - n • w` is an `N`-unit of the field of `U`, and `z y - n • y = l • c`.
  have h_mul :
      l • (unitsRep z w - n • w) =
        ↑(fixedSUnitsRep N U z ⟨_, hyE⟩ - n • (⟨_, hyE⟩ : fixedSUnits N U)) := by
    rw [smul_sub, ← map_nsmul, smul_comm]
    rfl
  exact ⟨⟨unitsRep z w - n • w, mem_sUnits_of_nsmul_mem h_mul, h_fix w hyE h_frob⟩,
    (Subtype.ext h_mul).symm⟩

/-- The equivariant maps given by power residue symbols. For `a : ι → V` and `c` fixed by `G` (in
the kernel of the coboundary map `coboundaryMap V.ρ`), the map from (`N`-units) `× ℤ` to `V` given
by `(y, k) ↦ ∑ (i, δ), b (δ y) i • δ⁻¹ (a i) + k • c` is `G ⧸ U`-equivariant, where `W` is the
action of `G ⧸ U` on `V`. -/
private noncomputable def symbolIntertwiningMap {G K R : Type} [Group G] [TopologicalSpace G]
    [Field K] [EmbeddedNumberField K] [MulSemiringAction G Ω] [IsProGalois G K Ω] [CommRing R]
    {l N : ℕ} [Fact l.Prime] {V : DiscreteModule R G} {U : OpenNormalSubgroup G}
    [Module (ZMod l) V] [NeZero N] {ι : Type} [Fintype ι]
    (W : Representation ℤ (G ⧸ U.toOpenSubgroup.toSubgroup) V) (hW : ∀ g : G, ⇑(V.ρ g) = W g)
    (b : fixedSUnits N U →+ ι → ZMod l) :
    (ι → V) × (coboundaryMap V.ρ).toAddMonoidHom.ker →+
      ((fixedSUnitsRep N U).prod
        (Representation.trivial ℤ (G ⧸ U.toOpenSubgroup.toSubgroup) ℤ)).IntertwiningMap W :=
  let β : fixedSUnits N U →+ ι × (G ⧸ U.toOpenSubgroup.toSubgroup) → ZMod l :=
    mk' (fun y (i, δ) ↦ b (fixedSUnitsRep N U δ y) i) (by simp [funext_iff])
  mk' (fun (a, c) ↦
      ⟨.coprod (∑ θ : ι × G ⧸ (U.toOpenSubgroup : Subgroup G),
        .smulRight (.proj θ ∘ₗ β.toIntLinearMap) (W θ.2⁻¹ (a θ.1))) (.smulRight .id c),
        fun δ ↦ by
          -- equivariance: on units shift the index by `δ`; on `ℤ` use that `c` is fixed
          have hc_fixed (g : G) : (c : V) = W g c :=
            (eq_of_sub_eq_zero (congrFun c.prop g)).symm.trans (congrFun (hW g) c)
          ext y
          · simpa [β, ZMod.map_smul] using sum_equiv (.prodCongr 1 (.mulRight δ)) _ _ (by simp)
          · simpa using δ.ind' hc_fixed⟩)
    fun _ _ ↦ by ext <;> simp [sum_add_distrib]

/-- Let `W` be the action of `G ⧸ U` on `V` (that is, `V.ρ g = W g`), let `l` kill `V`, and let
`z - n` be injective on `V`. Let `τ` be a Higman trace: `∑ δ, δ (τ (δ⁻¹ a)) = a`. Let `b` and
`h_fix` be as in `exists_act_sub_nsmul_eq_nsmul_of_symbol_eq_zero`. Then every `G ⧸ U`-equivariant
`x` from (`N`-units) `× ℤ` to `V` is given by symbols: it lies in the range of
`symbolIntertwiningMap W hW b`. -/
private lemma mem_range_symbolIntertwiningMap {G K R : Type} [Group G] [TopologicalSpace G]
    [Field K] [EmbeddedNumberField K] [MulSemiringAction G Ω] [IsProGalois G K Ω] [CommRing R]
    {l N : ℕ} [Fact l.Prime] {V : DiscreteModule R G} {U : OpenNormalSubgroup G}
    [Module (ZMod l) V] [NeZero N] {ι : Type} [Fintype ι]
    (W : Representation ℤ (G ⧸ U.toOpenSubgroup.toSubgroup) V) (hW : ∀ g : G, ⇑(V.ρ g) = W g)
    (h_tors : ∀ a : V, l • a = 0) {z : G} {n : ℕ} (h_inj_sub : Function.Injective ⇑(V.ρ z - n))
    (τ : V →+ V) (hτ : ∀ a : V, ∑ δ : G ⧸ (U.toOpenSubgroup : Subgroup G), W δ (τ (W δ⁻¹ a)) = a)
    (frob : ι → G) (b : fixedSUnits N U →+ ι → ZMod l)
    (hb : ∀ (y : fixedSUnits N U) (r : DiscreteUnits Ω), l • r = ↑y → ∀ i : ι,
      (rootPowHom Ω l).val (b y i) = unitsRep (frob i) r - r)
    (h_fix : ∀ r : DiscreteUnits Ω, l • r ∈ fixedSUnits N U → (∀ i : ι, unitsRep (frob i) r = r) →
      unitsRep z r - n • r ∈ (unitsModule U.toOpenSubgroup.toSubgroup).H0)
    (x : ((fixedSUnitsRep N U).prod
      (Representation.trivial ℤ (G ⧸ U.toOpenSubgroup.toSubgroup) ℤ)).IntertwiningMap W) :
    x ∈ (symbolIntertwiningMap W hW b).range := by
  classical
  let ρ : Representation ℤ (G ⧸ U.toOpenSubgroup.toSubgroup) (fixedSUnits N U × ℤ) :=
    (fixedSUnitsRep N U).prod (.trivial _ _ ℤ)
  let β : fixedSUnits N U →+ ι × (G ⧸ U.toOpenSubgroup.toSubgroup) → ZMod l :=
    mk' (fun y (i, δ) ↦ b (fixedSUnitsRep N U δ y) i) (by simp [funext_iff])
  -- `x` kills every unit `y` whose symbols `β y` vanish.
  have h_kill (y : fixedSUnits N U) (hy : β y = 0) : x (y, 0) = 0 := by
    -- The symbols of `y` vanish, so `z y - n • y = l • c` for an `N`-unit `c`.
    have hy_symbol (i : ι) : b y i = 0 := by simpa [β] using congr_fun hy (i, 1)
    obtain ⟨c, hc⟩ := exists_act_sub_nsmul_eq_nsmul_of_symbol_eq_zero frob b hb h_fix y hy_symbol
    have hc_pair : ρ z (y, 0) - n • (y, 0) = l • (c, 0) := Prod.ext hc (by simp [ρ])
    -- As `l` kills `V`, `z - n` kills the value of `x`.
    have h_zero : W z (x (y, 0)) - n • x (y, 0) = 0 := by
      rw [← x.isIntertwining, ← map_nsmul, ← map_sub, hc_pair, map_nsmul, h_tors]
    exact (injective_iff_map_eq_zero _).mp h_inj_sub _ (by simpa [hW] using h_zero)
  -- Write `x (y, 0) = v (β y)` with `v` linear, then average `v` with `τ`.
  obtain ⟨v, hv⟩ : ∃ v : _ →ₗ[ZMod l] V, ∀ y, v (β y) = x (y, 0) :=
    exists_linearMap_factor_of_ker_le β (x.toAddMonoidHom.comp (inl (fixedSUnits N U) ℤ)) h_kill
  -- `x (0, 1)` is fixed by `G`.
  refine ⟨(fun i ↦ ∑ δ, W δ (τ (v (Pi.single (i, δ) 1))),
    ⟨x (0, 1), by simp [funext_iff, coboundaryMap, hW, ← x.isIntertwining]⟩), ?_⟩
  ext y
  swap
  · simp [symbolIntertwiningMap]
  suffices h_coords :
      ∑ θ, β y θ • ∑ g, W θ.2⁻¹ (W g (τ (v (Pi.single (θ.1, g) 1)))) = x (y, 0) by
    simpa [symbolIntertwiningMap, β] using h_coords
  -- Expand `x (y, 0) = ∑ δ, δ (τ (v (β (δ⁻¹ y))))` in coordinates; the two sums match under
  -- `((i, δ), g) ↦ (δ⁻¹ * g, i, g)`.
  rw [← hτ (x _)]
  suffices h_reindex :
      ∑ p : (ι × (G ⧸ U.toOpenSubgroup.toSubgroup)) × (G ⧸ U.toOpenSubgroup.toSubgroup),
        β y p.1 • W p.1.2⁻¹ (W p.2 (τ (v (Pi.single (p.1.1, p.2) 1)))) =
      ∑ q : (G ⧸ U.toOpenSubgroup.toSubgroup) × (ι × (G ⧸ U.toOpenSubgroup.toSubgroup)),
        β (fixedSUnitsRep N U q.1⁻¹ y) q.2 • W q.1 (τ (v (Pi.single q.2 1))) by
    simpa [↓← x.isIntertwining, congrArg v (pi_eq_sum_univ' (β _)), ZMod.map_smul,
      ← sum_product', smul_sum, ← hv] using h_reindex
  refine sum_nbij' (fun ((i, δ), g) ↦ (δ⁻¹ * g, i, g)) (fun (δ, i, g) ↦ ((i, g / δ), g))
    ?_ ?_ ?_ ?_ ?_ <;> simp [β]

/-- Let `l` kill `V`, let `z - n` be injective on `V`, and let `z` raise the `l`-th roots of unity
in `Ω` (`New.Ω`, the algebraic closure of `ℚ`) to the power `n`. Then every `ℤ`-linear `x` from
(`N`-units) `× ℤ` to `V` that commutes with `z` kills the torsion. -/
private lemma torsion_le_ker_of_map_act_eq {G K R : Type} [Group G] [TopologicalSpace G]
    [Field K] [EmbeddedNumberField K] [MulSemiringAction G Ω] [IsProGalois G K Ω] [CommRing R]
    {l N : ℕ} [Fact l.Prime] {V : DiscreteModule R G} {U : OpenNormalSubgroup G}
    [Module (ZMod l) V] {z : G} {n : ℕ}
    (h_inj_sub : Function.Injective ⇑(V.ρ z - n)) (h_cyc : (cyclotomicCharMod Ω l z).val = n)
    (x : fixedSUnits N U × ℤ →ₗ[ℤ] V)
    (hx : ∀ y : fixedSUnits N U × ℤ, x (((fixedSUnitsRep N U).prod
      (Representation.trivial ℤ (G ⧸ U.toOpenSubgroup.toSubgroup) ℤ)) z y) = V.ρ z (x y)) :
    torsion ℤ (fixedSUnits N U × ℤ) ≤ LinearMap.ker x := by
  -- `z` acts on a torsion element `y` by an integer `a = n` modulo `l`, so `z - n` kills `x y`.
  intro y hy
  obtain ⟨a, ha, h_act⟩ := exists_act_torsion_eq_nsmul l z hy
  have h_na : (n : ZMod l) = a := h_cyc.symm.trans ha
  have h_eigen : V.ρ z (x y) = n • x y := calc
    V.ρ z (x y) = x (a • y) := by rw [← hx, h_act]
    _ = n • x y := by rw [map_nsmul, ← cast_smul_eq_nsmul (ZMod l), ← h_na, cast_smul_eq_nsmul]
  exact (injective_iff_map_eq_zero _).mp h_inj_sub _ (by simp [h_eigen])

/-- The converse of reciprocity on the kernel of `symbolIntertwiningMap`. Let `W` be the action of
`G ⧸ U` on `V`, let `τ` be a Higman trace, and let `h_conv` say that a family `f` satisfying the
symbol relations gives, for each `a : V`, a trivialised cocycle with value `∑ δ, δ (f (i, δ) • a)`
at each `γ i`. If `(a, c)` lies in the kernel, then `c = 0` and some trivialised cocycle takes the
value `a i` at each `γ i`. -/
private lemma exists_mem_trivialisedCocycles_of_mem_ker {G K R : Type} [Group G]
    [TopologicalSpace G] [Field K] [EmbeddedNumberField K] [MulSemiringAction G Ω]
    [IsProGalois G K Ω] [CommRing R] {l N : ℕ} [Fact l.Prime] {V : DiscreteModule R G}
    {U : OpenNormalSubgroup G} [Module (ZMod l) V] [NeZero N] [Finite V] {ι : Type}
    [Fintype ι] {I : Set G}
    (W : Representation ℤ (G ⧸ U.toOpenSubgroup.toSubgroup) V) (hW : ∀ g : G, ⇑(V.ρ g) = W g)
    (τ : V →+ V) (hτ : ∀ a : V, ∑ δ : G ⧸ (U.toOpenSubgroup : Subgroup G), W δ (τ (W δ⁻¹ a)) = a)
    (b : fixedSUnits N U →+ ι → ZMod l) (γ : ι → G)
    (h_conv : ∀ f : ι × G ⧸ U.toOpenSubgroup.toSubgroup → ZMod l,
      (∀ y : fixedSUnits N U, ∑ θ : ι × G ⧸ (U.toOpenSubgroup : Subgroup G),
        b (fixedSUnitsRep N U θ.2 y) θ.1 * f θ = 0) →
      ∀ a : V, ∃ P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I,
        ∀ i : ι, P.2 (γ i) = ∑ δ : G ⧸ U.toOpenSubgroup.toSubgroup, V.ρ δ.out (f (i, δ) • a))
    {a : ι → V} {c : (coboundaryMap V.ρ).toAddMonoidHom.ker}
    (h_ker : (a, c) ∈ (symbolIntertwiningMap W hW b).ker) :
    c = 0 ∧ ∃ P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I, ∀ i : ι, P.2 (γ i) = a i := by
  have h_zero : symbolIntertwiningMap W hW b (a, c) = 0 := AddMonoidHom.mem_ker.mp h_ker
  have hc : c = 0 := by simpa [symbolIntertwiningMap] using DFunLike.congr_fun h_zero (0, 1)
  refine ⟨hc, ?_⟩
  -- Each coordinate of `τ (δ⁻¹ (a i))` in a basis kills the symbols; the converse of reciprocity
  -- gives cocycles `P k`, to be added up.
  let basis := Module.finBasis (ZMod l) V
  have h_coord (k : Fin _) (y : fixedSUnits N U) :
      ∑ θ : ι × G ⧸ U.toOpenSubgroup.toSubgroup,
        b (fixedSUnitsRep N U θ.2 y) θ.1 * basis.repr (τ (W θ.2⁻¹ (a θ.1))) k = 0 := by
    simpa [symbolIntertwiningMap, ZMod.map_smul] using
      congr_arg (fun v ↦ basis.repr (τ v) k) (DFunLike.congr_fun h_zero (y, 0))
  have h_cocycles (k : Fin _) : ∃ P ∈ V.trivialisedCocycles (PlaceAboveLevel N) I, ∀ i : ι,
      P.2 (γ i) = ∑ δ : G ⧸ U.toOpenSubgroup.toSubgroup,
        V.ρ δ.out (basis.repr (τ (W δ⁻¹ (a i))) k • basis k) :=
    h_conv _ (h_coord k) (basis k)
  choose P hP h_val using h_cocycles
  refine ⟨∑ k, P k, sum_mem fun k _ ↦ hP k, fun i ↦ ?_⟩
  -- Interchange the sums, expand in the basis, and use the trace identity for `a i`.
  have h_expand (δ : G ⧸ U.toOpenSubgroup.toSubgroup) :
      ∑ k, V.ρ δ.out (basis.repr (τ (W δ⁻¹ (a i))) k • basis k) = W δ (τ (W δ⁻¹ (a i))) := by
    simp [← map_sum, hW]
  simpa [Prod.snd_sum, h_val, sum_comm (γ := Fin _), h_expand] using hτ (a i)

end New.IsLargeLevel

end SymbolMaps

/-- Counting along `r : T → J` and a surjection `p` from `ker r` onto `D`:
`#T = #(ker p) * #D * #(range r)`. -/
lemma AddMonoidHom.card_eq_card_ker_mul_card_mul_card_range {T J D : Type} [AddCommGroup T]
    [AddCommGroup J] [AddCommGroup D] (r : T →+ J) (p : r.ker →+ D) (hp : p.range = ⊤) :
    Nat.card T = Nat.card p.ker * Nat.card D * Nat.card r.range := by
  rw [← r.ker.card_mul_index, ← p.ker.card_mul_index, index_ker, index_ker, hp, card_top]

/-- Counting along `d : A → B` and a surjection `j` from `(ι → A) × ker d` onto `H`:
`#A ^ (#ι + 1) = #H * #(range d) * #(ker j)`. -/
lemma AddMonoidHom.card_pow_succ_eq_card_mul_card_range_mul_card_ker {ι A B H : Type} [Fintype ι]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup H] (d : A →+ B) (j : (ι → A) × d.ker →+ H)
    (hj : Function.Surjective j) :
    Nat.card A ^ (Fintype.card ι + 1) = Nat.card H * Nat.card d.range * Nat.card j.ker := by
  rw [pow_succ, ← card_eq_fintype_card, ← Nat.card_fun, ← d.ker.card_mul_index, ← mul_assoc,
    ← Nat.card_prod, ← j.ker.card_mul_index, index_ker, index_ker, j.range_eq_top.mpr hj,
    card_top, mul_rotate]

/-- Count of the trivialised cocycles, for split places indexed by `ι`. Let `V` be finite, killed by
the prime `l`, fixed by `U`, Higman-projective over `G ⧸ U`, with `z - n` injective; let `U` fix
`z r / r ^ n` whenever `r ^ l` is an `N`-unit fixed by `U` and every `s.φ i` fixes `r`. (a) There
are between one and `#V ^ (#ι + 1)` of them. (b) Exactly `#V ^ (#ι + 1)` if `z` raises the `l`-th
roots of unity to the power `n` and `K` is totally complex. Trivialised cocycles are pairs of `f` on
the places of Ω over `N` and ∞ and a continuous `c : G → V` zero on `I`, with
`g f(x) = f(gx) + c(g)`. `I` is inertia above the primes prime to `N` other than the split `v i`,
and `s.φ i ∈ U` are Frobenii at them. -/
lemma New.IsLargeLevel.SplitPlaces.card_trivialised_of_isHigmanProjective {G K R ι : Type} [Group G]
    [TopologicalSpace G] [Field K] [EmbeddedNumberField K] [MulSemiringAction G Ω]
    [IsProGalois G K Ω] [CommRing R] {l N : ℕ} [Fact l.Prime] [NeZero N] {V : DiscreteModule R G}
    {I : Set G} {U : OpenNormalSubgroup G} (s : SplitPlaces l N I U ι) [Fintype ι] {z : G} {n : ℕ}
    (hV_fin : V.FiniteKilledFixedInj l U z n)
    (hV_proj : V.IsHigmanProjective U.toOpenSubgroup.toSubgroup)
    (h_fix : ∀ r : DiscreteUnits Ω, l • r ∈ fixedSUnits N U → (∀ i : ι, unitsRep (s.φ i) r = r) →
      unitsRep z r - n • r ∈ (unitsModule U.toOpenSubgroup.toSubgroup).H0) :
    -- (a) the trivialised cocycles are finitely many, at most `#V ^ (#ι + 1)`
    V.HasFewCocycles (PlaceAboveLevel N) I (Fintype.card ι + 1) ∧
    -- (b) exactly that many if `z` acts on `l`-th roots of unity by `n` and `K` is totally complex
    ((cyclotomicCharMod Ω l z).val = n → IsTotallyComplex K →
      Nat.card (V.trivialisedCocycles (PlaceAboveLevel N) I) =
        Nat.card V ^ (Fintype.card ι + 1)) := by
  classical
  -- Write `Δ = G ⧸ U` and `H` for the `Δ`-maps from (`N`-units) `× ℤ` to `V`. We count both sides
  -- along the maps `r`, `p`, `j`, `d` below: with `H₀ ≤ H` the maps that kill torsion,
  -- `#trivialisedCocycles = #H₀ * #range d * #range r`,
  -- `#V ^ (#ι + 1) = #H * #range d * #ker j`,
  -- and `range r ≤ ker j`. Under the two extra hypotheses both inclusions are equalities.
  --
  -- Dirichlet: independent equivariant real forms `Λ` on (`N`-units) `× ℤ`, one for each
  -- `U`-orbit of places; the rank is at most the number of orbits.
  obtain ⟨h_units_fg, Λ, hΛ, h_indep, h_rank⟩ := dirichlet_fixedSUnits G N U
  obtain ⟨hV_finite, h_tors, h_triv, h_inj⟩ := hV_fin
  obtain ⟨τ, hτ_out⟩ := hV_proj
  have hV_module : Module (ZMod l) V := AddCommGroup.zmodModule h_tors
  -- `γ i` is an element of inertia above `s.v i` that multiplies an `l`-th root of a uniformiser
  -- by the fixed primitive `l`-th root of unity.
  choose γ hγ using fun i ↦ exists_isTameGeneratorFor G l (s.isPlaceOver i)
  -- Reciprocity. `hβ₀`: `β₀ y i` is the power residue symbol of the unit `y` at `s.φ i`.
  -- `h_rel`: a trivialised cocycle that vanishes at all `γ i` vanishes on `U`, and its values at
  -- the `γ i` satisfy one linear relation for each `y`. `h_conv`: the converse of the latter.
  obtain ⟨β₀, hβ₀, h_rel, h_conv⟩ := s.power_residue_reciprocity γ hγ h_triv
  let W : Representation ℤ (G ⧸ U.1.1) V :=
    QuotientGroup.lift _ (actionRep ℤ V V.ρ) fun g hg ↦ LinearMap.ext (h_triv g hg)
  have hW (g : G) : ⇑(V.ρ g) = W g := rfl
  have hτ (a : V) : ∑ δ, W δ (τ (W δ⁻¹ a)) = a := by simpa [hW] using hτ_out a
  let ρ : Representation ℤ (G ⧸ U.1.1) (fixedSUnits N U × ℤ) :=
    (fixedSUnitsRep N U).prod (.trivial _ _ ℤ)
  -- `d a` is the coboundary `g ↦ g a - a`.
  let d : V →+ G → V := (coboundaryMap V.ρ).toAddMonoidHom
  -- `j (a, c)`, for `c` fixed by `G`, sends `(y, k)` to `∑ β₀ (δ y) i • δ⁻¹ (a i) + k • c`.
  let j : (ι → V) × d.ker →+ ρ.IntertwiningMap W := symbolIntertwiningMap W hW β₀
  -- `r` evaluates a trivialised cocycle at the `γ i`; by reciprocity the values lie in `ker j`.
  let r : V.trivialisedCocycles (PlaceAboveLevel N) I →+ j.ker :=
    mk' (fun P ↦ ⟨(P.1.2 ∘ γ, 0), by
        have h_symbols (y : fixedSUnits N U) :
            ∑ θ : ι × G ⧸ U.1.1,
              β₀ (fixedSUnitsRep N U θ.2 y) θ.1 • W θ.2⁻¹ (P.1.2 (γ θ.1)) = 0 := by
          simpa [hW] using (h_rel _ P.2).2 y
        ext <;> simp [j, symbolIntertwiningMap, h_symbols]⟩)
      fun _ _ ↦ by ext <;> simp
  -- In `ker r` the cocycle vanishes on `U`, so the trivialisation descends to `U`-orbits.
  let f (P : r.ker) : MulAction.orbitRel.Quotient U.1.1 (PlaceAboveLevel N) → V :=
    Quotient.lift P.1.1.1 fun _ x ⟨g, hg⟩ ↦ by
      have h_gamma (i : ι) : P.1.1.2 (γ i) = 0 :=
        congrArg (fun q : j.ker ↦ q.1.1 i) P.2
      have h_zero : ∀ g ∈ U, P.1.1.2 g = 0 := (h_rel _ P.1.2).1 h_gamma
      simpa [← hg, h_triv, h_zero] using! (P.1.2.2.1 g x).symm
  have hf (P : r.ker) (g : G) (x : MulAction.orbitRel.Quotient U.1.1 (PlaceAboveLevel N)) :
      W g (f P x) = f P ((g : G ⧸ U.1.1) • x) + P.1.1.2 g :=
    x.ind' (P.1.2.2.1 g)
  -- There the cocycle is a coboundary: average `f P` with `τ` along the orbit of `x₀`.
  have h_cob (P : r.ker) : P.1.1.2 ∈ d.range := by
    let x₀ : PlaceAboveLevel N := Classical.arbitrary _
    exact ⟨∑ δ, W δ (τ (W δ⁻¹ (f P (δ • ⟦x₀⟧)))), funext fun g ↦
      sub_eq_of_eq_add' (W.apply_sum_trace_eq_add τ hτ (f P) ⟦x₀⟧ g (P.1.1.2 g) (hf P g))⟩
  let p : r.ker →+ d.range := mk' (fun P ↦ ⟨P.1.1.2, h_cob P⟩) (by tauto)
  -- `j` is onto: every equivariant `x` is given by the symbols.
  have h_onto : Function.Surjective j :=
    mem_range_symbolIntertwiningMap W hW h_tors h_inj τ hτ s.φ β₀ hβ₀ h_fix
  have h_finite_maps : Finite (ρ.IntertwiningMap W) := .of_surjective j h_onto
  -- `ker p` consists of the equivariant functions on the `U`-orbits of places; by Dirichlet's
  -- theorem and `card_hom_lattice_eq_card_equivariant` there are as many as maps in `H₀`, those
  -- that kill torsion.
  let H₀ := {x : ρ.IntertwiningMap W // torsion ℤ (fixedSUnits N U × ℤ) ≤ LinearMap.ker x.1}
  have h_ker_p : Nat.card H₀ = Nat.card p.ker := by
    rw [card_hom_lattice_eq_card_equivariant l hτ hΛ h_indep h_rank]
    exact card_congr
      { toFun F := ⟨⟨⟨⟨(F.1 ⟦·⟧), 0⟩, by fun_prop,
          fun g x ↦ by simpa [hW] using! (F.2 g ⟦x⟧).symm, by simp⟩, rfl⟩, rfl⟩
        invFun P := ⟨f P, fun δ ↦ δ.ind' (by simp [hf, Subtype.mk.inj P.2])⟩
        left_inv F := Subtype.ext (funext fun x ↦ x.inductionOn fun _ ↦ rfl)
        right_inv := fun ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, rfl⟩ ↦ rfl }
  -- `p` is onto: the constant function `a` trivialises the coboundary of `a`.
  have h_range_p : p.range = ⊤ := by
    refine p.range_eq_top.mpr fun ⟨_cocycle, a, ha⟩ ↦
      ⟨⟨⟨(fun _ ↦ a, (V.ρ · a - a)), by fun_prop, ?_⟩, ?_⟩, Subtype.ext ha⟩
    · simp +contextual [h_triv _ (s.mem_and_conj_mem ..).1]
    · simp [Subtype.ext_iff, funext_iff, r, h_triv, s.decompGroup_le (s.isPlaceOver _) (hγ _).1.1]
  have h_left : Nat.card (V.trivialisedCocycles (PlaceAboveLevel N) I) =
      Nat.card H₀ * Nat.card d.range * Nat.card r.range := by
    rw [h_ker_p, r.card_eq_card_ker_mul_card_mul_card_range p h_range_p]
  have h_right : Nat.card V ^ (card ι + 1) =
      Nat.card (ρ.IntertwiningMap W) * Nat.card d.range * Nat.card j.ker :=
    d.card_pow_succ_eq_card_mul_card_range_mul_card_ker j h_onto
  rw [DiscreteModule.HasFewCocycles, h_left, h_right]
  refine ⟨⟨?_, ?_⟩, fun h_cyc _ ↦ ?_⟩
  · have h_nonempty : Nonempty H₀ := ⟨0, by simp⟩
    exact mul_pos (mul_pos card_pos card_pos) card_pos
  · grw [r.range.card_le_card_addGroup, Finite.card_subtype_le]
  -- Equality, first part: every `x` kills torsion, since `z` acts on a torsion element `y` by an
  -- integer `a = n` modulo `l`, so that `z - n` kills `x y`.
  have h_torsion (x : ρ.IntertwiningMap W) : torsion ℤ _ ≤ LinearMap.ker x.1 :=
    torsion_le_ker_of_map_act_eq h_inj h_cyc x.1 fun y ↦
      (Representation.IntertwiningMap.isIntertwining _ _ x z y).trans (congrFun (hW z) (x y)).symm
  -- Second part: `r` is onto, by the converse of reciprocity.
  have h_range_r : r.range = ⊤ := by
    refine r.range_eq_top.mpr fun ⟨⟨a, c⟩, h_ker⟩ ↦ ?_
    obtain ⟨rfl, P, hP, hPγ⟩ := exists_mem_trivialisedCocycles_of_mem_ker W hW τ hτ β₀ γ
      (h_conv (isTotallyComplex_of_algebra K _)) h_ker
    exact ⟨⟨P, hP⟩, Subtype.ext (Prod.ext (funext hPγ) rfl)⟩
  rw [h_range_r, card_top, Nat.card_congr (.subtypeUnivEquiv h_torsion)]

/-- Under the hypotheses of `card_trivialised_of_isHigmanProjective`, there are between one and
`#V ^ (#ι + 1)` trivialised cocycles. -/
lemma New.IsLargeLevel.SplitPlaces.hasFewCocycles_of_isHigmanProjective {G K R ι : Type} [Group G]
    [TopologicalSpace G] [Field K] [EmbeddedNumberField K] [MulSemiringAction G Ω]
    [IsProGalois G K Ω] [CommRing R] {l N : ℕ} [Fact l.Prime] [NeZero N] {V : DiscreteModule R G}
    {I : Set G} {U : OpenNormalSubgroup G} (s : SplitPlaces l N I U ι) [Fintype ι] {z : G} {n : ℕ}
    (hV_fin : V.FiniteKilledFixedInj l U z n)
    (hV_proj : V.IsHigmanProjective U.toOpenSubgroup.toSubgroup)
    (h_fix : ∀ r : DiscreteUnits Ω, l • r ∈ fixedSUnits N U →
      (∀ i : ι, unitsRep (s.φ i) r = r) →
      unitsRep z r - n • r ∈ (unitsModule U.toOpenSubgroup.toSubgroup).H0) :
    V.HasFewCocycles (PlaceAboveLevel N) I (Fintype.card ι + 1) :=
  (s.card_trivialised_of_isHigmanProjective hV_fin hV_proj h_fix).left

/-- Under the hypotheses of `card_trivialised_of_isHigmanProjective`, if `K` is totally complex and
`z` raises the `l`-th roots of unity to the power `n`, there are exactly `#V ^ (#ι + 1)`
trivialised cocycles. -/
lemma New.IsLargeLevel.SplitPlaces.card_trivialisedCocycles_eq_of_isHigmanProjective
    {G K R ι : Type} [Group G] [TopologicalSpace G] [Field K] [EmbeddedNumberField K]
    [MulSemiringAction G Ω] [IsProGalois G K Ω] [CommRing R] {l N : ℕ} [Fact l.Prime] [NeZero N]
    {V : DiscreteModule R G} {I : Set G} {U : OpenNormalSubgroup G} (s : SplitPlaces l N I U ι)
    [Fintype ι] {z : G} {n : ℕ} (hV_fin : V.FiniteKilledFixedInj l U z n)
    (hV_proj : V.IsHigmanProjective U.toOpenSubgroup.toSubgroup)
    (h_fix : ∀ r : DiscreteUnits Ω, l • r ∈ fixedSUnits N U →
      (∀ i : ι, unitsRep (s.φ i) r = r) →
      unitsRep z r - n • r ∈ (unitsModule U.toOpenSubgroup.toSubgroup).H0)
    [IsTotallyComplex K] (hz : (cyclotomicCharMod Ω l z).val = n) :
    Nat.card (V.trivialisedCocycles (PlaceAboveLevel N) I) = Nat.card V ^ (Fintype.card ι + 1) :=
  (s.card_trivialised_of_isHigmanProjective hV_fin hV_proj h_fix).right hz inferInstance

end ProjectiveCount

/-! ## The count for modules with a central scalar -/

section GreenbergWilesBound

open NumberField Function Set Nat New.DiscreteModule trivialisedCocycles Quotient Subgroup
  commutatorElement

attribute [local instance low] Fintype.ofFinite

/-- Let the Frobenii detect the roots of units (`U` fixes every `x` that all `s.φ i` fix with
`m • x` an `N`-unit fixed by `U`), and let `z` be central modulo `U` and fix the `l`-th roots of
unity, `l ∣ m`. If `l • x` is an `N`-unit fixed by `U` and the Frobenii fix `x`, then every `g` that
fixes `l • x` fixes `z x - x`. -/
lemma New.IsLargeLevel.SplitPlaces.fixes_sub_of_frobeniiDetectRoots {K ι : Type} [Field K]
    [EmbeddedNumberField K] {l m N : ℕ} [NeZero l] [NeZero m] {I : Set Gal(Ω/K)}
    {U : OpenNormalSubgroup Gal(Ω/K)} (s : SplitPlaces (G := Gal(Ω/K)) (K := K) m N I U ι)
    (hlm : l ∣ m) (hdetect : s.FrobeniiDetectRoots) {z : Gal(Ω/K)}
    (hz : (cyclotomicCharMod Ω l z).val = (1 : ℕ)) (hcentral : ∀ g : Gal(Ω/K), ⁅z, g⁆ ∈ U)
    (x : DiscreteUnits Ω) (hx : l • x ∈ fixedSUnits N U) (hφ : ∀ i : ι, unitsRep (s.φ i) x = x)
    (g : Gal(Ω/K)) (hg : unitsRep g (l • x) = l • x) :
    unitsRep g (unitsRep z x - 1 • x) = unitsRep z x - 1 • x := by
  -- `U` fixes `x`, so `g` and `z` commute on `x`, and `z` fixes the `l`-torsion element `g x - x`.
  obtain ⟨q, rfl⟩ := hlm
  have hU : ∀ k ∈ U, unitsRep k x = x :=
    hdetect x (by simpa [mul_nsmul] using nsmul_mem hx q) hφ
  have hswap : unitsRep g (unitsRep z x) = unitsRep z (unitsRep g x) := by
    -- Apply `z * g` to the fact that the commutator `⁅z, (g * z)⁻¹⁆ ∈ U` fixes `x`.
    have hcomm : unitsRep ⁅z, (g * z)⁻¹⁆ x = x := hU _ (hcentral (g * z)⁻¹)
    simpa [commutatorElement_def] using congrArg (unitsRep (z * g)) hcomm
  have htors : l • (unitsRep g x - x) = 0 := by rw [smul_sub, ← map_nsmul, hg, sub_self]
  have hz_fix : unitsRep z (unitsRep g x - x) = unitsRep g x - x := by
    simpa using cyclotomicCharMod_eq_iff_unitsRep.mp hz htors
  rw [map_sub] at hz_fix
  linear_combination (norm := (simp; abel)) hswap + hz_fix

/-- The exact count over an open subgroup `B` of `G = Gal(Ω/K)` that contains `U` and `z`. Let `K`
be totally complex, let `S` be split places for `l`, and let `z` fix the `l`-th roots of unity.
Suppose (`hfix`) that for every `x` fixed by the Frobenii `S.φ i` with `l • x` an `N`-unit fixed
by `U`, every `g` fixing `l • x` fixes `z x - x`. Let `U ≤ Q` in `B`, with `Q` fixing the `l`-th
roots of unity, and let `W` be a `B`-module that is finite, killed by `l`, fixed by `Q`, with
`z - 1` injective, and projective over `B/Q` in Higman's sense. Then `W` has exactly
`#W ^ (#(ι × G/B) + 1)` trivialised cocycles. -/
private lemma New.IsLargeLevel.SplitPlaces.card_trivialised_restrict_of_isHigmanProjective
    {K R ι : Type} [Field K] [EmbeddedNumberField K] [CommRing R] {l N : ℕ} [Fact l.Prime]
    [NeZero N] {I : Set Gal(Ω/K)} [Fintype ι] [IsTotallyComplex K]
    {U : OpenNormalSubgroup Gal(Ω/K)} (S : SplitPlaces l N I U ι) {z : Gal(Ω/K)}
    (hz : (cyclotomicCharMod Ω l z).1 = (1 : ℕ))
    (hfix : ∀ x : DiscreteUnits Ω, l • x ∈ fixedSUnits N U → (∀ i : ι, unitsRep (S.φ i) x = x) →
      ∀ g : Gal(Ω/K), unitsRep g (l • x) = l • x →
        unitsRep g (unitsRep z x - 1 • x) = unitsRep z x - 1 • x)
    {B : OpenSubgroup Gal(Ω/K)} (hUB : U.toOpenSubgroup.toSubgroup ≤ B) (hzB : z ∈ B)
    (Q : OpenNormalSubgroup B.toSubgroup) (hUQ : U.toOpenSubgroup.toSubgroup.subgroupOf B ≤ Q)
    (hQ : ∀ g ∈ Q, cyclotomicCharMod Ω l g = 1) {W : DiscreteModule R B.toSubgroup}
    (hW : W.FiniteKilledFixedInj l Q ⟨z, hzB⟩ 1)
    (hhig : W.IsHigmanProjective Q.toOpenSubgroup.toSubgroup) :
    W.HasFewCocycles (PlaceAboveLevel N) ((↑) ⁻¹' I) (Fintype.card (ι × Gal(Ω/K) ⧸ B.1) + 1) ∧
      Nat.card (W.trivialisedCocycles (PlaceAboveLevel N) ((↑) ⁻¹' I)) =
        Nat.card W ^ (Fintype.card (ι × Gal(Ω/K) ⧸ B.1) + 1) := by
  classical
  -- With `1` among the coset representatives, the `S.φ i` are among the Frobenii over `B`.
  let S' := S.liftToSubgroup B Q hUB hUQ hQ (update out ⟦1⟧ 1) (by clear * -; grind [out_eq'])
  refine (S'.card_trivialised_of_isHigmanProjective hW hhig fun x hx hφ g ↦ ?_).imp_right
    fun heq ↦ heq hz (isTotallyComplex_of_algebra K _)
  -- `using!`: the Frobenius of `S'` at `(i, ⟦1⟧)` is `S.φ i` only after unfolding `liftToSubgroup`.
  have hφ_S (i : ι) : unitsRep (S.φ i) x = x := by simpa [S', liftToSubgroup] using! hφ ⟨i, ⟦1⟧⟩
  -- `l • x` is an `N`-unit fixed by `U`, as it is one fixed by `Q ≥ U`.
  have hx_U : l • x ∈ fixedSUnits N U := ⟨hx.1, fun u ↦ hx.2 ⟨⟨u, hUB u.2⟩, hUQ u.2⟩⟩
  exact hfix x hx_U hφ_S g (hx.2 g)

/-- The exact count for modules killed by `l`. Let `S`, `z` and `hfix` be as in
`card_trivialised_restrict_of_isHigmanProjective`, with `z` central modulo `U` and fixing the `l`-th
roots of unity, and let `K` be totally complex. Suppose that for every short exact sequence
`W₁ → W → W₂` of `G`-modules, with `W` finite, killed by `l`, fixed by `U` and with `z - 1`
injective, the induced map on trivialised cocycles of `W` and `W₂` is onto. Then every such `W` has
exactly `#W ^ (#ι + 1)` trivialised cocycles: the ratio of the two counts is multiplicative, and `1`
on projective modules. -/
private lemma New.IsLargeLevel.SplitPlaces.card_trivialised_eq_of_map_range_eq_top
    {K R ι : Type} [Field K] [EmbeddedNumberField K] [CommRing R] {l N : ℕ} [Fact l.Prime]
    [NeZero N] {I : Set Gal(Ω/K)} [Fintype ι] [IsTotallyComplex K]
    {U : OpenNormalSubgroup Gal(Ω/K)} (S : SplitPlaces l N I U ι) {z : Gal(Ω/K)}
    (hz : (cyclotomicCharMod Ω l z).1 = (1 : ℕ))
    (hcentral : ∀ g : Gal(Ω/K), ⁅z, g⁆ ∈ U)
    (hfix : ∀ x : DiscreteUnits Ω, l • x ∈ fixedSUnits N U → (∀ i : ι, unitsRep (S.φ i) x = x) →
      ∀ g : Gal(Ω/K), unitsRep g (l • x) = l • x →
        unitsRep g (unitsRep z x - 1 • x) = unitsRep z x - 1 • x)
    (hlift : ∀ {W₁ W W₂ : DiscreteModule R Gal(Ω/K)} {j : W₁.Hom W} {π : W.Hom W₂},
      IsShortExact j π → W.FiniteKilledFixedInj l U z 1 → (map (PlaceAboveLevel N) I π).range = ⊤)
    (W : DiscreteModule R Gal(Ω/K)) (hW : W.FiniteKilledFixedInj l U z 1) :
    Nat.card (W.trivialisedCocycles (PlaceAboveLevel N) I) = Nat.card W ^ (Fintype.card ι + 1) := by
  let ratio (X : DiscreteModule R Gal(Ω/K)) (_ : X.FiniteKilledFixedInj l U z 1) : ℚ≥0 :=
    Nat.card (X.trivialisedCocycles (PlaceAboveLevel N) I) / (Nat.card X ^ (Fintype.card ι + 1) : ℕ)
  have hone : ratio W hW = 1 := by
    refine IsMultiplicative.eq_one_of_eq_one_on_isHigmanProjective R l U ratio hcentral
      (fun hses hX ↦ ?_)
      hW fun hX hhig ↦ ?_
    · simp [ratio, mul_pow, hses.card_eq_card_mul_card, mul_div_mul_comm,
      card_eq_of_isShortExact _ I hses,
        hlift hses hX]
    · -- The count for a projective module is exact.
      have hX_finite : Finite _ := hX.finite
      simp [ratio, S.card_trivialisedCocycles_eq_of_isHigmanProjective hX hhig
        (fun x hx hφ g ↦ hfix x hx hφ g (hx.2 g)) hz]
  exact cast_injective (eq_of_div_eq_one hone)

/-- A trivialised cocycle `p = (trivialisation, cocycle)` is determined by its trivialisation. -/
private lemma New.DiscreteModule.trivialisedCocycles.fst_injective {R G X : Type} [CommRing R]
    [Group G] [TopologicalSpace G] [MulAction G X] [Nonempty X] {I : Set G}
    (W : DiscreteModule R G) :
    Injective fun p : W.trivialisedCocycles X I ↦ (p : (X → W) × (G → W)).fst := by
  rintro ⟨⟨f, c⟩, -, h_triv, -⟩ ⟨⟨f', c'⟩, -, h_triv', -⟩ (rfl : f = f')
  obtain ⟨y⟩ : Nonempty X := inferInstance
  have h_cocycle (g : G) : c g = c' g := add_left_cancel ((h_triv g y).symm.trans (h_triv' g y))
  exact Subtype.ext (Prod.ext rfl (funext h_cocycle))

/-- Lifting from an upper bound that projective modules attain. Let `l` be prime, `U` open normal in
the compact group `G`, and `z` central modulo `U`. Consider the modules `F` that are finite, killed
by `l`, fixed by `U` and on which `ρ z - 1` is injective. Suppose each has between one and `#F ^ k`
trivialised cocycles, and those projective over `G ⧸ U` in Higman's sense have at least `#F ^ k`.
Then along a short exact sequence `W₁ → W → W₂` with `W` such a module, every trivialised cocycle
of `W₂` lifts to `W`. -/
private lemma New.DiscreteModule.trivialisedCocycles.map_range_eq_top_of_hasFewCocycles
    {R G X : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MulAction G X] {I : Set G} {l k : ℕ} [Fact l.Prime]
    {U : OpenNormalSubgroup G} {z : G} (hcentral : ∀ g : G, ⁅z, g⁆ ∈ U)
    (h_upper : ∀ F : DiscreteModule R G,
      F.FiniteKilledFixedInj l U z 1 → F.HasFewCocycles X I k)
    (h_proj : ∀ F : DiscreteModule R G, F.FiniteKilledFixedInj l U z 1 → F.IsHigmanProjective U →
      Nat.card F ^ k ≤ Nat.card (F.trivialisedCocycles X I))
    {W₁ W W₂ : DiscreteModule R G} {j : W₁.Hom W} {π : W.Hom W₂} (hses : IsShortExact j π)
    (hW : W.FiniteKilledFixedInj l U z 1) :
    (map X I π).range = ⊤ := by
  classical
  -- If the count is maximal for `B`, cocycles lift and the count is maximal for the submodule `A`.
  have h_squeeze {A B C : DiscreteModule R G} {u : A.Hom B} {v : B.Hom C}
      (h_exact : IsShortExact u v) (hB : B.FiniteKilledFixedInj l U z 1)
      (h_max : Nat.card B ^ k ≤ Nat.card (B.trivialisedCocycles X I)) :
      (map X I v).range = ⊤ ∧ Nat.card A ^ k ≤ Nat.card (A.trivialisedCocycles X I) :=
    (hasFewCocycles_of_isShortExact h_exact (h_upper A (hB.left_of_isShortExact h_exact))
      (h_upper C (hB.right_of_isShortExact h_exact))).right h_max
  -- Embed `W` by constants in the module `F` of functions on a quotient of `G ⧸ U` that
  -- `exists_diagonalPermModule_isHigmanProjective` provides; it is projective, as the indicator of
  -- `1` has trace one.
  obtain ⟨Z, hZ_normal, hperm⟩ := exists_diagonalPermModule_isHigmanProjective R l U hcentral
  let Y : Type := (G ⧸ (U : Subgroup G)) ⧸ Z
  let F : DiscreteModule R G := W.diagonalPermModule U Z Y
  have hF : F.FiniteKilledFixedInj l U z 1 := (hperm hW Y).left
  have hF_proj : F.IsHigmanProjective U :=
    (hperm hW Y).right (Pi.single 1 1) fun y ↦ by simp [inv_mul_eq_one, Pi.single_apply]
  let const : W.Hom F := ⟨LinearMap.const, fun _ ↦ rfl⟩
  obtain ⟨-, -, h_mkQ_surj⟩ := isShortExact_submodule _ _ const.range.2
  have hW_max : Nat.card W ^ k ≤ Nat.card (W.trivialisedCocycles X I) :=
    (h_squeeze (u := const) ⟨const_injective, const.1.exact_map_mkQ_range, h_mkQ_surj⟩ hF
      (h_proj F hF hF_proj)).right
  exact (h_squeeze hses hW hW_max).left

/-- Lifting by corestriction. Let `B` be an open subgroup of finite index prime to `l` that contains
the conjugation-stable set `I`. Let `π : W → W₂` be onto, with `I` fixing `W` and `l` killing `W₂`,
and let `πB` be `π` as a map of `B`-modules. If every trivialised cocycle of `W₂` for `B` lifts to
`W`, then so does every trivialised cocycle of `W₂` for `G`. -/
private lemma New.DiscreteModule.trivialisedCocycles.map_range_eq_top_of_restrictTo
    {R G X : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MulAction G X] [Nonempty X] {I : Set G} {B : OpenSubgroup G} [Fintype (G ⧸ B.toSubgroup)]
    (hI : ∀ g ∈ I, g ∈ B ∧ ∀ t : G, t⁻¹ * g * t ∈ I) {l : ℕ} (hcop : l.Coprime B.toSubgroup.index)
    {W W₂ : DiscreteModule R G} {π : W.Hom W₂} (hπ_surj : Surjective π)
    (h_fix : ∀ g ∈ I, ∀ m : W, W.ρ g m = m) (h_kill : ∀ u : W₂, l • u = 0)
    {πB : (W.restrictTo B).Hom (W₂.restrictTo B)} (hπB : ∀ m : W, πB m = π m)
    (h_lift : (map X ((↑) ⁻¹' I) πB).range = ⊤) :
    (map X I π).range = ⊤ := by
  refine (map X I π).range_eq_top.mpr fun ⟨⟨f, x⟩, hx_cont, hfx, hxI⟩ ↦ ?_
  -- Lift the restriction of `(f, x)` to a trivialised cocycle `(q, c)` of `W` for `B`.
  have h_res : (f, x ∘ (↑)) ∈ (W₂.restrictTo B).trivialisedCocycles X ((↑) ⁻¹' I) :=
    ⟨by fun_prop, fun g ↦ hfx g, fun g ↦ hxI g⟩
  obtain ⟨⟨⟨q, c⟩, hq⟩, hπq⟩ := (map X ((↑) ⁻¹' I) πB).range_eq_top.mp h_lift ⟨_, h_res⟩
  have hπq_apply (y : X) : π (q y) = f y :=
    (hπB (q y)).symm.trans (congrFun (congrArg Prod.fst (Subtype.ext_iff.mp hπq)) y)
  -- The corestriction of `(q, c)` maps to `i • f + ∑ x δ`, with `i` the index of `B`; remove the
  -- constant `∑ x δ = π m` and invert `i` modulo `l`.
  obtain ⟨m, hm⟩ : ∃ m : W, π m = ∑ δ : G ⧸ B.toSubgroup, x δ.out := hπ_surj _
  have h_const : (fun _ : X ↦ m, fun g : G ↦ W.ρ g m - m) ∈ W.trivialisedCocycles X I :=
    ⟨by fun_prop, by simp, fun g hg ↦ sub_eq_zero.mpr (h_fix g hg m)⟩
  obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) B.toSubgroup.index := hcop.isCoprime
  have h_invert (y : X) : b • B.toSubgroup.index • f y = f y := by
    simpa [add_smul, mul_smul, h_kill] using congrArg (· • f y) hab
  -- The trivialisation determines the cocycle, so only first components need be compared.
  refine ⟨⟨_, zsmul_mem (sub_mem (corestrict_mem B hI hq) h_const) b⟩, fst_injective W₂ ?_⟩
  simpa [trivialisedCocycles.map, π.isIntertwining, hπq_apply, hfx, hm, index, funext_iff,
    Finset.sum_add_distrib] using h_invert

/-- Let `P` be an open subgroup of index prime to `l` that contains all commutators `⁅z, g⁆`. Then
some open subgroup `B ≥ P` normalises `P` and contains `z`, and both the index of `P` in `B` and the
index of `B` are prime to `l`. -/
private lemma OpenSubgroup.exists_le_normal_mem_coprime_index {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (P : OpenSubgroup G) {l : ℕ}
    (hcop : l.Coprime P.toSubgroup.index) {z : G} (hcentral : ∀ g : G, ⁅z, g⁆ ∈ P) :
    ∃ B : OpenSubgroup G,
      P ≤ B ∧
      (P.toSubgroup.subgroupOf B).Normal ∧
      z ∈ B ∧
      l.Coprime (P.toSubgroup.subgroupOf B).index ∧
      l.Coprime B.toSubgroup.index := by
  -- Take the normaliser of `P`.
  let B : OpenSubgroup G := ⟨_, isOpen_mono P.toSubgroup.le_normalizer P.isOpen⟩
  have hz (g : G) : g ∈ P ↔ z * g * z⁻¹ ∈ P := by
    rw [show z * g * z⁻¹ = ⁅z, g⁆ * g by simp [commutatorElement_def],
      mul_mem_cancel_left (hcentral g)]
  have hcop_mul : l.Coprime (P.toSubgroup.relIndex B * B.toSubgroup.index) := by
    rwa [relIndex_mul_index le_normalizer]
  exact ⟨B, le_normalizer, normal_in_normalizer, hz, coprime_mul_iff_right.mp hcop_mul⟩

/-- Let `K` be totally complex and `r ≠ 0`, and let `s` be split places for `U` indexed by the
finite type `ι`, at levels `l ^ r` and `N`: distinct primes prime to `N` with Frobenii `s.φ i` in
`U`, where `I` is the union of the inertia groups above the other primes prime to `N`. Let `V` be
finite, killed by `l ^ r`, fixed by `U`, with `ρ(z) − 1` injective; let `z` have `l`-adic cyclotomic
character `1` and all `⁅z, g⁆` in `U`; and let `U` fix every `x ∈ Ωˣ` that the Frobenii `s.φ i` fix
and whose `l ^ r`-th power is an `N`-unit of the field of `U`. Then `V` has at least one and at most
`#V ^ (#ι + 1)` cocycles trivialised at the places above `N` and infinity (`PlaceAboveLevel N`) and
on `I`.

This is only an upper bound in the spirit of the Greenberg–Wiles formula: it counts trivialised
cocycles over a totally complex field, given such an element `z`, and its statement involves no dual
Selmer group. -/
theorem New.IsLargeLevel.SplitPlaces.hasFewCocycles_of_central {K R ι : Type} [Field K]
    [EmbeddedNumberField K] [CommRing R] {l r N : ℕ} [Fact l.Prime] [NeZero N] {I : Set Gal(Ω/K)}
    {V : DiscreteModule R Gal(Ω/K)} [Fintype ι] [IsTotallyComplex K]
    {U : OpenNormalSubgroup Gal(Ω/K)} (s : SplitPlaces (l ^ r) N I U ι) (hr : r ≠ 0) {z : Gal(Ω/K)}
    (hV : V.FiniteKilledFixedInj (l ^ r) U z 1) (hcyc : cyclotomicChar Ω l z = 1)
    (hcentral : ∀ g : Gal(Ω/K), ⁅z, g⁆ ∈ U) (hdetect : s.FrobeniiDetectRoots) :
    V.HasFewCocycles (PlaceAboveLevel N) I (Fintype.card ι + 1) := by
  classical
  -- Over a group `B` normalising an `l`-Sylow group `P/U` the count of trivialised cocycles of a
  -- module killed by `l` is squeezed to its maximum, so they lift along exact sequences, over `B`
  -- and by corestriction over the whole group. The count is then multiplicative, hence exact by
  -- `IsMultiplicative.eq_one_of_eq_one_on_isHigmanProjective`; finally `V` is filtered by modules
  -- killed by `l`.
  have hlr : l ∣ l ^ r := dvd_pow_self l hr
  have hz : (cyclotomicCharMod Ω l z).1 = (1 : ℕ) :=
    cyclotomicCharMod_eq_of_dvd hlr (by simp [cyclotomicCharMod_prime_pow_eq, hcyc])
  obtain ⟨P, hUP, hcop : l.Coprime P.1.index, hP : ∀ g ∈ P, ∃ k, g ^ l ^ k ∈ U⟩ :=
    exists_open_sylow l U
  have hfix (x : DiscreteUnits Ω) (hx : l • x ∈ fixedSUnits N U)
      (hφ : ∀ i : ι, unitsRep (s.φ i) x = x) :
      ∀ g : Gal(Ω/K), unitsRep g (l • x) = l • x →
        unitsRep g (unitsRep z x - 1 • x) = unitsRep z x - 1 • x :=
    s.fixes_sub_of_frobeniiDetectRoots hlr hdetect hz hcentral x hx hφ
  -- The split places serve for `l` in place of `l ^ r`.
  let S : SplitPlaces l N I U ι :=
    { s with
      dvd_level := hlr.trans s.dvd_level,
      cyclotomicCharMod_eq_one g hg := cyclotomicCharMod_eq_one_of_dvd hlr
        (s.cyclotomicCharMod_eq_one g hg) }
  -- An open subgroup `B` normalises `P` and contains `z`, whose commutators lie in `U ≤ P`.
  obtain ⟨B, hPB, hnormal, hzB, hcopP, hcopB⟩ : ∃ B : OpenSubgroup Gal(Ω/K), P ≤ B ∧
      (P.1.subgroupOf B).Normal ∧ z ∈ B ∧
      l.Coprime (P.1.subgroupOf B).index ∧ l.Coprime B.1.index :=
    P.exists_le_normal_mem_coprime_index hcop fun g ↦ hUP (hcentral g)
  have hUB : (U : Subgroup Gal(Ω/K)) ≤ B := hUP.trans hPB
  -- The data over the fixed field of `B`, where each split place has one place above it for each
  -- coset of `B`.
  let U' : OpenNormalSubgroup B.1 := ⟨U.1.comap _ (by fun_prop), U.2.subgroupOf B⟩
  let I' : Set B.1 := (↑) ⁻¹' I
  let z' : B.1 := ⟨z, hzB⟩
  let k := Fintype.card (ι × Gal(Ω/K) ⧸ B.1) + 1
  -- Upper bound: filter by `P`-invariants; modules fixed by `P` are projective over `B/P`, whose
  -- order is prime to `l`.
  have hupper : ∀ (W : DiscreteModule R B.1) (_ : W.FiniteKilledFixedInj l U' z' 1),
      W.HasFewCocycles (PlaceAboveLevel N) I' k := by
    refine devissage_induction l.pow_one (P.1.subgroupOf B) U' (fun g ↦ hP g) (fun W _ hW ↦ ?_)
      fun hses _ h₁ h₂ ↦ (hasFewCocycles_of_isShortExact hses h₁ h₂).1
    have h_finite_index : Finite (B.1 ⧸ P.1.subgroupOf B) :=
      (P.1.subgroupOf B).quotient_finite_of_isOpen P.2.preimage_val
    refine (S.card_trivialised_restrict_of_isHigmanProjective hz hfix hUB hzB
      ⟨⟨_, P.2.preimage_val⟩, hnormal⟩ (fun g hg ↦ hUP hg) (fun g hg ↦ ?_) hW
      (hW.isHigmanProjective_of_coprime hcopP)).1
    -- A power `g ^ l ^ i` lies in `U`, and `t ^ l ^ i = t` in `ZMod l`.
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (g : Gal(Ω/K)) ^ l ^ i ∈ U := hP g hg
    show cyclotomicCharMod Ω l (g : Gal(Ω/K)) = 1
    simpa [← Units.val_eq_one] using S.cyclotomicCharMod_eq_one _ hi
  -- Modules that are projective over `B/U` attain the bound.
  have hproj (F : DiscreteModule R B.1) (hF : F.FiniteKilledFixedInj l U' z' 1)
      (hhig : F.IsHigmanProjective U') :
      Nat.card F ^ k ≤ Nat.card (F.trivialisedCocycles (PlaceAboveLevel N) I') := by
    have h_card : Nat.card (F.trivialisedCocycles (PlaceAboveLevel N) I') = Nat.card F ^ k :=
      (S.card_trivialised_restrict_of_isHigmanProjective hz hfix hUB hzB U' le_rfl
        (fun g ↦ S.cyclotomicCharMod_eq_one g) hF hhig).right
    exact h_card.ge
  -- So cocycles lift over `B`, hence by corestriction over the whole group.
  have hlift {W₁ W W₂ : DiscreteModule R Gal(Ω/K)} {j : W₁.Hom W} {π : W.Hom W₂}
      (hses : IsShortExact j π) (hW : W.FiniteKilledFixedInj l U z 1) :
      (map (PlaceAboveLevel N) I π).range = ⊤ := by
    have hWB : (W.restrictTo B).FiniteKilledFixedInj l U' z' 1 :=
      ⟨hW.finite, hW.nsmul_eq_zero, fun g hg ↦ hW.trivialOn g hg, hW.injective⟩
    have hI (g : Gal(Ω/K)) (hg : g ∈ I) : g ∈ B ∧ ∀ t : Gal(Ω/K), t⁻¹ * g * t ∈ I :=
      (s.mem_and_conj_mem g hg).imp_left fun hgU ↦ hUB hgU
    let πB : (W.restrictTo B).Hom (W₂.restrictTo B) := ⟨π.toLinearMap, fun g ↦ π.isIntertwining' g⟩
    have hliftB : (map (PlaceAboveLevel N) I' πB).range = ⊤ :=
      map_range_eq_top_of_hasFewCocycles (U := U') (z := z') (fun g ↦ hcentral g) hupper hproj
        (hses.restrictAlong _) hWB
    -- Corestriction from `B` to the whole group.
    have hsurj : Surjective π := hses.right.right
    have hI_fix (g : Gal(Ω/K)) (hg : g ∈ I) (m : W) : W.ρ g m = m :=
      hW.trivialOn g (s.mem_and_conj_mem g hg).left m
    have hkill : ∀ u : W₂, l • u = 0 := (hW.right_of_isShortExact hses).nsmul_eq_zero
    have hπB (m : W) : πB m = π m := rfl
    exact map_range_eq_top_of_restrictTo hI hcopB hsurj hI_fix hkill hπB hliftB
  -- Filter `V` by modules killed by `l`; for those the count is exact.
  refine devissage_induction rfl U U (fun g hg ↦ ⟨0, by simpa⟩) (fun W hW hW' ↦ ?_)
    (fun hses _ h₁ h₂ ↦ (hasFewCocycles_of_isShortExact hses h₁ h₂).1) V hV
  have h_count : Nat.card (W.trivialisedCocycles (PlaceAboveLevel N) I) =
      Nat.card W ^ (Fintype.card ι + 1) :=
    S.card_trivialised_eq_of_map_range_eq_top hz hcentral hfix hlift W hW'
  exact mem_of_eq_of_mem h_count ⟨by simp [hW.finite], le_rfl⟩

end GreenbergWilesBound
