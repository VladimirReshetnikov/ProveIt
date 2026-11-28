import Lib.General.Measure.IdempotentKernel

/-!
# Quotient measures via cutoffs: unfolding, covolume, unimodularity, periodic means

A group `H` with a measure `ν` acts on a measure space `(X, μ)`. Integration over `H \ X` is done on
`X` itself. A cutoff (`New.IsCutoff ν β`) is a measurable `β : X → [0, ∞]` with
`∫ β (h • x) dν(h) = 1` for every `x`. For a discrete subgroup `Γ` of a group `G` with counting
measure, and a Haar measure `μ` on `G`, `Γ.quotMeasure μ` integrates over `Γ \ G`, and its total
mass is the covolume of `Γ`.

## Main definitions and results

* `New.orbitMeasure`: the measure `β μ` on `X`, for the chosen weight `β = New.chosenCutoff ν`. It
  is meant for `H`-invariant integrands, and for actions where a cutoff exists (`New.HasCutoff`);
  then `β` is a cutoff (`New.isCutoff_chosenCutoff`).
* `New.IsCutoff.measurePreserving`, `New.measurePreserving_orbitMeasure`: the map `(x, h) ↦ h • x`
  carries `(β μ) × ν` to `μ`; the other results on unfolding follow from this and Fubini's theorem.
* `New.identDistrib_orbitMeasure_of_unfold`, `New.identDistrib_orbitMeasure`: invariant functions
  have the same distribution for every measure that unfolds to `μ`. So the choice of cutoff does not
  matter when `ν` is inversion invariant and `μ` is invariant, both s-finite.
* `New.integral_quotMeasure_tsum`: `∫_{Γ\G} ∑_γ f(γ g) = ∫_G f`.
* `New.isMulRightInvariant_of_finite_covolume`: a group with a discrete subgroup of finite covolume
  is unimodular.
* `New.quotMean_tsum_eq_integral`: the mean of `x ↦ ∑ γ, F (γ + x)` is `∫ F dμ` divided by the
  covolume.

## Relation to the literature

Known result: Invariant integration on a quotient (Weil's formula), unfolding and unimodularity.
Here the quotient integral is integration against a measurable weight of total mass one on each
orbit, so no orbit space or section is needed to define it; existence is proved for proper actions
and for discrete subgroups. Source: O. Kallenberg, Invariant measures and disintegrations with
applications to Palm and related kernels, Probab. Theory Related Fields 139 (2007) 285-310 (as
cited in D. Gentner, G. Last, Math. Z. 267 (2011), §2); for the classical form, N. Bourbaki,
Intégration VII, 1963.
-/

/-!
## Cutoff weights and the quotient measure

* `Subgroup.IsCocompact`: every element of `G` has a translate by the subgroup in a fixed compact
  set.

The definitions have additive versions, except `Subgroup.FixesLeft`.
-/

section QuotientMeasureDefs

open MeasureTheory Measure

variable {H X G : Type*} [MeasurableSpace H] [MeasurableSpace X] [SMul H X] (ν : Measure H)
  (μ : Measure X) [Group G] (N : Subgroup G)

/-- The subgroup N of G is cocompact: there is a compact C ⊂ G such that every g has a translate
γg in C with γ ∈ N. -/
@[to_additive]
abbrev Subgroup.IsCocompact [TopologicalSpace G] : Prop :=
  ∃ C : Set G, IsCompact C ∧ ∀ g : G, ∃ γ ∈ N, γ * g ∈ C

/-- The function F on G is left invariant under the subgroup N: F(γg) = F(g) for all γ ∈ N and g
∈ G. -/
@[simp]
abbrev Subgroup.FixesLeft {W : Sort*} (F : G → W) : Prop := ∀ γ ∈ N, ∀ g : G, F (γ * g) = F g

namespace New

/-- The property that β: X → [0, ∞] is measurable and ∫_H β(hx) dν(h) = 1 for every x in X. -/
@[to_additive IsAddCutoff]
def IsCutoff (β : X → ENNReal) : Prop := Measurable β ∧ ∀ x : X, ∫⁻ h : H, β (h • x) ∂ν = 1

/-- A chosen weight for the action of `H`, with measure `ν`, on `X`. It is a cutoff when the action
has one (`New.isCutoff_chosenCutoff`); otherwise it is an unspecified function. -/
@[to_additive chosenAddCutoff]
noncomputable abbrev chosenCutoff : X → ENNReal := Classical.epsilon (IsCutoff ν)

/-- The measure βμ on X for the weight β = `New.chosenCutoff ν`. When a cutoff exists
(`New.HasCutoff`), ν is inversion invariant and μ is H-invariant, both s-finite, integrating an
H-invariant function against it gives the integral over H\X, for every choice of cutoff. -/
@[to_additive addOrbitMeasure]
noncomputable abbrev orbitMeasure : Measure X := μ.withDensity (chosenCutoff ν)

/-- The hypothesis that the action of H, with measure ν, on X admits a cutoff: a measurable
weight with integral one over each orbit. -/
@[to_additive HasAddCutoff]
abbrev HasCutoff (X : Type*) [MeasurableSpace X] [SMul H X] : Prop :=
  Fact (∃ β : X → ENNReal, IsCutoff (X := X) ν β)

/-- If the action of `H`, with measure `ν`, on `X` has a cutoff, the chosen weight is a cutoff. -/
@[to_additive isAddCutoff_chosenAddCutoff]
lemma isCutoff_chosenCutoff [h_cutoff : HasCutoff ν X] :
    IsCutoff ν (chosenCutoff ν : X → ENNReal) :=
  Classical.epsilon_spec h_cutoff.out

/-- If the action has a cutoff, the chosen weight is measurable. -/
@[to_additive measurable_chosenAddCutoff]
lemma measurable_chosenCutoff [HasCutoff ν X] : Measurable (chosenCutoff ν : X → ENNReal) :=
  (isCutoff_chosenCutoff ν).1

/-- If the action has a cutoff, the chosen weight has integral one over each orbit. -/
@[to_additive lintegral_chosenAddCutoff_vadd]
lemma lintegral_chosenCutoff_smul [HasCutoff ν X] (x : X) :
    ∫⁻ h : H, chosenCutoff ν (h • x) ∂ν = 1 :=
  (isCutoff_chosenCutoff ν).2 x

/-- Shortcut: the `MulAction` instance of a subgroup `N` on its ambient group `G`. -/
@[to_additive]
instance (priority := high) mulActionSubgroupSelf : MulAction N G := inferInstance

/-- Shortcut: the `SMul` instance of a subgroup `N` on its ambient group `G`. -/
@[to_additive]
instance (priority := high) smulSubgroupSelf : SMul N G := inferInstance

/-- The measure on G that computes integrals over N\G, when N with counting measure has a cutoff
(for example when N is discrete) and μ is invariant under N. It is μ weighted by a cutoff chosen for
the action of N, with counting measure, on G. By default μ is `volume`. -/
@[to_additive]
noncomputable abbrev _root_.Subgroup.quotMeasure [MeasurableSpace G]
    (μ : Measure G := by volume_tac) : Measure G :=
  orbitMeasure (@count N _) μ

end New

end QuotientMeasureDefs

/-!
## Independence of the cutoff and unfolding

* `New.lintegral_orbitMeasure_lintegral`: unfolding for lower integrals,
  `∫_{H\X} ∫_H f(h • x) = ∫_X f`.
-/

section QuotientMeasure

open MeasureTheory Measure ProbabilityTheory

variable {H X W Y : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace W]
  [MeasurableSpace Y] [NormedAddCommGroup W] [NormedSpace ℝ W] [BorelSpace W]
  {F : X → Y} {f : X → W}

namespace New

to_additive_name_hint Quot AddQuot

/-- A measure that unfolds to `μ` computes the quotient measure. Suppose that the action of `H` on
`X` has a cutoff for `ν` (a weight with integral one over each orbit), let `σ` carry `ρ` to `ν`, and
let `(z, l) ↦ σ l • T z` carry `m × ρ` to `μ`, with `T` measurable. Then a measurable `H`-invariant
function `F` has the same distribution under `New.orbitMeasure ν μ` (`μ` weighted by a chosen
cutoff) as `F ∘ T` under `m`. -/
@[to_additive identDistrib_addOrbitMeasure_of_unfold]
lemma identDistrib_orbitMeasure_of_unfold [SMul H X] [MeasurableSMul₂ H X] {ν : Measure H}
    {μ : Measure X} {Z L : Type*} [MeasurableSpace Z] [MeasurableSpace L] {ρ : Measure L}
    [SFinite ρ] [c : HasCutoff ν X] {σ : L → H} (hσ_pres : MeasurePreserving σ ρ ν) {T : Z → X}
    {m : Measure Z} [SFinite m]
    (h_unfold : MeasurePreserving (fun p : Z × L ↦ σ p.2 • T p.1) (m.prod ρ) μ) (hF : Measurable F)
    (hT : Measurable T) (h_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    IdentDistrib F (F ∘ T) (orbitMeasure ν μ) m := by
  -- Test both laws against a measurable `f`. Unfold `μ` along `(z, l) ↦ σ l • T z`: as `F` is
  -- invariant, the integral over `l` is that of the chosen cutoff `β` over an orbit, which is `1`.
  let β : X → ENNReal := chosenCutoff ν
  have ⟨hβ_meas, hβ_one⟩ : IsCutoff ν β := isCutoff_chosenCutoff ν
  have hσ : Measurable σ := hσ_pres.measurable
  refine ⟨by fun_prop, by fun_prop, ext_of_lintegral _ fun f hf ↦ ?_⟩
  have h_orbit (x : X) : ∫⁻ l, β (σ l • x) ∂ρ = 1 := by
    rw [← hβ_one x, ← hσ_pres.lintegral_comp (by fun_prop)]
  calc
    _ = ∫⁻ x, β x * f (F x) ∂μ := by
      rw [lintegral_map hf hF]
      exact lintegral_withDensity_eq_lintegral_mul _ hβ_meas (by fun_prop)
    _ = ∫⁻ p, β (σ p.2 • T p.1) * f (F (T p.1)) ∂m.prod ρ := by
      simp (disch := fun_prop) [← h_unfold.lintegral_comp, h_inv]
    _ = ∫⁻ z, ∫⁻ l, β (σ l • T z) * f (F (T z)) ∂ρ ∂m := lintegral_prod _ (by fun_prop)
    _ = ∫⁻ z, f (F (T z)) ∂m := by simp (disch := fun_prop) [lintegral_mul_const, h_orbit]
    _ = ∫⁻ y, f y ∂m.map (F ∘ T) := (lintegral_map hf (hF.comp hT)).symm

variable [Group H] [MulAction H X] [MeasurableInv H] [MeasurableSMul₂ H X]
  {ν : Measure H} [SFinite (α := H) ν]
  {μ : Measure X} [SFinite μ] [SMulInvariantMeasure H X μ] {β : X → ENNReal}

@[to_additive]
instance {S : Subgroup H} : MeasurableSMul₂ S X := ⟨.smul (by fun_prop) measurable_snd⟩

/-! ### Unfolding with a given cutoff -/

/-- Let a group H act measurably on X, ν an s-finite measure on H, μ an s-finite H-invariant
measure on X, β : X → [0,∞] measurable. Then (x,h) ↦ hx pushes (βμ) × ν forward to the measure
with density x ↦ ∫ β(h⁻¹x) dν(h) with respect to μ. -/
@[to_additive]
lemma measurePreserving_smul_prod (hβ : Measurable β) :
    MeasurePreserving (fun p : X × H ↦ p.2 • p.1) ((μ.withDensity β).prod ν)
      (μ.withDensity fun x : X ↦ ∫⁻ h : H, β (h • x) ∂ν.inv) := by
  have h_smul : Measurable fun p : X × H ↦ p.2 • p.1 := by fun_prop
  refine ⟨h_smul, ext fun s hs ↦ ?_⟩
  -- Both sides are integrals over `h`; for fixed `h` substitute `x ↦ h • x`, which preserves `μ`.
  have h_slice (h : H) : μ.withDensity β ((h • ·) ⁻¹' s) = ∫⁻ x in s, β (h⁻¹ • x) ∂μ := by
    rw [← (measurePreserving_smul h μ).setLIntegral_comp_preimage hs (by fun_prop)]
    simp (disch := measurability)
  rw [map_apply h_smul hs, prod_apply_symm (h_smul hs), withDensity_apply _ hs]
  calc
    _ = ∫⁻ h, ∫⁻ x in s, β (h⁻¹ • x) ∂μ ∂ν := lintegral_congr h_slice
    _ = ∫⁻ x in s, ∫⁻ h, β (h⁻¹ • x) ∂ν ∂μ := lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ x in s, ∫⁻ h, β (h • x) ∂ν.inv ∂μ := by
      simp (disch := fun_prop) [Measure.inv, lintegral_map]

/-- Unfolding: for an inversion invariant s-finite measure `ν` on `H`, an s-finite invariant measure
`μ` on `X` and a cutoff `β`, the map `(x, h) ↦ h • x` carries `(β μ) × ν` to `μ`. -/
@[to_additive]
lemma IsCutoff.measurePreserving [IsInvInvariant ν] (hβ : IsCutoff ν β) :
    MeasurePreserving (fun p : X × H ↦ p.2 • p.1) ((μ.withDensity β).prod ν) μ := by
  -- The density in `measurePreserving_smul_prod` is `1`: `ν` is invariant under inversion and the
  -- integral of `β` over each orbit is `1`.
  have ⟨hβ_meas, hβ_one⟩ := hβ
  simpa [hβ_one] using measurePreserving_smul_prod (ν := ν) (μ := μ) hβ_meas

/-- Independence of the cutoff. Let `ν` be an s-finite, inversion-invariant measure on the group `H`
and `μ` an s-finite, `H`-invariant measure on `X`. If `β` is a cutoff (measurable, with
`∫⁻ h, β (h • x) ∂ν = 1` for every `x`), then every measurable `H`-invariant `F` has the same
distribution under `μ.withDensity β` as under `orbitMeasure ν μ`, which is `μ` weighted by a fixed
chosen cutoff and stands in on `X` for the quotient measure on `H \ X`. -/
lemma identDistrib_orbitMeasure [IsInvInvariant ν] (hβ : IsCutoff ν β) (hF : Measurable F)
    (h_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    IdentDistrib F F (orbitMeasure ν μ) (μ.withDensity β) :=
  identDistrib_orbitMeasure_of_unfold (c := ⟨β, hβ⟩) (.id ν) hβ.measurePreserving hF measurable_id
    h_inv

/-- A cutoff `β` for an inversion invariant s-finite measure `ν` on `H` is finite almost everywhere
for every s-finite `H`-invariant measure `μ` on `X`. -/
lemma IsCutoff.ae_cutoff_lt_top [IsInvInvariant ν] (hβ : IsCutoff ν β) :
    ∀ᵐ x : X ∂μ, β x < ⊤ := by
  -- Unfold `μ`: the integral of `β` over each orbit is finite, so `β` is finite almost everywhere.
  have ⟨h_meas, h_one⟩ := hβ
  have h_orbit (x : X) : ∀ᵐ h : H ∂ν, β (h • x) < ⊤ :=
    ae_lt_top (by fun_prop) (by simp [h_one])
  rw [← hβ.measurePreserving.hasLaw.ae_iff (by measurability)]
  have h_prod : ∀ᵐ p : X × H ∂(μ.withDensity β).prod ν, β (p.2 • p.1) < ⊤ := by
    simp (disch := measurability) [ae_prod_iff_ae_ae, h_orbit]
  exact h_prod

/-- Let a group `H` act measurably on `X`, with `ν` an s-finite, inversion-invariant measure on `H`
and `μ` an s-finite, `H`-invariant measure on `X`. Let `β` be a cutoff, meaning a measurable
`β : X → [0, ∞]` with `∫ β (h • x) dν(h) = 1` for every `x`. Then for any measurable, `H`-invariant
`f` with values in a real normed space, the integral of `f` against the quotient measure
`orbitMeasure ν μ` (the measure `μ` weighted by a chosen cutoff) equals `∫ β(y) • f(y) dμ`. -/
lemma IsCutoff.integral_orbitMeasure [IsInvInvariant ν] (hβ : IsCutoff ν β)
    (h_inv : ∀ (h : H) (y : X), f (h • y) = f y) (hf : Measurable f := by fun_prop) :
    ∫ y : X, f y ∂orbitMeasure ν μ = ∫ y : X, (β y).toReal • f y ∂μ := by
  have ⟨hβ_meas, _⟩ := hβ
  rw [(identDistrib_orbitMeasure hβ hf h_inv).integral_eq,
    integral_withDensity_eq_integral_toReal_smul hβ_meas hβ.ae_cutoff_lt_top]

/-! ### Unfolding with the chosen cutoff -/

/-- Unfolding for the quotient measure (Weil's formula): let `ν` be an s-finite, inversion-invariant
measure on `H`, and `μ` an s-finite, `H`-invariant measure on `X`. Suppose the action of `H` on `X`
has a cutoff, meaning a measurable weight on `X` whose `ν`-integral over each orbit is one. Then
`(x, h) ↦ h • x` carries `orbitMeasure ν μ × ν` to `μ`. Here `orbitMeasure ν μ` is `μ` weighted by a
chosen cutoff, a measure on `X` standing in for the quotient measure on `H \ X`. -/
@[to_additive measurePreserving_addOrbitMeasure]
lemma measurePreserving_orbitMeasure [IsInvInvariant ν] [c : HasCutoff ν X] :
    MeasurePreserving (fun p : X × H ↦ p.2 • p.1) ((orbitMeasure ν μ).prod ν) μ :=
  (isCutoff_chosenCutoff ν).measurePreserving

/-- Let the action of H on X have a cutoff for the inversion invariant measure ν and let the
invariant measure μ be positive on nonempty open sets. An H-stable property that holds almost
everywhere for the quotient measure `New.orbitMeasure` holds on a dense subset of X. -/
lemma dense_of_ae_orbitMeasure [IsInvInvariant ν] [c : HasCutoff ν X] [TopologicalSpace X]
    [BorelSpace X] [μ.IsOpenPosMeasure]
    {p : X → Prop} (h_stable : ∀ (h : H) (x : X), p x → p (h • x))
    (h_ae : ∀ᵐ x : X ∂orbitMeasure ν μ, p x) :
    Dense {x : X | p x} := by
  -- The closure of `{x | p x}` is measurable, so unfolding shows that it has full measure for `μ`.
  have h_full : ∀ᵐ x ∂μ, x ∈ closure {x | p x} := by
    rw [← (measurePreserving_orbitMeasure (ν := ν)).hasLaw.ae_iff (by measurability)]
    have h_ae_prod : ∀ᵐ z : X × H ∂(orbitMeasure ν μ).prod ν, p z.1 :=
      quasiMeasurePreserving_fst.ae h_ae
    exact h_ae_prod.mono fun z hz ↦ subset_closure (h_stable z.2 z.1 hz)
  exact .of_closure (dense_of_ae h_full)

/-- Unfolding for `lintegral`: let `ν` be an s-finite, inversion-invariant measure on `H`, and `μ`
an s-finite, `H`-invariant measure on `X`. Suppose the action has a cutoff, meaning a measurable
weight on `X` whose `ν`-integral over each orbit is one. Then for measurable `f : X → [0, ∞]`,
integrating the orbit integral `x ↦ ∫⁻ h, f (h • x) ∂ν` against `orbitMeasure ν μ` gives
`∫⁻ x, f x ∂μ`. Here `orbitMeasure ν μ` is `μ` weighted by a chosen cutoff, a measure on `X`
standing in for the quotient measure on `H \ X`. -/
@[to_additive lintegral_addOrbitMeasure_lintegral]
lemma lintegral_orbitMeasure_lintegral [IsInvInvariant ν] [c : HasCutoff ν X] {f : X → ENNReal}
    (hf : Measurable f) :
    ∫⁻ x : X, ∫⁻ h : H, f (h • x) ∂ν ∂orbitMeasure ν μ = ∫⁻ x : X, f x ∂μ := by
  rw [← (measurePreserving_orbitMeasure (ν := ν)).lintegral_comp hf]
  exact lintegral_lintegral (by fun_prop)

end New

end QuotientMeasure

/-!
## Existence of cutoffs and unfolding a sum over a discrete subgroup

* `New.hasCutoff_of_proper`: a proper action on a σ-compact Hausdorff space has a cutoff.
* `New.hasCutoff_count`: a discrete subgroup `Γ` acting on `G` by left translation has a cutoff.
-/

section CutoffExistence

open MeasureTheory Measure Set ENNReal

namespace New

variable {I H X G : Type*} [MeasurableSpace I] [MeasurableSpace H] [Countable I] [Group G]
  [MeasurableSingletonClass I] [MeasurableSingletonClass H] [MeasurableSpace X] [TopologicalSpace G]

/-! ### Counting measure and sums of weights -/

lemma measurePreserving_count (e : I ≃ H) : MeasurePreserving e count count := by
  -- Push the sum of Dirac measures forward term by term and reindex it along `e`.
  refine ⟨.of_discrete, (Measure.map_sum .of_discrete).trans ?_⟩
  simp [count, ← Function.comp_def]

/-- The integral of a complex function against the counting measure of a countable set is its sum
(both are zero when the function is not summable). -/
lemma integral_count_eq_tsum (f : I → ℂ) : ∫ x : I, f x ∂count = ∑' x : I, f x := by
  simpa [count] using integral_sum_dirac (f := f) (c := 1) (x := id) fun _ ↦ ENNReal.one_ne_top

/-- If nonnegative weights `f x` in `[0, ∞]` sum to one, the sum of their multiples of a complex
number `z` is `z`. -/
lemma tsum_toReal_smul_of_tsum_eq_one {I : Type*} {f : I → ℝ≥0∞} (h : ∑' x : I, f x = 1) (z : ℂ) :
    ∑' x : I, (f x).toReal • z = z := by
  -- Each `f x` is finite, so `toReal` and the cast to `ℂ` commute with the sum.
  have h_fin (x : I) : f x ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top (by simp [h]) x
  have h_real : ∑' x : I, (f x).toReal = 1 := by
    rw [← tsum_toReal_eq h_fin, h, toReal_one]
  simp [tsum_mul_right, ← Complex.ofReal_tsum, h_real]

variable (Γ N : Subgroup G) [DiscreteTopology Γ] [Group H] [MulAction H X] [MeasurableMul H]
  [MeasurableSMul₂ H X]
  {ν : Measure H} [SFinite (α := H) ν] [IsMulRightInvariant ν] [TopologicalSpace H]

/-! ### Existence of cutoffs -/

open scoped Classical in
/-- A proper action of `H` on a σ-compact Hausdorff space `X` has a cutoff (a measurable weight with
integral one over each orbit) for every nonzero s-finite right-invariant measure `ν` on `H` that is
finite on compact sets. -/
@[to_additive hasAddCutoff_of_proper]
instance hasCutoff_of_proper [TopologicalSpace X] [c : SigmaCompactSpace X] [T2Space X]
    [OpensMeasurableSpace X] [ProperSMul H X] [IsFiniteMeasureOnCompacts ν] [NeZero ν] :
    HasCutoff ν X := by
  -- Exhaust `X` by compact sets `K n` and let `t n x = ν {h | h • x ∈ K n}`, finite by properness
  -- and constant on orbits. On the orbit of `x` take the least `n` with `t n x > 0`; the cutoff is
  -- `(t n x)⁻¹` on `K n` and `0` elsewhere.
  obtain ⟨K, hK, h_cover⟩ : ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ :=
    c.isSigmaCompact_univ
  let t (n : ℕ) (x : X) : ℝ≥0∞ := ν {h : H | h • x ∈ K n}
  have h_pos (x : X) : ∃ n : ℕ, 0 < t n x := by
    -- the sets `{h | h • x ∈ K n}` cover `H`, and `ν ≠ 0`
    by_contra! h_null
    have h_union : ⋃ n : ℕ, {h : H | h • x ∈ K n} = univ := by
      simp [← ofPred_exists, ← mem_iUnion, h_cover]
    have h_zero : ν univ = 0 := by
      rw [← h_union]
      exact measure_iUnion_null fun n ↦ nonpos_iff_eq_zero.1 (h_null n)
    exact NeZero.ne ν (measure_univ_eq_zero.1 h_zero)
  have h_fin (n : ℕ) (x : X) : t n x ≠ ∞ := by
    -- properness: the elements of `H` that move `x` into a compact set form a compact set
    have h_compact : IsCompact {h : H | h • x ∈ K n} := by
      simpa using ProperSMul.isCompact_setOfPred_inter_nonempty (G := H)
        (isCompact_singleton (x := x)) (hK n)
    exact h_compact.measure_ne_top
  have h_inv (n : ℕ) (x : X) (g : H) : t n (g • x) = t n x := by
    simpa [mul_smul] using measure_preimage_mul_right ν g {h | h • x ∈ K n}
  have h_meas (n : ℕ) : Measurable (t n) :=
    measurable_measure_prodMk_right (measurable_smul (hK n).measurableSet)
  let β (x : X) : ℝ≥0∞ := (K (Nat.find (h_pos x))).indicator (t (Nat.find (h_pos x)))⁻¹ x
  have hβ_meas : Measurable β :=
    .find (fun n ↦ (h_meas n).inv.indicator (hK n).measurableSet)
      (fun n ↦ h_meas n measurableSet_Ioi) h_pos
  refine ⟨β, hβ_meas, fun x ↦ ?_⟩
  set n : ℕ := Nat.find (h_pos x) with hn
  have hβ (h : H) : β (h • x) =
      ((fun g : H ↦ g • x) ⁻¹' K n).indicator (fun _ ↦ (t n x)⁻¹) h := by
    simp [β, indicator, h_inv, hn]
  simp only [hβ]
  rw [lintegral_indicator_const (measurable_smul_const x (hK n).measurableSet)]
  exact ENNReal.inv_mul_cancel (Nat.find_spec (h_pos x)).ne' (h_fin n x)

/-- On a discrete group `H` with measurable singletons, the counting measure is a Haar measure. -/
@[to_additive /-- On a discrete additive group with measurable singletons, the counting measure is
a Haar measure. -/]
instance [DiscreteTopology H] : IsHaarMeasure (count (α := H)) where
  lt_top_of_isCompact _ hK := count_apply_lt_top.2 hK.finite_of_discrete
  map_mul_left_eq_self := map_mul_left_eq_self count
  open_pos _ _ hU := count_ne_zero hU

/-! ### Cosets of a subgroup and subgroups of discrete subgroups -/

/-- For a subgroup `N` of `G`, the bijection `(G ⧸ N) × N ≃ G` sending `(q, u)` to `u * r⁻¹`,
where `r = q.out` is the chosen representative of the left coset `q`. The elements `r⁻¹`
represent the right cosets of `N`. -/
noncomputable abbrev cosetProdEquiv : (G ⧸ N) × N ≃ G where
  toFun := fun (q, u) ↦ u * q.out⁻¹
  invFun γ :=
    -- with `q` the coset of `γ⁻¹`, the element `γ * q.out` lies in `N`
    (↑γ⁻¹, ⟨γ⁻¹⁻¹ * (↑γ⁻¹ : G ⧸ N).out, QuotientGroup.eq.1 (↑γ⁻¹ : G ⧸ N).out_eq.symm⟩)
  left_inv x := by aesop
  right_inv x := by aesop

omit [TopologicalSpace G] in
lemma cosetProdEquiv_apply (q : G ⧸ N) (u : N) :
    cosetProdEquiv N (q, u) = (u : G) * q.out⁻¹ := rfl

omit [TopologicalSpace G] in
/-- The coset component of `γ` is the left coset of `γ⁻¹`. -/
lemma cosetProdEquiv_symm_apply_fst (γ : G) :
    ((cosetProdEquiv N).symm γ).1 = ((γ⁻¹ : G) : G ⧸ N) := rfl

omit [TopologicalSpace G] in
/-- The `N`-component of `γ` is `γ` times the chosen representative of the left coset of
`γ⁻¹`. -/
lemma cosetProdEquiv_symm_apply_snd (γ : G) :
    (((cosetProdEquiv N).symm γ).2 : G) = γ * ((γ⁻¹ : G) : G ⧸ N).out := by
  simp [cosetProdEquiv]

instance : DiscreteTopology (Γ.subgroupOf N) :=
  have h_cont : Continuous (Subtype.val : N → G) := continuous_subtype_val
  .preimage_of_continuous_injective Γ.carrier h_cont Subtype.val_injective

instance : DiscreteTopology ↥(Γ ⊓ N) :=
  .of_subset (s := (Γ : Set G)) (inferInstanceAs (DiscreteTopology Γ)) (by simp)

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  {S X : Type*} [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
  [SetLike S X] {N : S} {μ : Measure G} [IsHaarMeasure μ]

@[to_additive]
instance : Countable Γ := countable_of_Lindelof_of_discrete

instance : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _

/-- A closed set `N` in a locally compact space is locally compact, as a subspace. -/
instance locallyCompactSpace_of_isClosed [hN : IsClosed (X := X) N] : LocallyCompactSpace N :=
  hN.locallyCompactSpace
/-! ### Discrete subgroups of a locally compact group -/

/-- A discrete subgroup `Γ` of `G`, with counting measure, acting on `G` by left translation has a
cutoff. -/
@[to_additive addCutoff]
instance hasCutoff_count : HasCutoff (count (α := Γ)) G := inferInstance

/-- For the trivial subgroup of `G` and a left Haar measure `μ`, the quotient measure is `μ`. -/
lemma quotMeasure_bot : Subgroup.quotMeasure ⊥ μ = μ := by
  -- The constant `1` is a cutoff for the trivial group, and the quotient measure does not depend
  -- on the cutoff.
  have h_cut : IsCutoff (count : Measure (⊥ : Subgroup G)) (1 : G → ℝ≥0∞) :=
    ⟨measurable_one, by simp⟩
  have h_map : (Subgroup.quotMeasure ⊥ μ).map id = (μ.withDensity 1).map id :=
    (identDistrib_orbitMeasure h_cut measurable_id (by simp)).map_eq
  simpa using h_map

/-- For a discrete subgroup `Γ` of `G`, a left Haar measure `μ` and an integrable `f`, the sum
`g ↦ ∑' γ, f (γ * g)` is integrable for the quotient measure on `Γ \ G`. -/
lemma integrable_quotMeasure_tsum {f : G → ℂ} (hf : Integrable f μ) :
    Integrable (fun g : G ↦ ∑' γ : Γ, f (γ * g)) (Γ.quotMeasure μ) := by
  -- The map `(g, γ) ↦ γ * g` carries the product of the quotient measure with the counting
  -- measure to `μ`; integrals against the counting measure are sums.
  obtain ⟨h_prod, -⟩ :
      Integrable (fun p : G × Γ ↦ f (p.2 * p.1)) ((Γ.quotMeasure μ).prod count) ∧
      ∫ g : G, ∫ γ : Γ, f (γ * g) ∂count ∂Γ.quotMeasure μ = ∫ g : G, f g ∂μ :=
    (measurePreserving_orbitMeasure (ν := (count : Measure Γ))).fubini hf
  simpa only [integral_count_eq_tsum] using h_prod.integral_prod_left

/-- For a discrete subgroup `Γ` of `G`, a left Haar measure `μ` and an integrable `f`, the
integral of `g ↦ ∑' γ, f (γ * g)` over `Γ \ G` is `∫ f dμ`. -/
lemma integral_quotMeasure_tsum_eq {f : G → ℂ} (hf : Integrable f μ) :
    ∫ g : G, ∑' γ : Γ, f (γ * g) ∂Γ.quotMeasure μ = ∫ g : G, f g ∂μ := by
  -- Fubini along `(g, γ) ↦ γ * g`.
  obtain ⟨-, h_fubini⟩ :
      Integrable (fun p : G × Γ ↦ f (p.2 * p.1)) ((Γ.quotMeasure μ).prod count) ∧
      ∫ g : G, ∫ γ : Γ, f (γ * g) ∂count ∂Γ.quotMeasure μ = ∫ g : G, f g ∂μ :=
    (measurePreserving_orbitMeasure (ν := (count : Measure Γ))).fubini hf
  simpa only [integral_count_eq_tsum] using h_fubini

/-- Unfolding of a sum over a discrete subgroup `Γ` of `G`, for a left Haar measure `μ` and an
integrable `f`: `g ↦ ∑' γ, f (γ * g)` is integrable for the quotient measure on `Γ \ G`, and its
integral is `∫ f dμ`. This is Weil's integration formula for a discrete subgroup. -/
lemma integral_quotMeasure_tsum {f : G → ℂ} (hf : Integrable f μ) :
    Integrable (fun g : G ↦ ∑' γ : Γ, f (γ * g)) (Γ.quotMeasure μ) ∧
      ∫ g : G, ∑' γ : Γ, f (γ * g) ∂Γ.quotMeasure μ = ∫ g : G, f g ∂μ :=
  ⟨integrable_quotMeasure_tsum Γ hf, integral_quotMeasure_tsum_eq Γ hf⟩

end New

end CutoffExistence

/-!
## Transport along equivariant measure preserving maps

Integrals over a quotient `H \ X` are integrals against the measure `New.orbitMeasure ν μ`, which is
`μ` weighted by a chosen cutoff. It depends on that choice, so only invariant functions have a well
defined distribution; results are stated with `IdentDistrib`.

* `New.identDistrib_orbitMeasure_comp`: change of variables along an equivariant measure preserving
  map.
-/

section QuotientTransport

open MeasureTheory ProbabilityTheory New

variable {H X H' Y Z : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace H']
  [MeasurableSpace Y] [MeasurableSpace Z] [Group H] [MulAction H X] [MeasurableInv H]
  [MeasurableSMul₂ H X] {ν : Measure H} [SFinite (α := H) ν] [ν.IsInvInvariant]
  {μ : Measure X} [SFinite μ] [SMulInvariantMeasure H X μ] [HasCutoff ν X]

/-- Change of variables on quotients. Let `σ : H → H'` and `T : X → Y` preserve the measures, with
`T (h • x) = σ h • T x`. For a measurable `H'`-invariant `F` on `Y`, the function `F ∘ T` on `H \ X`
and the function `F` on `H' \ Y` have the same distribution. -/
@[to_additive identDistrib_addOrbitMeasure_comp]
lemma New.identDistrib_orbitMeasure_comp [SMul H' Y] [MeasurableSMul₂ H' Y] {ν' : Measure H'}
    {μ' : Measure Y} [HasCutoff ν' Y] {σ : H → H'} (hσ : MeasurePreserving σ ν ν') {T : X → Y}
    (hT : MeasurePreserving T μ μ') (h_equiv : ∀ (a : H) (x : X), T (a • x) = (σ a : H') • T x)
    {F : Y → Z} (hF_inv : ∀ (a : H') (y : Y), F (a • y) = F y) (hF : Measurable F := by fun_prop) :
    IdentDistrib (fun x : X ↦ F (T x)) F (orbitMeasure ν μ) (orbitMeasure ν' μ') := by
  -- `orbitMeasure ν μ` unfolds to `μ`, and `T` is equivariant, so along `σ` and `T` it unfolds to
  -- `μ'`.
  have h_eq : (fun p : X × H ↦ σ p.2 • T p.1) = T ∘ fun p : X × H ↦ p.2 • p.1 :=
    funext fun p ↦ (h_equiv p.2 p.1).symm
  have h_unfold : MeasurePreserving (fun p : X × H ↦ σ p.2 • T p.1)
      ((orbitMeasure ν μ).prod ν) μ' := by
    rw [h_eq]
    exact hT.comp measurePreserving_orbitMeasure
  exact (identDistrib_orbitMeasure_of_unfold hσ h_unfold hF hT.measurable hF_inv).symm

/-- If `μ` is right invariant on the group `X` and `(h • x) * g = h • (x * g)`, then right
translation by `g` does not change the distribution on `H \ X` of a measurable `H`-invariant
function. -/
lemma New.identDistrib_orbitMeasure_mul_right [Group X] [MeasurableMul₂ X] [IsScalarTower H X X]
    [μ.IsMulRightInvariant] (g : X) {F : X → Z} (hF_inv : ∀ (h : H) (y : X), F (h • y) = (F y : Z))
    (hF : Measurable F := by fun_prop) :
    IdentDistrib (fun x : X ↦ F (x * g)) F (orbitMeasure ν μ) (orbitMeasure ν μ) :=
  identDistrib_orbitMeasure_comp (.id _) (measurePreserving_mul_right μ g)
    (fun h x ↦ smul_mul_assoc h x g) hF_inv hF

end QuotientTransport

/-!
## Unimodularity and finite covolume of cocompact discrete subgroups

* `New.isFiniteMeasure_quotMeasure_of_cocompact`: a cocompact discrete subgroup has finite covolume.
-/

section Unimodular

open MeasureTheory Set Measure NeZero

namespace New

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [IsHaarMeasure μ]
  {Γ : Subgroup G} [DiscreteTopology Γ]

@[to_additive ne_addQuot]
instance : NeZero (Γ.quotMeasure μ) :=
  -- Unfolding carries `Γ.quotMeasure μ ⊗ count` to `μ`, which is not zero.
  ⟨fun h_zero ↦ by
    have h_map : ((Γ.quotMeasure μ).prod count).map (fun p : G × Γ ↦ p.2 • p.1) = μ :=
      measurePreserving_orbitMeasure.map_eq
    simp [h_zero, ne'] at h_map⟩

/-- A group with a lattice is unimodular: if Γ is discrete in the locally compact second
countable Hausdorff group G and Γ\G has finite volume for the left Haar measure μ, then μ is
right invariant. -/
lemma isMulRightInvariant_of_finite_covolume (_h_finite : IsFiniteMeasure (Γ.quotMeasure μ)) :
    IsMulRightInvariant μ := by
  -- Right translation by `g` scales `μ` by the modular character. It commutes with the left action
  -- of `Γ`, so the quotient has the same volume for `μ` and for the scaled measure.
  refine ⟨fun g ↦ ?_⟩
  have h_mod : μ.map (· * g) = modularCharacterFun g • μ :=
    map_right_mul_eq_modularCharacterFun_smul μ g
  have h_equiv (γ : Γ) (x : G) : γ • x * g = γ • (x * g) := smul_mul_assoc γ x g
  have h_translate : MeasurePreserving (· * g) μ (modularCharacterFun g • μ) :=
    ⟨measurable_mul_const g, h_mod⟩
  have h_vol : ∫⁻ _ : G, 1 ∂Γ.quotMeasure (modularCharacterFun g • μ) =
      ∫⁻ _ : G, 1 ∂Γ.quotMeasure μ :=
    (identDistrib_orbitMeasure_comp (.id (count : Measure Γ)) h_translate h_equiv
      (fun _ _ ↦ rfl) measurable_one).symm.lintegral_eq
  -- The volume is finite and nonzero, so the factor is one. (`withDensity_apply` would expand the
  -- quotient measures, so it is removed from `simp`.)
  have h_scale : (modularCharacterFun g : ENNReal) * Γ.quotMeasure μ univ =
      Γ.quotMeasure μ univ := by
    simpa [← coe_nnreal_smul, -withDensity_apply, withDensity_smul_measure] using h_vol
  have h_one : modularCharacterFun g = 1 := by
    simpa [ne, ENNReal.mul_eq_right, -withDensity_apply] using h_scale
  rw [h_mod, h_one, one_smul]

instance [CompactSpace G] : IsMulRightInvariant μ := by
  -- The trivial subgroup is a lattice of a compact group.
  apply isMulRightInvariant_of_finite_covolume (Γ := ⊥)
  rw [quotMeasure_bot]
  infer_instance

instance [IsMulRightInvariant μ] : IsInvInvariant μ := by
  -- `μ.inv` and `μ` are left invariant, so both are multiples of the Haar measure normalized on
  -- `K = K₀ ∪ K₀⁻¹`; the factors agree because `K` is symmetric.
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  let K : TopologicalSpace.PositiveCompacts G := K₀ ⊔ K₀.map _ continuous_inv (isOpenMap_inv G)
  have h_mass : μ.inv K = μ K := by simp [K, union_comm]
  constructor
  calc
    μ.inv = μ.inv K • haarMeasure K := haarMeasure_unique _ K
    _ = μ K • haarMeasure K := by rw [h_mass]
    _ = μ := (haarMeasure_unique μ K).symm

variable (μ)

/-- A cocompact discrete subgroup `Γ` of `G` has finite covolume: if some compact set `C` meets
every orbit `Γ g`, the quotient measure of the left Haar measure `μ` on `Γ \ G` is finite. -/
@[to_additive isFiniteMeasure_addOrbitMeasure]
lemma isFiniteMeasure_quotMeasure_of_cocompact :
    Γ.IsCocompact → IsFiniteMeasure (Γ.quotMeasure μ) := by
  -- Unfolding: the mass of the quotient is at most the integral over it of the number of `γ` with
  -- `γ • x ∈ C` (that number is at least one), and this integral is at most `μ C < ∞`.
  rintro ⟨C, hC, h_meets⟩
  set σ : Measure G := Γ.quotMeasure μ
  let E : Set (G × Γ) := (fun p : G × Γ ↦ p.2 • p.1) ⁻¹' C
  have h_one_le (x : G) : 1 ≤ count (Prod.mk x ⁻¹' E) := by
    obtain ⟨γ, hγ, hγC⟩ := h_meets x
    have h_mem : (⟨γ, hγ⟩ : Γ) ∈ Prod.mk x ⁻¹' E := hγC
    exact (ENNReal.le_tsum ⟨⟨γ, hγ⟩, h_mem⟩).trans le_count_apply
  constructor
  calc σ univ = ∫⁻ _, 1 ∂σ := lintegral_one.symm
    _ ≤ ∫⁻ x, count (Prod.mk x ⁻¹' E) ∂σ := lintegral_mono h_one_le
    _ = σ.prod count E := (prod_apply (hC.measurableSet.preimage (by fun_prop))).symm
    -- unfolding: `(x, γ) ↦ γ • x` carries the product measure to `μ`
    _ ≤ μ C := measurePreserving_orbitMeasure.measure_preimage_le C
    _ < ⊤ := hC.measure_lt_top

omit [T2Space G] in
/-- If the left Haar measure `μ` is also right invariant, every s-finite right invariant measure
is `d • μ` for some `d` in `[0, ∞]`. -/
lemma exists_eq_smul_haar [μ.IsMulRightInvariant] {ν : Measure G} [SFinite ν]
    (_hν : ν.IsMulRightInvariant) :
    ∃ d : ENNReal, ν = d • μ := by
  -- Compare the left invariant measures `ν.inv` and `(μ V)⁻¹ • μ`, for a set `V` of finite positive
  -- measure, by `measure_mul_lintegral_eq`.
  obtain ⟨V, hV_meas, -, hV_pos, hV_fin⟩ :
      ∃ V : Set G, MeasurableSet V ∧ V ⊆ univ ∧ 0 < μ V ∧ μ V < ⊤ :=
    μ.exists_subset_measure_lt_top .univ (NeZero.pos _)
  refine ⟨ν.inv V * (μ V)⁻¹, Eq.symm ?_⟩
  refine ext_of_lintegral _ fun f hf ↦ ?_
  have h_compare : ν.inv V * ∫⁻ y : G, f y ∂(μ V)⁻¹ • μ =
      ∫⁻ x : G, ((μ V)⁻¹ • μ) ((· * x) ⁻¹' V) * f x⁻¹ ∂ν.inv :=
    measure_mul_lintegral_eq ν.inv ((μ V)⁻¹ • μ) hV_meas f hf
  -- Right invariance of `μ` makes the weight one.
  have h_weight (x : G) : ((μ V)⁻¹ • μ) ((· * x) ⁻¹' V) = 1 := by
    simp [ENNReal.inv_mul_cancel hV_pos.ne' hV_fin.ne]
  -- The two inversions cancel.
  simpa [h_weight, mul_assoc, measurableEmbedding_inv.lintegral_map, inv_def] using h_compare

end New

end Unimodular

namespace New

/-!
## The mean of a periodic function over a compact quotient

The mean of a periodic function on a topological abelian group `B` over a compact quotient `B ⧸ B₀`,
for the Haar probability measure. Functions stay on `B`; they are read on the quotient through
chosen representatives `q.out`.

* `New.quotMean_quotMean`: the mean may be computed in two steps, along a continuous homomorphism
  from a product `A × A'` onto `B`.
-/

section PeriodicMean
/- `B₀` and `A₀` are subgroups with compact quotient, `F` is a function on `B` and `φ` is a
homomorphism from `A` to `B`. -/
variable {B A : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  (B₀ : AddSubgroup B) [CompactSpace (B ⧸ B₀)]
  (F : B → ℂ) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  (A₀ : AddSubgroup A) [CompactSpace (A ⧸ A₀)] (φ : A →+ B)

/-- The property that a function F on a topological abelian group B is continuous and satisfies
F(γ+x)=F(x) for all γ in the subgroup B₀ and all x. -/
def IsContPeriodic : Prop := Continuous F ∧ ∀ᵉ (γ ∈ B₀) (x : B), F (γ + x) = F x

/-- The Borel σ-algebra on the quotient B/B₀ of a topological abelian group B by a subgroup B₀. -/
scoped instance IsDualFamily.quotMeasurableSpace : MeasurableSpace (B ⧸ B₀) := borel _

open IsDualFamily MeasureTheory QuotientAddGroup Function

instance : BorelSpace (B ⧸ B₀) := ⟨rfl⟩

instance : IsProbabilityMeasure (α := B ⧸ B₀) (Measure.addHaarMeasure ⊤) :=
  ⟨Measure.addHaarMeasure_self⟩

/-- The mean of a complex-valued function `F` over the compact quotient `B ⧸ B₀`. It is the integral
of `F q.out` against the Haar probability measure, where `q.out` is a chosen coset
representative. -/
noncomputable def quotMean : ℂ := ∫ q : B ⧸ B₀, F q.out ∂Measure.addHaarMeasure ⊤

/-- A bound for `F` bounds its mean, the measure being a probability measure. -/
lemma norm_quotMean_le {F : B → ℂ} {C : ℝ} (h : ∀ x : B, ‖F x‖ ≤ C) : ‖quotMean B₀ F‖ ≤ C := by
  simpa [quotMean] using norm_integral_le_of_norm_le_const (μ := .addHaarMeasure ⊤)
    (.of_forall fun q : B ⧸ B₀ ↦ h q.out)

variable {B₀ F}

@[simp]
lemma quotMean_const_mul (c : ℂ) (F : B → ℂ) :
    quotMean B₀ (fun x : B ↦ c * F x) = c * quotMean B₀ F :=
  integral_const_mul c _

@[simp]
lemma quotMean_const (c : ℂ) : quotMean B₀ (fun _ : B ↦ c) = c := by simp [quotMean]

omit [IsTopologicalAddGroup B] [CompactSpace (B ⧸ B₀)] in
/-- A continuous `B₀`-periodic function takes at the chosen representative of the coset of `x`
the same value as at `x`. -/
lemma IsContPeriodic.apply_out_mk (h : IsContPeriodic B₀ F) (x : B) :
    F (mk x : B ⧸ B₀).out = F x := by
  obtain ⟨γ, hγ⟩ : ∃ γ : B₀, (mk x : B ⧸ B₀).out = x + γ := mk_out_eq_add B₀ x
  rw [hγ, add_comm, h.2 γ γ.2 x]

omit [IsTopologicalAddGroup B] [CompactSpace (B ⧸ B₀)] in
/-- A continuous `B₀`-periodic function, read at coset representatives, is continuous on
`B ⧸ B₀`. -/
lemma IsContPeriodic.continuous_out (h : IsContPeriodic B₀ F) :
    Continuous fun q : B ⧸ B₀ ↦ F q.out := by
  -- the composite with the projection is `F`
  refine (isQuotientMap_mk B₀).continuous_iff.2 ?_
  simpa [comp_def, h.apply_out_mk] using h.1

/-- A continuous `B₀`-periodic function, read at coset representatives, is integrable on the
compact quotient `B ⧸ B₀`. -/
lemma IsContPeriodic.integrable_out (h : IsContPeriodic B₀ F) :
    Integrable (fun q : B ⧸ B₀ ↦ F q.out) (Measure.addHaarMeasure ⊤) :=
  h.continuous_out.integrable_of_hasCompactSupport (.of_compactSpace _)

/-- A translate of a continuous `B₀`-periodic function has the same mean over `B ⧸ B₀`. -/
lemma quotMean_translate (h : IsContPeriodic B₀ F) (a : B) :
    quotMean B₀ (fun x : B ↦ F (x + a)) = quotMean B₀ F := by
  -- Haar measure on the quotient is invariant under translation by the class of `a`
  calc
    _ = ∫ q : B ⧸ B₀, F (q + a).out ∂.addHaarMeasure ⊤ := by simp [quotMean, ← h.apply_out_mk]
    _ = _ := integral_add_right_eq_self (fun q : B ⧸ B₀ ↦ F q.out) ↑a

/-- Let `φ : A × A' → B` be a continuous surjective homomorphism that sends `A₀ × A₁` into `B₀`; all
three quotients are compact and `A` is second countable. For `F` continuous and `B₀`-periodic, the
mean of `F (φ (a, a'))` over `A' ⧸ A₁` and then over `A ⧸ A₀` is the mean of `F` over `B ⧸ B₀`. -/
lemma quotMean_quotMean (h : IsContPeriodic B₀ F) [SecondCountableTopology A] {A' : Type*}
    [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] (A₁ : AddSubgroup A')
    [CompactSpace (A' ⧸ A₁)] (φ : A × A' →+ B) (hφ : Continuous φ)
    (h₀ : ∀ a ∈ A₀, ∀ b ∈ A₁, φ (a, b) ∈ B₀) (hs : Surjective φ) :
    quotMean A₀ (fun a : A ↦ quotMean A₁ fun b : A' ↦ F (φ (a, b))) = quotMean B₀ F := by
  -- `φ` induces a continuous surjective homomorphism `ψ` of the compact quotients, so `ψ`
  -- preserves the Haar probability measures; then Fubini.
  have h_le : A₀.prod A₁ ≤ B₀.comap φ := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact h₀ a ha b hb
  let ψ : (A ⧸ A₀) × (A' ⧸ A₁) →+ B ⧸ B₀ :=
    (map (A₀.prod A₁) B₀ φ h_le).comp (prodAddEquiv A₀ A₁).symm.toAddMonoidHom
  have hψ_mk (x : A × A') : (φ x : B ⧸ B₀) = ψ (x.1, x.2) := rfl
  -- continuity of a map on a quotient is tested after composing with the projection
  have hψ_cont : Continuous ψ :=
    (isOpenQuotientMap_mk.prodMap isOpenQuotientMap_mk).continuous_comp_iff.1
      (continuous_mk.comp hφ)
  have hψ_surj : Surjective ψ := fun q ↦ by
    obtain ⟨x, hx⟩ := (mk_surjective.comp hs) q
    exact ⟨(x.1, x.2), (hψ_mk x).symm.trans hx⟩
  have hψ_preserving : MeasurePreserving ψ
      ((Measure.addHaarMeasure ⊤).prod (.addHaarMeasure ⊤)) (.addHaarMeasure ⊤) :=
    ψ.measurePreserving hψ_cont hψ_surj (by simp)
  -- periodicity lets `F` be read at any representative
  have h_read (p : (A ⧸ A₀) × (A' ⧸ A₁)) : F (φ (p.1.out, p.2.out)) = F (ψ p).out := by
    rw [← h.apply_out_mk, hψ_mk]
    simp
  calc quotMean A₀ (fun a : A ↦ quotMean A₁ fun b : A' ↦ F (φ (a, b)))
      = ∫ p : A ⧸ A₀, ∫ q : A' ⧸ A₁, F (ψ (p, q)).out ∂.addHaarMeasure ⊤ ∂.addHaarMeasure ⊤ := by
        simp only [quotMean, ← h_read]
    _ = quotMean B₀ F := (hψ_preserving.fubini h.integrable_out).2

/-- The mean of a continuous `B₀`-periodic function may be computed after pull-back along a
continuous surjective homomorphism `φ : A → B` that sends `A₀` into `B₀`. -/
lemma quotMean_comp (h : IsContPeriodic B₀ F) (h₀ : ∀ a ∈ A₀, φ a ∈ B₀) (hs : Surjective φ)
    (hφ : Continuous φ := by
      simp
      fun_prop) :
    quotMean A₀ (fun a : A ↦ F (φ a)) = quotMean B₀ F := by
  -- `quotMean_quotMean` with the trivial group as first factor
  have h_surj : Surjective (φ.comp (AddMonoidHom.snd Unit A)) := hs.comp Prod.snd_surjective
  have h_two : quotMean (⊤ : AddSubgroup Unit) (fun _ : Unit ↦ quotMean A₀ fun a : A ↦ F (φ a)) =
      quotMean B₀ F :=
    quotMean_quotMean (A := Unit) ⊤ h A₀ (φ.comp (AddMonoidHom.snd Unit A)) hφ.snd'
      (fun _ _ ↦ h₀) h_surj
  -- the mean over the trivial quotient is evaluation of the constant
  rwa [quotMean_const] at h_two

end PeriodicMean

/-!
## The periodic mean as an average against the quotient measure

Let `B₀` be a discrete cocompact subgroup of a locally compact abelian group `B` with Haar measure
`μ`. The measure `B₀.quotMeasure μ` on `B`, assumed finite, plays the role of the restriction of
`μ` to a fundamental domain; its mass is the covolume of `B₀`.

* `New.average_quotMeasure_eq_quotMean`: the mean `New.quotMean` of a continuous periodic function
  over `B ⧸ B₀` is its average against `B₀.quotMeasure μ`.
-/

section PeriodicUnfolding

open MeasureTheory Measure QuotientAddGroup IsDualFamily

variable {B : Type*} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [MeasurableSpace B] [BorelSpace B] [PolishSpace B] [LocallyCompactSpace B] (B₀ : AddSubgroup B)
  (μ : Measure B) [CompactSpace (B ⧸ B₀)] [DiscreteTopology B₀] [μ.IsAddHaarMeasure]
  [IsFiniteMeasure (B₀.quotMeasure μ)]

/-- Here `B₀.quotMeasure μ` is μ weighted by a cutoff for the action of B₀, a measure on B that
computes integrals over B ⧸ B₀. `quotMean B₀ F` is the integral of F over B ⧸ B₀ against the Haar
probability measure. For B₀ discrete and cocompact in B, μ a Haar measure with `B₀.quotMeasure μ`
finite, and F continuous and B₀-periodic, the average of F against `B₀.quotMeasure μ` equals
`quotMean B₀ F`. -/
lemma average_quotMeasure_eq_quotMean {F : B → ℂ} (hF : IsContPeriodic B₀ F) :
    ⨍ x : B, F x ∂B₀.quotMeasure μ = quotMean B₀ F := by
  have h_mk : Measurable (mk : B → B ⧸ B₀) := continuous_mk.measurable
  -- The image `m` of `B₀.quotMeasure μ` in the quotient is translation invariant, because `μ` is:
  -- `identDistrib_addOrbitMeasure_comp` transports the distribution of an invariant function, here
  -- `mk`, along an equivariant measure preserving map, here the translation by `a`.
  set m : Measure (B ⧸ B₀) := (B₀.quotMeasure μ).map mk with hm
  have h_translate (a : B) :
      (B₀.quotMeasure μ).map (fun x : B ↦ (mk (a + x) : B ⧸ B₀)) = m := by
    have h_equiv (γ : B₀) (x : B) : a + (γ +ᵥ x) = γ +ᵥ (a + x) := add_left_comm a (γ : B) x
    exact (identDistrib_addOrbitMeasure_comp (.id (count : Measure B₀))
      (measurePreserving_add_left μ a) h_equiv (by simp) h_mk).map_eq
  have h_inv : m.IsAddLeftInvariant :=
    ⟨forall_mk.2 fun a ↦ (Measure.map_map (measurable_const_add _) h_mk).trans (h_translate a)⟩
  -- So it is the Haar probability measure times the total mass of `B₀.quotMeasure μ`.
  have h_haar : m = (B₀.quotMeasure μ) Set.univ • addHaarMeasure ⊤ := by
    simpa [hm, h_mk, -withDensity_apply] using addHaarMeasure_unique m ⊤
  have h_integral : ∫ x : B, F x ∂B₀.quotMeasure μ =
      (B₀.quotMeasure μ).real Set.univ • quotMean B₀ F :=
    calc ∫ x : B, F x ∂B₀.quotMeasure μ = ∫ x : B, F (mk x : B ⧸ B₀).out ∂B₀.quotMeasure μ := by
          simp only [hF.apply_out_mk]
      _ = ∫ q : B ⧸ B₀, F q.out ∂m := (integral_map h_mk.aemeasurable
          hF.continuous_out.aestronglyMeasurable).symm
      _ = (B₀.quotMeasure μ).real Set.univ • quotMean B₀ F := by
          rw [h_haar, integral_smul_measure, ← real_def, quotMean]
  -- The mass is finite and not zero, and the average divides by it.
  rw [average_eq, h_integral, inv_smul_smul₀ measureReal_univ_ne_zero]

/-- Unfolding: if `F` is integrable on `B` and `G x = ∑_{γ ∈ B₀} F (γ + x)` converges everywhere
and is continuous and `B₀`-periodic, then the mean of `G` over `B ⧸ B₀` is `∫ F dμ` divided by the
covolume of `B₀` (the mass of `B₀.quotMeasure μ`). -/
lemma quotMean_tsum_eq_integral {F G : B → ℂ} (hF : Integrable F μ) (hG : IsContPeriodic B₀ G)
    (h_sum : ∀ x : B, HasSum (fun γ : B₀ ↦ (F (γ +ᵥ x) : ℂ)) (G x)) :
    quotMean B₀ G = ((B₀.quotMeasure μ).real Set.univ)⁻¹ • ∫ x : B, F x ∂μ := by
  -- Average `G` against `B₀.quotMeasure μ` and unfold `∫ F` into the sums over `B₀`.
  have h_unfold : ∫ x : B, ∫ γ : B₀, F (γ +ᵥ x) ∂count ∂B₀.quotMeasure μ = ∫ x : B, F x ∂μ :=
    (measurePreserving_addOrbitMeasure.fubini hF).2
  have h_orbit (x : B) : ∫ γ : B₀, F (γ +ᵥ x) ∂count = G x := by
    rw [integral_count_eq_tsum, (h_sum x).tsum_eq]
  rw [← average_quotMeasure_eq_quotMean B₀ μ hG, average_eq, ← h_unfold]
  simp only [h_orbit]

end PeriodicUnfolding

end New
