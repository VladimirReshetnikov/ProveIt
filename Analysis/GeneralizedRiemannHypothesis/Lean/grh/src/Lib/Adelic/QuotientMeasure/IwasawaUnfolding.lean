import Lib.Adelic.QuotientMeasure.Basic

/-!
# Unfolding over orbits and integration in Iwasawa coordinates

This file proves integration formulas on a quotient `Γ \ G` by a discrete subgroup `Γ`. An integral
over `Γ \ G` of a sum over translates is unfolded to an integral over the quotient by the subgroup
that keeps a block, in particular by the stabiliser of a point. Integrals of functions invariant
under a closed subgroup `N` are then written in Iwasawa coordinates `G = N · i(M) · K`.

* `Γ.quotMeasure μ`: the measure on `G` that integrates left `Γ`-invariant functions over `Γ \ G`.
* `N.FixesLeft F`: `F (γ * g) = F g` for all `γ ∈ N` and `g ∈ G`.

## Main definitions and results

* `New.integral_tsum_eq_integral_tsum_block`: the integral over `Γ \ G` of the sum over all
  translates of a block `C` is the integral over `S \ G` of the sum over `C`, where `S` is the
  group that keeps `C`. `New.integral_tsum_block` adds integrability and termwise integration.
* `New.integral_tsum_orbit_eq_integral_stabilizer`: the case of one orbit, with `S` the image of the
  stabiliser of a point.
* `New.lintegral_iwasawa`: `dn dm dk` in the coordinates `i m * n * k` is a multiple of Haar
  measure.
* `New.integral_quotMeasure_iwasawa`: the integral over `Γ \ G` of a function `F` invariant under
  `N` and `Γ` is a nonzero constant times the integral of `w m * F (i m * k)`, where conjugation by
  `i m` scales the Haar measure of `N` by `w m`.

## Relation to the literature

Known result: The unfolding trick and the integration formula in Iwasawa coordinates on a quotient
by a discrete subgroup. Weil's formula for invariant integration on a quotient is in
`Lib.Adelic.QuotientMeasure.Basic`.
-/

/-!
## Unfolding a sum over an orbit

The unfolding trick for sums over a countable set `Y` with an action of a group `Λ`, which `i`
identifies with a discrete subgroup `Γ` of `G`. The summands `k y : G → ℂ` are measurable and
equivariant: `k (γ • y) (i γ * x) = k y x`.
-/

section OrbitUnfolding

open MeasureTheory Measure MulAction ProbabilityTheory ENNReal Set

open scoped Classical in
/-- Let `i` be injective, and let `γ` carry a point of `C` into `C` exactly when `i γ` lies in the
subgroup `S` of the range of `i`. If `β` has sum `1` over each `S`-orbit in `G`, then the sum of
`β (i γ * x)` over the `γ` that carry `y` into `C` is `1`, provided that there is such a `γ`. -/
lemma New.tsum_cutoff_smul_mem_eq_one {Λ G Y : Type*} [Group Λ] [Group G] [MulAction Λ Y]
    {i : Λ →* G} (hi : Function.Injective i) {S : Subgroup G} (hS : S ≤ i.range) {C : Set Y}
    (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S) {β : G → ℝ≥0∞}
    (hβ_one : ∀ x : G, ∑' s : S, β (s * x) = 1) {y : Y} {γ₀ : Λ} (hγ₀ : γ₀ • y ∈ C) (x : G) :
    ∑' γ : Λ, (if γ • y ∈ C then β (i γ * x) else 0) = 1 := by
  -- The point `(γ * γ₀) • y` lies in `C` exactly when `i γ ∈ S`.
  let b : G → ℝ≥0∞ := (S : Set G).indicator fun g ↦ β (g * (i γ₀ * x))
  calc ∑' γ : Λ, (if γ • y ∈ C then β (i γ * x) else 0)
    _ = ∑' γ : Λ, (if (γ * γ₀) • y ∈ C then β (i (γ * γ₀) * x) else 0) :=
        ((Equiv.mulRight γ₀).tsum_eq _).symm
    _ = ∑' γ : Λ, b (i γ) := by simp [b, indicator, mul_smul, mul_assoc, hC _ _ hγ₀]
    _ = ∑' g : G, b g := hi.tsum_eq fun g hg ↦ hS (support_indicator_subset hg)
    _ = ∑' s : S, β (s * (i γ₀ * x)) := (tsum_subtype (S : Set G) _).symm
    _ = 1 := hβ_one (i γ₀ * x)

/-- If the `k y` are measurable and `∑ ‖k y‖` has finite integral for `ν`, then `(x, y) ↦ k y x` is
integrable for the product of `ν` with the counting measure. -/
lemma New.integrable_prod_count_of_lintegral_lt_top {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y] {ν : Measure X} {k : Y → X → ℂ}
    (hk_meas : ∀ y : Y, Measurable (k y)) (h_fin : ∫⁻ x : X, ∑' y : Y, ‖k y x‖ₑ ∂ν < ∞) :
    Integrable (fun p : X × Y ↦ k p.2 p.1) (ν.prod count) := by
  have h_meas : Measurable fun p : X × Y ↦ k p.2 p.1 := measurable_from_prod_countable_left hk_meas
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ h_meas.enorm.aemeasurable]
  simpa only [lintegral_count] using h_fin

/-- If the `k y` are measurable and `∑ ‖k y‖` has finite integral, then `∑ k y` is integrable. -/
lemma New.integrable_tsum_of_lintegral_lt_top {X Y : Type*} [MeasurableSpace X] [Countable Y]
    {ν : Measure X} [SFinite ν] {k : Y → X → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (h_fin : ∫⁻ x : X, ∑' y : Y, ‖k y x‖ₑ ∂ν < ∞) :
    Integrable (fun x : X ↦ ∑' y : Y, k y x) ν := by
  let : MeasurableSpace Y := ⊤
  have h_prod : Integrable (fun p : X × Y ↦ k p.2 p.1) (ν.prod count) :=
    integrable_prod_count_of_lintegral_lt_top hk_meas h_fin
  simpa only [integral_count_eq_tsum] using h_prod.integral_prod_left

variable {Λ G Y : Type*} [Group Λ] [Group G] [TopologicalSpace G] [MeasurableSpace G]
  [MulAction Λ Y] [Countable Y] {i : Λ →* G}

omit [Group G] [TopologicalSpace G] in
/-- If the `k y` are almost everywhere strongly measurable and `∑ ‖k y‖` has finite integral, then
the integrals of the `k y` sum to the integral of `∑ k y`. -/
lemma New.hasSum_integral_of_lintegral_tsum_lt_top {k : Y → G → ℂ} {ν : Measure G}
    (h_fin : ∫⁻ x : G, ∑' y : Y, ‖k y x‖ₑ ∂ν < ∞)
    (h_meas : ∀ y : Y, AEStronglyMeasurable (k y) ν := by fun_prop) :
    HasSum (fun y : Y ↦ ∫ x : G, k y x ∂ν) (∫ x : G, ∑' y : Y, k y x ∂ν) := by
  rw [lintegral_tsum (by fun_prop)] at h_fin
  rw [integral_tsum h_meas h_fin.ne]
  have h_le : ∑' y : Y, ‖∫ x, k y x ∂ν‖ₑ ≤ ∑' y : Y, ∫⁻ x, ‖k y x‖ₑ ∂ν :=
    ENNReal.tsum_le_tsum fun y ↦ enorm_integral_le_lintegral_enorm (k y)
  exact (Summable.of_enorm (h_le.trans_lt h_fin).ne).hasSum

open scoped Classical in
omit [MeasurableSpace G] [Countable Y] in
/-- Let `i` map `Λ` isomorphically onto `Γ`, let `γ` carry a point of `C` into `C` exactly when
`i γ` lies in the subgroup `S` of `Γ`, and let `D` be the union of the translates of `C`. If `β` has
sum `1` over each `S`-orbit in `G`, then the sum of `β (i γ * x)` over the `γ` that carry `y` into
`C` is `1` if `y ∈ D` and `0` otherwise. -/
lemma New.tsum_cutoff_smul_mem_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {C D : Set Y} (hS : S ≤ Γ)
    (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S) (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C)
    {β : G → ℝ≥0∞} (hβ_one : ∀ x : G, ∑' s : S, β (s * x) = 1) (y : Y) (x : G) :
    ∑' γ : Λ, (if γ • y ∈ C then β (i γ * x) else 0) = if y ∈ D then 1 else 0 := by
  subst hΓ
  split_ifs with hy
  · obtain ⟨γ₀, hγ₀⟩ := (hD y).1 hy
    exact tsum_cutoff_smul_mem_eq_one hi hS hC hβ_one hγ₀ x
  · simp [not_exists.1 (mt (hD y).2 hy)]

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [BorelSpace G]

/-- Unfolding of a sum of nonnegative terms over the translates of a block. Let `i` map `Λ`
isomorphically onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into `C` exactly when
`i γ` lies in `S ≤ Γ`, and let `D` be the union of the translates of `C`. For measurable `g y` with
`g (γ • y) (i γ * x) = g y x`, the integral of `∑_D g y` over `Γ \ G` (that is, against
`Γ.quotMeasure μ`) is the integral of `∑_C g y` over `S \ G`. -/
lemma New.lintegral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C)
    {g : Y → G → ℝ≥0∞} (hg_meas : ∀ y : Y, Measurable (g y))
    (hg_inv : ∀ (γ : Λ) (y : Y) (x : G), g (γ • y) (i γ * x) = g y x) :
    ∫⁻ x : G, ∑' y : D, g y x ∂Γ.quotMeasure μ = ∫⁻ x : G, ∑' y : C, g y x ∂S.quotMeasure μ := by
  classical
  -- With `β` the cutoff of `S`, unfold the integral of `β x * ∑_C g y x` over `G` along `Γ` and
  -- substitute `y ↦ γ • y` in the term of `i γ`.
  have : DiscreteTopology S := .of_subset (s := Γ) inferInstance hS
  let β : G → ℝ≥0∞ := chosenCutoff (count : Measure S)
  obtain ⟨hβ_meas, hβ_int⟩ : IsCutoff (count : Measure S) β := isCutoff_chosenCutoff count
  have hβ_one (x : G) : ∑' s : S, β (s * x) = 1 := by
    simpa [lintegral_count, Subgroup.smul_def] using hβ_int x
  have h_term (γ : Λ) (x : G) : β (i γ * x) * ∑' y : C, g y (i γ * x) =
      ∑' y : Y, (if γ • y ∈ C then β (i γ * x) else 0) * g y x := by
    rw [tsum_subtype C fun y ↦ g y (i γ * x), ← (MulAction.toPerm γ).tsum_eq,
      ← ENNReal.tsum_mul_left]
    simp [indicator, hg_inv]
  have h_sum (x : G) : ∑' δ : Γ, β (δ * x) * ∑' y : C, g y (δ * x) = ∑' y : D, g y x := by
    subst hΓ
    calc ∑' δ : i.range, β (δ * x) * ∑' y : C, g y (δ * x)
      _ = ∑' γ : Λ, β (i γ * x) * ∑' y : C, g y (i γ * x) := ((i.ofInjective hi).tsum_eq _).symm
      _ = ∑' y : Y, (∑' γ : Λ, if γ • y ∈ C then β (i γ * x) else 0) * g y x := by
          simp only [h_term, ← ENNReal.tsum_mul_right]
          exact ENNReal.tsum_comm
      _ = ∑' y : D, g y x := by
          simp [tsum_cutoff_smul_mem_block hi rfl hS hC hD hβ_one, tsum_subtype D fun y ↦ g y x,
            indicator]
  have hS_meas : S.quotMeasure μ = μ.withDensity β := rfl
  calc ∫⁻ x, ∑' y : D, g y x ∂Γ.quotMeasure μ
    _ = ∫⁻ x, ∫⁻ δ : Γ, β (δ • x) * ∑' y : C, g y (δ • x) ∂count ∂Γ.quotMeasure μ := by
        simp only [lintegral_count, ← h_sum, Subgroup.smul_def, smul_eq_mul]
    _ = ∫⁻ x, β x * ∑' y : C, g y x ∂μ :=
        lintegral_orbitMeasure_lintegral (f := fun x ↦ β x * ∑' y : C, g y x) (by fun_prop)
    _ = ∫⁻ x, ∑' y : C, g y x ∂S.quotMeasure μ := by
        simp (disch := fun_prop) [hS_meas, lintegral_withDensity_eq_lintegral_mul]

/-- Let `i` map `Λ` isomorphically onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into
`C` exactly when `i γ` lies in `S ≤ Γ`, and let `D` be the union of the translates of `C`. For
measurable `k y` with `k (γ • y) (i γ * x) = k y x`, the integral of `∑_D ‖k y‖` over `Γ \ G` is
the integral of `∑_C ‖k y‖` over `S \ G`. -/
lemma New.lintegral_tsum_enorm_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x) :
    ∫⁻ x : G, ∑' y : D, ‖k y x‖ₑ ∂Γ.quotMeasure μ = ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ :=
  lintegral_tsum_block hi hΓ hS hC hD (g := fun y x ↦ ‖k y x‖ₑ) (fun y ↦ (hk_meas y).enorm)
    fun γ y x ↦ congrArg enorm (hk γ y x)

/-- Unfolding of the integral of a sum over the translates of a block. Let `i` map `Λ`
isomorphically onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into `C` exactly when
`i γ` lies in `S ≤ Γ`, and let `D` be the union of the translates of `C`. Let the `k y` be
measurable with `k (γ • y) (i γ * x) = k y x`. If `∑_C ‖k y‖` has finite integral over `S \ G`,
then the integral of `∑_D k y` over `Γ \ G` is the integral of `∑_C k y` over `S \ G`. -/
lemma New.integral_tsum_eq_integral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    (h_fin : ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ < ∞) :
    ∫ x : G, ∑' y : D, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ := by
  -- The functions `(x, y) ↦ k y x` on `(Γ \ G) × D` and on `(S \ G) × C` have the same
  -- distribution; the claim follows by Fubini.
  let : MeasurableSpace Y := ⊤
  have h_meas : Measurable fun p : Y × G ↦ k p.1 p.2 := measurable_from_prod_countable_right hk_meas
  have h_unfold (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
      ∫⁻ x, ∑' y : D, f (k y x) ∂Γ.quotMeasure μ = ∫⁻ x, ∑' y : C, f (k y x) ∂S.quotMeasure μ :=
    lintegral_tsum_block hi hΓ hS hC hD (g := fun y x ↦ f (k y x)) (by fun_prop) (by simp [hk])
  have h_dist : IdentDistrib (fun p : G × D ↦ k p.2 p.1) (fun p : G × C ↦ k p.2 p.1)
      ((Γ.quotMeasure μ).prod count) ((S.quotMeasure μ).prod count) := by
    refine ⟨by fun_prop, by fun_prop, ext_of_lintegral _ fun f hf ↦ ?_⟩
    simpa (disch := fun_prop) only [lintegral_map, lintegral_prod, lintegral_count]
      using h_unfold f hf
  have hC_int : Integrable (fun p : G × C ↦ k p.2 p.1) ((S.quotMeasure μ).prod count) :=
    integrable_prod_count_of_lintegral_lt_top (fun y : C ↦ hk_meas y) h_fin
  have hD_int := h_dist.integrable_iff.2 hC_int
  calc ∫ x, ∑' y : D, k y x ∂Γ.quotMeasure μ
    _ = ∫ p : G × D, k p.2 p.1 ∂(Γ.quotMeasure μ).prod count := by
        simp only [integral_prod _ hD_int, integral_count_eq_tsum]
    _ = ∫ p : G × C, k p.2 p.1 ∂(S.quotMeasure μ).prod count := h_dist.integral_eq
    _ = ∫ x, ∑' y : C, k y x ∂S.quotMeasure μ := by
        simp only [integral_prod _ hC_int, integral_count_eq_tsum]

/-- Unfolding of a sum of integrals over the translates of a block. Let `i` map `Λ` isomorphically
onto the discrete subgroup `Γ`, let `γ` carry a point of `C` into `C` exactly when `i γ` lies in
`S ≤ Γ`, and let `D` be the union of the translates of `C`. Let the `k y` be measurable with
`k (γ • y) (i γ * x) = k y x`. If `∑_C ‖k y‖` has finite integral over `S \ G`, then the sum over
`D` of the integrals of `k y` against the measure of `Γ \ G` is the integral of `∑_C k y` over
`S \ G`. -/
lemma New.tsum_integral_eq_integral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    (h_fin : ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ < ∞) :
    ∑' y : D, ∫ x : G, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ := by
  rw [← integral_tsum_eq_integral_tsum_block hi hΓ hS hC hD hk_meas hk h_fin]
  rw [← lintegral_tsum_enorm_block hi hΓ hS hC hD hk_meas hk] at h_fin
  exact (hasSum_integral_of_lintegral_tsum_lt_top h_fin).tsum_eq

/-- Unfolding of a sum over the translates of a block. The group `Λ` acts on `Y` and `i` maps it
isomorphically onto the discrete subgroup `Γ` of `G`; the terms are measurable and satisfy
`k (γ • y) (i γ * x) = k y x`. The block `C ⊆ Y` is such that `γ` carries a point of `C` into `C`
exactly when `i γ` lies in `S ≤ Γ`, and `D` is the union of the translates of `C`. Suppose that
`∑_D ‖k y‖` has finite integral over `Γ \ G` or that `∑_C ‖k y‖` has finite integral over `S \ G`.
Then `∑_C k y` is integrable over `S \ G`. Its integral equals the integral of `∑_D k y` over
`Γ \ G`. It also equals the sum over `D` of the integrals of `k y` against the measure of `Γ \ G`.
-/
lemma New.integral_tsum_block (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {C D : Set Y}
    (hS : S ≤ Γ) (hC : ∀ γ : Λ, ∀ y ∈ C, γ • y ∈ C ↔ i γ ∈ S)
    (hD : ∀ y : Y, y ∈ D ↔ ∃ γ : Λ, γ • y ∈ C) {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    (h_fin : ∫⁻ x : G, ∑' y : D, ‖k y x‖ₑ ∂Γ.quotMeasure μ < ∞ ∨
      ∫⁻ x : G, ∑' y : C, ‖k y x‖ₑ ∂S.quotMeasure μ < ∞) :
    Integrable (fun x : G ↦ ∑' y : C, k y x) (S.quotMeasure μ) ∧
    ∫ x : G, ∑' y : D, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ ∧
    ∑' y : D, ∫ x : G, k y x ∂Γ.quotMeasure μ = ∫ x : G, ∑' y : C, k y x ∂S.quotMeasure μ := by
  -- The two finiteness hypotheses are equivalent.
  rw [lintegral_tsum_enorm_block hi hΓ hS hC hD hk_meas hk, or_self] at h_fin
  exact ⟨integrable_tsum_of_lintegral_lt_top (fun y : C ↦ hk_meas y) h_fin,
    integral_tsum_eq_integral_tsum_block hi hΓ hS hC hD hk_meas hk h_fin,
    tsum_integral_eq_integral_tsum_block hi hΓ hS hC hD hk_meas hk h_fin⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [Countable Y] in
/-- If `k (γ • y) (i γ * x) = k y x`, then the term `k y` is invariant on the left under the image
`S` of the stabiliser of `y`. -/
lemma New.fixesLeft_map_stabilizer {S : Subgroup G} {k : Y → G → ℂ}
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    {y : Y} (h_stab : (stabilizer Λ y).map i = S) : S.FixesLeft (k y) := by
  subst h_stab
  rintro _ ⟨γ, hγ, rfl⟩ x
  rw [← hk γ y x, mem_stabilizer_iff.1 hγ]

/-- Unfolding of a sum over an orbit. Let `i` be injective with discrete range `Γ`, let the terms
`k z` be measurable and equivariant, and let `S` be the image under `i` of the stabiliser of `y`.
Suppose that the sum of the `‖k z‖` over the orbit of `y` has finite integral over `Γ \ G`, or that
`k y` is integrable over `S \ G`. Then `k y` is integrable over `S \ G`, and its integral equals the
integral over `Γ \ G` of the sum of the `k z` over the orbit, and also the sum of their
integrals. -/
lemma New.integral_tsum_orbit_eq_integral_stabilizer (hi : Function.Injective i)
    [DiscreteTopology i.range] {μ : Measure G} [IsHaarMeasure μ]
    {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x) {y : Y}
    (h_fin : ∫⁻ x : G, ∑' z : orbit Λ y, ‖k z x‖ₑ ∂i.range.quotMeasure μ < ∞ ∨
      Integrable (k y) (((stabilizer Λ y).map i).quotMeasure μ)) :
    Integrable (k y) (((stabilizer Λ y).map i).quotMeasure μ) ∧
    ∫ x : G, ∑' z : orbit Λ y, k z x ∂i.range.quotMeasure μ =
      ∫ x : G, k y x ∂((stabilizer Λ y).map i).quotMeasure μ ∧
    ∑' z : orbit Λ y, ∫ x : G, k z x ∂i.range.quotMeasure μ =
      ∫ x : G, k y x ∂((stabilizer Λ y).map i).quotMeasure μ := by
  -- The case `C = {y}` of `integral_tsum_block`: the orbit is the union of the translates of `{y}`.
  have hC : ∀ γ : Λ, ∀ z ∈ ({y} : Set Y),
      γ • z ∈ ({y} : Set Y) ↔ i γ ∈ (stabilizer Λ y).map i := by
    simp [Subgroup.mem_map_iff_mem hi]
  have hD (z : Y) : z ∈ orbit Λ y ↔ ∃ γ : Λ, γ • z ∈ ({y} : Set Y) := by
    simp [mem_orbit_symm (a₁ := z), mem_orbit_iff]
  have h_block : ∫⁻ x, ∑' z : orbit Λ y, ‖k z x‖ₑ ∂i.range.quotMeasure μ < ∞ ∨
      ∫⁻ x, ∑' z : ({y} : Set Y), ‖k z x‖ₑ ∂((stabilizer Λ y).map i).quotMeasure μ < ∞ :=
    h_fin.imp_right fun h_int ↦ by simpa [HasFiniteIntegral] using h_int.hasFiniteIntegral
  simpa using
    integral_tsum_block hi rfl ((stabilizer Λ y).map_le_range i) hC hD hk_meas hk h_block

/-- Unfolding of a sum over an orbit, with the subgroups and the orbit given by equations: `Γ` is
the discrete range of the injective map `i`, `S` the image of the stabiliser of `y`, and `D` the
orbit of `y`. Here `Γ.quotMeasure μ` is the measure on `G` that computes integrals over `Γ \ G`: the
Haar measure `μ` weighted by a cutoff for `Γ`, and likewise for `S`. The terms `k z` are measurable
and equivariant. Suppose that `∑ ‖k z‖`, over all `z : Y`, has finite integral over `Γ \ G` or that
`k y` is integrable over `S \ G`. Then `k y` is integrable over `S \ G`, and its integral equals the
integral of `∑_D k z` over `Γ \ G` and also the sum over `D` of the integrals of `k z` against
`Γ.quotMeasure μ`. -/
lemma New.integral_tsum_orbit_of_lt_top_or_integrable (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {D : Set Y}
    {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    {y : Y} (h_stab : (stabilizer Λ y).map i = S) (h_orbit : ∀ z : Y, z ∈ D ↔ y ∈ orbit Λ z)
    (h_fin : ∫⁻ x : G, ∑' z : Y, ‖k z x‖ₑ ∂Γ.quotMeasure μ < ∞ ∨
      Integrable (k y) (S.quotMeasure μ)) :
    Integrable (k y) (S.quotMeasure μ) ∧
    ∫ x : G, ∑' z : D, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ ∧
    ∑' z : D, ∫ x : G, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ := by
  obtain rfl : D = orbit Λ y := Set.ext fun z ↦ (h_orbit z).trans mem_orbit_symm
  subst hΓ h_stab
  -- The sum over the orbit is at most the sum over all of `Y`.
  exact integral_tsum_orbit_eq_integral_stabilizer hi hk_meas hk <| h_fin.imp_left <|
    (lintegral_mono fun x ↦ ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _).trans_lt

/-- Left invariance of `k y` and unfolding over the orbit `D` of `y`, as one statement. Here `i`
maps `Λ` isomorphically onto the discrete subgroup `Γ`, `S` is the image under `i` of the stabiliser
of `y`, and the `k z` are measurable and equivariant. The conclusion has two parts. The first says
that `k y` is left `S`-invariant (`S.FixesLeft (k y)`). The second is the implication proved in
`integral_tsum_orbit_of_lt_top_or_integrable`: if `∑ ‖k z‖` has finite integral over `Γ \ G` or
`k y` is integrable over `S \ G`, then `k y` is integrable over `S \ G`, and its integral equals
both the integral of `∑_D k z` over `Γ \ G` and the sum over `D` of the integrals of the `k z`. -/
lemma New.integral_tsum_orbit (hi : Function.Injective i) {Γ S : Subgroup G}
    [DiscreteTopology Γ] (hΓ : i.range = Γ) {μ : Measure G} [IsHaarMeasure μ] {D : Set Y}
    {k : Y → G → ℂ} (hk_meas : ∀ y : Y, Measurable (k y))
    (hk : ∀ (γ : Λ) (y : Y) (x : G), k (γ • y) (i γ * x) = k y x)
    {y : Y} (h_stab : (stabilizer Λ y).map i = S) (h_orbit : ∀ z : Y, z ∈ D ↔ y ∈ orbit Λ z) :
    S.FixesLeft (k y) ∧
    ((∫⁻ x : G, ∑' z : Y, ‖k z x‖ₑ ∂Γ.quotMeasure μ < ∞ ∨ Integrable (k y) (S.quotMeasure μ)) →
      Integrable (k y) (S.quotMeasure μ) ∧
      ∫ x : G, ∑' z : D, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ ∧
      ∑' z : D, ∫ x : G, k z x ∂Γ.quotMeasure μ = ∫ x : G, k y x ∂S.quotMeasure μ) :=
  ⟨fixesLeft_map_stabilizer hk h_stab,
    integral_tsum_orbit_of_lt_top_or_integrable hi hΓ hk_meas hk h_stab h_orbit⟩

end OrbitUnfolding

/-!
## Iwasawa integration formula

Integration in Iwasawa coordinates on a unimodular group `G = N · i(M) · K`, with `N` closed, `K`
compact and `i : M →* G` continuous. It is used for constant terms along a unipotent radical `N`.
-/

section IwasawaIntegration

open MeasureTheory Measure ENNReal NeZero ProbabilityTheory Function

/-- Let `J f x` be measurable in `x`, and let `J f x₀` be obtained from `J f y` by a finite nonzero
factor that depends on `y` only. Then this factor can be absorbed into a measurable weight: for
measurable `β` there is a measurable `g` with `g y * J f y = β y * J f x₀`. -/
lemma New.exists_measurable_mul_eq_of_scale {X : Type*} [MeasurableSpace X]
    {J : (X → ℝ≥0∞) → X → ℝ≥0∞} {x₀ : X} (hJ : ∀ f : X → ℝ≥0∞, Measurable f → Measurable (J f))
    (h_scale : ∀ y : X, ∃ r : ℝ≥0∞, r ≠ 0 ∧ r ≠ ∞ ∧
      ∀ f : X → ℝ≥0∞, Measurable f → r * J f y = J f x₀)
    {β : X → ℝ≥0∞} (hβ : Measurable β) :
    ∃ g : X → ℝ≥0∞, Measurable g ∧
      ∀ (y : X) (f : X → ℝ≥0∞), Measurable f → g y * J f y = β y * J f x₀ := by
  by_cases! h_const : ∀ (y : X) (f : X → ℝ≥0∞), Measurable f → J f y = J f x₀
  · exact ⟨β, hβ, fun y f hf ↦ by rw [h_const y f hf]⟩
  -- Otherwise some `J f` is everywhere finite and nonzero; the factor at `x` is `J f x₀ / J f x`.
  obtain ⟨y₀, f, hf, h_ne⟩ := h_const
  obtain ⟨r, hr_zero, hr_top, hr⟩ := h_scale y₀
  have h_zero : J f x₀ ≠ 0 := fun h ↦ h_ne (by simpa [h, hr_zero] using hr f hf)
  have h_top : J f x₀ ≠ ∞ := fun h ↦
    h_ne (by simpa [h, hr_zero, hr_top, mul_eq_top] using hr f hf)
  refine ⟨fun x ↦ β x * (J f x₀ / J f x), hβ.mul (measurable_const.div (hJ f hf)),
    fun x φ hφ ↦ ?_⟩
  obtain ⟨s, hs_zero, -, hs⟩ := h_scale x
  have hx_zero : J f x ≠ 0 := fun h ↦ h_zero (by rw [← hs f hf, h, mul_zero])
  have hx_top : J f x ≠ ∞ := fun h ↦ h_top (by rw [← hs f hf, h, mul_top hs_zero])
  have h_div : J f x₀ / J f x = s := by
    rw [← hs f hf, ENNReal.mul_div_cancel_right hx_zero hx_top]
  simp only [h_div, mul_assoc, hs φ hφ]

/-- A function that is integrable for `∞ • q` vanishes `q`-almost everywhere. -/
lemma New.ae_eq_zero_of_integrable_top_smul {X : Type*} [MeasurableSpace X] {q : Measure X}
    {F : X → ℂ} (h_int : Integrable F (∞ • q)) : F =ᵐ[q] 0 := by
  have hF : AEStronglyMeasurable F q :=
    h_int.aestronglyMeasurable.mono_ac (absolutelyContinuous_smul top_ne_zero)
  have h_lt : ∞ * ∫⁻ x, ‖F x‖ₑ ∂q < ∞ := by
    simpa [HasFiniteIntegral] using h_int.hasFiniteIntegral
  have h_norm : ∫⁻ x, ‖F x‖ₑ ∂q = 0 := by simpa [mul_lt_top_iff] using h_lt
  filter_upwards [(lintegral_eq_zero_iff' hF.enorm).1 h_norm] with x hx using by simpa using hx

/-- Division of an integral formula by a factor `c ∈ (0, ∞]` of the measure. For finite nonzero `V`
there is `a ≠ 0` such that, if `F` is measurable and integrable for `c • q` with integral `V * I`,
then `F` is integrable for `q` with integral `a * I`. -/
lemma New.exists_integral_eq_mul_of_smul_measure {X : Type*} [MeasurableSpace X] (q : Measure X)
    {c V : ℝ≥0∞} (hc : c ≠ 0) (hV_zero : V ≠ 0) (hV_top : V ≠ ∞) :
    ∃ a ≠ (0 : ℝ), ∀ (F : X → ℂ) (I : ℂ), Measurable F → Integrable F (c • q) →
      ∫ x : X, F x ∂(c • q) = V.toReal * I → Integrable F q ∧ ∫ x : X, F x ∂q = a * I := by
  have hV : V.toReal ≠ 0 := toReal_ne_zero.2 ⟨hV_zero, hV_top⟩
  rcases eq_or_ne c ∞ with rfl | hc_top
  · -- For `c = ∞`, integrability forces `F = 0` almost everywhere, and both sides vanish.
    refine ⟨1, one_ne_zero, fun F I _ h_int h_eq ↦ ?_⟩
    have hF_zero : F =ᵐ[q] 0 := ae_eq_zero_of_integrable_top_smul h_int
    obtain rfl : I = 0 := by simpa [hV] using h_eq
    exact ⟨(integrable_zero X ℂ q).congr hF_zero.symm, by simp [integral_eq_zero_of_ae hF_zero]⟩
  · have hc_real : c.toReal ≠ 0 := toReal_ne_zero.2 ⟨hc, hc_top⟩
    refine ⟨V.toReal / c.toReal, div_ne_zero hV hc_real,
      fun F I _ h_int h_eq ↦ ⟨(integrable_smul_measure hc hc_top).1 h_int, ?_⟩⟩
    rw [integral_smul_measure, Complex.real_smul] at h_eq
    simp [div_mul_eq_mul_div, ← h_eq, hc_real]

/-- Let `i a` lie in `N` only for `a = 1`, let `δ` be injective, and let `Γ` contain every `i (δ d)`
and lie in the union of the `N · i (δ d)⁻¹`. Then every element of `Γ` is uniquely `i (δ d) * γ`
with `γ ∈ Γ ∩ N`. -/
lemma New.exists_equiv_prod_subgroupOf {G M D : Type*} [Group G] [Group M] {N Γ : Subgroup G}
    {i : M →* G} (h_triv : ∀ a : M, i a ∈ N → a = 1) {δ : D → M} (hδ : δ.Injective)
    (hδ_mem : ∀ d : D, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d : D, g * i (δ d) ∈ N) :
    ∃ e : D × Γ.subgroupOf N ≃ Γ,
      ∀ (d : D) (γ : Γ.subgroupOf N), (e (d, γ) : G) = i (δ d) * (γ : N) := by
  let φ (p : D × Γ.subgroupOf N) : Γ :=
    ⟨i (δ p.1) * (p.2 : N), mul_mem (hδ_mem p.1) (Subgroup.mem_subgroupOf.1 p.2.property)⟩
  refine ⟨.ofBijective φ ⟨?_, fun g ↦ ?_⟩, fun d γ ↦ rfl⟩
  · rintro ⟨d, γ⟩ ⟨d', γ'⟩ h
    have h_eq : i (δ d) * (γ : N) = i (δ d') * (γ' : N) := congrArg Subtype.val h
    have h_mem : i ((δ d)⁻¹ * δ d') ∈ N := by
      simpa [QuotientGroup.eq] using congrArg (QuotientGroup.mk : G → G ⧸ N) h_eq
    obtain rfl : d = d' := hδ (inv_mul_eq_one.1 (h_triv _ h_mem))
    simpa using h_eq
  · obtain ⟨d, h_mem⟩ : ∃ d : D, (g : G)⁻¹ * i (δ d) ∈ N := hΓ _ (inv_mem g.property)
    let γ : Γ.subgroupOf N :=
      ⟨⟨(g : G)⁻¹ * i (δ d), h_mem⟩, mul_mem (inv_mem g.property) (hδ_mem d)⟩
    exact ⟨(d, γ⁻¹), by simp [φ, γ]⟩

variable {G M : Type*} [Group G] [Group M] [TopologicalSpace G] [IsTopologicalGroup G]
  [PolishSpace G] (w : M → ℝ) [MeasurableSpace G] [BorelSpace G] [TopologicalSpace M]
  [IsTopologicalGroup M] [MeasurableSpace M] [BorelSpace M]
  (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ]
  (ν : Measure M) [IsHaarMeasure ν]
  {N K Γ : Subgroup G} [IsMulRightInvariant ν] [CompactSpace K]
  (κ : Measure K) [IsHaarMeasure κ]
  {lam : Measure N} [IsHaarMeasure lam] (i : M →* G)

omit [IsHaarMeasure ν] [IsHaarMeasure lam] in
/-- Let `N` be unimodular, and let conjugation by `i m` multiply integrals over `N` by `w m`. The
integral of `f (i a * u * (n * i m * k) * l⁻¹)` over `K × M × N`, times `w m`, is the integral of
`f (i a * u * l⁻¹)`. -/
lemma New.ofReal_mul_lintegral_iwasawa_translate [IsMulRightInvariant lam]
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    {f : G → ℝ≥0∞} (hf : Measurable f) (n : N) (m : M) (k : K) :
    ENNReal.ofReal (w m) *
        ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * (n * i m * k) * l⁻¹) ∂lam ∂ν ∂κ =
      ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * l⁻¹) ∂lam ∂ν ∂κ := by
  -- Absorb `n` into `u`, move `i m` past `u`, then absorb `m` into `a` and `k` into `l`.
  have h_move (x z : G) : ENNReal.ofReal (w m) * ∫⁻ u : N, f (x * u * (n * i m * k) * z) ∂lam =
      ∫⁻ u : N, f (x * i m * u * (k * z)) ∂lam :=
    calc ENNReal.ofReal (w m) * ∫⁻ u : N, f (x * u * (n * i m * k) * z) ∂lam
      _ = ENNReal.ofReal (w m) * ∫⁻ u : N, f (x * u * i m * (k * z)) ∂lam := by
        rw [← lintegral_mul_right_eq_self (fun u : N ↦ f (x * u * i m * (k * z))) n]
        simp [mul_assoc]
      _ = ∫⁻ u : N, f (x * (i m * u * (i m)⁻¹) * i m * (k * z)) ∂lam :=
        (h_conj m (fun y ↦ f (x * y * i m * (k * z))) (by fun_prop)).symm
      _ = ∫⁻ u : N, f (x * i m * u * (k * z)) ∂lam := by simp [mul_assoc]
  calc
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i (a * m) * u * (k * l⁻¹)) ∂lam ∂ν ∂κ := by
      simp only [← lintegral_const_mul' _ _ ofReal_ne_top, map_mul, ← h_move]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * (k * l⁻¹)) ∂lam ∂ν ∂κ :=
      lintegral_congr fun l ↦
        lintegral_mul_right_eq_self (fun a : M ↦ ∫⁻ u : N, f (i a * u * (k * l⁻¹)) ∂lam) m
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, f (i a * u * l⁻¹) ∂lam ∂ν ∂κ := by
      rw [← lintegral_mul_right_eq_self _ k]
      simp

omit [PolishSpace G] [IsMulRightInvariant ν] [CompactSpace K] in
/-- Suppose that conjugation by `i m` multiplies integrals over `N` by `w m`. The integral of
`g ((i a * u)⁻¹ * (x * l))` over `K × M × N` is the same for `x = n * i m * k` as for `x = 1`. -/
lemma New.lintegral_iwasawa_inv_mul_translate
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    {g : G → ℝ≥0∞} (hg : Measurable g) (n : N) (m : M) (k : K) :
    ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (n * i m * k * l)) ∂lam ∂ν ∂κ =
      ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν ∂κ := by
  -- Move `(i a)⁻¹` past `u⁻¹` to absorb `n` into `u`; then absorb `m` into `a` and `k` into `l`.
  have h_absorb (a : M) (z : G) :
      ∫⁻ u : N, g ((i a * u)⁻¹ * (n * z)) ∂lam = ∫⁻ u : N, g ((i a * u)⁻¹ * z) ∂lam := by
    have h_move (y : G) : ∫⁻ u : N, g ((i a * u)⁻¹ * y) ∂lam =
        ENNReal.ofReal (w a) * ∫⁻ u : N, g ((i a)⁻¹ * ((u : G)⁻¹ * y)) ∂lam := by
      simpa [mul_assoc] using h_conj a (fun x ↦ g ((i a)⁻¹ * (x⁻¹ * y))) (by fun_prop)
    rw [h_move, h_move, ← lintegral_mul_left_eq_self _ n]
    simp [mul_assoc]
  calc
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (i m * (k * l))) ∂lam ∂ν ∂κ := by
      simp only [mul_assoc, h_absorb]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * (k * l)) ∂lam ∂ν ∂κ := by
      refine lintegral_congr fun l ↦ ?_
      rw [← lintegral_mul_left_eq_self _ m]
      simp [mul_assoc]
    _ = ∫⁻ l : K, ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν ∂κ :=
      lintegral_mul_left_eq_self (fun l : K ↦ ∫⁻ a : M, ∫⁻ u : N, g ((i a * u)⁻¹ * l) ∂lam ∂ν) k

variable [LocallyCompactSpace G]

/-- Iwasawa integration formula. Let `G`, `M` and the closed subgroup `N` be unimodular, `K`
compact, and `i : M →* G` and `w : M → ℝ` continuous. Suppose that `G = N · i(M) · K` and that
conjugation by `i m` multiplies integrals over `N` by `w m > 0`. Then the measure `dn dm dk` in the
coordinates `i m * n * k` is `d` times the Haar measure `μ` on `G`, for some `d ∈ [0, ∞]` (`d` may
be infinite, for instance if `i` has noncompact kernel). Here `lam`, `ν`, `κ` are Haar measures on
`N`, `M`, `K`. -/
lemma New.lintegral_iwasawa [PolishSpace M] [LocallyCompactSpace M]
    (hN : IsClosed (N : Set G)) (_hw : Continuous w) (hw_pos : ∀ m : M, 0 < w m) (hi : Continuous i)
    (h_dec : ∀ g : G, ∃ᵉ (n : N) (m : M) (k : K), g = n * i m * k)
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    [IsMulRightInvariant lam] :
    ∃ d : ℝ≥0∞, ∀ f : G → ℝ≥0∞, Measurable f →
      ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ = d * ∫⁻ g : G, f g ∂μ := by
  -- Let `J f y` be the integral of `f (i m * n * y * k⁻¹)`; the left side is `J f 1`. Moving `y`
  -- only divides `J f y` by `w`, so `J f 1 = ∫ g y * J f y` for a suitable weight `g`. After Fubini
  -- and a translation of `y`, this is `∫ d x * f x`, where `d x`, an integral of `g`, is constant.
  obtain ⟨β, hβ, hβ_int⟩ := (inferInstance : HasCutoff μ G).out
  have hβ_one : ∫⁻ x, β x ∂μ = 1 := by simpa using hβ_int 1
  let π : Measure ((M × N) × K) := (ν.prod lam).prod κ
  let b (p : M × N) : G := i p.1 * p.2
  have hπ (φ : G → K → ℝ≥0∞) (hφ : Measurable (uncurry φ)) :
      ∫⁻ h, φ (b h.1) h.2 ∂π = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, φ (i m * n) k ∂lam ∂ν ∂κ := by
    rw [lintegral_prod_symm _ (by fun_prop)]
    exact lintegral_congr fun k ↦ lintegral_prod _ (by fun_prop)
  let J (f : G → ℝ≥0∞) (y : G) : ℝ≥0∞ := ∫⁻ h, f (b h.1 * y * h.2⁻¹) ∂π
  have hJ (f : G → ℝ≥0∞) (hf : Measurable f) (y : G) :
      J f y = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * y * k⁻¹) ∂lam ∂ν ∂κ :=
    hπ (fun x k ↦ f (x * y * k⁻¹)) (by fun_prop)
  have h_scale (y : G) : ∃ r : ℝ≥0∞, r ≠ 0 ∧ r ≠ ∞ ∧
      ∀ f : G → ℝ≥0∞, Measurable f → r * J f y = J f 1 := by
    obtain ⟨n, m, k, rfl⟩ := h_dec y
    refine ⟨.ofReal (w m), (ofReal_pos.2 (hw_pos m)).ne', ofReal_ne_top, fun f hf ↦ ?_⟩
    simpa only [hJ f hf, mul_one] using
      ofReal_mul_lintegral_iwasawa_translate w ν κ i h_conj hf n m k
  -- The weight `g` satisfies `g y * J f y = β y * J f 1`.
  obtain ⟨g, hg, hgJ⟩ := exists_measurable_mul_eq_of_scale (fun f hf ↦ by fun_prop) h_scale hβ
  let d (x : G) : ℝ≥0∞ := ∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) ∂π
  have hd (x : G) : d x = d 1 := by
    obtain ⟨n, m, k, rfl⟩ := h_dec x
    have hd_eq (z : G) := hπ (fun y l ↦ g (y⁻¹ * (z * l))) (by fun_prop)
    simpa only [d, hd_eq, one_mul] using lintegral_iwasawa_inv_mul_translate w ν κ i h_conj hg n m k
  refine ⟨d 1, fun f hf ↦ ?_⟩
  calc ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ
    _ = J f 1 := by
      rw [hJ f hf, ← lintegral_inv_eq_self]
      simp
    _ = ∫⁻ y, g y * J f y ∂μ := by simp [hgJ _ f hf, lintegral_mul_const _ hβ, hβ_one]
    _ = ∫⁻ h, ∫⁻ y, g y * f (b h.1 * y * h.2⁻¹) ∂μ ∂π := by
      simp (disch := fun_prop) only [J, ← lintegral_const_mul]
      exact lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ h, ∫⁻ x, g ((b h.1)⁻¹ * (x * h.2)) * f x ∂μ ∂π := by
      congr with ⟨p, k⟩
      rw [← lintegral_mul_left_eq_self _ (b p)⁻¹, ← lintegral_mul_right_eq_self _ (k : G)]
      simp [mul_assoc]
    _ = ∫⁻ x, ∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) * f x ∂π ∂μ := lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ x, d x * f x ∂μ := lintegral_congr fun x ↦ lintegral_mul_const _ (by fun_prop)
    _ = d 1 * ∫⁻ x, f x ∂μ := by simp_rw [hd, lintegral_const_mul _ hf]

omit [TopologicalSpace M] [IsTopologicalGroup M] [MeasurableSpace M] [BorelSpace M] in
/-- Let `i a` lie in the closed unimodular subgroup `N` only for `a = 1`, let `δ` be injective, and
let the discrete group `Γ` contain every `i (δ d)` and lie in the union of the `N · i (δ d)⁻¹`.
Suppose that conjugation by `i m` multiplies integrals over `N` by `w m`. Then `w m` times the
integral over `(Γ ∩ N) \ N` (that is, against `quotMeasure lam`) of a sum over `Γ` unfolds to a sum
over `d` of integrals over `N` against the Haar measure `lam`. -/
lemma New.ofReal_mul_lintegral_quotMeasure_tsum [IsMulRightInvariant lam]
    (hN : IsClosed (N : Set G))
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {D : Type*} [Countable D] {δ : D → M} (hδ : δ.Injective)
    (hδ_mem : ∀ d : D, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d : D, g * i (δ d) ∈ N) [DiscreteTopology Γ]
    {f : G → ℝ≥0∞} (hf : Measurable f) (m : M) (k : G) :
    ENNReal.ofReal (w m) *
        ∫⁻ n : N, ∑' γ : Γ, f (γ * (n * (i m * k))) ∂(Γ.subgroupOf N).quotMeasure lam =
      ∑' d : D, ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam := by
  -- Write the elements of `Γ` as `i (δ d) * γ` with `γ ∈ Γ ∩ N`, unfold the quotient measure to
  -- `lam`, and move `i m` past `n`.
  obtain ⟨e, he⟩ := exists_equiv_prod_subgroupOf h_triv hδ hδ_mem hΓ
  simp only [← e.tsum_eq, ENNReal.tsum_prod', he]
  rw [lintegral_tsum (by fun_prop), ← ENNReal.tsum_mul_left]
  refine tsum_congr fun d ↦ ?_
  calc ENNReal.ofReal (w m) * ∫⁻ n : N, ∑' γ : Γ.subgroupOf N,
        f (i (δ d) * (γ : N) * (n * (i m * k))) ∂(Γ.subgroupOf N).quotMeasure lam
    _ = ENNReal.ofReal (w m) * ∫⁻ n : N, f (i (δ d) * n * i m * k) ∂lam := by
      rw [← lintegral_orbitMeasure_lintegral (ν := (count : Measure (Γ.subgroupOf N)))
        (f := fun n : N ↦ f (i (δ d) * n * i m * k)) (by fun_prop)]
      simp [lintegral_count, Subgroup.smul_def, mul_assoc]
    _ = ∫⁻ n : N, f (i (δ d) * (i m * n * (i m)⁻¹) * i m * k) ∂lam :=
      (h_conj m (fun y ↦ f (i (δ d) * y * i m * k)) (by fun_prop)).symm
    _ = ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam := by simp [mul_assoc]

/-- Unfolding in Iwasawa coordinates. Let `μ`, `ν`, `κ`, `lam` be Haar measures on the unimodular
group `G`, the unimodular group `M`, the compact subgroup `K` and the closed subgroup `N`, and let
`i` and `w` be continuous. Suppose that `G = N · i(M) · K`, that conjugation by `i m` multiplies
integrals over `N` by `w m > 0`, and that `i a` lies in `N` only for `a = 1`. Let `δ` be injective,
and let `Γ` be discrete, contain every `i (δ d)` and lie in the union of the `N · i (δ d)⁻¹`, with
`Γ ∩ N` cocompact in `N` (`IsCocompact`: every element of `N` has a left translate by `Γ ∩ N` in a
fixed compact set). Let `α` be a measure on `M` that unfolds to `ν` along `δ`. There is `c ≠ 0` such
that for measurable `F`, left invariant under `N` and `Γ` (`FixesLeft`): if
`(m, k) ↦ w m * F (i m * k)` is integrable for `α × κ`, then `F` is integrable over `Γ \ G` (against
`Γ.quotMeasure μ`), and its integral is `c` times the integral of `w m * F (i m * k)`. -/
lemma New.integral_quotMeasure_iwasawa [PolishSpace M] [LocallyCompactSpace M]
    (hN : IsClosed (N : Set G)) (hw : Continuous w) (hw_pos : ∀ m : M, 0 < w m) (hi : Continuous i)
    (h_dec : ∀ g : G, ∃ᵉ (n : N) (m : M) (k : K), g = n * i m * k)
    (h_conj : ∀ (m : M) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ n : N, f (i m * n * (i m)⁻¹) ∂lam = ENNReal.ofReal (w m) * ∫⁻ n : N, f n ∂lam)
    (h_triv : ∀ a : M, i a ∈ N → a = 1) {D : Type*}
    [Countable D] {δ : D → M} (hδ : δ.Injective) (α : Measure M) [SFinite α]
    (hα : ∀ f : M → ℝ≥0∞, Measurable f → ∫⁻ m : M, f m ∂ν = ∫⁻ m : M, ∑' d : D, f (δ d * m) ∂α)
    (hδ_mem : ∀ d : D, i (δ d) ∈ Γ) (hΓ : ∀ g ∈ Γ, ∃ d : D, g * i (δ d) ∈ N) [DiscreteTopology Γ]
    (h_cocpt : (Γ.subgroupOf N).IsCocompact) :
    ∃ c ≠ (0 : ℝ), ∀ F : G → ℂ, Measurable F → N.FixesLeft F → Γ.FixesLeft F →
      Integrable (fun p : M × K ↦ (w p.1 : ℂ) * F (i p.1 * p.2)) (α.prod κ) →
      Integrable F (Γ.quotMeasure μ) ∧
      ∫ g : G, F g ∂Γ.quotMeasure μ =
        c * ∫ p : M × K, (w p.1 : ℂ) * F (i p.1 * p.2) ∂α.prod κ := by
  -- The Iwasawa formula with factor `r`, unfolded along `Γ = {i (δ d) * γ}`, says that the measure
  -- `w · (α × κ) × (Γ ∩ N)\N` in the coordinates `n * i m * k` is the quotient of `r • μ` by `Γ`.
  -- The cocompact subgroup `Γ ∩ N` is a lattice in `N`, so `N` is unimodular.
  let lam' : Measure N := (Γ.subgroupOf N).quotMeasure lam
  have h_finite : IsFiniteMeasure lam' := isFiniteMeasure_quotMeasure_of_cocompact lam h_cocpt
  have : lam.IsMulRightInvariant := isMulRightInvariant_of_finite_covolume h_finite
  obtain ⟨r, h_iwa⟩ := lintegral_iwasawa (lam := lam) w μ ν κ i hN hw hw_pos hi h_dec h_conj
  -- For `f = 1` the left side of `h_iwa` is a product of nonzero total masses.
  have hr : r ≠ 0 := fun h ↦ by simpa [h, NeZero.ne] using h_iwa 1 measurable_one
  have hw_meas : Measurable fun p : M × K ↦ ENNReal.ofReal (w p.1) := by fun_prop
  let ρ : Measure (M × K) := (α.prod κ).withDensity fun p ↦ .ofReal (w p.1)
  let σ (p : M × K) : G := i p.1 * p.2
  let τ (p : (M × K) × N) : G := p.2 * σ p.1
  have h_unfold : MeasurePreserving (fun p : ((M × K) × N) × Γ ↦ p.2 • τ p.1)
      ((ρ.prod lam').prod count) (r • μ) := by
    refine ⟨by fun_prop, ext_of_lintegral _ fun f hf ↦ ?_⟩
    calc
      _ = ∫⁻ p : M × K, ∫⁻ n : N, ∑' γ : Γ, f (γ * (n * (i p.1 * p.2))) ∂lam' ∂ρ := by
        simp (disch := fun_prop) only [lintegral_map, lintegral_prod, lintegral_count,
          Subgroup.smul_def, smul_eq_mul, τ, σ]
      _ = ∫⁻ k : K, ∫⁻ m : M, ∑' d : D, ∫⁻ n : N, f (i (δ d * m) * n * k) ∂lam ∂α ∂κ := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hw_meas (by fun_prop),
          lintegral_prod_symm _ (by fun_prop)]
        simp only [Pi.mul_apply, lam',
          ofReal_mul_lintegral_quotMeasure_tsum w i hN h_conj h_triv hδ hδ_mem hΓ hf]
      _ = ∫⁻ k : K, ∫⁻ m : M, ∫⁻ n : N, f (i m * n * k) ∂lam ∂ν ∂κ :=
        lintegral_congr fun k ↦ (hα (fun m ↦ ∫⁻ n : N, f (i m * n * k) ∂lam) (by fun_prop)).symm
      _ = ∫⁻ g, f g ∂(r • μ) := by rw [h_iwa f hf, lintegral_smul_measure, smul_eq_mul]
  obtain ⟨c, hc, h_div⟩ := exists_integral_eq_mul_of_smul_measure (Γ.quotMeasure μ) hr
    (NeZero.ne (lam' .univ)) (measure_ne_top lam' .univ)
  refine ⟨c, hc, fun F hF hFN hFΓ h_weighted ↦ ?_⟩
  -- By `h_unfold`, `F` on `Γ \ G` has the law of `F ∘ τ`, and `F ∘ τ` does not depend on `n`.
  have hFτ (p : (M × K) × N) : F (τ p) = F (σ p.1) := hFN p.2 p.2.property (σ p.1)
  have h_law : IdentDistrib F (fun p : M × K ↦ F (σ p)) (r • Γ.quotMeasure μ)
      (lam' .univ • ρ) := by
    rw [← show Γ.quotMeasure (r • μ) = r • Γ.quotMeasure μ from withDensity_smul_measure r _]
    refine (identDistrib_orbitMeasure_of_unfold (T := τ) (.id (count : Measure Γ)) h_unfold hF
      (by fun_prop) fun γ x ↦ hFΓ γ γ.property x).trans ⟨by fun_prop, by fun_prop, ?_⟩
    simp (disch := fun_prop) only [hFτ, ← map_fst_prod, map_map, comp_def]
  have h_int : Integrable (fun p : M × K ↦ F (σ p)) ρ := by
    simpa [ρ, σ, integrable_withDensity_iff_integrable_smul' hw_meas, hw_pos, le_of_lt]
      using h_weighted
  refine h_div F _ hF (h_law.integrable_iff.2 (h_int.smul_measure (measure_ne_top lam' .univ))) ?_
  rw [h_law.integral_eq, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hw_meas (by simp)]
  simp [σ, hw_pos, le_of_lt]
end IwasawaIntegration
