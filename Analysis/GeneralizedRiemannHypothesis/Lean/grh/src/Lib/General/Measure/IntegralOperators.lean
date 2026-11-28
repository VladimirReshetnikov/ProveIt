import Lib.Adelic.QuotientMeasure.Basic

/-!
# Product measures, layer cake bounds, cocompact subgroups and L² bounds of integral operators

This file rearranges the coordinates of finite powers of a σ-finite measure space, bounds integrals
of negative powers under polynomial volume growth by a layer cake argument, shows that continuous
functions on a group G that are left invariant under a cocompact subgroup Γ are integrable for
finite measures on G, and passes L² bounds of integral operators with measurable, integrable kernels
to finite products. It also contains Tonelli's theorem for finite products, products of cocompact
subgroups, and two small constructions, `New.padTuple` and `New.unitOrOne`.

Among the imported notions in the statements are `Subgroup.FixesLeft Γ F`, meaning `F (γ g) = F g`
for `γ ∈ Γ`, and the following.

* `Subgroup.IsCocompact Γ`: some compact set `C ⊆ G` meets every orbit `Γg`.

## Main definitions and results

* `New.lintegral_rpow_neg_le_of_measure_sublevel_le`: if the sublevel sets `{u ≤ R}` of a measurable
  function `u ≥ 1` have measure at most `(K R^e)^d V`, with `K ≥ 0`, then the integral of `u^(-A)`
  has an explicit bound for `A > e d`. The measure is arbitrary, so the result also bounds sums
  (counting measure). For finite `V`, `New.integrable_rpow_neg_of_measure_sublevel_le` and
  `New.integral_rpow_neg_le_of_measure_sublevel_le` are the forms for the Bochner integral;
  `New.DiscreteSeries.integral_rpow_neg_le_of_measure_le` joins them.
* `New.integrable_of_isCocompact`: continuous left Γ-invariant functions are integrable for finite
  measures on G.
* `New.IsL2Contraction`: a finite family of kernels defines an operator of norm at most one between
  two `L²` spaces, tested on bounded measurable functions. By `New.IsL2Contraction.pi`, the bound
  passes to the product of finitely many such families, for σ-finite measures and measurable kernels
  that are integrable in the last variable.
-/

/-! ## Regrouping, currying and flipping coordinates of product measures -/

section ProductMeasure

open MeasureTheory Sigma

variable {Y ι κ : Type*} {α : Type*} {n : ι → Type*} [Fintype Y] [Fintype ι] [Fintype κ]
  [∀ i : ι, Fintype (n i)] [MeasureSpace α] [SigmaFinite (volume : Measure α)]

/-- For a bijection `e` from the disjoint union of the finite types `n i` onto `Y`, the regrouping
map `α^Y → ∏ i, α^(n i)`, `x ↦ (x (e ⟨i, j⟩))_{i, j}`, preserves the product volume measures. -/
lemma New.measurePreserving_sigma (e : Sigma n ≃ Y) :
    MeasurePreserving fun (x : Y → α) (i : ι) (j : n i) ↦ x (e ⟨i, j⟩) := by
  -- The map is reindexing along `e` followed by currying, which preserves the volumes of boxes.
  have h_uncurry :
      MeasurePreserving (MeasurableEquiv.piCurry fun (i : ι) (_ : n i) ↦ α).symm := by
    refine ⟨by fun_prop, .symm (Measure.pi_eq fun s _ ↦ ?_)⟩
    have h_box : (uncurry : ((i : ι) → n i → α) → Sigma n → α) ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i : ι ↦ Set.univ.pi fun j : n i ↦ s ⟨i, j⟩ :=
      Set.ext fun x ↦ by simp [Sigma.forall, uncurry]
    rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_piCurry_symm, h_box]
    simp only [volume_pi_pi, Fintype.prod_sigma]
  exact h_uncurry.symm.comp (volume_measurePreserving_piCongrLeft (fun _ : Y ↦ α) e).symm

/-- Currying, `α^(ι × κ) → (α^κ)^ι`, preserves the product volume measures. -/
lemma New.measurePreserving_curry : MeasurePreserving (MeasurableEquiv.curry ι κ α) :=
  measurePreserving_sigma (.sigmaEquivProd ι κ)

/-- Exchanging the two indices, `(α^κ)^ι → (α^ι)^κ`, preserves the product volume measures. -/
lemma New.measurePreserving_flip : MeasurePreserving (flip : (ι → κ → α) → κ → ι → α) :=
  -- Uncurry, then curry again with the two indices swapped.
  (measurePreserving_sigma ((Equiv.sigmaEquivProd κ ι).trans (.prodComm κ ι))).comp
    measurePreserving_curry.symm

end ProductMeasure

/-! ## A layer cake bound for negative powers -/

section LayerCake

open MeasureTheory Set Real Filter

variable {S : Type*} [MeasurableSpace S] {ν : Measure S} {u : S → ℝ} {K A c : ℝ} {e d : ℕ}
  {V : ENNReal}

/-- For an exponent `p > 0`, the Lebesgue integral of `t^(p-1)` over `(0, 1]` is `1/p`. -/
lemma New.lintegral_Ioc_rpow_sub_one {p : ℝ} (hp : 0 < p) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (p - 1)) = ENNReal.ofReal p⁻¹ := by
  have h_exp : -1 < p - 1 := by linarith
  have h_value : ∫ t in (0 : ℝ)..1, t ^ (p - 1) = p⁻¹ := by
    simp [integral_rpow (.inl h_exp), zero_rpow hp.ne']
  rw [← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_rpow' h_exp).1
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ rpow_nonneg ht.1.le (p - 1)),
    ← intervalIntegral.integral_of_le zero_le_one, h_value]

/-- Layer cake bound for a negative power. Let `u ≥ 1` be measurable and suppose that
`ν {u ≤ R} ≤ (K R^e)^d V` for all `R ≥ 1`, where `K ≥ 0`. If `e d < A` and `A ≤ c (A - e d)`, then
the Lebesgue integral of `u^(-A)` is at most `K^d c V`. -/
lemma New.lintegral_rpow_neg_le_of_measure_sublevel_le (hu_meas : Measurable u)
    (hu : ∀ s : S, 1 ≤ u s) (hK : 0 ≤ K)
    (h_vol : ∀ R ≥ (1 : ℝ), ν {s : S | u s ≤ R} ≤ ENNReal.ofReal ((K * R ^ e) ^ d) * V)
    (hA : e * d < A) (hc : A ≤ c * (A - e * d)) :
    ∫⁻ s : S, ENNReal.ofReal (u s ^ (-A)) ∂ν ≤ ENNReal.ofReal (K ^ d * c) * V := by
  -- Layer cake: ∫ u^(-A) = A ∫ ν{t ≤ u⁻¹} t^(A-1) dt ≤ c p ∫ g = c p M / p = c M, where M = K^d V,
  -- p = A - e d, and g(t) = M t^(p-1) on (0, 1], 0 beyond, bounds the integrand.
  have hA_pos : 0 < A := (show (0 : ℝ) ≤ e * d by positivity).trans_lt hA
  have hc_nonneg : 0 ≤ c := by nlinarith
  let p : ℝ := A - e * d
  let M : ENNReal := .ofReal (K ^ d) * V
  have hp : 0 < p := sub_pos.2 hA
  let g : ℝ → ENNReal := (Iic 1).indicator fun t : ℝ ↦ M * .ofReal (t ^ (p - 1))
  have h_layer (t : ℝ) (ht : 0 < t) : ν {s : S | t ≤ (u s)⁻¹} * .ofReal (t ^ (A - 1)) ≤ g t := by
    by_cases h_le : t ≤ 1
    · have h_set : {s : S | t ≤ (u s)⁻¹} = {s : S | u s ≤ t⁻¹} :=
        Set.ext fun s ↦ le_inv_comm₀ ht (one_pos.trans_le (hu s))
      have h_pow : (K * t⁻¹ ^ e) ^ d * t ^ (A - 1) = K ^ d * t ^ (p - 1) := by
        rw [sub_right_comm, rpow_sub ht (A - 1), ← Nat.cast_mul, rpow_natCast]
        ring
      calc ν {s : S | t ≤ (u s)⁻¹} * .ofReal (t ^ (A - 1))
          ≤ .ofReal ((K * t⁻¹ ^ e) ^ d) * V * .ofReal (t ^ (A - 1)) := by
            grw [h_set, h_vol t⁻¹ ((one_le_inv₀ ht).2 h_le)]
        _ = M * .ofReal (t ^ (p - 1)) := by
            rw [mul_right_comm, ← ENNReal.ofReal_mul (by positivity), h_pow,
              ENNReal.ofReal_mul (by positivity), mul_right_comm]
        _ = g t := by simp [g, h_le]
    · -- the level set is empty, since u⁻¹ ≤ 1 < t
      have h_set : {s : S | t ≤ (u s)⁻¹} = ∅ :=
        eq_empty_of_forall_notMem fun s hs ↦ h_le (hs.trans (inv_le_one_of_one_le₀ (hu s)))
      simp [h_set]
  calc ∫⁻ s : S, .ofReal (u s ^ (-A)) ∂ν
      = ∫⁻ s : S, .ofReal ((u s)⁻¹ ^ A) ∂ν := by simp only [rpow_neg_eq_inv_rpow]
    _ = .ofReal A * ∫⁻ t in Ioi 0, ν {s : S | t ≤ (u s)⁻¹} * .ofReal (t ^ (A - 1)) :=
        lintegral_rpow_eq_lintegral_meas_le_mul ν
          (.of_forall fun s ↦ inv_nonneg.2 (zero_le_one.trans (hu s)))
          hu_meas.inv.aemeasurable hA_pos
    _ ≤ .ofReal (c * p) * ∫⁻ t in Ioi 0, g t := by
        grw [← hc, setLIntegral_mono' measurableSet_Ioi h_layer]
    _ = .ofReal (c * p) * (M * .ofReal p⁻¹) := by
        rw [setLIntegral_indicator measurableSet_Iic, inter_comm, Ioi_inter_Iic,
          lintegral_const_mul _ (by fun_prop), New.lintegral_Ioc_rpow_sub_one hp]
    _ = .ofReal (K ^ d * c) * V := by
        rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel_right₀ hp.ne',
          mul_right_comm, ← ENNReal.ofReal_mul (by positivity)]

/-- Let `u ≥ 1` be measurable and suppose that `ν {u ≤ R} ≤ (K R^e)^d V` for all `R ≥ 1`, where
`K ≥ 0` and `V` is finite. Then `u^(-A)` is integrable for `A > e d`. -/
lemma New.integrable_rpow_neg_of_measure_sublevel_le (hu_meas : Measurable u)
    (hu : ∀ s : S, 1 ≤ u s) (hK : 0 ≤ K) (hV : V ≠ ⊤)
    (h_vol : ∀ R ≥ (1 : ℝ), ν {s : S | u s ≤ R} ≤ ENNReal.ofReal ((K * R ^ e) ^ d) * V)
    (hA : e * d < A) :
    Integrable (fun s : S ↦ u s ^ (-A)) ν := by
  -- The layer cake bound with `c = A / (A - e d)` is finite.
  have h_le : ∫⁻ s : S, .ofReal (u s ^ (-A)) ∂ν ≤ .ofReal (K ^ d * (A / (A - e * d))) * V :=
    lintegral_rpow_neg_le_of_measure_sublevel_le hu_meas hu hK h_vol hA
      (div_mul_cancel₀ A (sub_pos.2 hA).ne').ge
  refine ⟨(hu_meas.pow_const (-A)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (.of_forall fun s ↦ rpow_nonneg (zero_le_one.trans (hu s)) (-A))]
  exact h_le.trans_lt (by finiteness)

/-- Let `u ≥ 1` be measurable and suppose that `ν {u ≤ R} ≤ (K R^e)^d V` for all `R ≥ 1`, where
`K ≥ 0` and `V` is finite. If `e d < A` and `A ≤ c (A - e d)`, then `∫ u^(-A) dν ≤ K^d c V`. -/
lemma New.integral_rpow_neg_le_of_measure_sublevel_le (hu_meas : Measurable u)
    (hu : ∀ s : S, 1 ≤ u s) (hK : 0 ≤ K) (hV : V ≠ ⊤)
    (h_vol : ∀ R ≥ (1 : ℝ), ν {s : S | u s ≤ R} ≤ ENNReal.ofReal ((K * R ^ e) ^ d) * V)
    (hA : e * d < A) (hc : A ≤ c * (A - e * d)) :
    ∫ s : S, u s ^ (-A) ∂ν ≤ K ^ d * c * V.toReal := by
  have hc_nonneg : 0 ≤ c := by nlinarith [show (0 : ℝ) ≤ e * d by positivity]
  calc ∫ s : S, u s ^ (-A) ∂ν = (∫⁻ s : S, .ofReal (u s ^ (-A)) ∂ν).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (.of_forall fun s ↦ rpow_nonneg (zero_le_one.trans (hu s)) (-A))
          (hu_meas.pow_const (-A)).aestronglyMeasurable
    _ ≤ (ENNReal.ofReal (K ^ d * c) * V).toReal :=
        ENNReal.toReal_mono (by finiteness)
          (lintegral_rpow_neg_le_of_measure_sublevel_le hu_meas hu hK h_vol hA hc)
    _ = K ^ d * c * V.toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- Let `u ≥ 1` be measurable and suppose that `ν {u ≤ R} ≤ (K R^e)^d V` for all `R ≥ 1`, where
`K ≥ 0` and `V` is finite. If `e d < A` and `A ≤ c (A - e d)`, then `u^(-A)` is integrable and
`∫ u^(-A) dν ≤ K^d c V`. -/
lemma New.DiscreteSeries.integral_rpow_neg_le_of_measure_le {ν : Measure S} {u : S → ℝ} {K A c : ℝ}
    {e d : ℕ} {V : ENNReal} (hu_meas : Measurable u) (hu : ∀ s : S, 1 ≤ u s) (hK : 0 ≤ K)
    (hV : V ≠ ⊤) (h_vol : ∀ R ≥ (1 : ℝ), ν {s : S | u s ≤ R} ≤ ENNReal.ofReal ((K * R ^ e) ^ d) * V)
    (hA : e * d < A) (hc : A ≤ c * (A - e * d)) :
    Integrable (fun s : S ↦ u s ^ (-A)) ν ∧ ∫ s : S, u s ^ (-A) ∂ν ≤ K ^ d * c * V.toReal :=
  ⟨integrable_rpow_neg_of_measure_sublevel_le hu_meas hu hK hV h_vol hA,
    integral_rpow_neg_le_of_measure_sublevel_le hu_meas hu hK hV h_vol hA hc⟩

end LayerCake

/-! ## Cocompact subgroups -/

section CocompactIntegrable

open MeasureTheory

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  {Γ : Subgroup G}

/-- If the subgroup `Γ` of `G` is cocompact (some compact set meets every orbit `Γg`), then a
continuous function `F : G → ℂ` with `F (γ g) = F g` for `γ ∈ Γ` is integrable for every finite
measure on `G`. -/
lemma New.integrable_of_isCocompact (hΓ : Γ.IsCocompact) [MeasurableSpace G]
    [OpensMeasurableSpace G]
    {μ : Measure G} [IsFiniteMeasure μ] {F : G → ℂ} (hF_cont : Continuous F)
    (hF_inv : Γ.FixesLeft F) :
    Integrable F μ := by
  -- By invariance every value of `F` is taken on the compact set `C`, where `‖F‖` is bounded.
  obtain ⟨C, hC, h_cover⟩ := hΓ
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF_cont.continuousOn
  refine .of_bound (by fun_prop) M (.of_forall fun g ↦ ?_)
  obtain ⟨γ, hγ, h_mem⟩ := h_cover g
  rw [← hF_inv γ hγ g]
  exact hM (γ * g) h_mem

/-- If `Γ ≤ G` and `Δ ≤ H` are cocompact (some compact set meets every orbit of left
multiplication), then `Γ × Δ` is cocompact in `G × H`. -/
lemma New.isCocompact_prod {Δ : Subgroup H} (hΓ : Γ.IsCocompact) (hΔ : Δ.IsCocompact) :
    (Γ.prod Δ).IsCocompact := by
  -- The product of the two compact sets meets every orbit.
  obtain ⟨C, hC, hC_cover⟩ := hΓ
  obtain ⟨D, hD, hD_cover⟩ := hΔ
  refine ⟨C ×ˢ D, hC.prod hD, fun ⟨g, h⟩ ↦ ?_⟩
  obtain ⟨γ, hγ, hγg⟩ := hC_cover g
  obtain ⟨δ, hδ, hδh⟩ := hD_cover h
  exact ⟨(γ, δ), Subgroup.mem_prod.2 ⟨hγ, hδ⟩, Set.mk_mem_prod hγg hδh⟩

end CocompactIntegrable

/-! ## Tonelli for products, L² contractions, padded tuples and units -/

section IntegralOperators

open MeasureTheory Measure Fin Fintype

namespace New

variable {V Y X I A : Type*} [MeasurableSpace Y] {μ : Measure Y} [NormedAddCommGroup V]
  [NormedSpace ℝ V] [MeasurableSpace X] [Monoid A]

/-- Tonelli's theorem for a finite product: the integral of `∏ i, f i (x i)` over the product
measure is the product of the integrals, for σ-finite measures and measurable `f i` with values
in `[0, ∞]`. -/
lemma lintegral_pi_prod {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i : ι, MeasurableSpace (X i)]
    (μ : ∀ i : ι, Measure (X i)) [∀ i : ι, SigmaFinite (μ i)] {f : ∀ i : ι, X i → ENNReal}
    (hf : ∀ i : ι, Measurable (f i)) :
    ∫⁻ x : (i : ι) → X i, ∏ i : ι, f i (x i) ∂Measure.pi μ = ∏ i : ι, ∫⁻ x : X i, f i x ∂μ i := by
  classical
  rcases isEmpty_or_nonempty ((i : ι) → X i) with h_empty | ⟨⟨x₀⟩⟩
  · -- some factor `X i` is empty, and both sides vanish
    obtain ⟨i, hi⟩ := isEmpty_pi.1 h_empty
    rw [lintegral_of_isEmpty, Finset.prod_eq_zero (Finset.mem_univ i) (lintegral_of_isEmpty _ _)]
  -- Integrate out one coordinate at a time: induction on the set `s` of factors. The coordinates
  -- outside `s` are held at the point `x₀`.
  have h_marginal (s : Finset ι) :
      (∫⋯∫⁻_s, (fun x : (j : ι) → X j ↦ ∏ i ∈ s, f i (x i)) ∂μ) x₀ =
        ∏ i ∈ s, ∫⁻ x : X i, f i x ∂μ i := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      -- integrate over `x i` first: the other factors do not depend on it and come out
      have h_inner (x : (j : ι) → X j) :
          ∫⁻ t : X i, ∏ j ∈ insert i s, f j (Function.update x i t j) ∂μ i =
            (∫⁻ t : X i, f i t ∂μ i) * ∏ j ∈ s, f j (x j) := by
        simp +contextual [Finset.prod_insert hi, Function.update_of_ne,
          ne_of_mem_of_not_mem _ hi, lintegral_mul_const _ (hf i)]
      rw [lmarginal_insert' _ (by fun_prop) hi, Finset.prod_insert hi, ← ih]
      simp only [h_inner]
      exact lintegral_const_mul _ (by fun_prop)
  rw [lintegral_eq_lmarginal_univ x₀, h_marginal]

/-- The bound `‖x.toReal • v‖ₑ ≤ x * ‖v‖ₑ`; for `x = ∞` the left side is `0`. -/
lemma enorm_toReal_smul_le (x : ENNReal) (v : V) : ‖x.toReal • v‖ₑ ≤ x * ‖v‖ₑ := by
  cases x with
  | top => simp
  | coe r => simp [enorm_smul]

/-- Let `φ` be measurable with values in `[0, ∞]` and `F` almost everywhere strongly measurable.
If `∫⁻ φ ‖F‖` is finite, then `φ • F` is integrable (`φ = ∞` is read as `0`). -/
lemma integrable_toReal_smul {φ : Y → ENNReal} {F : Y → V} (hφ : Measurable φ)
    (hF : AEStronglyMeasurable F μ) (h_fin : ∫⁻ y : Y, φ y * ‖F y‖ₑ ∂μ < ⊤) :
    Integrable (fun y : Y ↦ (φ y).toReal • F y) μ :=
  ⟨hφ.ennreal_toReal.aestronglyMeasurable.smul hF,
    (lintegral_mono fun y ↦ enorm_toReal_smul_le (φ y) (F y)).trans_lt h_fin⟩

/-- If `f` is jointly measurable in `(x, y)` and `μ` is s-finite, then `x ↦ ∫ y, f x y ∂μ` is
measurable. -/
@[fun_prop]
lemma measurable_integral [SFinite μ] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    {f : X → Y → V} (hf : Measurable ↿f) :
    Measurable fun x : X ↦ ∫ y : Y, f x y ∂μ :=
  hf.stronglyMeasurable.integral_prod_right.measurable

/-! ### `L²` bounds of integral operators -/

/-- The finite family of kernels `k i : X → Y → ℂ`, integrated against `μ`, satisfies the bound
`∫ ∑ᵢ |∫ φ(y) kᵢ(x, y) dμ(y)|² dm(x) ≤ ∫ |φ|² dn` for every bounded measurable `φ : Y → ℂ`.
For measurable kernels that are integrable in `y`, this says that the integral operator from
`L²(Y, n)` to `L²(X, m)^I` has norm at most one on bounded functions. -/
def IsL2Contraction [Fintype I] (m : Measure X) (μ n : Measure Y) (k : I → X → Y → ℂ) : Prop :=
  ∀ (φ : Y → ℂ) (C : ℝ), Measurable φ → (∀ y : Y, ‖φ y‖ ≤ C) →
    ∫⁻ x : X, ∑ i : I, ‖∫ y : Y, φ y * k i x y ∂μ‖ₑ ^ 2 ∂m ≤ ∫⁻ y : Y, ‖φ y‖ₑ ^ 2 ∂n

/-- Let `k` and `k'` be finite families of measurable kernels, integrable in the last variable
against `μ` and `μ'`, each satisfying `IsL2Contraction`. For `k` this means
`∫ ∑ i, |∫ φ y * k i x y dμ|² dm ≤ ∫ |φ|² dn` for every bounded measurable `φ`. Then, for s-finite
measures, the family of products `k i x y * k' i' x' y'`, indexed by `I × I'`, satisfies the same
bound for the product measures `m.prod m'`, `μ.prod μ'` and `n.prod n'`. -/
lemma IsL2Contraction.prod {X' Y' I' : Type*} [MeasurableSpace X'] [MeasurableSpace Y'] [Fintype I]
    [Fintype I'] {m : Measure X} {m' : Measure X'} {n : Measure Y} {μ' n' : Measure Y'} [SFinite m]
    [SFinite m'] [SFinite μ] [SFinite μ'] [SFinite n] [SFinite n'] {k : I → X → Y → ℂ}
    {k' : I' → X' → Y' → ℂ} (hk : ∀ i : I, Measurable ↿(k i)) (hk' : ∀ i : I', Measurable ↿(k' i))
    (hi : ∀ (i : I) (x : X), Integrable (k i x) μ)
    (hi' : ∀ (i : I') (x : X'), Integrable (k' i x) μ') (h : IsL2Contraction m μ n k)
    (h' : IsL2Contraction m' μ' n' k') :
    IsL2Contraction (m.prod m') (μ.prod μ') (n.prod n')
      fun (i : I × I') (x : X × X') (y : Y × Y') ↦ k i.1 x.1 y.1 * k' i.2 x.2 y.2 := by
  intro φ C hφ hC
  -- `ψ i x` is `φ` with the first operator applied in the first variable; it is again bounded.
  let ψ (i : I) (x : X) (y' : Y') : ℂ := ∫ y : Y, φ (y, y') * k i x y ∂μ
  have hψ (i : I) (x : X) (y' : Y') : ‖ψ i x y'‖ ≤ ∫ y : Y, C * ‖k i x y‖ ∂μ :=
    norm_integral_le_of_norm_le ((hi i x).norm.const_mul C)
      (.of_forall fun y ↦ by grw [norm_mul, hC])
  have h_fubini (i : I) (i' : I') (x : X × X') :
      ∫ y : Y × Y', φ y * (k i x.1 y.1 * k' i' x.2 y.2) ∂μ.prod μ' =
        ∫ y' : Y', ψ i x.1 y' * k' i' x.2 y' ∂μ' := by
    rw [integral_prod_symm _
      (((hi i x.1).mul_prod (hi' i' x.2)).bdd_mul hφ.aestronglyMeasurable (.of_forall hC))]
    simp only [ψ, ← mul_assoc, integral_mul_const]
  simp only [h_fubini, sum_prod_type]
  -- Apply `h'` to each `ψ i x`, exchange the integrals, and apply `h` to each `φ (·, y')`.
  calc ∫⁻ x : X × X', ∑ i : I, ∑ i' : I',
        ‖∫ y' : Y', ψ i x.1 y' * k' i' x.2 y' ∂μ'‖ₑ ^ 2 ∂m.prod m'
    _ ≤ ∫⁻ x, ∫⁻ x', ∑ i, ∑ i', ‖∫ y', ψ i x y' * k' i' x' y' ∂μ'‖ₑ ^ 2 ∂m' ∂m :=
      lintegral_prod_le _
    _ = ∫⁻ x, ∑ i, ∫⁻ x', ∑ i', ‖∫ y', ψ i x y' * k' i' x' y' ∂μ'‖ₑ ^ 2 ∂m' ∂m :=
      lintegral_congr fun x ↦ lintegral_finsetSum _ (by fun_prop)
    _ ≤ ∫⁻ x, ∑ i, ∫⁻ y', ‖ψ i x y'‖ₑ ^ 2 ∂n' ∂m :=
      lintegral_mono fun x ↦ Finset.sum_le_sum fun i _ ↦
        h' (ψ i x) (∫ y : Y, C * ‖k i x y‖ ∂μ) (by fun_prop) (hψ i x)
    _ = ∫⁻ x, ∫⁻ y', ∑ i, ‖ψ i x y'‖ₑ ^ 2 ∂n' ∂m :=
      lintegral_congr fun x ↦ (lintegral_finsetSum _ (by fun_prop)).symm
    _ = ∫⁻ y', ∫⁻ x, ∑ i, ‖ψ i x y'‖ₑ ^ 2 ∂m ∂n' := lintegral_lintegral_swap (by fun_prop)
    _ ≤ ∫⁻ y', ∫⁻ y, ‖φ (y, y')‖ₑ ^ 2 ∂n ∂n' :=
      lintegral_mono fun y' ↦ h (fun y ↦ φ (y, y')) C (by fun_prop) fun y ↦ hC (y, y')
    _ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂n.prod n' :=
      (lintegral_prod_symm (fun y ↦ ‖φ y‖ₑ ^ 2) (by fun_prop)).symm

/-- The bound `New.IsL2Contraction` is unchanged by renaming the indices of the family and by
measure preserving measurable equivalences in the two variables. -/
lemma IsL2Contraction.of_comp_equiv {X' Y' I' : Type*} [MeasurableSpace X'] [MeasurableSpace Y']
    [Fintype I] [Fintype I'] {m : Measure X} {m' : Measure X'} {n : Measure Y} {μ' n' : Measure Y'}
    {k : I → X → Y → ℂ} {k' : I' → X' → Y' → ℂ} (EI : I' ≃ I) {EX : X' ≃ᵐ X} {EY : Y' ≃ᵐ Y}
    (hm : MeasurePreserving EX m' m) (hμ : MeasurePreserving EY μ' μ)
    (hn : MeasurePreserving EY n' n)
    (h_kernel : ∀ (i : I') (x : X') (y : Y'), k (EI i) (EX x) (EY y) = k' i x y)
    (h : IsL2Contraction m' μ' n' k') :
    IsL2Contraction m μ n k := by
  intro φ C hφ hC
  -- After the changes of variables this is the bound for `k'`, applied to `φ ∘ EY`.
  simp only [← hm.map_eq, ← hμ.map_eq, ← hn.map_eq, lintegral_map_equiv, integral_map_equiv,
    ← EI.sum_comp, h_kernel]
  exact h (fun y ↦ φ (EY y)) C (by fun_prop) fun y ↦ hC (EY y)

/-- The case of `New.IsL2Contraction.pi` in which the factors are indexed by `Fin N`. Suppose that,
for each `j`, the finite family of kernels `k j i : X → Y → ℂ` is jointly measurable, integrable in
`y` against `μ j`, and an L² contraction for the σ-finite measures `m j`, `μ j`, `n j`; an L²
contraction means `∫ ∑ᵢ |∫ φ(y) kᵢ(x, y) dμ(y)|² dm(x) ≤ ∫ |φ|² dn` for every bounded measurable
`φ`. Then the product kernels `(x, y) ↦ ∏ j, k j (i j) (x j) (y j)`, indexed by `i : ∀ j, I j`, form
an L² contraction for `Measure.pi m`, `Measure.pi μ`, `Measure.pi n`. -/
lemma IsL2Contraction.pi_fin {N : ℕ} {I : Fin N → Type*} [∀ j : Fin N, Fintype (I j)]
    {m : Fin N → Measure X} {μ n : Fin N → Measure Y} [∀ j : Fin N, SigmaFinite (m j)]
    [∀ j : Fin N, SigmaFinite (μ j)] [∀ j : Fin N, SigmaFinite (n j)]
    {k : ∀ j : Fin N, I j → X → Y → ℂ} (hk : ∀ (j : Fin N) (i : I j), Measurable ↿(k j i))
    (hi : ∀ (j : Fin N) (i : I j) (x : X), Integrable (k j i x) (μ j))
    (h : ∀ j : Fin N, IsL2Contraction (m j) (μ j) (n j) (k j)) :
    IsL2Contraction (Measure.pi m) (Measure.pi μ) (Measure.pi n)
      fun (i : ∀ j : Fin N, I j) (x : Fin N → X) (y : Fin N → Y) ↦
        ∏ j : Fin N, k j (i j) (x j) (y j) := by
  -- Induct on `N`: split off the factor `0` and apply `IsL2Contraction.prod`.
  induction N with
  | zero =>
    -- no factor: all three measures are Dirac measures on a point and the kernel is `1`
    simp [IsL2Contraction, pi_of_empty _, prod_empty]
  | succ N ih =>
    -- `k'` is the product of the kernels other than `k 0`
    let k' (i : ∀ j : Fin N, I j.succ) (x : Fin N → X) (y : Fin N → Y) : ℂ :=
      ∏ j : Fin N, k j.succ (i j) (x j) (y j)
    have h_rest : IsL2Contraction (.pi fun j : Fin N ↦ m j.succ) (.pi fun j : Fin N ↦ μ j.succ)
        (.pi fun j : Fin N ↦ n j.succ) k' :=
      ih (fun j ↦ hk j.succ) (fun j ↦ hi j.succ) fun j ↦ h j.succ
    have hi' (i : ∀ j : Fin N, I j.succ) (x : Fin N → X) :
        Integrable (k' i x) (.pi fun j : Fin N ↦ μ j.succ) :=
      .fintype_prod fun j ↦ hi j.succ (i j) (x j)
    -- Transport the bound for the factor `0` times the other factors to the product of all factors.
    let EX : X × (Fin N → X) ≃ᵐ (Fin (N + 1) → X) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) ↦ X) 0).symm
    let EY : Y × (Fin N → Y) ≃ᵐ (Fin (N + 1) → Y) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) ↦ Y) 0).symm
    have h_kernel (i : I 0 × ∀ j : Fin N, I j.succ) (x : X × (Fin N → X)) (y : Y × (Fin N → Y)) :
        ∏ j : Fin (N + 1), k j (consEquiv I i j) (EX x j) (EY y j) =
          k 0 i.1 x.1 y.1 * k' i.2 x.2 y.2 := by
      simp [EX, EY, k', prod_univ_succ]
    exact .of_comp_equiv (consEquiv I) (measurePreserving_piFinSuccAbove m 0).symm
      (measurePreserving_piFinSuccAbove μ 0).symm (measurePreserving_piFinSuccAbove n 0).symm
      h_kernel ((h 0).prod (hk 0) (fun i ↦ by fun_prop) (hi 0) hi' h_rest)

/-- On common spaces `X` and `Y`, let each `k v` be a finite family of measurable kernels,
integrable in the last variable, whose integral operator has `L²` norm at most one
(`New.IsL2Contraction` for σ-finite measures `m v` on `X` and `μ v`, `n v` on `Y`). Then the
same holds for the family of products `∏ v, k v (i v) (x v) (y v)` and the product measures. -/
lemma IsL2Contraction.pi {ι : Type*} [Fintype ι] [DecidableEq ι] {I : ι → Type*}
    [∀ v : ι, Fintype (I v)] {m : ι → Measure X} {μ n : ι → Measure Y} [∀ v : ι, SigmaFinite (m v)]
    [∀ v : ι, SigmaFinite (μ v)] [∀ v : ι, SigmaFinite (n v)] {k : ∀ v : ι, I v → X → Y → ℂ}
    (hk : ∀ (v : ι) (i : I v), Measurable ↿(k v i))
    (hi : ∀ (v : ι) (i : I v) (x : X), Integrable (k v i x) (μ v))
    (h : ∀ v : ι, IsL2Contraction (m v) (μ v) (n v) (k v)) :
    IsL2Contraction (Measure.pi m) (Measure.pi μ) (Measure.pi n)
      fun (i : ∀ v : ι, I v) (x : ι → X) (y : ι → Y) ↦ ∏ v : ι, k v (i v) (x v) (y v) := by
  -- Number the factors by `e` and reindex the bound for factors indexed by `Fin (card ι)`.
  let e : Fin (card ι) ≃ ι := (equivFin ι).symm
  have h_kernel (i : ∀ j : Fin (card ι), I (e j)) (x : Fin (card ι) → X) (y : Fin (card ι) → Y) :
      ∏ v : ι, k v (e.piCongrLeft I i v) (MeasurableEquiv.piCongrLeft (fun _ ↦ X) e x v)
          (MeasurableEquiv.piCongrLeft (fun _ ↦ Y) e y v) =
        ∏ j : Fin (card ι), k (e j) (i j) (x j) (y j) := by
    simp [← e.prod_comp, MeasurableEquiv.piCongrLeft]
  exact .of_comp_equiv (e.piCongrLeft I) (measurePreserving_piCongrLeft m e)
    (measurePreserving_piCongrLeft μ e) (measurePreserving_piCongrLeft n e) h_kernel
    (pi_fin (fun j ↦ hk (e j)) (fun j ↦ hi (e j)) fun j ↦ h (e j))

/-! ### Padded tuples and units -/

/-- The sequence indexed by `ℕ` that is the tuple `c` at indices below `n`, `t` at index `n`, and
`1` at indices above `n`. -/
def padTuple {C : Type*} {n : ℕ} [One C] (c : Fin n → C) (t : C) (a : ℕ) : C :=
  if h : a < n then c ⟨a, h⟩ else if a = n then t else 1

open scoped Classical in
/-- The element `c` as a unit if it is invertible, and the unit `1` otherwise. -/
noncomputable def unitOrOne (c : A) : Aˣ := if h : IsUnit c then h.unit else 1

@[simp]
lemma unitOrOne_val (c : Aˣ) : unitOrOne (c : A) = c := by simp [unitOrOne]

/-- If the units are open in `A` and carry the subspace topology, then `unitOrOne` (an element as a
unit, or `1` if it is not invertible) is continuous at every unit `c`. -/
lemma continuousAt_unitOrOne (c : Aˣ) [TopologicalSpace A] [h : IsOpenUnits A] :
    ContinuousAt unitOrOne (c : A) := by
  -- The units embed openly in `A`, and `unitOrOne` is a left inverse of the embedding.
  rw [← h.isOpenEmbedding_unitsVal.continuousAt_iff,
    show unitOrOne ∘ (Units.val : Aˣ → A) = id from funext unitOrOne_val]
  exact continuousAt_id

end New

end IntegralOperators
