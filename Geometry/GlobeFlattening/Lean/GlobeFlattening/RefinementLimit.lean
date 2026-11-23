import GlobeFlattening.GoodSet
import GlobeFlattening.LimitDifferentiability
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Uniform convergence and the local-first tail estimate

The radius from the starting stage bounds all later radii. The geometric
tail estimate therefore retains a factor of that starting radius. For
differentiability, the improved estimate pays for the first step and the
geometric tail starts at the next, smaller radius.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GlobeFlattening

variable {X : Type*} [TopologicalSpace X]
variable {s : Set X} {stage : ℕ → X → ℝ} {radius : ℕ → ℝ} {u : X → ℝ}

omit [TopologicalSpace X] in
/-- Control the global tail starting at an arbitrary stage, using its own radius. -/
theorem refinement_tail_bound
    (hanti : Antitone radius)
    (hstep : ∀ n, ∀ x ∈ s, |stage (n + 1) x - stage n x| ≤ radius n / 2 / (2 : ℝ)^n)
    {x : X} (hx : x ∈ s) (hu : Tendsto (fun n => stage n x) atTop (𝓝 (u x))) (n : ℕ) :
    |u x - stage n x| ≤ radius n / (2 : ℝ)^n := by
  have ht : Tendsto (fun k : ℕ => stage (k + n) x) atTop (𝓝 (u x)) :=
    hu.comp (tendsto_add_atTop_nat n)
  have h : ∀ k : ℕ, dist (stage (k + n) x) (stage (k + 1 + n) x) ≤
      (radius n / (2 : ℝ)^n) / 2 / (2 : ℝ)^k := by
    intro k
    rw [show k + 1 + n = k + n + 1 by omega, dist_comm, Real.dist_eq]
    calc
      _ ≤ radius (k + n) / 2 / (2 : ℝ)^(k + n) := hstep _ x hx
      _ ≤ radius n / 2 / (2 : ℝ)^(k + n) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (hanti (by omega)) (by norm_num))
          (by positivity)
      _ = _ := by rw [pow_add]; ring
  have htail := dist_le_of_le_geometric_two_of_tendsto₀ h ht
  rw [← Real.dist_eq, dist_comm]
  simpa only [zero_add] using htail

/-- The explicit geometric error bounds tend to zero for any fixed numerator. -/
theorem tendsto_dyadic_ratio_zero (c : ℝ) :
    Tendsto (fun n : ℕ => c / (2 : ℝ)^n) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa [div_eq_mul_inv, inv_pow] using hpow.const_mul c

/-- A nonnegative radius halving at each stage gives both scale monotonicity
and convergence of the scales to zero. -/
theorem antitone_and_tendsto_zero_of_halving {radius : ℕ → ℝ}
    (hnonneg : ∀ n, 0 ≤ radius n) (hhalve : ∀ n, radius (n + 1) ≤ radius n / 2) :
    Antitone radius ∧ Tendsto radius atTop (𝓝 0) := by
  refine ⟨antitone_nat_of_succ_le (fun n => (hhalve n).trans (by linarith [hnonneg n])), ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_dyadic_ratio_zero (radius 0)) hnonneg
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      change radius (n + 1) ≤ radius 0 / (2 : ℝ)^(n + 1)
      rw [pow_succ, ← div_div]
      exact (hhalve n).trans <| div_le_div_of_nonneg_right ih (by norm_num)

/-- Summably small steps converge uniformly on the set carrying the estimates.
The limit is continuous there and has an explicit error bound at every stage. -/
theorem exists_uniform_refinement_limit
    (hanti : Antitone radius) (hcontinuous : ∀ n, ContinuousOn (stage n) s)
    (hstep : ∀ n, ∀ x ∈ s, |stage (n + 1) x - stage n x| ≤ radius n / 2 / (2 : ℝ)^n) :
    ∃ u : X → ℝ, TendstoUniformlyOn stage u atTop s ∧ ContinuousOn u s ∧
      ∀ n, ∀ x ∈ s, |u x - stage n x| ≤ radius n / (2 : ℝ)^n := by
  classical
  have hpoint (x : X) : x ∈ s → ∃ y : ℝ, Tendsto (fun n => stage n x) atTop (𝓝 y) := by
    intro hx
    apply cauchySeq_tendsto_of_complete
    apply cauchySeq_of_le_geometric_two (C := radius 0)
    intro n
    rw [dist_comm, Real.dist_eq]
    exact (hstep n x hx).trans
      (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right (hanti (Nat.zero_le n))
        (by norm_num)) (by positivity))
  let limit (x : X) : ℝ := if hx : x ∈ s then (hpoint x hx).choose else 0
  have hlim (x : X) (hx : x ∈ s) :
      Tendsto (fun n => stage n x) atTop (𝓝 (limit x)) := by
    simpa only [limit, dif_pos hx] using (hpoint x hx).choose_spec
  have htail (n : ℕ) (x : X) (hx : x ∈ s) :
      |limit x - stage n x| ≤ radius n / (2 : ℝ)^n :=
    refinement_tail_bound hanti hstep hx (hlim x hx) n
  have hg := tendsto_dyadic_ratio_zero (radius 0)
  have hunif : TendstoUniformlyOn stage limit atTop s := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    filter_upwards [(tendsto_order.1 hg).2 ε hε] with n hn x hx
    rw [Real.dist_eq]
    exact (htail n x hx).trans_lt
      ((div_le_div_of_nonneg_right (hanti (Nat.zero_le n)) (by positivity)).trans_lt hn)
  exact ⟨limit, hunif, hunif.continuousOn (Frequently.of_forall hcontinuous), htail⟩

omit [TopologicalSpace X] in
/-- Use the improved bound for step `n + 1` and start the global estimate at
that next stage. This is the local-first split in the report. -/
theorem refinement_local_tail
    (hanti : Antitone radius)
    (hstep : ∀ n, ∀ x ∈ s, |stage (n + 1) x - stage n x| ≤ radius n / 2 / (2 : ℝ)^n)
    {x : X} (hx : x ∈ s) (hu : Tendsto (fun n => stage n x) atTop (𝓝 (u x)))
    {n : ℕ} {localError : ℝ} (hlocal : |stage (n + 1) x - stage n x| ≤ localError) :
    |u x - stage n x| ≤ localError + radius (n + 1) / (2 : ℝ)^(n + 1) := by
  have htail := refinement_tail_bound hanti hstep hx hu (n + 1)
  calc
    _ = |(u x - stage (n + 1) x) + (stage (n + 1) x - stage n x)| := by
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

omit [TopologicalSpace X] in
/-- The horizontal lower-slope inequality survives the limit. -/
theorem lower_slope_of_tendstoUniformlyOn
    (hu : TendstoUniformlyOn stage u atTop s) {x₁ x₂ : X} (h₁ : x₁ ∈ s) (h₂ : x₂ ∈ s)
    {slope : ℕ → ℝ} {slopeLimit run : ℝ}
    (hslope : Tendsto slope atTop (𝓝 slopeLimit))
    (hbound : ∀ n, slope n * run ≤ stage n x₂ - stage n x₁) :
    slopeLimit * run ≤ u x₂ - u x₁ :=
  le_of_tendsto_of_tendsto' (hslope.mul tendsto_const_nhds)
    ((hu.tendsto_at h₂).sub (hu.tendsto_at h₁)) hbound

/-- A compact domain and an oscillation budget allow a mesh obtained by
dividing any positive total width into sufficiently many equal pieces. -/
theorem exists_refinement_mesh {Y Z : Type*} [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {domain : Set Y} {f : Y → Z} (hc : IsCompact domain) (hf : ContinuousOn f domain)
    {totalWidth maxWidth oscillation : ℝ} (htotal : 0 < totalWidth)
    (hmax : 0 < maxWidth) (hosc : 0 < oscillation) :
    ∃ N : ℕ, 0 < N ∧ 0 < totalWidth / (N : ℝ) ∧ totalWidth / (N : ℝ) ≤ maxWidth ∧
      ∀ x ∈ domain, ∀ y ∈ domain, dist x y ≤ totalWidth / (N : ℝ) →
        dist (f x) (f y) ≤ oscillation := by
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (hc.uniformContinuousOn_of_continuous hf) oscillation hosc
  obtain ⟨N, hN⟩ := exists_nat_gt (max (totalWidth / r) (totalWidth / maxWidth))
  have hNr := (le_max_left _ _).trans_lt hN
  have hNm := (le_max_right _ _).trans_lt hN
  have hpos : (0 : ℝ) < N := (div_pos htotal hr).trans hNr
  have hsmall : totalWidth / (N : ℝ) < r := by
    rw [div_lt_iff₀ hpos, mul_comm]
    exact (div_lt_iff₀ hr).mp hNr
  have hwidth : totalWidth / (N : ℝ) < maxWidth := by
    rw [div_lt_iff₀ hpos, mul_comm]
    exact (div_lt_iff₀ hmax).mp hNm
  refine ⟨N, by exact_mod_cast hpos, div_pos htotal hpos, hwidth.le, ?_⟩
  intro x hx y hy hdist
  exact (hmod x hx y hy (hdist.trans_lt hsmall)).le

/-- The scale in the difference-quotient argument is half the trimming
radius. A sharper stage error at that scale and the global estimate together
give the required Fréchet derivative through all points of the domain. -/
theorem hasFDerivWithinAt_of_refinement_limit {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {domain : Set E} {f : E → ℝ} {approx : ℕ → E → ℝ}
    {radius localCoeff control : ℕ → ℝ} {D : ℕ → E →L[ℝ] ℝ} {A : E →L[ℝ] ℝ} {p : E}
    (hp : p ∈ domain) (hanti : Antitone radius) (hpos : ∀ n, 0 < radius n)
    (hradius : Tendsto radius atTop (𝓝 0))
    (hu : TendstoUniformlyOn approx f atTop domain)
    (hstep : ∀ n, ∀ x ∈ domain,
      |approx (n + 1) x - approx n x| ≤ radius n / 2 / (2 : ℝ)^n)
    (hcontrol : Tendsto control atTop (𝓝 0))
    (hbound : ∀ n, ‖D n - A‖ + 4 * (localCoeff n + 1 / (2 : ℝ)^(n + 1)) ≤ control n)
    (hgood : ∀ᶠ n in atTop, ∀ q ∈ domain, ‖q - p‖ < radius n / 2 →
      approx n q - approx n p = D n (q - p) ∧
      |approx (n + 1) q - approx n q| ≤ localCoeff n * radius (n + 1)) :
    HasFDerivWithinAt f A domain p := by
  apply hasFDerivWithinAt_of_affine_approximations
    (radius := fun n => radius n / 2)
    (tail := fun n => 2 * (localCoeff n + 1 / (2 : ℝ)^(n + 1)))
    hp
    (fun _ _ h => div_le_div_of_nonneg_right (hanti h) (by norm_num))
    (fun n => div_pos (hpos n) (by norm_num))
    (by simpa using hradius.div_const 2)
    hcontrol
  · intro n
    convert hbound n using 1
    ring
  · filter_upwards [hgood] with n hn
    intro q hq hdist
    have hlocal := (hn q hq hdist).2
    refine ⟨(hn q hq hdist).1, ?_⟩
    rw [Real.norm_eq_abs]
    calc
      _ ≤ localCoeff n * radius (n + 1) + radius (n + 1) / (2 : ℝ)^(n + 1) :=
        refinement_local_tail hanti hstep hq (hu.tendsto_at hq) hlocal
      _ = _ := by ring

/-- Convergence of the affine derivatives and decay of the relative
next-step error suffice for the local-first argument. -/
theorem hasFDerivWithinAt_of_refinement_limit_of_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {domain : Set E} {f : E → ℝ} {approx : ℕ → E → ℝ}
    {radius localCoeff : ℕ → ℝ} {D : ℕ → E →L[ℝ] ℝ} {A : E →L[ℝ] ℝ} {p : E}
    (hp : p ∈ domain) (hanti : Antitone radius) (hpos : ∀ n, 0 < radius n)
    (hradius : Tendsto radius atTop (𝓝 0))
    (hu : TendstoUniformlyOn approx f atTop domain)
    (hstep : ∀ n, ∀ x ∈ domain,
      |approx (n + 1) x - approx n x| ≤ radius n / 2 / (2 : ℝ)^n)
    (hD : Tendsto D atTop (𝓝 A)) (hCoeff : Tendsto localCoeff atTop (𝓝 0))
    (hgood : ∀ᶠ n in atTop, ∀ q ∈ domain, ‖q - p‖ < radius n / 2 →
      approx n q - approx n p = D n (q - p) ∧
      |approx (n + 1) q - approx n q| ≤ localCoeff n * radius (n + 1)) :
    HasFDerivWithinAt f A domain p := by
  have herror := (tendsto_dyadic_ratio_zero 1).comp (tendsto_add_atTop_nat 1)
  have hnorm : Tendsto (fun n => ‖D n - A‖) atTop (𝓝 0) := by
    simpa using (hD.sub (g := fun _ : ℕ => A) tendsto_const_nhds).norm
  have hcontrol : Tendsto (fun n => ‖D n - A‖ + 4 * (localCoeff n + 1 / (2 : ℝ)^(n + 1)))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using hnorm.add ((hCoeff.add herror).const_mul 4)
  exact hasFDerivWithinAt_of_refinement_limit hp hanti hpos hradius hu hstep hcontrol
    (fun _ => le_rfl) hgood

/-- The local bound from one old affine tile divided by the next trimming
radius has the explicit dyadic majorant from the report. The formula uses
only the mesh cap at the old stage. -/
theorem local_refinement_dyadic_bound {δ hOld hNew : ℝ} {n : ℕ}
    (hOld_le : hOld ≤ 3 * δ / (4 : ℝ)^n) (hNew_nonneg : 0 ≤ hNew) :
    (2 * hOld + 3 * δ / (4 : ℝ)^(n + 1)) * hNew ≤
      (108 * δ / (2 : ℝ)^n) * (hNew / (2 : ℝ)^(n + 4)) := by
  have hpow : (4 : ℝ)^n = ((2 : ℝ)^n)^2 := by
    calc
      _ = (2 : ℝ)^(2 * n) := by rw [pow_mul]; norm_num
      _ = _ := by rw [Nat.mul_comm 2 n, pow_mul]
  calc
    _ ≤ (2 * (3 * δ / (4 : ℝ)^n) + 3 * δ / (4 : ℝ)^(n + 1)) * hNew :=
      mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hOld_le (by norm_num)) le_rfl)
        hNew_nonneg
    _ = _ := by
      rw [pow_succ, hpow, pow_add (2 : ℝ) n 4]
      field_simp; ring

/-- Assemble the scalar construction from the rectangular refinement
estimates. The derivative holds on a measurable, co-null set and is
classical at each of its points. The width slope and base-stage error are
valid up to the entire boundary of the box. -/
theorem exists_scalar_limit_of_refinement_stages
    {box domain : Set (ℝ × ℝ)} (hopen : IsOpen domain) (hsub : domain ⊆ box)
    {approx : ℕ → ℝ × ℝ → ℝ} {good : ℕ → Set (ℝ × ℝ)}
    {radius slopeError localCoeff : ℕ → ℝ}
    {latitudeSlope : ℝ → ℝ} {stageSlope : ℕ → ℝ → ℝ}
    {tileSlope : ℕ → ℝ × ℝ → ℝ}
    (hpos : ∀ n, 0 < radius n) (hhalve : ∀ n, radius (n + 1) ≤ radius n / 2)
    (hcontinuous : ∀ n, ContinuousOn (approx n) box)
    (hstep : ∀ n, ∀ q ∈ box,
      |approx (n + 1) q - approx n q| ≤ radius n / 2 / (2 : ℝ)^n)
    (hgood : ∀ n, MeasurableSet (good n))
    (hbad : (∑' n, volume (domain \ good n)) ≠ ∞)
    (hSlopeLimit : ∀ y, Tendsto (fun n => stageSlope n y) atTop (𝓝 (latitudeSlope y)))
    (hSlope : ∀ n, ∀ p ∈ box, ∀ q ∈ box, p.2 = q.2 → p.1 ≤ q.1 →
      stageSlope n p.2 * (q.1 - p.1) ≤ approx n q - approx n p)
    (hSlopeError : Tendsto slopeError atTop (𝓝 0))
    (hLocalCoeff : Tendsto localCoeff atTop (𝓝 0))
    (haccuracy : ∀ n, ∀ p ∈ good n, p ∈ domain →
      |tileSlope n p - latitudeSlope p.2| ≤ slopeError n)
    (htile : ∀ n, ∀ p ∈ good n, p ∈ domain → ∀ q ∈ domain, ‖q - p‖ < radius n / 2 →
      approx n q - approx n p = tileSlope n p * (q.1 - p.1) ∧
        |approx (n + 1) q - approx n q| ≤ localCoeff n * radius (n + 1)) :
    ∃ u : ℝ × ℝ → ℝ, ∃ E : Set (ℝ × ℝ),
      ContinuousOn u box ∧ MeasurableSet E ∧ E ⊆ domain ∧ volume (domain \ E) = 0 ∧
      (∀ q ∈ box, |u q - approx 0 q| ≤ radius 0) ∧
      (∀ p ∈ box, ∀ q ∈ box, p.2 = q.2 → p.1 ≤ q.1 →
        latitudeSlope p.2 * (q.1 - p.1) ≤ u q - u p) ∧
      ∀ p ∈ E, HasFDerivAt u (latitudeSlope p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) p := by
  obtain ⟨hanti, hrad⟩ := antitone_and_tendsto_zero_of_halving
    (fun n => (hpos n).le) hhalve
  obtain ⟨u, hu, hcu, htail⟩ := exists_uniform_refinement_limit hanti hcontinuous hstep
  let E := eventualGoodSet good ∩ domain
  have hE : MeasurableSet E := (measurableSet_eventualGoodSet hgood).inter hopen.measurableSet
  have hnull : volume (domain \ E) = 0 := by
    simpa only [E, sdiff_inter_self_eq_sdiff] using measure_diff_eventualGoodSet volume hbad
  refine ⟨u, E, hcu, hE, inter_subset_right, hnull, ?_, ?_, ?_⟩
  · intro q hq
    simpa using htail 0 q hq
  · intro p hp q hq hlat hlong
    exact lower_slope_of_tendstoUniformlyOn hu hp hq (hSlopeLimit p.2)
      (fun n => hSlope n p hp q hq hlat hlong)
  · intro p hp
    have hevent : ∀ᶠ n in atTop, p ∈ good n := mem_eventualGoodSet.mp hp.1
    have hTileSlope : Tendsto (fun n => tileSlope n p) atTop (𝓝 (latitudeSlope p.2)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [Real.norm_eq_abs]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSlopeError
        (Eventually.of_forall (fun n => abs_nonneg _))
        (hevent.mono fun n hn => haccuracy n p hn hp.2)
    have hD := hTileSlope.smul (g := fun _ : ℕ => ContinuousLinearMap.fst ℝ ℝ ℝ)
      tendsto_const_nhds
    have hAff : ∀ᶠ n in atTop, ∀ q ∈ domain, ‖q - p‖ < radius n / 2 →
        approx n q - approx n p =
          (tileSlope n p • ContinuousLinearMap.fst ℝ ℝ ℝ) (q - p) ∧
        |approx (n + 1) q - approx n q| ≤ localCoeff n * radius (n + 1) := by
      filter_upwards [hevent] with n hn
      intro q hq hdist
      exact htile n p hn hp.2 q hq hdist
    exact (hasFDerivWithinAt_of_refinement_limit_of_tendsto hp.2 hanti hpos hrad
      (hu.mono hsub) (fun n q hq => hstep n q (hsub hq)) hD hLocalCoeff hAff).hasFDerivAt
      (hopen.mem_nhds hp.2)

end GlobeFlattening
