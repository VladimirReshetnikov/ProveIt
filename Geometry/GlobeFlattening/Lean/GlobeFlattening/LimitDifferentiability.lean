import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Differentiating a limit inside shrinking affine tiles

This formalizes the scale selection and difference-quotient argument in the
report. The estimate applies to every nearby point within the domain.
-/

open Filter Set
open scoped Topology

namespace GlobeFlattening

/-- Every positive distance below `radius N` lies between two consecutive radii
with lower index at least `N`. -/
theorem exists_radius_band {radius : ℕ → ℝ} (hanti : Antitone radius)
    (hzero : Tendsto radius atTop (𝓝 0)) {N : ℕ} {r : ℝ}
    (hr : 0 < r) (hNr : r < radius N) :
    ∃ n ≥ N, radius (n + 1) ≤ r ∧ r < radius n := by
  have hex : ∃ k, radius k ≤ r :=
    ((tendsto_order.1 hzero).2 r hr).exists.imp fun _ hk => hk.le
  have hN : N < Nat.find hex := by
    by_contra! hle
    exact (not_le_of_gt hNr) ((hanti hle).trans (Nat.find_spec hex))
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : Nat.find hex ≠ 0)
  refine ⟨n, by omega, ?_, ?_⟩
  · simpa [hn] using Nat.find_spec hex
  · exact lt_of_not_ge (Nat.find_min hex (by omega : n < Nat.find hex))

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Approximate linearity inside each late tile, with a tail bound at the
next radius, suffices for Fréchet differentiability. -/
theorem hasFDerivWithinAt_of_linearization_bounds
    {s : Set E} {p : E} {u : E → F} {uStage : ℕ → E → F}
    {radius tail linearError : ℕ → ℝ} {A : E →L[ℝ] F}
    (hp : p ∈ s) (hanti : Antitone radius) (hpos : ∀ n, 0 < radius n)
    (hzero : Tendsto radius atTop (𝓝 0))
    (hlinearError : Tendsto linearError atTop (𝓝 0)) (htail : Tendsto tail atTop (𝓝 0))
    (hgood : ∀ᶠ n in atTop, ∀ q ∈ s, ‖q - p‖ < radius n →
      ‖uStage n q - uStage n p - A (q - p)‖ ≤ linearError n * ‖q - p‖ ∧
      ‖u q - uStage n q‖ ≤ tail n * radius (n + 1)) :
    HasFDerivWithinAt u A s p := by
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hcontrol : Tendsto (fun n => linearError n + 2 * tail n) atTop (𝓝 0) := by
    simpa using hlinearError.add (htail.const_mul 2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hgood.and ((tendsto_order.1 hcontrol).2 ε hε))
  have hnear : ∀ᶠ q in 𝓝[s] p, ‖q - p‖ < radius N :=
    (Metric.eventually_nhds_iff.2 ⟨radius N, hpos N, fun q hq => by
      simpa [dist_eq_norm] using hq⟩).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with q hq hnearq
  by_cases hqp : q = p
  · simp [hqp]
  have hdist : 0 < ‖q - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hqp)
  obtain ⟨n, hn, hlo, hhi⟩ := exists_radius_band hanti hzero hdist hnearq
  obtain ⟨hlinear, hqerror⟩ := (hN n hn).1 q hq hhi
  have hperror := ((hN n hn).1 p hp (by simpa using hpos n)).2
  have htail_nonneg : 0 ≤ tail n :=
    nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hperror) (hpos (n + 1))
  have hdecompose : u q - u p - A (q - p) =
      (u q - uStage n q) - (u p - uStage n p) + (uStage n q - uStage n p - A (q - p)) := by abel
  rw [hdecompose]
  calc
    _ ≤ ‖u q - uStage n q‖ + ‖u p - uStage n p‖ + ‖uStage n q - uStage n p - A (q - p)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ tail n * ‖q - p‖ + tail n * ‖q - p‖ + linearError n * ‖q - p‖ := by
      have hscale := mul_le_mul_of_nonneg_left hlo htail_nonneg
      exact add_le_add (add_le_add (hqerror.trans hscale) (hperror.trans hscale)) hlinear
    _ = (linearError n + 2 * tail n) * ‖q - p‖ := by ring
    _ ≤ ε * ‖q - p‖ := mul_le_mul_of_nonneg_right (hN n hn).2.le hdist.le

end GlobeFlattening
