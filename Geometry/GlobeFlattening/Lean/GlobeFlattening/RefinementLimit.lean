import GlobeFlattening.GoodSet
import GlobeFlattening.LimitDifferentiability
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
    Tendsto (fun n : ℕ => c / (2 : ℝ)^n) atTop (𝓝 0) :=
  (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).const_div_atTop c

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
  choose! limit hlim using hpoint
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

/-- Assemble the scalar construction from the rectangular refinement
estimates. The derivative holds on a measurable, co-null set and is
classical at each of its points. The width slope and base-stage error are
valid up to the entire boundary of the box. -/
theorem exists_scalar_limit_of_refinement_stages
    {box domain : Set (ℝ × ℝ)} (hopen : IsOpen domain) (hsub : domain ⊆ box)
    {approx : ℕ → ℝ × ℝ → ℝ} {good : ℕ → Set (ℝ × ℝ)}
    {radius linearError localCoeff : ℕ → ℝ} {latitudeSlope : ℝ → ℝ}
    (hpos : ∀ n, 0 < radius n) (hhalve : ∀ n, radius (n + 1) ≤ radius n / 2)
    (hcontinuous : ∀ n, ContinuousOn (approx n) box)
    (hstep : ∀ n, ∀ q ∈ box,
      |approx (n + 1) q - approx n q| ≤ radius n / 2 / (2 : ℝ)^n)
    (hgood : ∀ n, MeasurableSet (good n))
    (hbad : (∑' n, volume (domain \ good n)) ≠ ∞)
    (hSlope : ∀ n, ∀ p ∈ box, ∀ q ∈ box, p.2 = q.2 → p.1 ≤ q.1 →
      latitudeSlope p.2 * (q.1 - p.1) ≤ approx n q - approx n p)
    (hLinearError : Tendsto linearError atTop (𝓝 0))
    (hLocalCoeff : Tendsto localCoeff atTop (𝓝 0))
    (htile : ∀ n, ∀ p ∈ good n, ∀ q ∈ domain, dist q p ≤ radius n / 2 →
      |approx n q - approx n p - latitudeSlope p.2 * (q.1 - p.1)| ≤ linearError n * dist q p ∧
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
    exact ge_of_tendsto' ((hu.tendsto_at hq).sub (hu.tendsto_at hp))
      (fun n => hSlope n p hp q hq hlat hlong)
  · intro p hp
    have hevent : ∀ᶠ n in atTop, p ∈ good n := mem_eventualGoodSet.mp hp.1
    let tail := fun n => 2 * (localCoeff n + 1 / (2 : ℝ)^(n + 1))
    have herror := (tendsto_dyadic_ratio_zero 1).comp (tendsto_add_atTop_nat 1)
    have hTailZero : Tendsto tail atTop (𝓝 0) := by
      simpa [tail, Function.comp_def] using (hLocalCoeff.add herror).const_mul 2
    refine (hasFDerivWithinAt_of_linearization_bounds
      (u := u) (uStage := approx) (radius := fun n => radius n / 2) (tail := tail)
      (A := latitudeSlope p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) hp.2
      (fun _ _ h => div_le_div_of_nonneg_right (hanti h) (by norm_num))
      (fun n => div_pos (hpos n) (by norm_num)) (by simpa using hrad.div_const 2)
      hLinearError hTailZero ?_).hasFDerivAt (hopen.mem_nhds hp.2)
    filter_upwards [hevent] with n hn
    intro q hq hdist
    obtain ⟨hlinear, hlocal⟩ := htile n p hn q hq (by simpa [dist_eq_norm] using hdist.le)
    refine ⟨hlinear, ?_⟩
    rw [Real.norm_eq_abs]
    -- Use the local bound once, then pay only the tail after the next step.
    calc
      _ ≤ |u q - approx (n + 1) q| + |approx (n + 1) q - approx n q| := abs_sub_le ..
      _ ≤ radius (n + 1) / (2 : ℝ)^(n + 1) + localCoeff n * radius (n + 1) :=
        add_le_add (htail (n + 1) q (hsub hq)) hlocal
      _ = _ := by dsimp [tail]; ring

end GlobeFlattening
