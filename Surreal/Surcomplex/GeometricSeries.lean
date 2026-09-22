import Surreal.Foundations.SignSequencePowerSeries
import Surreal.Surcomplex.PowerSeries
import Surreal.Surcomplex.FineTopology
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Actual geometric strong sums and their finite remainders

For every surreal or surcomplex infinitesimal, including zero, its powers
are strongly summable and their actual strong sum is `(1 - x)⁻¹`.
Mapping the formal geometric identity through admissible evaluation proves
`a:eq:geom`; the exact finite remainder proves the algebraic clause of
`a:ex:geometric`, including its remainder valuation. For nonzero inputs the partial sums do not converge to
any point in the fine topology: a convergent small sequence would have to
be eventually constant, whereas consecutive partial sums differ by a
nonzero power. Thus strong summation is distinct from topological summation.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

open Filter Topology

/-- Powers of an actual infinitesimal form a strongly summable family. -/
theorem stronglySummable_powers (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    StronglySummable (fun n : ℕ => x ^ n) := by
  simpa only [map_one, one_mul] using
    stronglySummable_coeff_mul_powers x hx (fun _ => 1)

private theorem geometric_evaluation_eq (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    powerSeriesEvaluation x hx (PowerSeries.mk 1) =
      strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) := by
  simpa only [PowerSeries.coeff_mk, Pi.one_apply, map_one, one_mul] using
    powerSeriesEvaluation_eq_strongSum x hx (PowerSeries.mk 1)

/-- The actual geometric identity before division. -/
theorem geometric_strongSum_mul (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) * (1 - x) = 1 := by
  have h := congrArg (powerSeriesEvaluation x hx)
    (PowerSeries.mk_one_mul_one_sub_eq_one ℝ)
  simpa only [map_mul, map_sub, map_one, powerSeriesEvaluation_X,
    geometric_evaluation_eq] using h

/-- The actual surreal geometric strong sum in `a:eq:geom`. -/
theorem geometric_strongSum (x : SignSequence.{u}) (hx : IsInfinitesimal x) :
    strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) = (1 - x)⁻¹ := by
  have h := geometric_strongSum_mul x hx
  have hne := right_ne_zero_of_mul_eq_one h
  apply mul_right_cancel₀ hne
  rw [h, inv_mul_cancel₀ hne]

/-- Exact error after the powers indexed from zero through `N`. -/
theorem geometric_strongSum_remainder (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (N : ℕ) :
    strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) -
      ∑ n ∈ Finset.range (N + 1), x ^ n = x ^ (N + 1) / (1 - x) := by
  have hne := right_ne_zero_of_mul_eq_one (geometric_strongSum_mul x hx)
  rw [geometric_strongSum x hx]
  apply (eq_div_iff hne).mpr
  rw [sub_mul, inv_mul_cancel₀ hne, geom_sum_mul_neg]
  ring

/-- Exact valuation of the geometric remainder, with infinity when `x = 0`. -/
theorem valuation_geometric_strongSum_remainder (x : SignSequence.{u})
    (hx : IsInfinitesimal x) (N : ℕ) :
    valuation (strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) -
      ∑ n ∈ Finset.range (N + 1), x ^ n) = (N + 1) • valuation x := by
  have hv : valuation (1 - x) = 0 := by
    rw [valuation.map_sub_eq_of_lt_left (by
      simpa only [valuation_one] using (isInfinitesimal_iff_valuation_pos x).mp hx),
      valuation_one]
  rw [geometric_strongSum_remainder x hx N, valuation_div, valuation.map_pow, hv, sub_zero]

/-- A nonzero infinitesimal's strong sum is never one of its finite partial sums. -/
theorem geometric_partialSum_ne_strongSum (x : SignSequence.{u}) (hx : IsInfinitesimal x)
    (hzero : x ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), x ^ n ≠
      strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) := by
  intro h
  have hr := geometric_strongSum_remainder x hx N
  rw [h, sub_self] at hr
  exact (div_ne_zero (pow_ne_zero _ hzero)
    (right_ne_zero_of_mul_eq_one (geometric_strongSum_mul x hx))) hr.symm

/-- For any nonzero input, geometric partial sums have no fine-topology limit. -/
theorem not_tendsto_geometric_partialSums (x : SignSequence.{u}) (hzero : x ≠ 0)
    (y : SignSequence.{u}) :
    ¬ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), x ^ n) atTop (𝓝 y) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_nhds_iff_eventually_eq _ _ _).mp h)
  have hs := hN (N + 1) (Nat.le_succ N)
  rw [Finset.sum_range_succ, hN N le_rfl] at hs
  exact (pow_ne_zero (N + 1) hzero) (add_eq_left.mp hs)

end

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations Filter Topology

noncomputable section

/-- Powers of an actual surcomplex infinitesimal form a strongly summable family. -/
theorem stronglySummable_powers (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    StronglySummable (fun n : ℕ => x ^ n) := by
  simpa only [map_one, one_mul] using
    stronglySummable_coeff_mul_powers x hx (fun _ => 1)

private theorem geometric_evaluation_eq (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    powerSeriesEvaluation x hx (PowerSeries.mk 1) =
      strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) := by
  simpa only [PowerSeries.coeff_mk, Pi.one_apply, map_one, one_mul] using
    powerSeriesEvaluation_eq_strongSum x hx (PowerSeries.mk 1)

/-- The actual geometric identity before division. -/
theorem geometric_strongSum_mul (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) * (1 - x) = 1 := by
  have h := congrArg (powerSeriesEvaluation x hx)
    (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simpa only [map_mul, map_sub, map_one, powerSeriesEvaluation_X,
    geometric_evaluation_eq] using h

/-- The actual surcomplex geometric strong sum in `a:eq:geom`. -/
theorem geometric_strongSum (x : Surcomplex.{u}) (hx : IsInfinitesimal x) :
    strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) = (1 - x)⁻¹ := by
  have h := geometric_strongSum_mul x hx
  have hne := right_ne_zero_of_mul_eq_one h
  apply mul_right_cancel₀ hne
  rw [h, inv_mul_cancel₀ hne]

/-- Exact error after the powers indexed from zero through `N`. -/
theorem geometric_strongSum_remainder (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (N : ℕ) :
    strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) -
      ∑ n ∈ Finset.range (N + 1), x ^ n = x ^ (N + 1) / (1 - x) := by
  have hne := right_ne_zero_of_mul_eq_one (geometric_strongSum_mul x hx)
  rw [geometric_strongSum x hx]
  apply (eq_div_iff hne).mpr
  rw [sub_mul, inv_mul_cancel₀ hne, geom_sum_mul_neg]
  ring

/-- Exact valuation of the geometric remainder, with infinity when `x = 0`. -/
theorem valuation_geometric_strongSum_remainder (x : Surcomplex.{u})
    (hx : IsInfinitesimal x) (N : ℕ) :
    valuation (strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) -
      ∑ n ∈ Finset.range (N + 1), x ^ n) = (N + 1) • valuation x := by
  have hv : valuation (1 - x) = 0 := by
    rw [valuation.map_sub_eq_of_lt_left (by
      simpa only [valuation_one] using (isInfinitesimal_iff_valuation_pos x).mp hx),
      valuation_one]
  rw [geometric_strongSum_remainder x hx N, valuation_div, valuation.map_pow, hv, sub_zero]

/-- A nonzero infinitesimal's strong sum is never one of its finite partial sums. -/
theorem geometric_partialSum_ne_strongSum (x : Surcomplex.{u}) (hx : IsInfinitesimal x)
    (hzero : x ≠ 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), x ^ n ≠
      strongSum (fun n : ℕ => x ^ n) (stronglySummable_powers x hx) := by
  intro h
  have hr := geometric_strongSum_remainder x hx N
  rw [h, sub_self] at hr
  exact (div_ne_zero (pow_ne_zero _ hzero)
    (right_ne_zero_of_mul_eq_one (geometric_strongSum_mul x hx))) hr.symm

/-- For any nonzero input, geometric partial sums have no fine-topology limit. -/
theorem not_tendsto_geometric_partialSums (x : Surcomplex.{u}) (hzero : x ≠ 0)
    (y : Surcomplex.{u}) :
    ¬ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), x ^ n) atTop (𝓝 y) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_nhds_iff_eventually_eq _ _ _).mp h)
  have hs := hN (N + 1) (Nat.le_succ N)
  rw [Finset.sum_range_succ, hN N le_rfl] at hs
  exact (pow_ne_zero (N + 1) hzero) (add_eq_left.mp hs)

end

end Surreal.Surcomplex
