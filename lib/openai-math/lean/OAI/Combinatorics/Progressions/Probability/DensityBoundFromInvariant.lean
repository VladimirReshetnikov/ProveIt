import OAI.Combinatorics.Progressions.Estimates.ZeroBasedExtremalSet
import OAI.Combinatorics.Progressions.Results.Statements

namespace OAI

section

namespace Erdos3

open Filter
open scoped BigOperators

theorem quantitativeDensityBound_of_eventually {k : ℕ} {C c η : ℝ}
    (hC : 0 < C) (hc : 0 < c) (hη : 0 < η)
    (hbound : ∀ᶠ N : ℕ in atTop, (extremalNumber k N : ℝ) ≤
      C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))) : QuantitativeDensityBound k := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hbound
  let C' := C + ∑ n ∈ Finset.range N₀, Real.exp (c * (Real.log (Real.log n)) ^ (1 + η))
  have hCC' : C ≤ C' := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
  refine ⟨C', c, η, hC.trans_le hCC', hc, hη, ?_⟩
  intro N _
  by_cases hlarge : N₀ ≤ N
  · exact (hN₀ N hlarge).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC' (Nat.cast_nonneg N)) (Real.exp_pos _).le)
  · have hNmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have hterm : Real.exp (c * (Real.log (Real.log N)) ^ (1 + η)) ≤ C' := by
      have hsum := Finset.single_le_sum (fun n (_ : n ∈ Finset.range N₀) => (Real.exp_pos
        (c * (Real.log (Real.log n)) ^ (1 + η))).le) hNmem
      exact hsum.trans (le_add_of_nonneg_left hC.le)
    have hscale : 1 ≤ C' * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) := by
      have h := mul_le_mul_of_nonneg_right hterm
        (Real.exp_pos (-c * (Real.log (Real.log N)) ^ (1 + η))).le
      have heq : Real.exp (c * (Real.log (Real.log N)) ^ (1 + η)) *
          Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) = 1 := by
        rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
      rwa [heq] at h
    have hcard : (extremalNumber k N : ℝ) ≤ N := by exact_mod_cast extremalNumber_le k N
    have hmul := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg (α := ℝ) N)
    nlinarith

end Erdos3

end

section

namespace Erdos3

open Filter

theorem quantitative_density_of_no_invariant {k : ℕ} (hk : 0 < k)
    {A β C₀ : ℝ} (hA : 0 < A) (hβ : 0 < β) (hβ1 : β < 1)
    (hno : ∀ S : APFreeInterval k,
      ¬ A * S.parameter ^ β + C₀ ≤ Real.log (Real.log S.length)) : QuantitativeDensityBound k := by
  let c := (1 / (2 * A)) ^ (1 / β)
  let η := 1 / β - 1
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have hη : 0 < η := by
    have hid : (1 / β) * β = 1 := one_div_mul_cancel hβ.ne'
    have hip : 0 < 1 / β := one_div_pos.mpr hβ
    dsimp [η]
    nlinarith
  have hηeq : 1 + η = 1 / β := by dsimp [η]; ring
  apply quantitativeDensityBound_of_eventually (Real.exp_pos 2) hc hη
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hloglog.eventually_ge_atTop (max 0 (2 * C₀)), eventually_ge_atTop (3 : ℕ)] with
    N hlarge hN
  obtain ⟨S, hS, hfree, hcard⟩ := exists_zero_based_extremalSet hk N
  by_cases hnonempty : S.Nonempty
  · let X : APFreeInterval k := ⟨N, by omega, S, hS, hnonempty, hfree⟩
    have hα : 0 < intervalDensity N S := intervalDensity_pos (by omega) hnonempty
    have hα1 : intervalDensity N S ≤ 1 := intervalDensity_le_one hS
    have hL : 0 ≤ Real.log (Real.log N) := (le_max_left _ _).trans hlarge
    have hC : 2 * C₀ ≤ Real.log (Real.log N) := (le_max_right _ _).trans hlarge
    have hfail : Real.log (Real.log N) < A * densityParameter (intervalDensity N S) ^ β + C₀ :=
      lt_of_not_ge (hno X)
    have hp := density_parameter_ge_of_invariant_failure hA hβ hL hC hfail
    have hdensity : intervalDensity N S ≤
        Real.exp 2 * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) := by
      calc
        _ ≤ Real.exp (2 - densityParameter (intervalDensity N S)) := density_le_exp_sub_parameter hα hα1
        _ ≤ Real.exp (2 - c * (Real.log (Real.log N)) ^ (1 + η)) := by
          apply Real.exp_le_exp.mpr
          rw [hηeq]
          linarith
        _ = _ := by simp only [sub_eq_add_neg, Real.exp_add, neg_mul]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    calc
      (extremalNumber k N : ℝ) = intervalDensity N S * N := by
        rw [← hcard]
        exact (div_mul_cancel₀ _ hN0).symm
      _ ≤ (Real.exp 2 * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))) * N :=
        mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg N)
      _ = _ := by ring
  · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [← hcard, hS0]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end Erdos3

end

end OAI
