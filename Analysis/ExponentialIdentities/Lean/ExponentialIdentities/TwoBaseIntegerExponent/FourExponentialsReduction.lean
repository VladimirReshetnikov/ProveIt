import ExponentialIdentities.TwoBaseIntegerExponent
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Reduction to Four Exponentials

This file formalizes the precise connection between the Alaoglu--Erdős conjecture and the
classical Four Exponentials Conjecture.  It proves the two required rational linear-independence
statements unconditionally, then derives `AlaogluErdosConjecture` from the real specialization of
Four Exponentials.  The conjectural input is recorded as a `Prop`, not asserted as an axiom.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-- An irrational real number is rationally linearly independent from one. -/
theorem linearIndependent_one_irrational {x : ℝ} (hx : Irrational x) :
    LinearIndependent ℚ ![(1 : ℝ), x] := by
  rw [LinearIndependent.pair_iff' (by norm_num : (1 : ℝ) ≠ 0)]
  intro q hq
  apply hx
  refine ⟨q, ?_⟩
  simpa using hq

/-- The logarithms of two and three are linearly independent over the rationals. -/
theorem linearIndependent_log_two_log_three :
    LinearIndependent ℚ ![Real.log 2, Real.log 3] := by
  rw [LinearIndependent.pair_iff'
    (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))]
  intro q hq
  change (q : ℝ) * Real.log 2 = Real.log 3 at hq
  have hqposR : (0 : ℝ) < q := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    by_contra hnpos
    have : (q : ℝ) ≤ 0 := le_of_not_gt hnpos
    nlinarith
  have hqpos : 0 < q := by exact_mod_cast hqposR
  have hnumpos : 0 < q.num := Rat.num_pos.mpr hqpos
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hnumpos.le
  have hmpos : 0 < m := by
    rw [hm] at hnumpos
    exact_mod_cast hnumpos
  have heq : (m : ℝ) * Real.log 2 = (q.den : ℝ) * Real.log 3 := by
    rw [Rat.cast_def, hm] at hq
    field_simp at hq
    simpa [mul_comm] using hq
  have hpowR : (2 : ℝ) ^ m = (3 : ℝ) ^ q.den := by
    apply Real.strictMonoOn_log.injOn
    · simp only [Set.mem_Ioi]
      positivity
    · simp only [Set.mem_Ioi]
      positivity
    simpa only [Real.log_pow] using heq
  have hpow : 2 ^ m = 3 ^ q.den := by exact_mod_cast hpowR
  have htwo_dvd : 2 ∣ 3 ^ q.den := by
    rw [← hpow]
    exact dvd_pow_self 2 hmpos.ne'
  have : 2 ∣ 3 := Nat.prime_two.dvd_of_dvd_pow htwo_dvd
  norm_num at this

/-- The real specialization of the classical Four Exponentials Conjecture. -/
def RealFourExponentialsConjecture : Prop :=
  ∀ u v : Fin 2 → ℝ,
    LinearIndependent ℚ u →
    LinearIndependent ℚ v →
    ∃ i j : Fin 2, Transcendental ℚ (Real.exp (u i * v j))

/-- The real Four Exponentials Conjecture implies the Alaoglu--Erdős conjecture. -/
theorem alaogluErdosConjecture_of_realFourExponentialsConjecture
    (hfour : RealFourExponentialsConjecture) : AlaogluErdosConjecture := by
  intro x h₂ h₃
  by_cases hxirr : Irrational x
  · have h₂alg : IsAlgebraic ℚ ((2 : ℝ) ^ x) := by
      obtain ⟨z, hz⟩ := h₂
      rw [← hz]
      exact isAlgebraic_int z
    have h₃alg : IsAlgebraic ℚ ((3 : ℝ) ^ x) := by
      obtain ⟨z, hz⟩ := h₃
      rw [← hz]
      exact isAlgebraic_int z
    obtain ⟨i, j, hij⟩ := hfour ![(1 : ℝ), x] ![Real.log 2, Real.log 3]
      (linearIndependent_one_irrational hxirr)
      linearIndependent_log_two_log_three
    exfalso
    apply hij
    fin_cases i <;> fin_cases j
    · simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
        (isAlgebraic_nat (R := ℚ) (A := ℝ) 2)
    · simpa [Real.exp_log (by norm_num : (0 : ℝ) < 3)] using
        (isAlgebraic_nat (R := ℚ) (A := ℝ) 3)
    · simpa [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm] using h₂alg
    · simpa [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), mul_comm] using h₃alg
  · apply IntegerExponent.integer_of_rational_of_two_rpow_integer
    · obtain ⟨q, hq⟩ := exists_rat_of_not_irrational hxirr
      exact ⟨q, hq.symm⟩
    · exact h₂

end LeanProofs.TwoBaseIntegerExponent
