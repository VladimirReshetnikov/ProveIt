import GowersSzemeredi.Proofs18IntervalQuadraticDichotomy
import GowersSzemeredi.Proofs18NaturalReindex
import Mathlib.NumberTheory.Bertrand

/-! A prime-free density increment with constants fixed by the initial
density lower bound. Later stages may have greater actual density. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def intervalQuadraticGain (delta : Real) : Real :=
  quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) / 8

def intervalQuadraticLengthExponent (delta : Real) : Real :=
  quadraticDiscrepancyExponent (intervalQuadraticUniformityParameter delta) / 16

def intervalQuadraticLengthFactor (delta : Real) : Real :=
  quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) /
    (8 * boundaryRefinementConstant
      (quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) / 64))

def intervalQuadraticStepThreshold (delta : Real) : Real :=
  max 4 (max (quadraticExponentialThreshold (intervalQuadraticUniformityParameter delta))
    (max (32 / quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta))
      (8193 / delta ^ 4)))

theorem intervalQuadratic_constants_pos {delta : Real} (hδ : 0 < delta) :
    0 < intervalQuadraticGain delta ∧ 0 < intervalQuadraticLengthExponent delta ∧
      0 < intervalQuadraticLengthFactor delta := by
  have hα := intervalQuadraticUniformityParameter_pos hδ
  have hτ : 0 < quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) := by
    unfold quadraticDiscrepancyParameter
    positivity
  have hC := section5LocalRefinementConstant_pos 1
    (4 * Real.pi * (quadraticDiscrepancyParameter (intervalQuadraticUniformityParameter delta) / 64))
  refine ⟨div_pos hτ (by norm_num), ?_, div_pos hτ (mul_pos (by norm_num) hC)⟩
  unfold intervalQuadraticLengthExponent quadraticDiscrepancyExponent cor711Exponent
  positivity

/-- Choose a comparable prime, use the fixed initial uniformity parameter,
and reindex the selected progression. No primality condition remains in the
iteration interface, and the lower density d may increase at every step. -/
theorem interval_quadratic_iteration_step
    (delta : Real) (hδ : 0 < delta) (hδone : delta ≤ 1)
    (L : Nat) (hL : intervalQuadraticStepThreshold delta ≤ L)
    (B : Finset (Fin L)) (d : Real) (hd : delta ≤ d) (hcard : d * L ≤ B.card) :
    HasNatAP (B.image Fin.val) 4 ∨
      ∃ l : Nat, ∃ B' : Finset (Fin l),
        intervalQuadraticLengthFactor delta * (L : Real) ^ intervalQuadraticLengthExponent delta ≤ l ∧
        (d + intervalQuadraticGain delta) * l ≤ B'.card ∧
        (HasNatAP (B'.image Fin.val) 4 → HasNatAP (B.image Fin.val) 4) := by
  classical
  let alpha := intervalQuadraticUniformityParameter delta
  let tau := quadraticDiscrepancyParameter alpha
  have hα : 0 < alpha := intervalQuadraticUniformityParameter_pos hδ
  have hαone : alpha ≤ 1 := intervalQuadraticUniformityParameter_le_one hδ.le hδone
  have hτ : 0 < tau := by dsimp [tau, quadraticDiscrepancyParameter]; positivity
  obtain ⟨hfour, hexp, hscale, hlarge⟩ : (4 : Real) ≤ L ∧
      quadraticExponentialThreshold alpha ≤ L ∧ 32 / tau ≤ L ∧ 8193 / delta ^ 4 ≤ L := by
    simpa only [intervalQuadraticStepThreshold, max_le_iff, alpha, tau] using hL
  have hLfour : 4 ≤ L := by exact_mod_cast hfour
  have hLpos : (0 : Real) < L := by positivity
  obtain ⟨N, hNprime, hNlower, hNupper⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * L) (by omega)
  letI : NeZero N := ⟨hNprime.ne_zero⟩
  letI : Fact N.Prime := ⟨hNprime⟩
  have hLN : (L : Real) ≤ N := by exact_mod_cast (by omega : L ≤ N)
  let D : Real := B.card / (L : Real)
  have hDcard : (B.card : Real) = D * L := by dsimp [D]; field_simp
  have hdD : d ≤ D := (le_div_iff₀ hLpos).mpr hcard
  have hδD : delta ≤ D := hd.trans hdD
  have hDone : D ≤ 1 := by
    apply (div_le_one hLpos).mpr
    exact_mod_cast (show B.card ≤ L by simpa using Finset.card_le_univ B)
  have hDfour : delta ^ 4 ≤ D ^ 4 := pow_le_pow_left₀ hδ.le hδD 4
  by_cases hu : UniformOfDegree (intervalExtension N (finiteIntervalBalance B D)) alpha 2
  · left
    apply interval_relative_uniform_hasNatAP_four hNlower hLfour (by omega) B D alpha
      (hδ.le.trans hδD) hDone hα.le
    · exact (intervalQuadraticUniformityParameter_count_error delta).trans
        (div_le_div_of_nonneg_right hDfour (by norm_num))
    · have hb := (div_le_iff₀ (pow_pos hδ 4)).mp hlarge
      have hm := mul_le_mul hDfour hLN (Nat.cast_nonneg _) (pow_nonneg (hδ.le.trans hδD) 4)
      nlinarith
    · exact hu
  · right
    have hscaleN : 32 ≤ tau * N := by
      have hs := (div_le_iff₀ hτ).mp hscale
      have hm := mul_le_mul_of_nonneg_left hLN hτ.le
      nlinarith
    obtain ⟨Q, hQ, _, hsize, hinc⟩ := natural_interval_quadratic_density_increment
      alpha hα hαone N L hNlower (hexp.trans hLN) hscaleN B D
      (hδ.le.trans hδD) hDone hDcard hu
    refine ⟨Q.length, Q.pullback (B.image Fin.val), ?_, ?_, Q.hasNatAP_of_pullback hQ _⟩
    · apply le_trans _ hsize
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hLN (intervalQuadratic_constants_pos hδ).2.1.le)
        (intervalQuadratic_constants_pos hδ).2.2.le
    · rw [Q.card_pullback hQ]
      apply le_trans _ hinc
      exact mul_le_mul_of_nonneg_right (by change d + intervalQuadraticGain delta ≤ D + intervalQuadraticGain delta; linarith) (Nat.cast_nonneg _)

end LeanProofs.GowersSzemeredi
