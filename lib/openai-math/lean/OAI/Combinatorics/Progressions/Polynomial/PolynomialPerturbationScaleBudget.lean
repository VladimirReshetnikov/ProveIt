import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

noncomputable def polynomialPerturbationScale (K M Q τ : ℝ) (m : ℕ) : ℝ :=
  min 1 (min (1 / (2 * (1 + K) * (1 + M)))
    (τ ^ 2 / (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M))))

theorem polynomialPerturbationScale_spec {K M Q τ : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (m : ℕ) :
    let t := polynomialPerturbationScale K M Q τ m
    0 < t ∧ t ≤ 1 ∧ K * (t * M) ≤ 1 / 2 ∧ t * M ≤ 1 ∧
      4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M))) ≤ τ := by
  let t := polynomialPerturbationScale K M Q τ m
  have ht : 0 < t := by dsimp [t, polynomialPerturbationScale]; positivity
  have ht1 : t ≤ 1 := min_le_left _ _
  have htK : t ≤ 1 / (2 * (1 + K) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htQ : t ≤ τ ^ 2 / (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hden : t * (2 * (1 + K) * (1 + M)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp htK
  have h2KM : 2 * K * M ≤ 2 * (1 + K) * (1 + M) := by nlinarith
  have hMden : M ≤ 2 * (1 + K) * (1 + M) := by nlinarith [mul_nonneg hK hM]
  have hsmall : K * (t * M) ≤ 1 / 2 := by
    have hh := (mul_le_mul_of_nonneg_left h2KM ht.le).trans hden
    nlinarith
  have hsecond : t * M ≤ 1 := (mul_le_mul_of_nonneg_left hMden ht.le).trans hden
  refine ⟨ht, ht1, hsmall, hsecond, ?_⟩
  have hdenQ : t * (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) ≤ τ ^ 2 :=
    (le_div_iff₀ (by positivity)).mp htQ
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hm2 : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hpoly : 16 * (m : ℝ) ^ 2 * Q * (1 + M) ≤
      16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M) := by
    gcongr
    linarith
  have hb := (mul_le_mul_of_nonneg_left hpoly ht.le).trans hdenQ
  have hroot := Real.sq_sqrt (show 0 ≤ Q * (t * (1 + M)) by positivity)
  have hroot0 := Real.sqrt_nonneg (Q * (t * (1 + M)))
  have hsquare : (4 * (m : ℝ) * Real.sqrt (Q * (t * (1 + M)))) ^ 2 ≤ τ ^ 2 := by
    calc
      _ = t * (16 * (m : ℝ) ^ 2 * Q * (1 + M)) := by
        rw [mul_pow, mul_pow, hroot]
        ring
      _ ≤ _ := hb
  nlinarith [mul_nonneg (show 0 ≤ 4 * (m : ℝ) by positivity) hroot0]

end Erdos3

end

section

namespace Erdos3

theorem polynomialPerturbationScale_inv_le {K M Q τ P : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (hP : 0 ≤ P)
    (m : ℕ) (hKP : 1 + K ≤ Real.exp P) (hMP : 1 + M ≤ Real.exp P)
    (hQP : 1 + Q ≤ Real.exp P) (hmP : (m : ℝ) + 1 ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) :
    (polynomialPerturbationScale K M Q τ m)⁻¹ ≤ 16 * Real.exp (6 * P) := by
  let E := 16 * Real.exp (6 * P)
  have hE : 0 < E := by dsimp [E]; positivity
  have hE1 : 1 ≤ E := by
    have he : 1 ≤ Real.exp (6 * P) := Real.one_le_exp_iff.mpr (by positivity)
    dsimp [E]
    linarith
  have hD1 : 2 * (1 + K) * (1 + M) ≤ E := by
    calc
      _ ≤ 2 * Real.exp P * Real.exp P := by gcongr
      _ = 2 * Real.exp (2 * P) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ 16 * Real.exp (6 * P) := by
        have he : Real.exp (2 * P) ≤ Real.exp (6 * P) := Real.exp_le_exp.mpr (by linarith)
        nlinarith [Real.exp_pos (6 * P)]
  have hD2 : (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) / τ ^ 2 ≤ E := by
    calc
      _ = 16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M) * (τ⁻¹) ^ 2 := by
        rw [div_eq_mul_inv, inv_pow]
      _ ≤ 16 * (Real.exp P) ^ 2 * Real.exp P * Real.exp P * (Real.exp P) ^ 2 := by gcongr
      _ = E := by
        rw [← Real.exp_nat_mul]
        simp only [mul_assoc, ← Real.exp_add]
        dsimp [E]
        congr 2
        ring
  have hsmall : 1 / E ≤ polynomialPerturbationScale K M Q τ m := by
    unfold polynomialPerturbationScale
    refine le_min ?_ (le_min ?_ ?_)
    · exact (div_le_iff₀ hE).mpr (by simpa using hE1)
    · exact one_div_le_one_div_of_le (by positivity) hD1
    · have he := one_div_le_one_div_of_le
        (by positivity : 0 < (16 * ((m : ℝ) + 1) ^ 2 * (1 + Q) * (1 + M)) / τ ^ 2) hD2
      simpa only [one_div_div] using he
  have hi := one_div_le_one_div_of_le (div_pos zero_lt_one hE) hsmall
  simpa only [one_div, inv_inv] using hi

theorem polynomialPerturbationScale_log_inv_le {K M Q τ P : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (hP : 0 ≤ P)
    (m : ℕ) (hKP : 1 + K ≤ Real.exp P) (hMP : 1 + M ≤ Real.exp P)
    (hQP : 1 + Q ≤ Real.exp P) (hmP : (m : ℝ) + 1 ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) :
    Real.log (polynomialPerturbationScale K M Q τ m)⁻¹ ≤ Real.log 16 + 6 * P := by
  have ht := (polynomialPerturbationScale_spec hK hM hQ hτ m).1
  have hi := polynomialPerturbationScale_inv_le hK hM hQ hτ hP m hKP hMP hQP hmP hτP
  have he := Real.log_le_log (inv_pos.mpr ht) hi
  simpa only [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] using he

end Erdos3

end

end OAI
