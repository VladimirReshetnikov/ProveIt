import OAI.Combinatorics.Progressions.Fourier.UniformSpectrumLogBounds

namespace OAI

section

namespace Erdos3

def uniformRetainedBiasLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  uniformBlockAccuracyLog n j t p v w + E

def uniformSpectrumCardLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  uniformSpectrumSizeLog n j t p v w +
    (max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) : ℕ) * E

def uniformRetainedFrequencyLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  1 + majorArcCoverLog n j p v + (majorArcCoverExponent n j : ℕ) *
    uniformRetainedBiasLog n j t p v w E

def uniformRetainedDenominatorLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  j * (3 + majorArcCoverLog n j p v) + (majorArcCoverExponent n j * j : ℕ) *
      uniformRetainedBiasLog n j t p v w E +
    (w + t * majorArcLengthLog n p + (majorArcLengthExponent n * t : ℕ) *
      uniformRetainedBiasLog n j t p v w E) + 2

theorem uniformRetainedLogs_nonneg (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ uniformRetainedBiasLog n j t p v w E ∧
      0 ≤ uniformSpectrumCardLog n j t p v w E ∧
      0 ≤ uniformRetainedFrequencyLog n j t p v w E ∧
      0 ≤ uniformRetainedDenominatorLog n j t p v w E := by
  obtain ⟨_, hA, hS⟩ := uniformSpectrumLogs_nonneg n j t hp hv hw
  have hC := majorArcCoverLog_nonneg n j hp hv
  have hL := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hB : 0 ≤ uniformRetainedBiasLog n j t p v w E := by
    unfold uniformRetainedBiasLog
    positivity
  refine ⟨hB, ?_, ?_, ?_⟩
  · unfold uniformSpectrumCardLog
    positivity
  · unfold uniformRetainedFrequencyLog
    positivity
  · unfold uniformRetainedDenominatorLog
    positivity

theorem uniformBlockRetainedBias_inverse_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    (uniformBlockRetainedBias n j t U V W ε)⁻¹ ≤
      Real.exp (uniformRetainedBiasLog n j t p v w E) := by
  have hA := uniformBlockSpectrumAccuracy_exp_bound n j t hU hV hp hv hw hUp hVv hWw
  rw [uniformBlockRetainedBias_eq n j t hU hW hε1, inv_div, div_eq_mul_inv]
  exact (mul_le_mul hA hεE (inv_nonneg.mpr hε.le) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm

theorem uniformSpectrumCardBound_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    uniformSpectrumSizeConstant n j t U V W /
        ε ^ max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) ≤
      Real.exp (uniformSpectrumCardLog n j t p v w E) := by
  have hS := uniformSpectrumSizeConstant_exp_bound n j t hU hV hW hp hv hw hUp hVv hWw
  have hpow := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hε.le) hεE hE
    (max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t)) le_rfl
  have hbound := (mul_le_mul hS hpow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  simpa only [uniformSpectrumCardLog, div_eq_mul_inv, inv_pow] using hbound

theorem uniformBlockSpectrumCardBudget_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    uniformBlockSpectrumCardBudget n j t U V W (uniformBlockRetainedBias n j t U V W ε) ≤
      Real.exp (uniformSpectrumCardLog n j t p v w E) := by
  exact (uniformBlockSpectrumCardBudget_le_accuracy_power n j t hU hW hε hε1).trans
    (uniformSpectrumCardBound_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE)

theorem uniformRetainedFrequency_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    2 * majorArcCoverConstant n j U V /
        (uniformBlockRetainedBias n j t U V W ε) ^ majorArcCoverExponent n j ≤
      Real.exp (uniformRetainedFrequencyLog n j t p v w E) := by
  have hζ : 0 ≤ uniformBlockRetainedBias n j t U V W ε :=
    (uniformBlockRetainedBias_spec n j t hU hW hε).1.le
  have hB := uniformBlockRetainedBias_inverse_exp_bound n j t hU hV hW hε hε1 hp hv hw
    hUp hVv hWw hεE
  have hB0 := (uniformRetainedLogs_nonneg n j t hp hv hw hE).1
  have hC := majorArcCoverConstant_exp_bound n j (zero_le_one.trans hU) hp hv hUp hVv
  have hC0 := zero_le_one.trans (majorArcCoverConstant_one_le n j hU hV)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbase := (mul_le_mul htwo hC hC0 (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hpow := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (majorArcCoverExponent n j) le_rfl
  have hbound := (mul_le_mul hbase hpow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  simpa only [uniformRetainedFrequencyLog, div_eq_mul_inv, inv_pow] using hbound

theorem uniformCharacterDenominatorBound_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    uniformCharacterDenominatorBound n j t U V W (uniformBlockRetainedBias n j t U V W ε) ≤
      Real.exp (uniformRetainedDenominatorLog n j t p v w E) := by
  let ζ := uniformBlockRetainedBias n j t U V W ε
  have hζ : 0 ≤ ζ := (uniformBlockRetainedBias_spec n j t hU hW hε).1.le
  have hB := uniformBlockRetainedBias_inverse_exp_bound n j t hU hV hW hε hε1 hp hv hw
    hUp hVv hWw hεE
  have hB0 := (uniformRetainedLogs_nonneg n j t hp hv hw hE).1
  have hC := majorArcCoverConstant_exp_bound n j (zero_le_one.trans hU) hp hv hUp hVv
  have hC0 := zero_le_one.trans (majorArcCoverConstant_one_le n j hU hV)
  have hClog := majorArcCoverLog_nonneg n j hp hv
  have hL := (majorArcConstants_exp_bounds n (zero_le_one.trans hU) hp hUp).2.2.1
  have hL0 := (majorArcLengthConstant_pos n hU).le
  have hLlog := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hthree : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hbase := (mul_le_mul hthree hC hC0 (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hnum := pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) j le_rfl
  have hpowC := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (majorArcCoverExponent n j * j) le_rfl
  have hfirst := (mul_le_mul hnum hpowC (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hLt := pow_le_exp_mul_of_le_exp hL0 hL hLlog t le_rfl
  have hpowL := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (majorArcLengthExponent n * t) le_rfl
  have hsecond := mul_le_mul
    (mul_le_mul hWw hLt (pow_nonneg hL0 _) (Real.exp_pos _).le) hpowL (by positivity) (by positivity)
  simp only [← Real.exp_add] at hsecond
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ (j : ℝ) * (3 + majorArcCoverLog n j p v) +
      ((majorArcCoverExponent n j * j : ℕ) : ℝ) * uniformRetainedBiasLog n j t p v w E)
    (by positivity : 0 ≤ w + (t : ℝ) * majorArcLengthLog n p +
      ((majorArcLengthExponent n * t : ℕ) : ℝ) * uniformRetainedBiasLog n j t p v w E)
    hfirst hsecond
  have hplus := one_add_le_exp_succ (by positivity) hsum
  unfold uniformCharacterDenominatorBound
  simp only [div_eq_mul_inv]
  calc
    _ = 1 + ((3 * majorArcCoverConstant n j U V) ^ j * ζ⁻¹ ^ (majorArcCoverExponent n j * j) +
        W * majorArcLengthConstant n U ^ t * ζ⁻¹ ^ (majorArcLengthExponent n * t)) := by ring
    _ ≤ _ := hplus
    _ = _ := by unfold uniformRetainedDenominatorLog; congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem uniformScaledRetainedFrequencyBound_le (n d : ℕ) {U V ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    uniformScaledRetainedFrequencyBound n d U V ζ ≤
      2 * majorArcCoverConstant n d U V / ζ ^ majorArcCoverExponent n d := by
  have hX := one_le_inverse_power (majorArcCoverConstant_one_le n d hU hV) hζ hζ1
    (majorArcCoverExponent n d)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ majorArcCoverConstant n d U V /
    ζ ^ majorArcCoverExponent n d by linarith)
  unfold uniformScaledRetainedFrequencyBound
  rw [mul_div_assoc]
  linarith

theorem uniformScaledRetainedDenominatorBound_le (n d t : ℕ) {U V W ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    uniformScaledRetainedDenominatorBound n d t U V W ζ ≤
      uniformCharacterDenominatorBound n d t U V W ζ := by
  have hX := one_le_inverse_power (majorArcCoverConstant_one_le n d hU hV) hζ hζ1
    (majorArcCoverExponent n d)
  have hf := uniformScaledRetainedFrequencyBound_le n d hU hV hζ hζ1
  rw [mul_div_assoc] at hf
  have hnonneg := uniformScaledRetainedFrequencyBound_nonneg n d U V ζ
  have hb : uniformScaledRetainedFrequencyBound n d U V ζ + 1 ≤
      3 * (majorArcCoverConstant n d U V / ζ ^ majorArcCoverExponent n d) := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ uniformScaledRetainedFrequencyBound n d U V ζ + 1) hb d
  have he : (3 * (majorArcCoverConstant n d U V / ζ ^ majorArcCoverExponent n d)) ^ d =
      (3 * majorArcCoverConstant n d U V) ^ d / ζ ^ (majorArcCoverExponent n d * d) := by
    rw [← mul_div_assoc, div_pow, pow_mul]
  rw [he] at hp
  have hl : 0 ≤ W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t) :=
    div_nonneg (mul_nonneg hW (pow_nonneg (majorArcLengthConstant_pos n hU).le _)) (pow_pos hζ _).le
  have hn : 0 ≤ (3 * majorArcCoverConstant n d U V) ^ d / ζ ^ (majorArcCoverExponent n d * d) := by
    have := (majorArcCoverConstant_one_le n d hU hV)
    positivity
  unfold uniformScaledRetainedDenominatorBound uniformCharacterDenominatorBound
  exact max_le (by linarith) (by linarith)

theorem uniformScaledRetained_exp_bounds (n d t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    let ζ := uniformBlockRetainedBias n d t U V W ε
    uniformScaledRetainedFrequencyBound n d U V ζ ≤ Real.exp (uniformRetainedFrequencyLog n d t p v w E) ∧
    uniformScaledRetainedDenominatorBound n d t U V W ζ ≤ Real.exp (uniformRetainedDenominatorLog n d t p v w E) := by
  obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n d t hU hW hε
  exact ⟨(uniformScaledRetainedFrequencyBound_le n d hU hV hζ hζ1).trans
      (uniformRetainedFrequency_exp_bound n d t hU hV hW hε hε1 hp hv hw hE hUp hVv hWw hεE),
    (uniformScaledRetainedDenominatorBound_le n d t hU hV hW hζ hζ1).trans
      (uniformCharacterDenominatorBound_exp_bound n d t hU hV hW hε hε1 hp hv hw hE hUp hVv hWw hεE)⟩

end Erdos3

end

end OAI
