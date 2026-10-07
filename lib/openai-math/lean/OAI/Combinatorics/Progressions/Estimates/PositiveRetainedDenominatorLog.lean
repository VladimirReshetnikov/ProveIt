import OAI.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
import OAI.Combinatorics.Progressions.Fourier.UniformSpectrumLogBounds

namespace OAI

section

namespace Erdos3

def positiveModerateLengthLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  majorArcLengthLog n p + majorArcLengthLog (n + 1) p + 2

def positiveModerateCoverLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  majorArcLengthLog (n + 1) p + 1 + majorArcCoverLog n j p (v + 4) +
    majorArcCoverLog (n + 1) j p v + 1

def positiveModerateSpectrumLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  j * (195 + 4 * positiveModerateCoverLog n j p v)

def positiveModerateAccuracyLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w : A) : A :=
  1 + positiveModerateSpectrumLog n j p v + (positiveModerateSpectrumExponent n j : ℕ) +
    (w + t * ((positiveModerateLengthExponent n : ℕ) + positiveModerateLengthLog n p)) + 2

theorem positiveModerateLogs_nonneg (n j t : ℕ) {p v w : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ positiveModerateLengthLog n p ∧ 0 ≤ positiveModerateCoverLog n j p v ∧
      0 ≤ positiveModerateSpectrumLog n j p v ∧ 0 ≤ positiveModerateAccuracyLog n j t p v w := by
  have hn := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hn1 := (majorArcBaseLogs_nonneg (n + 1) hp).2.2.1
  have hc := majorArcCoverLog_nonneg n j hp (by positivity : 0 ≤ v + 4)
  have hc1 := majorArcCoverLog_nonneg (n + 1) j hp hv
  have hL : 0 ≤ positiveModerateLengthLog n p := by unfold positiveModerateLengthLog; positivity
  have hC : 0 ≤ positiveModerateCoverLog n j p v := by unfold positiveModerateCoverLog; positivity
  have hS : 0 ≤ positiveModerateSpectrumLog n j p v := by unfold positiveModerateSpectrumLog; positivity
  refine ⟨hL, hC, hS, ?_⟩
  unfold positiveModerateAccuracyLog
  positivity

theorem positiveModerateLengthConstant_exp_bound (n : ℕ) {U p : ℝ}
    (hU : 0 ≤ U) (hp : 0 ≤ p) (hUp : U ≤ Real.exp p) :
    positiveModerateLengthConstant n U ≤ Real.exp (positiveModerateLengthLog n p) := by
  have hn := (majorArcConstants_exp_bounds n hU hp hUp).2.2.1
  have hn1 := (majorArcConstants_exp_bounds (n + 1) hU hp hUp).2.2.1
  have hn0 := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hn10 := (majorArcBaseLogs_nonneg (n + 1) hp).2.2.1
  have hfirst := one_add_le_exp_succ hn0 hn
  have hsum := add_le_exp_add_one (by positivity : 0 ≤ majorArcLengthLog n p + 1) hn10 hfirst hn1
  exact hsum.trans_eq (by unfold positiveModerateLengthLog; congr 1; ring)

theorem positiveModerateCoverConstant_exp_bound (n j : ℕ) {U V p v : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) :
    positiveModerateCoverConstant n j U V ≤ Real.exp (positiveModerateCoverLog n j p v) := by
  have hl := (majorArcConstants_exp_bounds (n + 1) hU hp hUp).2.2.1
  have hl0 := (majorArcBaseLogs_nonneg (n + 1) hp).2.2.1
  have hplus := one_add_le_exp_succ hl0 hl
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have h4V : 4 * V ≤ Real.exp (v + 4) :=
    (mul_le_mul hfour hVv hV (Real.exp_pos _).le).trans_eq
      (by rw [← Real.exp_add, add_comm])
  have hc := majorArcCoverConstant_exp_bound n j hU hp (by positivity : 0 ≤ v + 4) hUp h4V
  have hc1 := majorArcCoverConstant_exp_bound (n + 1) j hU hp hv hUp hVv
  have hcc : 0 ≤ majorArcCoverConstant n j U (4 * V) := by
    simp only [majorArcCoverConstant, majorArcBiasConstant, majorArcErrorConstant, majorArcLocalizationConstant]
    positivity
  have hprod := (mul_le_mul hplus hc hcc (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hc0 := majorArcCoverLog_nonneg n j hp (by positivity : 0 ≤ v + 4)
  have hc10 := majorArcCoverLog_nonneg (n + 1) j hp hv
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ majorArcLengthLog (n + 1) p + 1 + majorArcCoverLog n j p (v + 4))
    hc10 hprod hc1
  exact hsum

theorem positiveModerateSpectrumConstant_exp_bound (n j : ℕ) {U V p v : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) :
    positiveModerateSpectrumConstant n j U V ≤ Real.exp (positiveModerateSpectrumLog n j p v) := by
  have hc := positiveModerateCoverConstant_exp_bound n j (zero_le_one.trans hU) hV hp hv hUp hVv
  have hc0 := (positiveModerateCoverConstant_one_le n j hU hV).trans' zero_le_one
  have hlog := (positiveModerateLogs_nonneg n j 0 hp hv (le_refl (0 : ℝ))).2.1
  have hp4 := pow_le_exp_mul_of_le_exp hc0 hc hlog 4 le_rfl
  have h195 : (195 : ℝ) ≤ Real.exp 195 := by linarith [Real.add_one_le_exp (195 : ℝ)]
  have hbase := (mul_le_mul h195 hp4 (pow_nonneg hc0 _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  exact pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) j le_rfl

theorem positiveModerateAccuracyScale_exp_bound (n j t : ℕ) {U V W p v w : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w) :
    positiveModerateAccuracyScale n j t U V W ≤ Real.exp (positiveModerateAccuracyLog n j t p v w) := by
  have hlen := positiveModerateLengthConstant_exp_bound n (zero_le_one.trans hU) hp hUp
  have hspec := positiveModerateSpectrumConstant_exp_bound n j hU hV hp hv hUp hVv
  obtain ⟨hL, _, hS, _⟩ := positiveModerateLogs_nonneg n j t hp hv hw
  have hlen0 := (positiveModerateLengthConstant_pos n hU).le
  have hspec0 : 0 ≤ positiveModerateSpectrumConstant n j U V := by
    unfold positiveModerateSpectrumConstant
    positivity
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowS : (2 : ℝ) ^ positiveModerateSpectrumExponent n j ≤
      Real.exp (positiveModerateSpectrumExponent n j : ℝ) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (positiveModerateSpectrumExponent n j) le_rfl
  have hpowL : (2 : ℝ) ^ positiveModerateLengthExponent n ≤
      Real.exp (positiveModerateLengthExponent n : ℝ) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (positiveModerateLengthExponent n) le_rfl
  have hfirst : 2 * positiveModerateSpectrumConstant n j U V * 2 ^ positiveModerateSpectrumExponent n j ≤
      Real.exp (1 + positiveModerateSpectrumLog n j p v + (positiveModerateSpectrumExponent n j : ℝ)) := by
    have hh := mul_le_mul (mul_le_mul htwo hspec hspec0 (Real.exp_pos _).le) hpowS
      (by positivity) (by positivity)
    simpa only [← Real.exp_add] using hh
  have hbase := (mul_le_mul hpowL hlen hlen0 (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hbasepow := pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) t le_rfl
  have hsecond := (mul_le_mul hWw hbasepow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ 1 + positiveModerateSpectrumLog n j p v + (positiveModerateSpectrumExponent n j : ℝ))
    (by positivity : 0 ≤ w + (t : ℝ) * ((positiveModerateLengthExponent n : ℝ) + positiveModerateLengthLog n p))
    hfirst hsecond
  have hplus := one_add_le_exp_succ (by positivity) hsum
  exact hplus.trans_eq (by unfold positiveModerateAccuracyLog; congr 1; ring)

end Erdos3

end

section

namespace Erdos3

def positiveRetainedBiasLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w E : A) : A :=
  positiveModerateAccuracyLog n j t p v w + E

def positiveSpectrumCardLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w E : A) : A :=
  positiveModerateSpectrumLog n j p v + (positiveModerateSpectrumExponent n j : ℕ) *
      positiveRetainedBiasLog n j t p v w E +
    (w + t * positiveModerateLengthLog n p + (positiveModerateLengthExponent n * t : ℕ) *
      positiveRetainedBiasLog n j t p v w E) + 1

def positiveRetainedFrequencyLog {A : Type*} [Semiring A] (n j t : ℕ) (p v w E : A) : A :=
  positiveModerateCoverLog n j p v + (positiveModerateCoverExponent n j : ℕ) *
    positiveRetainedBiasLog n j t p v w E + 1

theorem positiveRetainedLogs_nonneg (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ positiveRetainedBiasLog n j t p v w E ∧
      0 ≤ positiveSpectrumCardLog n j t p v w E ∧
      0 ≤ positiveRetainedFrequencyLog n j t p v w E := by
  obtain ⟨hL, hC, hS, hA⟩ := positiveModerateLogs_nonneg n j t hp hv hw
  have hB : 0 ≤ positiveRetainedBiasLog n j t p v w E := by
    unfold positiveRetainedBiasLog
    positivity
  refine ⟨hB, ?_, ?_⟩
  · unfold positiveSpectrumCardLog
    positivity
  · unfold positiveRetainedFrequencyLog
    positivity

theorem positiveModerateRetainedBias_inverse_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    (positiveModerateRetainedBias n j t U V W ε)⁻¹ ≤
      Real.exp (positiveRetainedBiasLog n j t p v w E) := by
  have hA := positiveModerateAccuracyScale_exp_bound n j t hU hV hp hv hw hUp hVv hWw
  unfold positiveModerateRetainedBias positiveRetainedBiasLog
  rw [inv_div, div_eq_mul_inv]
  exact (mul_le_mul hA hεE (inv_nonneg.mpr hε.le) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm

theorem positiveModerateSpectrumCardBudget_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    positiveModerateSpectrumCardBudget n j t U V W ε ≤
      Real.exp (positiveSpectrumCardLog n j t p v w E) := by
  let ζ := positiveModerateRetainedBias n j t U V W ε
  have hζ : 0 ≤ ζ := div_nonneg hε.le
    (zero_le_one.trans (positiveModerateAccuracyScale_one_le n j t (V := V) hU hW))
  have hB := positiveModerateRetainedBias_inverse_exp_bound n j t hU hV hε hp hv hw
    hUp hVv hWw hεE
  have hB0 := (positiveRetainedLogs_nonneg n j t hp hv hw hE).1
  obtain ⟨hL0, _, hS0, _⟩ := positiveModerateLogs_nonneg n j t hp hv hw
  have hL := positiveModerateLengthConstant_exp_bound n (zero_le_one.trans hU) hp hUp
  have hLnonneg := (positiveModerateLengthConstant_pos n hU).le
  have hS := positiveModerateSpectrumConstant_exp_bound n j hU hV hp hv hUp hVv
  have hBS := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (positiveModerateSpectrumExponent n j) le_rfl
  have hBL := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (positiveModerateLengthExponent n * t) le_rfl
  have hLt := pow_le_exp_mul_of_le_exp hLnonneg hL hL0 t le_rfl
  have hfirst := (mul_le_mul hS hBS (pow_nonneg (inv_nonneg.mpr hζ) _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hsecond := mul_le_mul
    (mul_le_mul hWw hLt (pow_nonneg hLnonneg _) (Real.exp_pos _).le) hBL
    (pow_nonneg (inv_nonneg.mpr hζ) _) (by positivity)
  simp only [← Real.exp_add] at hsecond
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ positiveModerateSpectrumLog n j p v +
      (positiveModerateSpectrumExponent n j : ℝ) * positiveRetainedBiasLog n j t p v w E)
    (by positivity : 0 ≤ w + (t : ℝ) * positiveModerateLengthLog n p +
      ((positiveModerateLengthExponent n * t : ℕ) : ℝ) * positiveRetainedBiasLog n j t p v w E)
    hfirst hsecond
  simpa only [positiveModerateSpectrumCardBudget, positiveSpectrumCardLog, div_eq_mul_inv, inv_pow] using hsum

theorem positiveRetainedFrequencyBound_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    positiveRetainedFrequencyBound n j U V (positiveModerateRetainedBias n j t U V W ε) ≤
      Real.exp (positiveRetainedFrequencyLog n j t p v w E) := by
  let ζ := positiveModerateRetainedBias n j t U V W ε
  have hζ : 0 ≤ ζ := div_nonneg hε.le
    (zero_le_one.trans (positiveModerateAccuracyScale_one_le n j t (V := V) hU hW))
  have hB := positiveModerateRetainedBias_inverse_exp_bound n j t hU hV hε hp hv hw
    hUp hVv hWw hεE
  have hB0 := (positiveRetainedLogs_nonneg n j t hp hv hw hE).1
  have hC := positiveModerateCoverConstant_exp_bound n j (zero_le_one.trans hU) hV hp hv hUp hVv
  have hC0 := (positiveModerateCoverConstant_one_le n j hU hV).trans' zero_le_one
  have hClog := (positiveModerateLogs_nonneg n j t hp hv hw).2.1
  have hpow := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (positiveModerateCoverExponent n j) le_rfl
  have hraw := (mul_le_mul hC hpow (pow_nonneg (inv_nonneg.mpr hζ) _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hplus := one_add_le_exp_succ
    (by positivity : 0 ≤ positiveModerateCoverLog n j p v +
      (positiveModerateCoverExponent n j : ℝ) * positiveRetainedBiasLog n j t p v w E) hraw
  unfold positiveRetainedFrequencyBound
  calc
    _ ≤ positiveModerateCoverConstant n j U V / ζ ^ positiveModerateCoverExponent n j + 1 :=
      (Nat.ceil_lt_add_one (div_nonneg hC0 (pow_nonneg hζ _))).le
    _ ≤ Real.exp (positiveRetainedFrequencyLog n j t p v w E) := by
      simpa only [positiveRetainedFrequencyLog, div_eq_mul_inv, inv_pow, add_comm] using hplus

end Erdos3

end

section

namespace Erdos3

def positiveRetainedDenominatorLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  j * (positiveRetainedFrequencyLog n j t p v w E + 1) +
    (w + t * positiveModerateLengthLog n p + (positiveModerateLengthExponent n * t : ℕ) *
      positiveRetainedBiasLog n j t p v w E)

def positiveRetainedComplexityLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w E : A) : A :=
  positiveSpectrumCardLog n j t p v w E + positiveRetainedFrequencyLog n j t p v w E +
    positiveRetainedDenominatorLog n j t p v w E

theorem positiveRetainedDenominatorLog_nonneg (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ positiveRetainedDenominatorLog n j t p v w E := by
  obtain ⟨hB, _, hF⟩ := positiveRetainedLogs_nonneg n j t hp hv hw hE
  have hL := (positiveModerateLogs_nonneg n j t hp hv hw).1
  unfold positiveRetainedDenominatorLog
  positivity

theorem positiveRetainedComplexityLog_bounds (n j t : ℕ) {p v w E : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E) :
    0 ≤ positiveRetainedComplexityLog n j t p v w E ∧
      positiveSpectrumCardLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p v w E ∧
      positiveRetainedFrequencyLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p v w E ∧
      positiveRetainedDenominatorLog n j t p v w E ≤ positiveRetainedComplexityLog n j t p v w E := by
  obtain ⟨_, hC, hF⟩ := positiveRetainedLogs_nonneg n j t hp hv hw hE
  have hD := positiveRetainedDenominatorLog_nonneg n j t hp hv hw hE
  unfold positiveRetainedComplexityLog
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem positiveRetainedDenominatorBound_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    positiveRetainedDenominatorBound n j t U V W (positiveModerateRetainedBias n j t U V W ε) ≤
      Real.exp (positiveRetainedDenominatorLog n j t p v w E) := by
  let ζ := positiveModerateRetainedBias n j t U V W ε
  have hζ : 0 ≤ ζ := div_nonneg hε.le
    (zero_le_one.trans (positiveModerateAccuracyScale_one_le n j t (V := V) hU hW))
  obtain ⟨hB0, _, hF0⟩ := positiveRetainedLogs_nonneg n j t hp hv hw hE
  have hL0 := (positiveModerateLogs_nonneg n j t hp hv hw).1
  have hF := positiveRetainedFrequencyBound_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE
  have hf0 := positiveRetainedFrequencyBound_nonneg n j U V ζ
  have hplus : positiveRetainedFrequencyBound n j U V ζ + 1 ≤
      Real.exp (positiveRetainedFrequencyLog n j t p v w E + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ hF0 hF
  have hfirst := pow_le_exp_mul_of_le_exp (by positivity) hplus (by positivity) j le_rfl
  have hB := positiveModerateRetainedBias_inverse_exp_bound n j t hU hV hε hp hv hw hUp hVv hWw hεE
  have hpow := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (positiveModerateLengthExponent n * t) le_rfl
  have hL := positiveModerateLengthConstant_exp_bound n (zero_le_one.trans hU) hp hUp
  have hlen0 := (positiveModerateLengthConstant_pos n hU).le
  have hLt := pow_le_exp_mul_of_le_exp hlen0 hL hL0 t le_rfl
  have hsecond := mul_le_mul
    (mul_le_mul hWw hLt (pow_nonneg hlen0 _) (Real.exp_pos _).le) hpow (by positivity) (by positivity)
  simp only [← Real.exp_add] at hsecond
  have hleft0 : 0 ≤ (j : ℝ) * (positiveRetainedFrequencyLog n j t p v w E + 1) := by positivity
  have hright0 : 0 ≤ w + (t : ℝ) * positiveModerateLengthLog n p +
      ((positiveModerateLengthExponent n * t : ℕ) : ℝ) * positiveRetainedBiasLog n j t p v w E := by positivity
  unfold positiveRetainedDenominatorBound positiveRetainedDenominatorLog
  apply max_le
  · exact hfirst.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right hright0))
  · have hb := hsecond.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hleft0))
    simpa only [div_eq_mul_inv, inv_pow] using hb

theorem positiveRetainedComplexity_exp_bounds (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    let ζ := positiveModerateRetainedBias n j t U V W ε
    let Q := positiveRetainedComplexityLog n j t p v w E
    positiveModerateSpectrumCardBudget n j t U V W ε ≤ Real.exp Q ∧
      positiveRetainedFrequencyBound n j U V ζ ≤ Real.exp Q ∧
      positiveRetainedDenominatorBound n j t U V W ζ ≤ Real.exp Q := by
  obtain ⟨_, hC, hF, hD⟩ := positiveRetainedComplexityLog_bounds n j t hp hv hw hE
  exact ⟨(positiveModerateSpectrumCardBudget_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hC),
    (positiveRetainedFrequencyBound_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hF),
    (positiveRetainedDenominatorBound_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hD)⟩

end Erdos3

end

end OAI
