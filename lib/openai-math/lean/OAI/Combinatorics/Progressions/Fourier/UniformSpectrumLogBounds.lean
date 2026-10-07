import OAI.Combinatorics.Progressions.Estimates.InactiveShortLogBounds
import OAI.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap

namespace OAI

section

namespace Erdos3

def majorArcBiasLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  (denseProductDensityConstant n * (2 * 3 ^ n) ^ denseProductExponent n : ℕ) +
    ((n + 1) * majorArcBiasExponent n : ℕ) * (1 + 2 * p)

def majorArcLocalizationLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  256 + 6 * p + ((n + 1) * 2 : ℕ) * (1 + 2 * p)

def majorArcLengthLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  majorArcLocalizationLog n p + majorArcBiasLog n p + 1

def majorArcErrorLog {A : Type*} [Semiring A] (n : ℕ) (p : A) : A :=
  majorArcBiasLog n p + (n + 1 : ℕ) * majorArcLocalizationLog n p

def majorArcCoverLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  j * (majorArcBiasLog n p + (n + 1 : ℕ) * p) + v + majorArcErrorLog n p + 2

theorem majorArcBaseLogs_nonneg (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ majorArcBiasLog n p ∧ 0 ≤ majorArcLocalizationLog n p ∧
      0 ≤ majorArcLengthLog n p ∧ 0 ≤ majorArcErrorLog n p := by
  unfold majorArcLengthLog majorArcErrorLog majorArcBiasLog majorArcLocalizationLog
  exact ⟨by positivity, by positivity, by positivity, by positivity⟩

theorem majorArcCoverLog_nonneg (n j : ℕ) {p v : ℝ} (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ majorArcCoverLog n j p v := by
  obtain ⟨hb, _, _, he⟩ := majorArcBaseLogs_nonneg n hp
  unfold majorArcCoverLog
  positivity

theorem majorArcConstants_exp_bounds (n : ℕ) {U p : ℝ}
    (hU : 0 ≤ U) (hp : 0 ≤ p) (hUp : U ≤ Real.exp p) :
    majorArcBiasConstant n U ≤ Real.exp (majorArcBiasLog n p) ∧
      majorArcLocalizationConstant n U ≤ Real.exp (majorArcLocalizationLog n p) ∧
      majorArcLengthConstant n U ≤ Real.exp (majorArcLengthLog n p) ∧
      majorArcErrorConstant n U ≤ Real.exp (majorArcErrorLog n p) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hU2 : U ^ 2 ≤ Real.exp (2 * p) :=
    pow_le_exp_mul_of_le_exp hU hUp hp 2 le_rfl
  have hbase : 2 * U ^ 2 ≤ Real.exp (1 + 2 * p) :=
    (mul_le_mul htwo hU2 (sq_nonneg U) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hbpow := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 * U ^ 2)
    hbase (by positivity) ((n + 1) * majorArcBiasExponent n) le_rfl
  let c : ℕ := denseProductDensityConstant n * (2 * 3 ^ n) ^ denseProductExponent n
  have hc : (c : ℝ) ≤ Real.exp (c : ℝ) := by linarith [Real.add_one_le_exp (c : ℝ)]
  have hb : majorArcBiasConstant n U ≤ Real.exp (majorArcBiasLog n p) := by
    calc
      _ = (c : ℝ) * (2 * U ^ 2) ^ ((n + 1) * majorArcBiasExponent n) := by
        simp only [majorArcBiasConstant, c, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ Real.exp (c : ℝ) * Real.exp (((n + 1) * majorArcBiasExponent n : ℕ) * (1 + 2 * p)) :=
        mul_le_mul hc hbpow (by positivity) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hU6 : U ^ 6 ≤ Real.exp (6 * p) :=
    pow_le_exp_mul_of_le_exp hU hUp hp 6 le_rfl
  have hlpow := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 * U ^ 2)
    hbase (by positivity) ((n + 1) * 2) le_rfl
  have h256 : (256 : ℝ) ≤ Real.exp 256 := by linarith [Real.add_one_le_exp (256 : ℝ)]
  have hl : majorArcLocalizationConstant n U ≤ Real.exp (majorArcLocalizationLog n p) := by
    unfold majorArcLocalizationConstant majorArcLocalizationLog
    calc
      _ ≤ Real.exp 256 * Real.exp (6 * p) * Real.exp (((n + 1) * 2 : ℕ) * (1 + 2 * p)) := by
        gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  obtain ⟨hb0, hl0, _, _⟩ := majorArcBaseLogs_nonneg n hp
  have hbc : 0 ≤ majorArcBiasConstant n U := by unfold majorArcBiasConstant; positivity
  have hlc : 0 ≤ majorArcLocalizationConstant n U := by unfold majorArcLocalizationConstant; positivity
  have hplus : majorArcBiasConstant n U + 1 ≤ Real.exp (majorArcBiasLog n p + 1) := by
    rw [add_comm]
    exact one_add_le_exp_succ hb0 hb
  have hlength : majorArcLengthConstant n U ≤ Real.exp (majorArcLengthLog n p) := by
    have hmul := (mul_le_mul hl hplus (by positivity) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
    exact hmul.trans_eq (by unfold majorArcLengthLog; congr 1; ring)
  have hlpow' := pow_le_exp_mul_of_le_exp hlc hl hl0 (n + 1) le_rfl
  have herror : majorArcErrorConstant n U ≤ Real.exp (majorArcErrorLog n p) :=
    (mul_le_mul hb hlpow' (pow_nonneg hlc _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  exact ⟨hb, hl, hlength, herror⟩

theorem majorArcCoverConstant_exp_bound (n j : ℕ) {U V p v : ℝ}
    (hU : 0 ≤ U) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) :
    majorArcCoverConstant n j U V ≤ Real.exp (majorArcCoverLog n j p v) := by
  obtain ⟨hb, _, _, he⟩ := majorArcConstants_exp_bounds n hU hp hUp
  obtain ⟨hb0, _, _, he0⟩ := majorArcBaseLogs_nonneg n hp
  have hbc : 0 ≤ majorArcBiasConstant n U := by unfold majorArcBiasConstant; positivity
  have hec : 0 ≤ majorArcErrorConstant n U := by
    unfold majorArcErrorConstant majorArcBiasConstant majorArcLocalizationConstant
    positivity
  have hUpow := pow_le_exp_mul_of_le_exp hU hUp hp (n + 1) le_rfl
  have hmul := (mul_le_mul hb hUpow (pow_nonneg hU _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hpow := pow_le_exp_mul_of_le_exp (mul_nonneg hbc (pow_nonneg hU _)) hmul
    (by positivity) j le_rfl
  have hfirst := one_add_le_exp_succ
    (by positivity : 0 ≤ (j : ℝ) * (majorArcBiasLog n p + (n + 1 : ℕ) * p)) hpow
  have hsecond := (mul_le_mul hVv he hec (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ (j : ℝ) * (majorArcBiasLog n p + (n + 1 : ℕ) * p) + 1)
    (add_nonneg hv he0) hfirst hsecond
  exact hsum.trans_eq (by unfold majorArcCoverLog; congr 1; ring)

end Erdos3

end

section

namespace Erdos3

def majorArcSpectrumLog {A : Type*} [Semiring A] (n j : ℕ) (p v : A) : A :=
  j * (195 + 4 * majorArcCoverLog n j p v)

def uniformBlockAccuracyLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w : A) : A :=
  1 + majorArcSpectrumLog n j p v + (majorArcSpectrumExponent n j : ℕ) +
    (w + t * ((majorArcLengthExponent n : ℕ) + majorArcLengthLog n p)) + 2

def uniformSpectrumSizeLog {A : Type*} [Semiring A]
    (n j t : ℕ) (p v w : A) : A :=
  majorArcSpectrumLog n j p v + (w + t * majorArcLengthLog n p) + 1 +
    (max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) : ℕ) *
      uniformBlockAccuracyLog n j t p v w

theorem uniformSpectrumLogs_nonneg (n j t : ℕ) {p v w : ℝ}
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ majorArcSpectrumLog n j p v ∧ 0 ≤ uniformBlockAccuracyLog n j t p v w ∧
      0 ≤ uniformSpectrumSizeLog n j t p v w := by
  have hC := majorArcCoverLog_nonneg n j hp hv
  have hL := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hS : 0 ≤ majorArcSpectrumLog n j p v := by
    unfold majorArcSpectrumLog
    positivity
  have hA : 0 ≤ uniformBlockAccuracyLog n j t p v w := by
    unfold uniformBlockAccuracyLog
    positivity
  refine ⟨hS, hA, ?_⟩
  unfold uniformSpectrumSizeLog
  positivity

theorem majorArcSpectrumConstant_exp_bound (n j : ℕ) {U V p v : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) :
    majorArcSpectrumConstant n j U V ≤ Real.exp (majorArcSpectrumLog n j p v) := by
  have hc := majorArcCoverConstant_exp_bound n j (zero_le_one.trans hU) hp hv hUp hVv
  have hc0 := zero_le_one.trans (majorArcCoverConstant_one_le n j hU hV)
  have hlog := majorArcCoverLog_nonneg n j hp hv
  have hp4 := pow_le_exp_mul_of_le_exp hc0 hc hlog 4 le_rfl
  have h195 : (195 : ℝ) ≤ Real.exp 195 := by linarith [Real.add_one_le_exp (195 : ℝ)]
  have hbase := (mul_le_mul h195 hp4 (pow_nonneg hc0 _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  exact pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) j le_rfl

theorem uniformBlockSpectrumAccuracy_exp_bound (n j t : ℕ) {U V W p v w : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w) :
    uniformBlockSpectrumAccuracyConstant n j t U V W + 1 ≤
      Real.exp (uniformBlockAccuracyLog n j t p v w) := by
  have hlen := (majorArcConstants_exp_bounds n (zero_le_one.trans hU) hp hUp).2.2.1
  have hspec := majorArcSpectrumConstant_exp_bound n j hU hV hp hv hUp hVv
  have hL := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hS := (uniformSpectrumLogs_nonneg n j t hp hv hw).1
  have hlen0 := (majorArcLengthConstant_pos n hU).le
  have hspec0 := majorArcSpectrumConstant_nonneg n j U V
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowS : (2 : ℝ) ^ majorArcSpectrumExponent n j ≤
      Real.exp (majorArcSpectrumExponent n j : ℝ) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (majorArcSpectrumExponent n j) le_rfl
  have hpowL : (2 : ℝ) ^ majorArcLengthExponent n ≤ Real.exp (majorArcLengthExponent n : ℝ) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (majorArcLengthExponent n) le_rfl
  have hfirst : 2 * majorArcSpectrumConstant n j U V * 2 ^ majorArcSpectrumExponent n j ≤
      Real.exp (1 + majorArcSpectrumLog n j p v + (majorArcSpectrumExponent n j : ℝ)) := by
    have hh := mul_le_mul (mul_le_mul htwo hspec hspec0 (Real.exp_pos _).le) hpowS
      (by positivity) (by positivity)
    simpa only [← Real.exp_add] using hh
  have hbase := (mul_le_mul hpowL hlen hlen0 (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hbasepow := pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) t le_rfl
  have hsecond := (mul_le_mul hWw hbasepow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ 1 + majorArcSpectrumLog n j p v + (majorArcSpectrumExponent n j : ℝ))
    (by positivity : 0 ≤ w + (t : ℝ) * ((majorArcLengthExponent n : ℝ) + majorArcLengthLog n p))
    hfirst hsecond
  have hplus := one_add_le_exp_succ (by positivity) hsum
  calc
    _ = 1 + (2 * majorArcSpectrumConstant n j U V * 2 ^ majorArcSpectrumExponent n j +
        W * (2 ^ majorArcLengthExponent n * majorArcLengthConstant n U) ^ t) := by
      unfold uniformBlockSpectrumAccuracyConstant
      ring
    _ ≤ _ := hplus
    _ = _ := by unfold uniformBlockAccuracyLog; congr 1; ring

theorem uniformSpectrumSizeConstant_exp_bound (n j t : ℕ) {U V W p v w : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w) :
    uniformSpectrumSizeConstant n j t U V W ≤ Real.exp (uniformSpectrumSizeLog n j t p v w) := by
  have hS := majorArcSpectrumConstant_exp_bound n j hU hV hp hv hUp hVv
  have hL := (majorArcConstants_exp_bounds n (zero_le_one.trans hU) hp hUp).2.2.1
  have hA := uniformBlockSpectrumAccuracy_exp_bound n j t hU hV hp hv hw hUp hVv hWw
  have hL0 := (majorArcBaseLogs_nonneg n hp).2.2.1
  obtain ⟨hS0, hA0, _⟩ := uniformSpectrumLogs_nonneg n j t hp hv hw
  have hlen0 := (majorArcLengthConstant_pos n hU).le
  have hspec0 := majorArcSpectrumConstant_nonneg n j U V
  have hLt := pow_le_exp_mul_of_le_exp hlen0 hL hL0 t le_rfl
  have hsecond := (mul_le_mul hWw hLt (pow_nonneg hlen0 _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hsum := add_le_exp_add_one hS0 (by positivity) hS hsecond
  have haccuracy0 : 0 ≤ uniformBlockSpectrumAccuracyConstant n j t U V W + 1 := by
    unfold uniformBlockSpectrumAccuracyConstant
    positivity
  have hpow := pow_le_exp_mul_of_le_exp haccuracy0 hA hA0
    (max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t)) le_rfl
  exact (mul_le_mul hsum hpow (pow_nonneg haccuracy0 _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm

theorem uniformSpectrumAbsoluteCap_exp_bound (n j t : ℕ) {U V W p v w : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w) :
    uniformSpectrumAbsoluteCap n j t U V W ≤ Real.exp (uniformSpectrumSizeLog n j t p v w + 1) := by
  have hbound := uniformSpectrumSizeConstant_exp_bound n j t hU hV hW hp hv hw hUp hVv hWw
  have hplus := one_add_le_exp_succ (uniformSpectrumLogs_nonneg n j t hp hv hw).2.2 hbound
  simpa only [uniformSpectrumAbsoluteCap, add_comm] using hplus

end Erdos3

end

end OAI
