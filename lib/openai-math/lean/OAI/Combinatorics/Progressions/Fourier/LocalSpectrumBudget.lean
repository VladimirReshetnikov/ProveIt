import OAI.Combinatorics.Progressions.Estimates.CyclicRelativeChang
import OAI.Combinatorics.Progressions.Sampling.LocalSamplingBudget

namespace OAI

section

namespace Erdos3

open scoped NNReal Pointwise

theorem samplingDensity_le_of_smallDoubling
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A S T : Finset G} (hA : A.Nonempty) (hS : S.Nonempty) (k : ℕ)
    {K : ℝ} (hK : 0 < K) (hdoubling : ((A + S).card : ℝ) ≤ K * A.card)
    (hcount : (((A.card : ℝ) ^ k / 2 * S.card) / ((A + S).card : ℝ) ^ k ≤ T.card)) :
    (S.card : ℝ) / (2 * K ^ k) ≤ T.card := by
  have hsumpos : (0 : ℝ) < (A + S).card := by exact_mod_cast (hA.add hS).card_pos
  have hden : 0 < ((A + S).card : ℝ) ^ k := pow_pos hsumpos _
  have hKden : 0 < 2 * K ^ k := mul_pos (by norm_num) (pow_pos hK _)
  apply le_trans _ hcount
  apply (div_le_div_iff₀ hKden hden).mpr
  have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hdoubling k
  calc
    _ ≤ (S.card : ℝ) * (K * A.card) ^ k :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow]; ring

namespace RelativeChangSanders

variable {N : ℕ} [NeZero N]

theorem localChangDimension_half_le_of_card
    (B : CyclicBohr.Set N) {T : Finset (ZMod N)} (hT : T.Nonempty)
    {K : ℝ} (hK : 0 < K) (k : ℕ)
    (hcount : (B.carrier.card : ℝ) / (2 * K ^ k) ≤ T.card) :
    localChangDimension B T (1 / 2) ≤ 8 * (1 + Real.log 4 + k * Real.log K) := by
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hBpos : (0 : ℝ) < B.carrier.card := by exact_mod_cast B.card_pos
  have hden : 0 < 2 * K ^ k := by positivity
  have hprod := (div_le_iff₀ hden).mp hcount
  have hratio : 2 * (B.carrier.card : ℝ) / T.card ≤ 4 * K ^ k := by
    rw [div_le_iff₀ hTpos]
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 2 * (B.carrier.card : ℝ) / T.card) hratio
  rw [Real.log_mul (by norm_num) (pow_ne_zero k hK.ne'), Real.log_pow] at hlog
  unfold localChangDimension
  norm_num
  linarith

theorem localChangBaseScale_ge_of_dimension_le
    (B : CyclicBohr.Set N) (T : Finset (ZMod N)) (eta D : ℝ)
    (hD : localChangDimension B T eta ≤ D) :
    (100 * ((2 * max B.rank 1 : ℕ) : ℝ≥0) *
      ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0))⁻¹ ≤ localChangBaseScale B T eta := by
  have hcap : localChangCap B T eta ≤ ⌈D⌉₊ + 1 :=
    Nat.add_le_add_right (Nat.ceil_mono hD) 1
  have hcap' : ((2 * localChangCap B T eta + 1 : ℕ) : ℝ≥0) ≤
      ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left 2 hcap) 1
  unfold localChangBaseScale
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hcap' (by positivity))

end RelativeChangSanders
end Erdos3

end

end OAI
