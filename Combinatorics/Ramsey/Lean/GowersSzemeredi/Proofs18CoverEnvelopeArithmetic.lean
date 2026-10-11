import GowersSzemeredi.Proofs18FiniteCoverBudgets

/-! Arithmetic for the proposed joint-cover envelope. This file proves
budgets, not discrepancy bounds or the existence of a localization scale.
The production inverse step must still be connected to this recursion. -/
set_option autoImplicit false
namespace LeanProofs.GowersSzemeredi

/-- The log-degree of the remainder density under fixed-tolerance covers. -/
def coverRhoDeg (k μD μ0 : Nat) : Nat := μ0 + μD + k + 4

/-- The log-degree of the lower-degree input parameter. -/
def coverDensDeg (k μD μ0 : Nat) : Nat := coverRhoDeg k μD μ0 + 2 * μD + 13

/-- Substitution of the tight class degree and the standard base budget. -/
theorem coverDensDeg_standard (k : Nat) :
    coverDensDeg k (68 * 2 ^ k) (2 ^ (k + 6) + 2) = 268 * 2 ^ k + k + 19 := by
  unfold coverDensDeg coverRhoDeg
  rw [pow_add]
  norm_num
  ring

/-- Proposed envelope step, after the analytic bounds are supplied. -/
def coverEnvelopeStep (k μ : Nat) : Nat :=
  max (268 * 2 ^ k + k + 33 + 4 * (k + 3) ^ 2 + μ)
    (40 * (k + 2) ^ 3 + 1095)

/-- The additive per-step cost fits half the induction budget. -/
theorem coverEnvelope_cost_le (k : Nat) :
    268 * 2 ^ k + k + 33 + 4 * (k + 3) ^ 2 ≤ 1024 * 2 ^ k := by
  have h : k + 33 + 4 * (k + 3) ^ 2 ≤ 756 * 2 ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show (2 : Nat) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k]
      nlinarith [Nat.zero_le (k ^ 2)]
  omega

/-- The polynomial localization overhead fits the full induction budget. -/
theorem coverEnvelope_overhead_le (k : Nat) :
    40 * (k + 2) ^ 3 + 1095 ≤ 2048 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show (2 : Nat) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k]
    have hs : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
    nlinarith [Nat.zero_le (k ^ 3)]

/-- One step preserves a budget proportional to `2^k`. -/
theorem coverEnvelopeStep_le {k μ : Nat} (hμ : μ ≤ 2048 * 2 ^ k) :
    coverEnvelopeStep (k + 1) μ ≤ 2048 * 2 ^ (k + 1) := by
  apply max_le
  · have hc := coverEnvelope_cost_le (k + 1)
    rw [show (2 : Nat) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k] at hc ⊢
    omega
  · exact coverEnvelope_overhead_le (k + 1)

/-- The candidate recursion, starting at the polynomial cubic envelope. -/
def coverEnvelope : Nat → Nat
  | 0 => 74
  | k + 1 => coverEnvelopeStep (k + 1) (coverEnvelope k)

/-- The candidate envelope fits in every dimension, without a finite
evaluation range. This is only the arithmetic part of the inverse theorem. -/
theorem coverEnvelope_le (k : Nat) : coverEnvelope k ≤ 2048 * 2 ^ k := by
  induction k with
  | zero => norm_num [coverEnvelope]
  | succ k ih => exact coverEnvelopeStep_le ih

/-- The proposed polynomial envelope leaves a factor-two margin in the
printed Theorem 18.1 budget at degree `k+2`. -/
theorem coverEnvelope_fits_theorem181 (k : Nat) :
    coverEnvelope k + 1 ≤ 2 ^ (k + 2 + 10) := by
  have h := coverEnvelope_le k
  have hpos := Nat.one_le_two_pow (n := k)
  rw [show k + 2 + 10 = k + 12 by omega, pow_add]
  norm_num
  omega

/-- The same candidate envelope fits the printed Szemeredi threshold
comparison at length `k+4`. Analytic scale bounds remain separate. -/
theorem coverEnvelope_fits_theorem182 (k : Nat) :
    coverEnvelope k + 2 * (k + 4) + 14 ≤ 2 ^ (k + 4 + 9) := by
  have h := coverEnvelope_le k
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  rw [show k + 4 + 9 = k + 13 by omega, pow_add]
  norm_num
  omega

namespace CoverParams
/-- The log-degree of the localization-exponent budget. -/
def coverExpDeg (k μD μ0 μK : Nat) : Nat :=
  max (coverRhoDeg k μD μ0 + 2 * μD + 9)
    (max (coverRhoDeg k μD μ0 + μD + k + 7) (μK + 2))

/-- The log-degree of the explicit modulus threshold. -/
def coverThreshDeg (k μD μ0 μK : Nat) : Nat :=
  max (coverExpDeg k μD μ0 μK + 4) (2 ^ (k + 6) + 5)

end CoverParams

/-- The envelope after one cover-based inverse step. -/
def envStepCover (k μD μ0 μK μ : Nat) : Nat :=
  max (coverDensDeg k μD μ0 + μ + 4 * (k + 3) ^ 2 + 14)
    (max (CoverParams.coverThreshDeg k μD μ0 μK + 3) (40 * (k + 2) ^ 3 + 1095))

/-- The standard localization-exponent envelope has an explicit closed form. -/
theorem coverExpDeg_standard (k : Nat) :
    CoverParams.coverExpDeg k (68 * 2 ^ k) (2 ^ (k + 6) + 2) (2 ^ (k + 5)) =
      268 * 2 ^ k + k + 15 := by
  have hk : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  unfold CoverParams.coverExpDeg coverRhoDeg
  simp only [pow_add]
  norm_num
  omega

/-- The actual cover-based envelope step is the candidate arithmetic step. -/
theorem envStepCover_standard (k μ : Nat) :
    envStepCover k (68 * 2 ^ k) (2 ^ (k + 6) + 2) (2 ^ (k + 5)) μ =
      coverEnvelopeStep k μ := by
  unfold envStepCover CoverParams.coverThreshDeg coverEnvelopeStep
  rw [coverDensDeg_standard, coverExpDeg_standard]
  simp only [pow_add]
  norm_num
  omega


/-- The envelope is large enough for the numerical stopping requirements. -/
theorem coverEnvelope_ge (k : Nat) : k + 42 ≤ coverEnvelope k := by
  cases k with
  | zero => norm_num [coverEnvelope]
  | succ k =>
    have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    have hmax := le_max_left
      (268 * 2 ^ (k + 1) + (k + 1) + 33 + 4 * (k + 1 + 3) ^ 2 + coverEnvelope k)
      (40 * (k + 1 + 2) ^ 3 + 1095)
    change k + 1 + 42 ≤ max _ _
    omega

/-- The linear stopping requirement fits the exponential envelope at every
length, including lengths larger than any fixed numerical cutoff. -/
theorem coverEnvelope_stopping_budget (k : Nat) :
    4 * (k + 4) + 20 ≤ 2 ^ coverEnvelope k := by
  have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hpow : 2 ^ (k + 6) ≤ 2 ^ coverEnvelope k :=
    Nat.pow_le_pow_right (by norm_num) (by have := coverEnvelope_ge k; omega)
  rw [pow_add] at hpow
  norm_num at hpow
  omega

end LeanProofs.GowersSzemeredi
