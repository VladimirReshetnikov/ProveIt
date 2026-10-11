import GowersSzemeredi.Proofs18CoverEnvelopeArithmetic

/-! A sharper budget for the same joint-cover recursion. These lemmas are
arithmetic prerequisites for improved inverse and Szemeredi bounds; the
analytic connection to the recursion is supplied by the cover inverse route. -/
set_option autoImplicit false
namespace LeanProofs.GowersSzemeredi

/-- Half of the sharper induction budget absorbs the step cost and the
increase of the linear interval-stopping overhead. -/
theorem coverEnvelope_cost_le_sharp (k : Nat) :
    268 * 2 ^ k + k + 35 + 4 * (k + 3) ^ 2 ≤ 512 * 2 ^ k := by
  have h : k + 35 + 4 * (k + 3) ^ 2 ≤ 244 * 2 ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show (2 : Nat) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k]
      nlinarith [Nat.zero_le (k ^ 2)]
  omega

/-- The localization overhead and the stopping overhead fit the sharper
budget from dimension two onwards. -/
theorem coverEnvelope_overhead_le_sharp : ∀ k, 2 ≤ k →
    40 * (k + 2) ^ 3 + 1095 + 2 * k + 22 ≤ 1024 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [show (2 : Nat) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k]
    have hs : k ≤ k ^ 2 := Nat.le_self_pow (by norm_num) k
    nlinarith [Nat.zero_le (k ^ 3)]

/-- The same envelope step preserves the sharper weighted budget. -/
theorem coverEnvelopeStep_le_sharp {k μ : Nat} (hk : 1 ≤ k)
    (hμ : μ + 2 * k + 22 ≤ 1024 * 2 ^ k) :
    coverEnvelopeStep (k + 1) μ + 2 * (k + 1) + 22 ≤ 1024 * 2 ^ (k + 1) := by
  have hc := coverEnvelope_cost_le_sharp (k + 1)
  have ht := coverEnvelope_overhead_le_sharp (k + 1) (by omega)
  unfold coverEnvelopeStep
  rw [show (2 : Nat) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k] at hc ht ⊢
  omega

/-- The envelope including its interval-stopping overhead fits `1024*2^k`
in every dimension at least two. -/
theorem coverEnvelope_le_sharp : ∀ k, 2 ≤ k →
    coverEnvelope k + 2 * k + 22 ≤ 1024 * 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih => exact coverEnvelopeStep_le_sharp (by omega) ih

/-- The inverse-envelope comparison with `d+8` in place of the printed
`d+10`, at degree `d=k+2`, for every `k≥2`. -/
theorem coverEnvelope_fits_sharper181 {k : Nat} (hk : 2 ≤ k) :
    coverEnvelope k + 1 ≤ 2 ^ (k + 2 + 8) := by
  have h := coverEnvelope_le_sharp k hk
  rw [show k + 2 + 8 = k + 10 by omega, pow_add]
  norm_num
  omega

/-- The Szemeredi-envelope comparison with `L+6` in place of the printed
`L+9`, at length `L=k+4`, for every `k≥2`. -/
theorem coverEnvelope_fits_sharper182 {k : Nat} (hk : 2 ≤ k) :
    coverEnvelope k + 2 * (k + 4) + 14 ≤ 2 ^ (k + 4 + 6) := by
  have h := coverEnvelope_le_sharp k hk
  rw [show k + 4 + 6 = k + 10 by omega, pow_add]
  norm_num
  omega

end LeanProofs.GowersSzemeredi
