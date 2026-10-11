import GowersSzemeredi.Proofs18LengthSixSzemeredi
import GowersSzemeredi.Proofs16PolynomialLemma9WithRemainder
import GowersSzemeredi.Proofs16VarietyTheoremThree

/-! **Theorem 18.2 and Corollary 18.7 at length six.**

This module is a bridge. `theorem_18_2_six_of_profiles` (light, kernel-checked
locally) needs the recurrence profiles in dimensions one and two at constants
`K, p ≤ 2^2000`. The explicit multilinear partition gives them in every
dimension `k`, with
* `K = ⌈multiaffinePartitionK (k+1) (2^(k+1))⌉`;
* `p = (k+1) · multiaffinePartitionP (k+1) (2^(k+1))`.

The chain is `multilinearPartitionBoundAt_explicit`, then
`commonDiffPartitionBoundAt_of`, `commonDiffPartitionTwoBoundAt_of`,
`polynomialSection16RecurrenceProfileAt_of` and
`section16RecurrenceProfileWith_of_polynomial`. At `k = 1, 2` these
constants are the named `explicitVarietyK`, `2 · explicitVarietyP`,
`explicitLiftK` and `explicitLiftP`. `explicit_constants_le` bounds all of
them by `2^1700`.

The imports reach the port's Schmidt constants, so this module is checked on
the full-verification host. Every step is a definitional instantiation of a
kernel-checked statement. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The recurrence profile in dimension `k` at the explicit constants. -/
theorem section16RecurrenceProfileWith_explicit (k : Nat) :
    Section16RecurrenceProfileWith k
      (familyRecThr k (Nat.ceil (multiaffinePartitionK (k + 1) (2 ^ (k + 1))))
        ((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1))))
      (familyRecExp k ((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))) := by
  have hK := two_le_multiaffinePartitionK (k + 1) (2 ^ (k + 1))
  have hp := multiaffinePartitionP_pos (k + 1) (2 ^ (k + 1))
  exact section16RecurrenceProfileWith_of_polynomial k _ _
    (polynomialSection16RecurrenceProfileAt_of k hK (Nat.mul_pos (Nat.succ_pos k) hp)
      (commonDiffPartitionTwoBoundAt_of k hK hp
        (commonDiffPartitionBoundAt_of k hK hp
          (multilinearPartitionBoundAt_explicit (k + 1) (Nat.succ_pos k)))))

theorem lengthSix_explicit_constants :
    2 ≤ explicitVarietyK ∧ 0 < (1 + 1) * explicitVarietyP ∧ 2 ≤ explicitLiftK ∧
      0 < explicitLiftP ∧
      (explicitVarietyK : Real) ≤ 2 ^ 2000 ∧ (((1 + 1) * explicitVarietyP : Nat) : Real) ≤ 2 ^ 2000 ∧
      (explicitLiftK : Real) ≤ 2 ^ 2000 ∧ (explicitLiftP : Real) ≤ 2 ^ 2000 := by
  obtain ⟨hLK, hLP, hVK, hVP⟩ := explicit_constants_le
  have h17 : (2 : Real) ^ 1700 ≤ 2 ^ 2000 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h17' : (2 : Real) * 2 ^ 1700 ≤ 2 ^ 2000 := by
    rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  refine ⟨by unfold explicitVarietyK; exact two_le_ceil_multiaffinePartitionK _ _,
    Nat.mul_pos (by norm_num) (by unfold explicitVarietyP; exact multiaffinePartitionP_pos _ _),
    by unfold explicitLiftK; exact two_le_ceil_multiaffinePartitionK _ _,
    by unfold explicitLiftP; exact Nat.mul_pos (by norm_num) (multiaffinePartitionP_pos _ _),
    hVK.trans h17, ?_, hLK.trans h17, hLP.trans h17⟩
  have hcast : (((1 + 1) * explicitVarietyP : Nat) : Real) = 2 * (explicitVarietyP : Real) := by
    push_cast; ring
  rw [hcast]
  exact (mul_le_mul_of_nonneg_left hVP (by norm_num)).trans h17'

/-- **Theorem 18.2 at length six**, with the source's threshold
`2^(2^(δ^(-2^32768)))`. -/
theorem theorem_18_2_six : Theorem182At 6 := by
  obtain ⟨hK1, hp1, hK2, hp2, hK1b, hp1b, hK2b, hp2b⟩ := lengthSix_explicit_constants
  -- unfold the named constants so that the profiles match syntactically
  have h1 : Section16RecurrenceProfileWith 1 (familyRecThr 1 explicitVarietyK ((1 + 1) * explicitVarietyP))
      (familyRecExp 1 ((1 + 1) * explicitVarietyP)) := by
    simpa only [explicitVarietyK, explicitVarietyP, Nat.reduceAdd, Nat.reducePow] using
      section16RecurrenceProfileWith_explicit 1
  have h2 : Section16RecurrenceProfileWith 2 (familyRecThr 2 explicitLiftK explicitLiftP)
      (familyRecExp 2 explicitLiftP) := by
    simpa only [explicitLiftK, explicitLiftP, Nat.reduceAdd, Nat.reducePow] using
      section16RecurrenceProfileWith_explicit 2
  exact theorem_18_2_six_of_profiles hK1 hp1 hK2 hp2 hK1b hp1b hK2b hp2b h1 h2

/-- **Corollary 18.7 at length six.** -/
theorem corollary_18_7_six : Corollary187At 6 :=
  theorem_18_2_six.corollary_18_7

/-- **Theorem 18.2 at every length up to six**, with the source thresholds. -/
theorem theorem_18_2_le_six {k : Nat} (hk : k ≤ 6) : Theorem182At k := by
  rcases Nat.lt_or_ge k 6 with h | h
  · exact theorem_18_2_le_five (by omega)
  · obtain rfl : k = 6 := by omega
    exact theorem_18_2_six

/-- **Corollary 18.7 at every length up to six.** -/
theorem corollary_18_7_le_six {k : Nat} (hk : k ≤ 6) : Corollary187At k :=
  (theorem_18_2_le_six hk).corollary_18_7

end LeanProofs.GowersSzemeredi
