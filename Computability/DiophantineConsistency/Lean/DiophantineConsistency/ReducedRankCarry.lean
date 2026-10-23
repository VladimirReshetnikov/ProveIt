import Diophantine.Paper1982.Carries
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# The shorter population-calibrated central-binomial rank

The rank is positive before a low-digit bound is known. Once `S<L=2^u`,
it has a high block `S+T` and the low complement of `S`. Its population
therefore differs from `u+pop(T)` by exactly the binary carry count.
-/

namespace DiophantineConsistency.ReducedRankCarry

open Jones1982

/-- Division-free natural data, valid even before the code is bounded. -/
def rank (L S T : ℕ) : ℕ := (L - 1) * S + L * T + (L - 1)

theorem rank_cast {L : ℕ} (hL : 1 ≤ L) (S T : ℕ) :
    (rank L S T : ℤ) = L * ((S : ℤ) + T + 1) - S - 1 := by
  unfold rank
  push_cast [Nat.cast_sub hL]
  ring

theorem rank_ge {L S T : ℕ} : L - 1 ≤ rank L S T := by
  unfold rank
  omega

theorem rank_pos {L S T : ℕ} (hL : 2 ≤ L) : 0 < rank L S T := by
  have h := rank_ge (L := L) (S := S) (T := T)
  omega

/-- The block decomposition needs only the low code bound; no bound on the
high block or ordering between the rank and divisibility base is assumed. -/
theorem rank_eq_blocks {L S T : ℕ} (hS : S < L) :
    rank L S T = (S + T) * L + (L - 1 - S) := by
  have hL : 1 ≤ L := by omega
  have hs : S ≤ L - 1 := by omega
  unfold rank
  zify [hL, hs]
  ring

theorem population {u S T : ℕ} (hS : S < 2 ^ u) :
    σ 2 (rank (2 ^ u) S T) + τ 2 S T = u + σ 2 T := by
  have hlow : 2 ^ u - 1 - S < 2 ^ u := by
    have hp : 0 < 2 ^ u := by positivity
    omega
  have hp : σ 2 (rank (2 ^ u) S T) =
      σ 2 (S + T) + σ 2 (2 ^ u - 1 - S) := by
    rw [rank_eq_blocks hS, lemma_2_5 hlow]
  have hc := lemma_2_6 hS
  have ht := lemma_2_2 S T
  omega

/-- Exact calibration converts the shorter rank into the same no-carry
predicate as the source mask. -/
theorem calibrated_iff {u v S T : ℕ} (hS : S < 2 ^ u)
    (hcal : u + σ 2 T = 2 * v) :
    (2 ^ v) ^ 2 ∣ (2 * rank (2 ^ u) S T).choose (rank (2 ^ u) S T) ↔
      τ 2 S T = 0 := by
  have hpow : (2 ^ v : ℕ) ^ 2 = 2 ^ (2 * v) := by rw [← pow_mul, Nat.mul_comm]
  rw [hpow, ← lemma_2_15]
  have h := population (T := T) hS
  rw [hcal] at h
  omega

/-- Package 59's source-mask population and rank length give its exact
threshold for every allowed power-of-two input, including exponent zero. -/
theorem split116_calibration {kappa : ℕ} (hkappa : 2 ≤ kappa) (k : ℕ) :
    (k + 2279 * (kappa + 2 * k)) +
      (139 * (kappa + 2 * k) - 31 * k - 22) =
        2 * ((8 * kappa - 11) + k + 1201 * (kappa + 2 * k)) := by
  omega

theorem split116_calibrated_iff {kappa k S T : ℕ} (hkappa : 2 ≤ kappa)
    (hS : S < 2 ^ (k + 2279 * (kappa + 2 * k)))
    (hmask : σ 2 T = 139 * (kappa + 2 * k) - 31 * k - 22) :
    (2 ^ ((8 * kappa - 11) + k + 1201 * (kappa + 2 * k))) ^ 2 ∣
      (2 * rank (2 ^ (k + 2279 * (kappa + 2 * k))) S T).choose
        (rank (2 ^ (k + 2279 * (kappa + 2 * k))) S T) ↔ τ 2 S T = 0 := by
  apply calibrated_iff hS
  rw [hmask]
  exact split116_calibration hkappa k

end DiophantineConsistency.ReducedRankCarry
