import IPRADerivations.Probability.Variance
import IPRADerivations.Foundations.DyadicNames

/-!
# The St Petersburg game

Packet: `probability/expected_value_ipra_2026-11-16`, Proposition `prop:st-petersburg` ("St Petersburg
game"): "Let the payoff be `2^n` with probability `2^{-n}` for `n ≥ 1`. The partial expectation through
outcome `N` is exactly `N` … The probabilities normalize because `∑_{n=1}^N 2^{-n} = 1 − 2^{-N}`."

On the scale `2^N` the outcome `n = i + 1` (`i < N`) has the probability numerator `2^{N ∸ (i+1)}`:

* `pB`, `eB`: the bodies of the probability numerators and of probability times payoff, with the
  parameter `N`;
* `term_const`: for `i < N`, `2^{N ∸ (i+1)} · 2^{i+1} = 2^N`, each term contributes `1`;
* `partial_expectation`: `∑_{i<N} 2^{N ∸ (i+1)} 2^{i+1} = N · 2^N`, i.e. the partial expectation through
  outcome `N` is `N`;
* `normalization`: `∑_{i<N} 2^{N ∸ (i+1)} + 1 = 2^N`, i.e. `∑_{n=1}^N 2^{-n} = 1 − 2^{-N}`.

So the partial expectations exceed every bound `B` at `N = B`: the divergence function is `D(B) = B`. The
statement about the extended expectation of the countable law is the reading of these finite identities.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.StPetersburg

open_ipra
open LeanProofs.IPRA.Probability.Variance (sum_const_of)
open LeanProofs.IPRA.Foundations.DyadicNames (eps eps_half)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The probability numerator `2^{N ∸ (i+1)}` of the outcome `i + 1`; variables `0 = i`, `1 = N`. -/
def pB : PTm 2 := pw two (monus (var 1) (succ (var 0)))

/-- Probability times payoff, `2^{N ∸ (i+1)} · 2^{i+1}`. -/
def eB : PTm 2 := pB * pw two (succ (var 0))

theorem inst2_pB (i N : PTm n) : inst2 pB i N = pw two (monus N (succ i)) := by
  simp [inst2, pB]

theorem inst2_eB (i N : PTm n) : inst2 eB i N = inst2 pB i N * pw two (succ i) := by
  simp [inst2, eB]

/-- Each outcome contributes `1`: `2^{N ∸ (i+1)} · 2^{i+1} = 2^N` for `i < N`. -/
theorem term_const {i N : PTm n} (h : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] inst2 eB i N ≐ pw two N := by
  rw [inst2_eB, inst2_pB]
  have h' : Γ ⊢[PRAAx] le (succ i) N := h
  have e₂ : Γ ⊢[PRAAx] monus N (succ i) + succ i ≐ N := by
    ipra_lc -natEq (eq_add_of_le h')
  exact (pw_add two (monus N (succ i)) (succ i)).eqSymm.eqTrans (congrAp2 powF e₂ (Prf.eqRefl (two : PTm n)))

/-- `prop:st-petersburg`: the partial expectation through outcome `N` is `N` (on the scale `2^N`). -/
theorem partial_expectation (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF eB) N N ≐ N * pw two N := by
  refine sum_const_of eB N (pw two N) N (.allI (.impI ?_))
  have e : Syn.shift (pw two N) = pw two (Syn.shift N) := by simp [Syn.shift]
  rw [e]
  exact term_const Prf.hyp0

/-! ## Normalization -/

theorem norm_step {K N : PTm n} (hK : Γ ⊢[PRAAx] lt K N)
    (ih : Γ ⊢[PRAAx] ap2 (sumF pB) K N + eps N K ≐ pw two N) :
    Γ ⊢[PRAAx] ap2 (sumF pB) (succ K) N + eps N (succ K) ≐ pw two N := by
  have s' := sum_succ' (Γ := Γ) pB K N
  rw [inst2_pB] at s'
  ipra_lc natEq s' + natEq ih - natEq (eps_half hK)

theorem norm_guard {K N : PTm n} (hK : Γ ⊢[PRAAx] le (succ K) N)
    (ih : Γ ⊢[PRAAx] le K N ⟶ (ap2 (sumF pB) K N + eps N K ≐ pw two N)) :
    Γ ⊢[PRAAx] ap2 (sumF pB) (succ K) N + eps N (succ K) ≐ pw two N :=
  norm_step hK (Prf.impE ih (le_trans (le_succ_self K) hK))

theorem norm_base (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF pB) zero N + eps N zero ≐ pw two N := by
  ipra_lc natEq (sum_zero (Γ := Γ) pB N) + natEq (congrAp2 powF (monus_zero (Γ := Γ) N) (Prf.eqRefl (two : PTm n)))

theorem norm_all (N : PTm n) :
    Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      (ap2 (sumF pB) (var 0) (Syn.shift N) + eps (Syn.shift N) (var 0) ≐ pw two (Syn.shift N))) := by
  refine qfIndAllUpTo N trivial ?_ ?_
  · simpa [eps] using norm_base (Γ := Γ) N
  · simp [eps]
    exact .impI (norm_step Prf.hyp0 Prf.hyp1)

/-- `prop:st-petersburg`: the probabilities of the first `N` outcomes add up to `1 − 2^{-N}`. -/
theorem normalization (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF pB) N N + one ≐ pw two N := by
  have a := Prf.allE N (norm_all (Γ := Γ) N)
  have e : (le (var 0) (Syn.shift N) ⟶
        (ap2 (sumF pB) (var 0) (Syn.shift N) + eps (Syn.shift N) (var 0) ≐ pw two (Syn.shift N))).subst
        (Syn.inst N) =
      (le N N ⟶ (ap2 (sumF pB) N N + eps N N ≐ pw two N)) := by
    simp
  rw [e] at a
  ipra_lc natEq (Prf.impE a (le_refl N)) -
    natEq ((congrAp2 powF (monus_self (Γ := Γ) N) (Prf.eqRefl (two : PTm n))).eqTrans (pw_zero two))

end LeanProofs.IPRA.Probability.StPetersburg
