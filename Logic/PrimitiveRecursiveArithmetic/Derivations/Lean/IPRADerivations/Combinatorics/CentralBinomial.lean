import IPRADerivations.Probability.BinomialLaw
import IPRADerivations.Probability.Variance
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.Geometry.HypercubeSplit
import IPRADerivations.Combinatorics.CatalanValuation
import IPRADerivations.Probability.MedianL1
import IPRADerivations.Combinatorics.BellTriangle

/-!
# The central binomial coefficient: unimodality and `4^n/(2n + 1) ≤ C(2n, n) ≤ 4^n`

Packet: `von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:binomial-lcm`, the second display
(cleared of the denominator). With the coefficients `C(m, k) = m!/(k!(m − k)!)`:

* `ratio`: `(k + 1) C(m, k + 1) = (m − k) C(m, k)` for `k < m`, from absorption and Pascal's rule;
* `rise`, `fall`: in row `2n`, `C(2n, k) ≤ C(2n, k + 1)` for `k < n` and `C(2n, k + 1) ≤ C(2n, k)` for
  `n ≤ k < 2n`;
* `central_left`, `central_right`, `central_max`: `C(2n, k) ≤ C(2n, n)` for every `k ≤ 2n` (reusable);
* `central_upper`: `C(2n, n) ≤ 4^n`, a term of the row sum `∑_k C(2n, k) = 2^{2n}`;
* `central_lower`: `4^n ≤ (2n + 1) C(2n, n)`, the row sum bounded by its largest term.

The divisibility chain `∏ p ∣ C(2n, n) ∣ lcm(1, …, 2n)` is not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CentralBinomial

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (pascal_at binom_sum_open bBody inst2_b)
open LeanProofs.IPRA.Probability.BinomialLaw (absorption)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

alias succ_pos' := Common.succ_pos

/-- `(k + 1) C(m, k + 1) = (m − k) C(m, k)` for `k < m`. -/
theorem ratio {k m : PTm n} (h : Γ ⊢[PRAAx] lt k m) :
    Γ ⊢[PRAAx] succ k * binom m (succ k) ≐ monus m k * binom m k := by
  ipra_lc natEq (absorption (le_of_lt h)) - (𝔞 k + 1) * natEq (pascal_at h) +
    𝔞 (binom m k) * natEq (eq_add_of_le (le_of_lt h))

/-- `C(2n, k) ≤ C(2n, k + 1)` for `k < n`. -/
theorem rise {k N : PTm n} (h : Γ ⊢[PRAAx] lt k N) :
    Γ ⊢[PRAAx] le (binom (two * N) k) (binom (two * N) (succ k)) := by
  have hk : Γ ⊢[PRAAx] lt k (two * N) := le_trans h (le_of_eq_add (d := N) (by ipra_ring))
  refine le_cancel_pos (succ_pos' k) (le_of_eq_add (d := monus N (succ k) * binom (two * N) k +
    monus N (succ k) * binom (two * N) k + binom (two * N) k) ?_)
  ipra_lc natEq (ratio hk) - 𝔞 (binom (two * N) k) * natEq (eq_add_of_le (le_of_lt hk)) +
    2 * 𝔞 (binom (two * N) k) * natEq (eq_add_of_le h)

/-- `C(2n, k + 1) ≤ C(2n, k)` for `n ≤ k < 2n`. -/
theorem fall {k N : PTm n} (h₁ : Γ ⊢[PRAAx] le N k) (h₂ : Γ ⊢[PRAAx] lt k (two * N)) :
    Γ ⊢[PRAAx] le (binom (two * N) (succ k)) (binom (two * N) k) := by
  refine le_cancel_pos (succ_pos' k) (le_of_eq_add (d := (monus k N + monus k N + one) * binom (two * N) k) ?_)
  ipra_lc -natEq (ratio h₂) + 𝔞 (binom (two * N) k) * natEq (eq_add_of_le (le_of_lt h₂)) +
    2 * 𝔞 (binom (two * N) k) * natEq (eq_add_of_le h₁)

/-! ## Moving out from the centre -/

/-- `C(2n, n) ≥ 1`. -/
theorem central_pos (N : PTm n) : Γ ⊢[PRAAx] le one (binom (two * N) N) := by
  have c' := natEq (LeanProofs.IPRA.Combinatorics.Catalan.cat_spec (Γ := Γ) N)
  refine le_of_eq_add (d := N * LeanProofs.IPRA.Combinatorics.Catalan.cat N + pred (LeanProofs.IPRA.Combinatorics.Catalan.cat N)) ?_
  ipra_lc -c' + natEq (LeanProofs.IPRA.Combinatorics.CatalanValuation.cat_pos (Γ := Γ) N)

theorem left_in {N j : PTm n} (h : Γ ⊢[PRAAx] le (succ j) N)
    (ih : Γ ⊢[PRAAx] le (binom (two * N) (monus N j)) (binom (two * N) N)) :
    Γ ⊢[PRAAx] le (binom (two * N) (monus N (succ j))) (binom (two * N) N) := by
  have e := eq_add_of_le h
  have m₁ : Γ ⊢[PRAAx] monus N j ≐ succ (monus N (succ j)) :=
    (congrMonus (e.eqTrans (by ipra_ring)) (.eqRefl j)).eqTrans (add_monus' _ _)
  have hk : Γ ⊢[PRAAx] lt (monus N (succ j)) N := le_of_eq_add (d := j) (e.eqTrans (by ipra_ring))
  exact le_trans (rise hk) (le_congr (congrBinom (.eqRefl _) m₁) (.eqRefl _) ih)

theorem left_out {N j : PTm n} (h : Γ ⊢[PRAAx] le N (succ j)) :
    Γ ⊢[PRAAx] le (binom (two * N) (monus N (succ j))) (binom (two * N) N) :=
  le_congr ((LeanProofs.IPRA.Combinatorics.BinomialIdentities.binom_zero' _).eqSymm.eqTrans
    (congrBinom (.eqRefl _) h.eqSymm)) (.eqRefl _) (central_pos N)

/-- Variables: `0 = j`, `1 = N`. -/
private abbrev leftF : Fm PTm 2 := le (binom (two * var 1) (monus (var 1) (var 0))) (binom (two * var 1) (var 1))

private theorem left₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] leftF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact le_congr (congrBinom (.eqRefl _) (monus_zero _)).eqSymm (.eqRefl _) (le_refl _)
  · exact .orE (le_total (succ (var 0)) (var 1)) (left_in Prf.hyp0 Prf.hyp1) (left_out Prf.hyp0)

/-- `C(2n, n − j) ≤ C(2n, n)`. -/
theorem central_left (N j : PTm n) : Γ ⊢[PRAAx] le (binom (two * N) (monus N j)) (binom (two * N) N) := by
  have h := inst (Γ := Γ) left₀ (![j, N] : Fin 2 → PTm n)
  simpa using h

theorem right_step {N j : PTm n} (h : Γ ⊢[PRAAx] le (succ j) N)
    (ih : Γ ⊢[PRAAx] le (binom (two * N) (N + j)) (binom (two * N) N)) :
    Γ ⊢[PRAAx] le (binom (two * N) (N + succ j)) (binom (two * N) N) := by
  have hk : Γ ⊢[PRAAx] lt (N + j) (two * N) := le_of_eq_add (d := monus N (succ j)) (by
    ipra_lc natEq (eq_add_of_le h))
  exact le_trans (le_congr (congrBinom (.eqRefl _) (add_succ _ _)).eqSymm (.eqRefl _)
    (fall (le_of_eq_add (d := j) (.eqRefl _)) hk)) ih

/-- `C(2n, n + j) ≤ C(2n, n)` for `j ≤ n`. -/
theorem central_right {N j : PTm n} (h : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] le (binom (two * N) (N + j)) (binom (two * N) N) := by
  have row : Γ ⊢[PRAAx] two * N ≐ N + N := by ipra_ring
  have hi := le_congr (.eqRefl _) row.eqSymm (add_le_add₂ (le_refl N) h)
  have complement := (congrMonus row (add_comm N j)).eqTrans (monus_add_add N j N)
  exact le_congr ((congrBinom (.eqRefl _) complement.eqSymm).eqTrans (BellTriangle.binom_symm hi))
    (.eqRefl _) (central_left N j)

alias monus_monus' := Common.monus_monus_of_le

theorem central_hi {N k : PTm n} (h₁ : Γ ⊢[PRAAx] le N k) (h : Γ ⊢[PRAAx] le k (two * N)) :
    Γ ⊢[PRAAx] le (binom (two * N) k) (binom (two * N) N) := by
  have hj := LeanProofs.IPRA.Order.monus_le_of_le_add (y := N) (z := N)
    (le_congr (.eqRefl _) (by ipra_ring) h)
  exact le_congr (congrBinom (.eqRefl _) (eq_add_of_le h₁).eqSymm) (.eqRefl _) (central_right hj)

/-- `C(2n, k) ≤ C(2n, n)` for `k ≤ 2n`. -/
theorem central_max {N k : PTm n} (h : Γ ⊢[PRAAx] le k (two * N)) :
    Γ ⊢[PRAAx] le (binom (two * N) k) (binom (two * N) N) :=
  .orE (le_total k N)
    (le_congr (congrBinom (.eqRefl _) (monus_monus' Prf.hyp0)) (.eqRefl _) (central_left N (monus N k)))
    (central_hi Prf.hyp0 h.wk)

/-! ## The row sum -/

/-- `∑_{k≤2n} C(2n, k) = 2^{2n}`. -/
theorem row_sum (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF bBody) (succ (two * N)) (two * N) ≐ pw two (two * N) := by
  have hs := inst (Γ := Γ) binom_sum_open ![two * N]
  simpa using hs

theorem shift_binom (a b : PTm n) : Syn.shift (binom a b) = binom (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

theorem shift_two_mul (a : PTm n) : Syn.shift (two * a) = two * Syn.shift a := by simp [Syn.shift]

/-- `C(2n, n) ≤ 4^n`, with `4^n = 2^{2n}`. -/
theorem central_upper (N : PTm n) : Γ ⊢[PRAAx] le (binom (two * N) N) (pw two (two * N)) := by
  have hn : Γ ⊢[PRAAx] lt N (succ (two * N)) :=
    (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := N) (by ipra_ring))
  have ht := term_le_sum bBody (x := two * N) hn
  rw [inst2_b] at ht
  exact le_congr (.eqRefl _) (row_sum N) ht

/-- `4^n ≤ (2n + 1) C(2n, n)`: the `2n + 1` terms of the row sum are each at most `C(2n, n)`. -/
theorem central_lower (N : PTm n) : Γ ⊢[PRAAx] le (pw two (two * N)) (succ (two * N) * binom (two * N) N) := by
  refine le_congr (row_sum N) (.eqRefl _) (sum_le_uniform_bound bBody (.allI (.impI ?_)))
  rw [inst2_b, shift_binom, shift_two_mul,
    show Syn.shift (succ (two * N)) = succ (two * Syn.shift N) by simp [Syn.shift]]
  exact central_max (LeanProofs.IPRA.Order.le_of_lt_succ Prf.hyp0)

end LeanProofs.IPRA.Combinatorics.CentralBinomial
