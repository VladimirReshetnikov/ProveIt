import IPRADerivations.Combinatorics.LegendreDigits
import IPRADerivations.DiophantineNumberTheory.ModularCertificate
import IPRADerivations.Foundations.CrossingSearch
import IPRADerivations.Core.LinearCombination

/-!
# Base-expansion divisibility rules

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem `el:digits`:
for a base `b ≥ 2`, `n ≡ ∑ d_i (mod b − 1)`, and if `m ∣ b^j` then divisibility by `m` depends only on the last
`j` digits of `n`.

The digits are `d_i = ⌊n/b^i⌋ mod b` and the digit sum is `s_b(n) = ∑_{i<n} d_i` (`LegendreDigits.dB`).

* `pred_pos`: `b − 1 ≥ 1` for `b ≥ 2`;
* **`digit_sum_rule`**: `n mod (b − 1) = s_b(n) mod (b − 1)` (the rules for `3` and `9` at `b = 10`), from the
  telescoped identity `s_b(n) + (b − 1) ∑_{j ≥ 1} ⌊n/b^j⌋ = n` (`LegendreDigits.legendre_digits`);
* **`last_digits`**: if `m ∣ b^j` then `n mod m = (n mod b^j) mod m`, and `last_digits_dvd`: `m ∣ n` exactly when
  `m ∣ (n mod b^j)`.

The alternating rule modulo `b + 1` is not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.DigitRules

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm qB' legendre_digits)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd')
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_add_mul)
open LeanProofs.IPRA.Foundations.CrossingSearch (monus_of_eq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The digit sum modulo `b − 1` -/

theorem two_split {b : PTm k} (hb : Γ ⊢[PRAAx] le two b) : Γ ⊢[PRAAx] b ≐ one + succ (monus b two) := by
  ipra_lc natEq (eq_add_of_le hb)

/-- `b − 1 ≥ 1` for `b ≥ 2`. -/
theorem pred_pos {b : PTm k} (hb : Γ ⊢[PRAAx] le two b) :
    Γ ⊢[PRAAx] monus b one ≐ succ (pred (monus b one)) :=
  pos_of_eq_succ (c := monus b two) (monus_of_eq (two_split hb))

/-- **The digit-sum rule**: `n mod (b − 1) = s_b(n) mod (b − 1)` for a base `b ≥ 2`. -/
theorem digit_sum_rule {b : PTm k} (hb : Γ ⊢[PRAAx] le two b) (m : PTm k) :
    Γ ⊢[PRAAx] rem m (monus b one) ≐ rem (ap2 (sumF Combinatorics.LegendreDigits.dB) m (pairT b m)) (monus b one) := by
  have l := legendre_digits hb m
  have e : Γ ⊢[PRAAx] m ≐ monus b one * ap2 (sumF qB') m (pairT b m) + ap2 (sumF Combinatorics.LegendreDigits.dB) m (pairT b m) :=
    l.eqSymm.eqTrans (add_comm _ _)
  exact (congrAp2 remF e (.eqRefl _)).eqTrans (rem_add_mul (pred_pos hb) _ _)

/-! ## The last digits -/

theorem last_alg {n P d q r c : PTm k} (e : Γ ⊢[PRAAx] n ≐ P * q + r) (f : Γ ⊢[PRAAx] P ≐ d * c) :
    Γ ⊢[PRAAx] n ≐ d * (c * q) + r := by
  ipra_lc natEq e + 𝔞 q * natEq f

/-- If `m ∣ b^j` then `n mod m = (n mod b^j) mod m`. -/
theorem last_digits {m b j : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hb : Γ ⊢[PRAAx] b ≐ succ (pred b))
    (h : Γ ⊢[PRAAx] dvd m (pw b j)) (n : PTm k) :
    Γ ⊢[PRAAx] rem n m ≐ rem (rem n (pw b j)) m := by
  have d := Prf.andE₁ (dm (pw_pos' hb j) n)
  have f := eq_of_dvd' hm h
  exact (congrAp2 remF (last_alg d f) (.eqRefl _)).eqTrans (rem_add_mul hm _ _)

/-- If `m ∣ b^j` then `m ∣ n` exactly when `m` divides the number formed by the last `j` digits. -/
theorem last_digits_dvd {m b j : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (h : Γ ⊢[PRAAx] dvd m (pw b j)) (n : PTm k) :
    Γ ⊢[PRAAx] (dvd m n ⟶ dvd m (rem n (pw b j))) ⋏ (dvd m (rem n (pw b j)) ⟶ dvd m n) := by
  have e := last_digits hm hb h n
  exact .andI (.impI (e.wk.eqSymm.eqTrans Prf.hyp0)) (.impI (e.wk.eqTrans Prf.hyp0))

end LeanProofs.IPRA.DiophantineNumberTheory.DigitRules
