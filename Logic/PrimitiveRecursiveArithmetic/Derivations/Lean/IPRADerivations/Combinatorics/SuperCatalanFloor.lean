import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.AnalyticNumberTheory.Totient
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# The floor inequality of the super-Catalan numbers (`catalan_numbers_ipra_2026-11-16`, (7.15))

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, Subsection "Super-Catalan integers":
for `S(m, n) = (2m)! (2n)! / (m! n! (m + n)!)` (7.14), "for every prime power `a = p^j`,
`⌊2m/a⌋ + ⌊2n/a⌋ ≥ ⌊m/a⌋ + ⌊n/a⌋ + ⌊(m + n)/a⌋` (7.15). After removing integer parts, this is
`⌊2u⌋ + ⌊2v⌋ ≥ ⌊u + v⌋` for `0 ≤ u, v < 1`, verified by the four cases `u < 1/2` or `u ≥ 1/2`,
and similarly for `v`."

The inequality is derived for every divisor `a ≥ 1` (not only prime powers), with
`m = a q_1 + r_1`, `n = a q_2 + r_2`:

* `two_quo_le`: `2 ⌊m/a⌋ ≤ ⌊2m/a⌋`;
* `two_quo_succ_le`: `2 ⌊m/a⌋ + 1 ≤ ⌊2m/a⌋` when `a ≤ 2 r_1` (the case `u ≥ 1/2`);
* `add_quo_lt`, `add_quo_ge`: `⌊(m + n)/a⌋` is `q_1 + q_2` when `r_1 + r_2 < a`, and
  `q_1 + q_2 + 1` when `a ≤ r_1 + r_2`;
* `half_cases`: `a ≤ r_1 + r_2` gives `a ≤ 2 r_1` or `a ≤ 2 r_2`;
* `super_floor`: (7.15).

Not derived: the summation of (7.15) over the powers of a prime with Legendre's formula, and
hence the integrality of `S(m, n)`.
-/

namespace LeanProofs.IPRA.Combinatorics.SuperCatalanFloor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (quo_eq)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

alias succ_pos₁ := Common.succ_pos

/-- `2 ⌊m/a⌋ ≤ ⌊2m/a⌋`. -/
theorem two_quo_le (m a' : PTm k) :
    Γ ⊢[PRAAx] le (two * quo m (succ a')) (quo (two * m) (succ a')) := by
  refine le_quo_of_mul_le (succ_pos₁ a') (le_of_eq_add (d := two * rem m (succ a')) ?_)
  ipra_lc 2 * natEq (Prf.andE₁ (div_mod (Γ := Γ) m a'))

/-- `2 ⌊m/a⌋ + 1 ≤ ⌊2m/a⌋` when the remainder is at least `a/2`. -/
theorem two_quo_succ_le {m a' : PTm k}
    (h : Γ ⊢[PRAAx] le (succ a') (two * rem m (succ a'))) :
    Γ ⊢[PRAAx] le (succ (two * quo m (succ a'))) (quo (two * m) (succ a')) := by
  refine le_quo_of_mul_le (succ_pos₁ a')
    (le_of_eq_add (d := monus (two * rem m (succ a')) (succ a')) ?_)
  ipra_lc 2 * natEq (Prf.andE₁ (div_mod (Γ := Γ) m a')) + natEq (eq_add_of_le h)

/-- No carry: `⌊(m + n)/a⌋ = ⌊m/a⌋ + ⌊n/a⌋`. -/
theorem add_quo_lt {m n a' : PTm k}
    (h : Γ ⊢[PRAAx] lt (rem m (succ a') + rem n (succ a')) (succ a')) :
    Γ ⊢[PRAAx] quo (m + n) (succ a') ≐ quo m (succ a') + quo n (succ a') := by
  refine quo_eq (succ_pos₁ a') ?_ h
  ipra_lc natEq (Prf.andE₁ (div_mod (Γ := Γ) m a')) + natEq (Prf.andE₁ (div_mod (Γ := Γ) n a'))

/-- A carry: `⌊(m + n)/a⌋ = ⌊m/a⌋ + ⌊n/a⌋ + 1`. -/
theorem add_quo_ge {m n a' : PTm k}
    (h : Γ ⊢[PRAAx] le (succ a') (rem m (succ a') + rem n (succ a'))) :
    Γ ⊢[PRAAx] quo (m + n) (succ a') ≐ succ (quo m (succ a') + quo n (succ a')) := by
  have d₁ := div_mod (Γ := Γ) m a'
  have d₂ := div_mod (Γ := Γ) n a'
  refine quo_eq (r := monus (rem m (succ a') + rem n (succ a')) (succ a')) (succ_pos₁ a') ?_ ?_
  · ipra_lc natEq (Prf.andE₁ d₁) + natEq (Prf.andE₁ d₂) + natEq (eq_add_of_le h)
  · refine le_of_eq_add (d := succ (monus (succ a') (succ (rem m (succ a'))) +
      monus (succ a') (succ (rem n (succ a'))))) ?_
    ipra_lc natEq (eq_add_of_le (Prf.andE₂ d₁)) + natEq (eq_add_of_le (Prf.andE₂ d₂)) + natEq (eq_add_of_le h)

/-- If two numbers sum to at least `a`, one of them is at least `a/2`. -/
theorem half_cases {r₁ r₂ a : PTm k} (h : Γ ⊢[PRAAx] le a (r₁ + r₂)) :
    Γ ⊢[PRAAx] le a (two * r₁) ⋎ le a (two * r₂) := by
  refine .orE (lt_or_le (two * r₁) a) ?_ (.orI₁ Prf.hyp0)
  refine .orE (lt_or_le (two * r₂) a) ?_ (.orI₂ Prf.hyp0)
  have u₁ := natEq (eq_add_of_le
    (Prf.hyp1 : (lt (two * r₂) a :: lt (two * r₁) a :: Γ) ⊢[PRAAx] lt (two * r₁) a))
  have u₂ := natEq (eq_add_of_le
    (Prf.hyp0 : (lt (two * r₂) a :: lt (two * r₁) a :: Γ) ⊢[PRAAx] lt (two * r₂) a))
  have g := natEq (eq_add_of_le (h.wk.wk :
    (lt (two * r₂) a :: lt (two * r₁) a :: Γ) ⊢[PRAAx] le a (r₁ + r₂)))
  refine succ_ne_zero' _ (a := succ (monus a (succ (two * r₁)) + monus a (succ (two * r₂)) +
    two * monus (r₁ + r₂) a)) ?_
  ipra_lc -u₁ - u₂ - 2 * g

/-- The case without a carry. -/
theorem case_lt {m n a' : PTm k}
    (h : Γ ⊢[PRAAx] lt (rem m (succ a') + rem n (succ a')) (succ a')) :
    Γ ⊢[PRAAx] le (quo m (succ a') + quo n (succ a') + quo (m + n) (succ a'))
      (quo (two * m) (succ a') + quo (two * n) (succ a')) := by
  refine le_of_eq_add (d := monus (quo (two * m) (succ a')) (two * quo m (succ a')) +
    monus (quo (two * n) (succ a')) (two * quo n (succ a'))) ?_
  ipra_lc natEq (eq_add_of_le (two_quo_le (Γ := Γ) m a')) + natEq (eq_add_of_le (two_quo_le (Γ := Γ) n a')) -
    natEq (add_quo_lt h)

/-- The case with a carry, the first remainder being at least `a/2`. -/
theorem case_ge₁ {m n a' : PTm k}
    (h : Γ ⊢[PRAAx] le (succ a') (rem m (succ a') + rem n (succ a')))
    (h₁ : Γ ⊢[PRAAx] le (succ a') (two * rem m (succ a'))) :
    Γ ⊢[PRAAx] le (quo m (succ a') + quo n (succ a') + quo (m + n) (succ a'))
      (quo (two * m) (succ a') + quo (two * n) (succ a')) := by
  refine le_of_eq_add (d := monus (quo (two * m) (succ a')) (succ (two * quo m (succ a'))) +
    monus (quo (two * n) (succ a')) (two * quo n (succ a'))) ?_
  ipra_lc natEq (eq_add_of_le (two_quo_succ_le h₁)) + natEq (eq_add_of_le (two_quo_le (Γ := Γ) n a')) -
    natEq (add_quo_ge h)

/-- The case with a carry, the second remainder being at least `a/2`. -/
theorem case_ge₂ {m n a' : PTm k}
    (h : Γ ⊢[PRAAx] le (succ a') (rem m (succ a') + rem n (succ a')))
    (h₂ : Γ ⊢[PRAAx] le (succ a') (two * rem n (succ a'))) :
    Γ ⊢[PRAAx] le (quo m (succ a') + quo n (succ a') + quo (m + n) (succ a'))
      (quo (two * m) (succ a') + quo (two * n) (succ a')) := by
  refine le_of_eq_add (d := monus (quo (two * m) (succ a')) (two * quo m (succ a')) +
    monus (quo (two * n) (succ a')) (succ (two * quo n (succ a')))) ?_
  ipra_lc natEq (eq_add_of_le (two_quo_le (Γ := Γ) m a')) + natEq (eq_add_of_le (two_quo_succ_le h₂)) -
    natEq (add_quo_ge h)

/-- (7.15): `⌊m/a⌋ + ⌊n/a⌋ + ⌊(m + n)/a⌋ ≤ ⌊2m/a⌋ + ⌊2n/a⌋` for every `a ≥ 1`. -/
theorem super_floor (m n a' : PTm k) :
    Γ ⊢[PRAAx] le (quo m (succ a') + quo n (succ a') + quo (m + n) (succ a'))
      (quo (two * m) (succ a') + quo (two * n) (succ a')) :=
  .orE (lt_or_le (rem m (succ a') + rem n (succ a')) (succ a')) (case_lt Prf.hyp0)
    (.orE (half_cases Prf.hyp0) (case_ge₁ Prf.hyp1 Prf.hyp0) (case_ge₂ Prf.hyp1 Prf.hyp0))

/-- (7.15) as a closed sentence. Variables: `0 = m`, `1 = n`, `2 = a − 1`. -/
theorem super_floor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (quo (var 0) (succ (var 2)) + quo (var 1) (succ (var 2)) +
        quo (var 0 + var 1) (succ (var 2)))
      (quo (two * var 0) (succ (var 2)) + quo (two * var 1) (succ (var 2)))) :=
  closeUniv 3 (super_floor _ _ _)

end LeanProofs.IPRA.Combinatorics.SuperCatalanFloor
