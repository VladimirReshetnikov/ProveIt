import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination

/-!
# Tail and error identities of a continued fraction

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, Theorem
`dio:cf-error`: for a positive rational `t` and the convergents `p_n/q_n`, `p_{n−1}/q_{n−1}`,

    [a₀; …, a_n, t] = (t p_n + p_{n−1}) / (t q_n + q_{n−1}),
    |[a₀; …, a_n, t] − p_n/q_n| = 1 / (q_n (t q_n + q_{n−1})),

with the distance at most `1/q_n²` for `t ≥ 1`, at most `1/(q_n q_{n+1})` for `t ≥ a_{n+1}`, and the value
between adjacent convergents.

"Insert `t` in the matrix identity and subtract `p_n/q_n`. The numerator of the difference is
`p_{n−1} q_n − p_n q_{n−1}`, of absolute value `1`." With `t = u/v` and the denominators cleared, the value is
`N/D` for `N = u p + v p'`, `D = u q + v q'` (the next column of the matrix product, scaled by `v`), where
`(p, q) = (p_n, q_n)`, `(p', q') = (p_{n−1}, q_{n−1})`. The statements hold for every matrix of determinant
`±1`; the two signs are the two parities of `n` (`Recurrences.det_step`).

* `err_even`, `prev_even`: if `p' q = p q' + 1` then `N q = p D + v` and `p' D = N q' + u`;
* `err_odd`, `prev_odd`: if `p q' = p' q + 1` then `p D = N q + v` and `N q' = p' D + u`;
* `between_even`, `between_odd`: for `u, v ≥ 1` the value `N/D` lies strictly between `p/q` and `p'/q'`;
* `den_ge`: `t ≥ 1` (`v ≤ u`) gives `v q ≤ D`, so the distance `v/(q D)` is at most `1/q²`;
* `den_next`: `t ≥ a` (`a v ≤ u`) gives `v (a q + q') ≤ D`, so the distance is at most `1/(q q_{n+1})`.

The identification of the nested fraction with the matrix column (`dio:continuants`, the value identity) is not
derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ContinuedFractionTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The numerator `u p + v p'` of the value with tail `t = u/v`. -/
abbrev Nm (u v p p' : PTm n) : PTm n := u * p + v * p'

/-- The denominator `u q + v q'`. -/
abbrev Dn (u v q q' : PTm n) : PTm n := u * q + v * q'

/-! ## The error identities -/

section Even

variable {p q p' q' : PTm n} (hdet : Γ ⊢[PRAAx] p' * q ≐ p * q' + one)
include hdet

/-- `N q = p D + v`: the value exceeds `p/q` by `v/(q D)`. -/
theorem err_even (u v : PTm n) : Γ ⊢[PRAAx] Nm u v p p' * q ≐ p * Dn u v q q' + v := by
  ipra_lc 𝔞 v * natEq hdet

/-- `p' D = N q' + u`: the value is below `p'/q'` by `u/(q' D)`. -/
theorem prev_even (u v : PTm n) : Γ ⊢[PRAAx] p' * Dn u v q q' ≐ Nm u v p p' * q' + u := by
  ipra_lc 𝔞 u * natEq hdet

/-- For `u, v ≥ 1`: `p/q < N/D < p'/q'`. -/
theorem between_even {u v : PTm n} (hu : Γ ⊢[PRAAx] le one u) (hv : Γ ⊢[PRAAx] le one v) :
    Γ ⊢[PRAAx] lt (p * Dn u v q q') (Nm u v p p' * q) ⋏ lt (Nm u v p p' * q') (p' * Dn u v q q') := by
  have a := natEq (err_even hdet u v); have b := natEq (prev_even hdet u v)
  refine .andI ?_ ?_
  · ipra_le sl hv with a
  · ipra_le sl hu with b

end Even

section Odd

variable {p q p' q' : PTm n} (hdet : Γ ⊢[PRAAx] p * q' ≐ p' * q + one)
include hdet

/-- `p D = N q + v`: the value is below `p/q` by `v/(q D)`. -/
theorem err_odd (u v : PTm n) : Γ ⊢[PRAAx] p * Dn u v q q' ≐ Nm u v p p' * q + v := by
  ipra_lc 𝔞 v * natEq hdet

/-- `N q' = p' D + u`: the value exceeds `p'/q'` by `u/(q' D)`. -/
theorem prev_odd (u v : PTm n) : Γ ⊢[PRAAx] Nm u v p p' * q' ≐ p' * Dn u v q q' + u := by
  ipra_lc 𝔞 u * natEq hdet

/-- For `u, v ≥ 1`: `p'/q' < N/D < p/q`. -/
theorem between_odd {u v : PTm n} (hu : Γ ⊢[PRAAx] le one u) (hv : Γ ⊢[PRAAx] le one v) :
    Γ ⊢[PRAAx] lt (p' * Dn u v q q') (Nm u v p p' * q') ⋏ lt (Nm u v p p' * q) (p * Dn u v q q') := by
  have a := natEq (err_odd hdet u v); have b := natEq (prev_odd hdet u v)
  refine .andI ?_ ?_
  · ipra_le sl hu with b
  · ipra_le sl hv with a

end Odd

/-! ## The bounds on the denominator -/

/-- `t ≥ 1` gives `v q ≤ D`: the distance `v/(q D)` from `p/q` is at most `1/q²`. -/
theorem den_ge {u v : PTm n} (q q' : PTm n) (h : Γ ⊢[PRAAx] le v u) :
    Γ ⊢[PRAAx] le (v * q) (Dn u v q q') := by
  ipra_le sl h * 𝔞 q + 𝔞 v * 𝔞 q'

/-- `t ≥ a` gives `v (a q + q') ≤ D`: the distance from `p/q` is at most `1/(q (a q + q'))`. -/
theorem den_next {u v a : PTm n} (q q' : PTm n) (h : Γ ⊢[PRAAx] le (a * v) u) :
    Γ ⊢[PRAAx] le (v * (a * q + q')) (Dn u v q q') := by
  ipra_le sl h * 𝔞 q

end LeanProofs.IPRA.DiophantineNumberTheory.ContinuedFractionTail
