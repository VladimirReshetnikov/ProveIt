import IPRADerivations.Algebra.FourResolvent
import IPRADerivations.DiophantineNumberTheory.SimultaneousGrid

/-!
# The effective asymptotic bound of the Bring radical

Packet: `algebra/bring_quintic_ipra_2026-11-16`, Theorem `thm:bring-asymptotic`: for `a = r⁵`, `r ≥ 1`, and
`y = −BR(a)` (so `y⁵ + y = r⁵`), "`0 ≤ r + BR(a) ≤ r^{−3}`, `0 ≤ 1 − (−BR(a))/r ≤ r^{−4}`. ... The parenthesized
factor in `r⁵ − y⁵ = y` is at least `r⁴`, and `y ≤ r`. Therefore `0 ≤ r − y ≤ y/r⁴ ≤ r^{−3}`. ... All inequalities
become integer polynomial inequalities after multiplying by positive powers of `r`."

For a rational approximation `y = p/q` satisfying the equation exactly in the cleared form
`p⁵ + p q⁴ = (rq)⁵` (`q, r ≥ 1`):

* `bring_asymptotic`: `p ≤ rq` (i.e. `y ≤ r`) and `r³ (rq − p) ≤ q` (i.e. `r − y ≤ r^{−3}`, equivalently
  `1 − y/r ≤ r^{−4}`). The first part: `rq < p` would give `(rq)⁵ < p⁵ ≤ p⁵ + pq⁴`. The second: with
  `s = rq − p`, `s (rq)⁴ ≤ s ∑ (rq)^i p^{4−i} = p q⁴ ≤ rq · q⁴`, then `r q⁴ ≥ 1` cancels; the certificate was
  found with `sympy`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.BringAsymptotic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.SimultaneousGrid (cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `y ≤ r`: `p⁵ + pq⁴ = (rq)⁵` gives `p ≤ rq`. -/
theorem y_le_r {p q r : PTm n}
    (h : Γ ⊢[PRAAx] p * p * p * p * p + p * (q * q * q * q) ≐ r * q * (r * q) * (r * q) * (r * q) * (r * q)) :
    Γ ⊢[PRAAx] le p (r * q) := by
  refine .orE (lt_or_le (r * q) p) ?_ Prf.hyp0
  have hl : (lt (r * q) p :: Γ) ⊢[PRAAx] le (succ (r * q)) p := Prf.hyp0
  have h1 : (lt (r * q) p :: Γ) ⊢[PRAAx] le (p * p * p * p * p) (r * q * (r * q) * (r * q) * (r * q) * (r * q)) :=
    le_of_eq_add (d := p * (q * q * q * q)) h.wk.eqSymm
  have h2 : (lt (r * q) p :: Γ) ⊢[PRAAx] le (succ (r * q * (r * q) * (r * q) * (r * q) * (r * q)))
      (p * p * p * p * p) := by
    ipra_le 5 * (𝔟 r * 𝔟 q) ^ 4 * (1 + sl hl) + 10 * (𝔟 r * 𝔟 q) ^ 3 * (1 + sl hl) ^ 2 +
      10 * (𝔟 r * 𝔟 q) ^ 2 * (1 + sl hl) ^ 3 + 5 * (𝔟 r * 𝔟 q) * (1 + sl hl) ^ 4 +
      5 * sl hl + 10 * sl hl ^ 2 + 10 * sl hl ^ 3 + 5 * sl hl ^ 4 + sl hl ^ 5
  exact le_lt_absurd _ h1 h2

/-- `thm:bring-asymptotic`: `y ≤ r` and `r³ (rq − p) ≤ q`, i.e. `0 ≤ r − y ≤ r^{−3}`. -/
theorem bring_asymptotic {p q r : PTm n} (hq : Γ ⊢[PRAAx] le one q) (hr : Γ ⊢[PRAAx] le one r)
    (h : Γ ⊢[PRAAx] p * p * p * p * p + p * (q * q * q * q) ≐ r * q * (r * q) * (r * q) * (r * q) * (r * q)) :
    Γ ⊢[PRAAx] le p (r * q) ⋏ le (r * r * r * monus (r * q) p) q := by
  have hp := y_le_r h
  refine .andI hp ?_
  have es := natEq (eq_add_of_le hp)
  have eh := natEq h
  have hX : Γ ⊢[PRAAx] le one (r * (q * q * q * q)) := by
    ipra_le sl hr * 𝔟 q ^ 4 + sl hq * (𝔟 q ^ 3 + 𝔟 q ^ 2 + 𝔟 q + 1)
  refine cancel_pos hX ?_
  ipra_le 𝔟 q ^ 4 * 𝔟 (monus (r * q) p) + 𝔟 (monus (r * q) p) *
      ((𝔟 r * 𝔟 q) ^ 3 * 𝔟 p + (𝔟 r * 𝔟 q) ^ 2 * 𝔟 p ^ 2 + 𝔟 r * 𝔟 q * 𝔟 p ^ 3 + 𝔟 p ^ 4) with
    eh + (𝔟 p ^ 4 + 𝔟 p ^ 3 * 𝔟 q * 𝔟 r + 𝔟 p ^ 2 * 𝔟 q ^ 2 * 𝔟 r ^ 2 + 𝔟 p * 𝔟 q ^ 3 * 𝔟 r ^ 3 +
      𝔟 q ^ 4 * 𝔟 r ^ 4 + 𝔟 q ^ 4) * es

end LeanProofs.IPRA.Algebra.BringAsymptotic
