import IPRADerivations.Analysis.Polynomials.Elimination.ChuVandermonde
import IPRADerivations.Core.LinearCombination

/-!
# The binomial sum for the Beta function at integers

Packet: `analysis/beta_function_ipra_2026-11-16`, Theorem `thm:inc-polynomial` ("Exact polynomial
formula") at `x = 1` together with the integer values of `thm:integer-values`:

`B(m + 1, n + 1) = ∑_{j=0}^{n} (−1)^j C(n, j) / (m + 1 + j) = n! / ((m + 1)(m + 2) ⋯ (m + n + 1))`,

"a finite sum identity with no analytic remainder" (the binomial theorem for `(1 − t)^n` integrated
termwise against `t^m`).

Multiplied by `(m + 1)_{n+1}`, the `j`-th term is `(−1)^j C(n, j) (m + 1)_j (m + 2 + j)_{n−j}`, so the
identity is the Chu–Vandermonde summation of `Analysis/ChuVandermonde` at `b = m + 1`, `d = 1`:

* `term_eq`: `(m + 1 + j) · (m + 1)_j (m + 2 + j)_{n−j} = (m + 1)_{n+1}` for `j ≤ n`, the clearing of the
  denominator `m + 1 + j`;
* `beta_binomial_sum`: `T⁺_n(m + 1, 1) = T⁻_n(m + 1, 1) + n!`, i.e.
  `(m + 1)_{n+1} ∑_j (−1)^j C(n, j)/(m + 1 + j) = n!`.

The integral itself is not formalized; `Analysis/BetaIntegers` has the factorial form of the value.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.BetaBinomialSum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.Pochhammer (poch poch_split poch_shift' poch_one)
open LeanProofs.IPRA.Analysis.ChuVandermonde (TE TO chu_vandermonde congrPoch)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `(m + 1 + j) · (m + 1)_j (m + 2 + j)_{N−j} = (m + 1)_{N+1}` for `j ≤ N`. -/
theorem term_eq {j N m : PTm n} (h : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] (succ m + j) * (poch (succ m) j * poch (succ m + one + j) (monus N j)) ≐
      poch (succ m) (succ N) := by
  have eN : Γ ⊢[PRAAx] succ N ≐ j + succ (monus N j) := by
    ipra_lc natEq (eq_add_of_le h)
  have ex : Γ ⊢[PRAAx] succ (succ m + j) ≐ succ m + one + j := by
    ipra_ring
  ipra_lc -natEq (congrPoch (.eqRefl (succ m)) eN) - natEq (poch_split (Γ := Γ) (succ m) j (succ (monus N j))) -
    𝔟(poch (succ m) j) * natEq (poch_shift' (Γ := Γ) (succ m + j) (monus N j)) -
    (𝔟 m + 1 + 𝔟 j) * 𝔟(poch (succ m) j) * natEq (congrPoch ex (.eqRefl (monus N j)))

/-- `thm:inc-polynomial` at `x = 1`, cleared by `(m + 1)_{N+1}`:
`∑_{j ≤ N} (−1)^j C(N, j) (m + 1)_j (m + 2 + j)_{N−j} = N!`, the signed sum by its even and odd parts. -/
theorem beta_binomial_sum (N m : PTm n) :
    Γ ⊢[PRAAx] TE N (succ m) one ≐ TO N (succ m) one + fact N :=
  (chu_vandermonde N (succ m) one).eqTrans (congrAdd (.eqRefl _) (poch_one N))

end LeanProofs.IPRA.Analysis.BetaBinomialSum
