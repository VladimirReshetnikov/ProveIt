import IPRADerivations.Analysis.BetaIntegers
import IPRADerivations.Core.LinearCombination

/-!
# The associativity identity of the Beta function at positive integers

Packet: `analysis/beta_function_ipra_2026-11-16`, `paper/sections/05_gamma.tex`, Corollary `cor:beta-assoc`:
`B(p, q) B(p + q, r) = B(q, r) B(q + r, p)`. At positive integers `p = m + 1`, `q = k + 1`, `r = j + 1` and
for the reciprocal `R(m, k) = 1 / B(m + 1, k + 1)` of `Analysis/BetaIntegers`, the identity is

`R(m, k) R(m + k + 1, j) = R(k, j) R(k + j + 1, m)`

(`rbeta_assoc`). Both sides are `(m + k + j + 2)! / (m! k! j!)`: the proof multiplies by `m! k! j!`, uses
`BetaIntegers.rbeta_fact` four times, and cancels, which is the division-free argument of the paper. The
real-argument statement and the Beta–Gamma identity behind it are not formalized.
-/

namespace LeanProofs.IPRA.Analysis.BetaAssociativity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Analysis.BetaIntegers (rbeta rbeta_fact)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-- `cor:beta-assoc` at positive integers: `R(m, k) R(m + k + 1, j) = R(k, j) R(k + j + 1, m)`. -/
theorem rbeta_assoc (m k j : PTm n) :
    Γ ⊢[PRAAx] rbeta m k * rbeta (succ (m + k)) j ≐ rbeta k j * rbeta (succ (k + j)) m := by
  have hc : Γ ⊢[PRAAx] succ (succ (m + k) + j) ≐ succ (succ (k + j) + m) := by
    ipra_ring
  have c₅ := natEq (congrAp2 factF hc (.eqRefl _) :
    Γ ⊢[PRAAx] fact (succ (succ (m + k) + j)) ≐ fact (succ (succ (k + j) + m)))
  refine mul_cancel (D := fact m * fact k * fact j)
    (pos_mul (pos_mul (fact_pos m) (fact_pos k)) (fact_pos j)) ?_
  ipra_lc (𝔞 (rbeta (succ (m + k)) j) * 𝔞 (fact j)) * natEq (rbeta_fact (Γ := Γ) m k) +
    natEq (rbeta_fact (Γ := Γ) (succ (m + k)) j) + c₅ - natEq (rbeta_fact (Γ := Γ) (succ (k + j)) m) -
    (𝔞 (rbeta (succ (k + j)) m) * 𝔞 (fact m)) * natEq (rbeta_fact (Γ := Γ) k j)

end LeanProofs.IPRA.Analysis.BetaAssociativity
