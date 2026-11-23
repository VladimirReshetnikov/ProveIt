import IPRADerivations.AnalyticNumberTheory.SieveFinite
import IPRADerivations.AnalyticNumberTheory.SieveWeightBound

/-!
# The finite sieve inequality

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `thm:finite-sieve`, first
inequality of `eq:finite-sieve`:

  "If `q, z ≥ 1` and `gcd(a, q) = 1`, then `π(x; q, a) ≤ x / (q G_q(z)) + z² + z`",

where `G_q(z) = Σ_{d ≤ z, d squarefree, gcd(d, q) = 1} 1/φ(d)`.

`finite_sieve` is this inequality for `q ≥ 1`, cleared of its denominators. With `P = ⟨q, ⟨a, z⟩⟩`,

* `A = Σ_{r ≤ z} [r ≥ 1] μ(r)² [gcd(r, q) = 1] z!/φ(r) = z! · G_q(z)`   (`SieveWeightOne.Asum`), and
* `π = Σ_{m < X} [m ≡ a (mod q)] [m prime]`                              (`SievePrimes.piB`),

it states, for `q ≥ 1`, `gcd(a, q) = 1` and `z ≥ 1`,

  `q · A · π ≤ X · z! + q · A · (z² + z)`,

that is `π ≤ X / (q G_q(z)) + z² + z` after division by `q A` (`A ≥ z! ≥ 1` by `SieveWeightOne.A_ge`).

Differences from the paper's statement:

* the count is over `0 ≤ m < X` rather than `1 ≤ n ≤ x`;
* the second inequality of `eq:finite-sieve` (`eq:sieve-denominator`: `G_q(z) ≥ (φ(q)/q) H_z`) is derived in
  `DenominatorBound` (`sieve_denominator`, `finite_sieve_second`).

The proof follows the paper: the quadratic majorant summed over the progression (`SieveInequality.sieve_ineq`,
`SievePrimesSharp.prime_sieve_ineq_sharp`), the explicit weights with `λ_1 = 1` and `Q(λ) = 1/G`
(`SieveWeightOne`, `SieveWeightForm`), and the weight bound `Σ |λ_d| ≤ z` (`SieveWeightBound.weight_bound`),
assembled in `SieveFinite.finite_sieve_of_bound`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.FiniteSieve

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePrimes (piB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightOne (Asum)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveFinite (finite_sieve_of_bound)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightBound (weight_bound)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `thm:finite-sieve`, first inequality, for `q ≥ 1`: `q A π(X; q, a) ≤ X z! + q A (z² + z)` with
`A = z! G_q(z)`. -/
theorem finite_sieve {X P : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) (hz : Γ ⊢[PRAAx] le one (sndT (sndT P))) :
    Γ ⊢[PRAAx] le
      (fstT P * (Asum P *
        ap2 (sumF piB) X (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) P))))
      (X * fact (sndT (sndT P)) +
        fstT P * (Asum P * (sndT (sndT P) * sndT (sndT P) + sndT (sndT P)))) :=
  finite_sieve_of_bound hq ha hz (weight_bound X hq)

end LeanProofs.IPRA.AnalyticNumberTheory.FiniteSieve
