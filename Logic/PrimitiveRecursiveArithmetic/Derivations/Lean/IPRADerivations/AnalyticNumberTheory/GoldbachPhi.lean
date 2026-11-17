import IPRADerivations.AnalyticNumberTheory.Totient

/-!
# Goldbach's statement gives totient sums

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Proposition
`prop:goldbach-phi`: if every even integer at least four is a sum of two primes, then every `2m`
(`m ≥ 1`) is `φ(p) + φ(q)` for primes `p, q`.

The implication is constructive and witness-producing: a Goldbach decomposition
`p + q = 2m + 2` of `2m + 2` gives the totient witnesses `p, q` directly, since `φ(p) = p − 1`
(`phi_prime`, the case `k = 0` of `Totient.totient_prime_power_at`). It does not prove Goldbach.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.GoldbachPhi

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody totient_prime_power_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `φ(p) + 1 = p` for a prime `p`. -/
theorem phi_prime {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) : Γ ⊢[PRAAx] phi p + one ≐ p := by
  have h := totient_prime_power_at (k := zero) hp
  have e : Γ ⊢[PRAAx] pw p (succ zero) ≐ p := pw_one p
  exact (congrAdd (congrAp2 (sumF totBody) e e).eqSymm (pw_zero p).eqSymm).eqTrans (h.eqTrans e)

/-- `prop:goldbach-phi`: primes `p, q` with `p + q = 2m + 2` satisfy `φ(p) + φ(q) = 2m`. -/
theorem goldbach_phi {p q m : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hq : Γ ⊢[PRAAx] prime q)
    (h : Γ ⊢[PRAAx] p + q ≐ succ (succ (two * m))) : Γ ⊢[PRAAx] phi p + phi q ≐ two * m := by
  have a := natEq (phi_prime hp); have b := natEq (phi_prime hq); have c := natEq h
  apply deriveNat; ipra_simps
  linear_combination a + b + c

end LeanProofs.IPRA.AnalyticNumberTheory.GoldbachPhi
