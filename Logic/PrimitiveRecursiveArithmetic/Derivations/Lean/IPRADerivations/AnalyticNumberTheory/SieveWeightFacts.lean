import IPRADerivations.AnalyticNumberTheory.SieveRough
import IPRADerivations.AnalyticNumberTheory.TotientCorollaries
import IPRADerivations.AnalyticNumberTheory.EulerProduct
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.AnalyticNumberTheory.Euler
import IPRADerivations.AnalyticNumberTheory.CoprimeModulus

/-!
# Two facts behind the explicit sieve weights

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, `eq:explicit-sieve-weights`:
`y_r = μ(r) / (φ(r) G)` and `λ_d = d Σ_{r ∈ D, d ∣ r} μ(r/d) μ(r) / (φ(r) G)`, where `D` is the set of squarefree
`d ≤ z` coprime to `q` ("The set `D` is closed under taking positive divisors").

To state these weights with natural numbers, the common denominator of the `1/φ(r)`, `r ≤ z`, is taken to be `z!`.

* `phi_le`: `φ(r) ≤ r` for `r ≥ 1`;
* `phi_quo`: `φ(r) · (z! / φ(r)) = z!` for `1 ≤ r ≤ z`, since every positive number up to `z` divides `z!`
  (`Primes.dvd_fact`);
* `cop_dvd`: a divisor `d ≥ 1` of `r` is coprime to `q` when `r` is (for `q ≥ 1`);
* `g_supp`: `[gcd(d, q) = 1] · ([d ∣ r] [gcd(r, q) = 1]) = [d ∣ r] [gcd(r, q) = 1]`: the closure of the coprimality
  condition under divisors, as an identity of indicators.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightFacts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientCorollaries (phi_lt)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (phi_one)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (dvd_fact)
open LeanProofs.IPRA.AnalyticNumberTheory.CoprimeModulus (cop_of_mul pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveRough (two_le_of)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd')
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The totient divides the factorial -/

/-- `φ(r) ≤ r` for `r ≥ 1`. -/
theorem phi_le {r : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) : Γ ⊢[PRAAx] le (phi r) r := by
  refine .orE (eq_or_ne r one) ?_ ?_
  · have h1 : ((r ≐ one) :: Γ) ⊢[PRAAx] r ≐ one := Prf.hyp0
    have e : ((r ≐ one) :: Γ) ⊢[PRAAx] phi r ≐ r :=
      (congrAp2 (sumF totBody) h1 h1).eqTrans (phi_one.eqTrans h1.eqSymm)
    exact le_congr e.eqSymm (.eqRefl _) (le_refl r)
  · exact le_of_lt (phi_lt (two_le_of (hr.wk (ψ := neg (r ≐ one))) Prf.hyp0))

/-- `φ(r) · (z! / φ(r)) = z!` for `1 ≤ r ≤ z`. -/
theorem phi_quo {r z : PTm n} (hr : Γ ⊢[PRAAx] r ≐ succ (pred r)) (hrz : Γ ⊢[PRAAx] le r z) :
    Γ ⊢[PRAAx] fact z ≐ phi r * quo (fact z) (phi r) := by
  have hp : Γ ⊢[PRAAx] phi r ≐ succ (pred (phi r)) := Order.phi_pos hr
  have hle : Γ ⊢[PRAAx] le (succ (pred (phi r))) z := le_congr hp (.eqRefl _) (le_trans (phi_le hr) hrz)
  have hd : Γ ⊢[PRAAx] dvd (phi r) (fact z) := dvd_congr_left hp.eqSymm (dvd_fact hle)
  exact eq_of_dvd' hp hd

/-! ## Coprimality passes to divisors -/

/-- A divisor `d ≥ 1` of `r` is coprime to `q ≥ 1` when `r` is. -/
theorem cop_dvd {d r q : PTm n} (hq : Γ ⊢[PRAAx] le one q) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (hdr : Γ ⊢[PRAAx] dvd d r) (hr : Γ ⊢[PRAAx] gcd r q ≐ one) : Γ ⊢[PRAAx] gcd d q ≐ one := by
  have e : Γ ⊢[PRAAx] r ≐ quo r d * d := (eq_of_dvd' hd hdr).eqTrans (mul_comm _ _)
  exact cop_of_mul (pos_of_one_le hq) ((congrGcd e.eqSymm (.eqRefl _)).eqTrans hr)

/-- `[gcd(d, q) = 1] · ([d ∣ r] [gcd(r, q) = 1]) = [d ∣ r] [gcd(r, q) = 1]` for `d ≥ 1`, `q ≥ 1`. -/
theorem g_supp {d r q : PTm n} (hq : Γ ⊢[PRAAx] le one q) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    Γ ⊢[PRAAx] eqb (gcd d q) one * (eqb (rem r d) zero * eqb (gcd r q) one) ≐
      eqb (rem r d) zero * eqb (gcd r q) one := by
  refine .orE (eq_or_ne (rem r d) zero) ?_ ?_
  · refine .orE (eq_or_ne (gcd r q) one) ?_ ?_
    · let C : List (Fm PTm n) := (gcd r q ≐ one) :: (rem r d ≐ zero) :: Γ
      have hdr : C ⊢[PRAAx] dvd d r := Prf.hyp1
      have hg : C ⊢[PRAAx] gcd d q ≐ one := cop_dvd hq.wk.wk hd.wk.wk hdr Prf.hyp0
      exact (congrMul (eqb_of_eq hg) (.eqRefl _)).eqTrans (one_mul _)
    · have z : (neg (gcd r q ≐ one) :: (rem r d ≐ zero) :: Γ) ⊢[PRAAx]
          eqb (rem r d) zero * eqb (gcd r q) one ≐ zero :=
        (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (mul_zero _)
      exact ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqTrans z.eqSymm
  · have z : (neg (rem r d ≐ zero) :: Γ) ⊢[PRAAx] eqb (rem r d) zero * eqb (gcd r q) one ≐ zero :=
      zero_mul_l (eqb_of_ne Prf.hyp0) _
    exact ((congrMul (.eqRefl _) z).eqTrans (mul_zero _)).eqTrans z.eqSymm

end LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightFacts
