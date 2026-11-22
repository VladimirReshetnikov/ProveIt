import IPRADerivations.AnalyticNumberTheory.SieveInequality
import IPRADerivations.AnalyticNumberTheory.SievePrimes

/-!
# The sieve inequality for the primes of a progression, for arbitrary signed weights

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, proof of `thm:finite-sieve`,
before the weights are chosen: for every weight vector `λ`,

  `(λ_1)² (π(x; q, a) − z) ≤ (x/q) Σ_{d,e} λ_d λ_e / [d, e] + (Σ_d |λ_d|)²`.

`prime_sieve_ineq` is this statement for signed weights `λ = λ⁺ − λ⁻` with natural parts given by bodies `U^±`,
`q = fst P ≥ 2`, `gcd(a₀, q) = 1` and `Z ≥ 2`, cleared of signs and of the division by `q`. With `a = λ⁺_1`,
`b = λ⁻_1`, the prime count `π = Σ_{m<X} [m ≡ a₀ (mod q)] [m prime]` (`SievePrimes.piB`), the bilinear forms `G^{st}`
and the weight sums `L^±` of `SieveInequality.sieve_ineq`:

  `q (a² + b²) π + q · 2ab · Z + X (G⁺⁻ + G⁻⁺) ≤ X (G⁺⁺ + G⁻⁻) + q (L⁺ + L⁻)² + q (a² + b²) Z + q · 2ab · π`,

that is `q (a − b)² (π − Z) ≤ X (G⁺⁺ + G⁻⁻ − G⁺⁻ − G⁻⁺) + q (L⁺ + L⁻)²`.

It combines `SieveInequality.sieve_ineq` with `SievePrimes.primes_le` (`π ≤ S + Z`) and `(a − b)² ≥ 0`
(`SieveMajorant.amgm`): the product of the two slacks `(a² + b² − 2ab)(S + Z − π)` is nonnegative.

The weights are still arbitrary here; `thm:finite-sieve` is this inequality at the explicit weights
`eq:explicit-sieve-weights`, whose evaluation (`λ_1 = 1`, `Q = 1/G`, `|λ_d| ≤ 1`) is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SievePrimeInequality

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (lB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveClosedForms (gU sgV)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveMajorant (S0 amgm)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveInequality (sieve_ineq)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePrimes (piB primes_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveDiagonal (Lb)
open LeanProofs.IPRA.Probability.Independence (dsum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The combination over opaque terms: from the sieve inequality for `S`, `π ≤ S + Z` and `2ab ≤ a² + b²`. -/
theorem combine {q X Z S π a b Goff Gdiag L : PTm n}
    (h : Γ ⊢[PRAAx] le (q * ((a * a + b * b) * S) + X * Goff)
      (X * Gdiag + q * (L * L) + q * ((two * (a * b)) * S)))
    (hp : Γ ⊢[PRAAx] le π (S + Z)) (hab : Γ ⊢[PRAAx] le (two * (a * b)) (a * a + b * b)) :
    Γ ⊢[PRAAx] le (q * ((a * a + b * b) * π) + q * ((two * (a * b)) * Z) + X * Goff)
      (X * Gdiag + q * (L * L) + q * ((a * a + b * b) * Z) + q * ((two * (a * b)) * π)) := by
  ipra_le sl h + 𝔞 q * (sl hab * sl hp)

/-- The sieve inequality for the primes of a progression, for arbitrary signed weights. -/
theorem prime_sieve_ineq (UP UN : PTm 2) {X Z P : PTm n} (hq : Γ ⊢[PRAAx] le two (fstT P))
    (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) (hZ : Γ ⊢[PRAAx] lt one Z) :
    Γ ⊢[PRAAx] le
      (fstT P * ((inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) *
          ap2 (sumF piB) X (pairT Z (pairT Z P))) +
        fstT P * ((two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) * Z) +
        X * (dsum (Lb (sndB (gU UP)) (sndB (sgV UN))) Z Z (pairT X P) +
          dsum (Lb (sndB (gU UN)) (sndB (sgV UP))) Z Z (pairT X P)))
      (X * (dsum (Lb (sndB (gU UP)) (sndB (sgV UP))) Z Z (pairT X P) +
          dsum (Lb (sndB (gU UN)) (sndB (sgV UN))) Z Z (pairT X P)) +
        fstT P * ((ap2 (sumF (sndB (lB UP))) Z (pairT X P) + ap2 (sumF (sndB (lB UN))) Z (pairT X P)) *
          (ap2 (sumF (sndB (lB UP))) Z (pairT X P) + ap2 (sumF (sndB (lB UN))) Z (pairT X P))) +
        fstT P * ((inst2 (lB UP) one P * inst2 (lB UP) one P + inst2 (lB UN) one P * inst2 (lB UN) one P) * Z) +
        fstT P * ((two * (inst2 (lB UP) one P * inst2 (lB UN) one P)) *
          ap2 (sumF piB) X (pairT Z (pairT Z P)))) :=
  combine (sieve_ineq UP UN (X := X) hq ha hZ) (primes_le X Z P) (amgm _ _)

end LeanProofs.IPRA.AnalyticNumberTheory.SievePrimeInequality
