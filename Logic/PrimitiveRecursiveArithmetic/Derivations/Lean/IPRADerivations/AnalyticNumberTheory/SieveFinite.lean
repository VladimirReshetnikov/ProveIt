import IPRADerivations.AnalyticNumberTheory.SieveWeightOne
import IPRADerivations.AnalyticNumberTheory.SievePrimesSharp
import IPRADerivations.Core.Gcd
import IPRADerivations.Core.Header

/-!
# The finite sieve inequality from a bound on the sum of the weights

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, proof of `thm:finite-sieve`:

  "`S(x; q, a, z) ≤ (x/q) Q(λ) + Σ_{d,e ∈ D} |λ_d λ_e| ≤ x/(qG) + z²`.  Every prime counted by `π(x; q, a)` and
  larger than `z` survives this sieve. At most `z` other primes occur."

This module assembles that argument at the explicit weights `eq:explicit-sieve-weights`, with the bound on the sum of
the weights left as a hypothesis. For `P = ⟨q, ⟨a, z⟩⟩`, `q ≥ 1`, `gcd(a, q) = 1`, `z ≥ 1`,
`A = z! G_q(z)` (`SieveWeightOne.Asum`), the prime count `π = π(X; q, a)` over `m < X` (`SievePrimes.piB`) and the sum
`L = Σ_{d ≤ z} (λ⁺_d + λ⁻_d)` of the natural parts of the cleared weights:

  `L ≤ c · A`   implies   `q · A · π ≤ X · z! + q · A · (c² + z)`                  (`finite_sieve_of_bound`),

that is `π(X; q, a) ≤ X / (q G_q(z)) + c² + z` after division by `q A`. The first inequality of `eq:finite-sieve`
is the case `c = z` (`eq:weight-bound`: `Σ |λ_d| ≤ z` in the paper's normalization).

It combines `SievePrimesSharp.prime_sieve_ineq_sharp` at the weights `UPw`, `UNw` with `λ⁺_1 = A`, `λ⁻_1 = 0`
(`SieveWeightOne.lam_P`, `lam_N`) and the value `z! · A` of the quadratic form (`SieveWeightForm.form_value`,
`SieveWeightOne.ky_sum`), and cancels one factor `A`.

The hypothesis `L ≤ c · A` is not discharged here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SieveFinite

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveExpansion (lB)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePrimes (piB)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePrimesSharp (prime_sieve_ineq_sharp)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightForm (UPw UNw form_value)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveWeightOne (Asum lam_P lam_N ky_sum)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The assembly over opaque terms, before the cancellation of `A`: from the sieve inequality for the primes,
`a = A`, `b = 0`, `G_diag = G_off + B A` and `L ≤ c A`. -/
theorem finite_alg {q a b π Z X Go Gd L A B c : PTm n}
    (H : Γ ⊢[PRAAx] le (q * ((a * a + b * b) * π) + q * ((two * (a * b)) * Z) + X * Go)
      (X * Gd + q * (L * L) + q * ((a * a + b * b) * Z) + q * ((two * (a * b)) * π)))
    (ea : Γ ⊢[PRAAx] a ≐ A) (eb : Γ ⊢[PRAAx] b ≐ zero) (eg : Γ ⊢[PRAAx] Gd ≐ Go + B * A)
    (hL : Γ ⊢[PRAAx] le L (c * A)) :
    Γ ⊢[PRAAx] le (A * (q * (A * π))) (A * (X * B + q * (A * (c * c + Z)))) := by
  have x1 := natEq ea; have x2 := natEq eb; have x3 := natEq eg
  ipra_le sl H + 𝔞 q * (sl hL * (𝔞 c * 𝔞 A + 𝔞 L)) with
    -𝔞 X * x3 - 𝔞 q * (𝔞 Z - 𝔞 π) * (𝔞 A + 𝔞 a - 𝔞 b) * (x1 - x2)

/-- The conclusion when `A = 0`. -/
theorem zero_case {q A π X B c Z : PTm n} (h : Γ ⊢[PRAAx] A ≐ zero) :
    Γ ⊢[PRAAx] le (q * (A * π)) (X * B + q * (A * (c * c + Z))) := by
  have x := natEq h
  ipra_le 𝔞 X * 𝔞 B with 𝔞 q * (𝔞 c * 𝔞 c + 𝔞 Z - 𝔞 π) * x

/-- The finite sieve inequality at the explicit weights, from a bound `L ≤ c A` on the sum of the weights:
`q A π ≤ X z! + q A (c² + z)`. -/
theorem finite_sieve_of_bound {X P c : PTm n} (hq : Γ ⊢[PRAAx] le one (fstT P))
    (ha : Γ ⊢[PRAAx] gcd (fstT (sndT P)) (fstT P) ≐ one) (hz : Γ ⊢[PRAAx] le one (sndT (sndT P)))
    (hL : Γ ⊢[PRAAx] le
      (ap2 (sumF (sndB (lB UPw))) (succ (sndT (sndT P))) (pairT X P) +
        ap2 (sumF (sndB (lB UNw))) (succ (sndT (sndT P))) (pairT X P)) (c * Asum P)) :
    Γ ⊢[PRAAx] le
      (fstT P * (Asum P *
        ap2 (sumF piB) X (pairT (succ (sndT (sndT P))) (pairT (succ (sndT (sndT P))) P))))
      (X * fact (sndT (sndT P)) + fstT P * (Asum P * (c * c + sndT (sndT P)))) := by
  have hZ : Γ ⊢[PRAAx] lt one (succ (sndT (sndT P))) := (succ_monus_succ _ _).eqTrans hz
  have H := prime_sieve_ineq_sharp UPw UNw (X := X) hq ha hZ
  have eg := (form_value (X := X) hq).eqTrans (congrAdd (.eqRefl _) (ky_sum P))
  have M := finite_alg H (lam_P P) (lam_N P) eg hL
  have pz : Γ ⊢[PRAAx] X * fact (sndT (sndT P)) + fstT P * (Asum P * (c * c + pred (succ (sndT (sndT P))))) ≐
      X * fact (sndT (sndT P)) + fstT P * (Asum P * (c * c + sndT (sndT P))) :=
    congrAdd (.eqRefl _) (congrMul (.eqRefl _) (congrMul (.eqRefl _) (congrAdd (.eqRefl _) (pred_succ _))))
  refine le_congr (.eqRefl _) pz ?_
  refine .orE (zero_or_succ (Asum P)) ?_ ?_
  · exact zero_case Prf.hyp0
  · have hA : ((Asum P ≐ succ (pred (Asum P))) :: Γ) ⊢[PRAAx] Asum P ≐ succ (pred (Asum P)) := Prf.hyp0
    exact mul_le_cancel (le_congr (congrMul hA (.eqRefl _)) (congrMul hA (.eqRefl _)) M.wk)

end LeanProofs.IPRA.AnalyticNumberTheory.SieveFinite
