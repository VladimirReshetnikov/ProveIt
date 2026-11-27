import IPRADerivations.AnalyticNumberTheory.SmoothTruncated
import IPRADerivations.AnalyticNumberTheory.TotientSumStep

/-!
# The prime step of the comparison `H ≤ G`

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, the proof of the
denominator bound `eq:sieve-denominator` (`eq:radical-bound`: "Summing over all possible radicals yields
`H_q(z) ≤ G_q(z)`").

For a modulus `a`, `F = z!` and a range `t`:

    S_a(t) = ∑_{1 ≤ m ≤ t} [m ∣ a^L] ⌊z!/m⌋        (`EulerDomination.Sm a L (z!) (t + 1)`),
    G_a(t) = ∑_{1 ≤ d ≤ t} [d ∣ a] ⌊z!/φ(d)⌋       (`TotientSumStep.Gs a z (t + 1)`).

**`prime_step`**: for a prime `p` with `gcd(p, a) = 1` and `t ≤ z`, if `S_a(t) ≤ G_a(t)` and
`S_{ap}(⌊t/p⌋) ≤ G_{ap}(⌊t/p⌋)`, then `S_{ap}(t) ≤ G_{ap}(t)`. Indeed

    p S_{ap}(t) ≤ p S_a(t) + S_{ap}(⌊t/p⌋) ≤ p G_a(t) + G_a(⌊t/p⌋) + W(⌊t/p⌋)
               ≤ p G_a(t) + (p − 1) W(t) + W(t) = p G_{ap}(t),

by `SmoothTruncated.trunc_step_succ`, `TotientSumStep.G_split` (at `t` and at `⌊t/p⌋`),
`TotientSumStep.W_scale` and the monotonicity of `W`. The radical grouping of the packet becomes this
recursion on the range; the induction over the range and over the primes is carried out separately.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.DenominatorPrimeStep

open_ipra exports
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (Sm)
open LeanProofs.IPRA.AnalyticNumberTheory.SmoothTruncated (trunc_step_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.TotientSumStep (Gs Ws G_split W_scale Ws_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Cancel a factor `p ≥ 1` in an inequality. -/
theorem le_of_mul_le {p X Y : PTm n} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p))
    (h : Γ ⊢[PRAAx] le (p * X) (p * Y)) : Γ ⊢[PRAAx] le X Y := by
  refine .orE (lt_or_le Y X) ?_ Prf.hyp0
  have hlt : (lt Y X :: Γ) ⊢[PRAAx] le (succ Y) X := Prf.hyp0
  have h' := h.wk (ψ := lt Y X)
  have e := natEq (hp1.wk (ψ := lt Y X))
  have bad : (lt Y X :: Γ) ⊢[PRAAx] le one zero := by
    ipra_le 𝔞 p * sl hlt + sl h' + 𝔞 (pred p) with e
  exact lt_zero_absurd _ bad

/-- `⌊x/p⌋ ≤ x` for `p ≥ 1`. -/
theorem quo_le {p : PTm n} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) (x : PTm n) : Γ ⊢[PRAAx] le (quo x p) x :=
  Division.quo_le_self (x := x) hp1

/-- **The prime step**: `S_a(t) ≤ G_a(t)` and `S_{ap}(⌊t/p⌋) ≤ G_{ap}(⌊t/p⌋)` give `S_{ap}(t) ≤ G_{ap}(t)`,
for a prime `p` with `gcd(p, a) = 1` and `t ≤ z`. -/
theorem prime_step {p a L z t : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hc : Γ ⊢[PRAAx] gcd p a ≐ one)
    (htz : Γ ⊢[PRAAx] le t z)
    (h2 : Γ ⊢[PRAAx] le (Sm a L (fact z) (succ t)) (Gs a z (succ t)))
    (h3 : Γ ⊢[PRAAx] le (Sm (a * p) L (fact z) (succ (quo t p))) (Gs (a * p) z (succ (quo t p)))) :
    Γ ⊢[PRAAx] le (Sm (a * p) L (fact z) (succ t)) (Gs (a * p) z (succ t)) := by
  have hp1 := p_pos (prime_two hp)
  have h1 := trunc_step_succ (a := a) (L := L) (F := fact z) hp t
  have e4 := natEq (G_split hp hc z t)
  have e5 := natEq (G_split hp hc z (quo t p))
  have e6 := natEq (W_scale hp hc htz)
  have e1 := natEq hp1
  have h7 : Γ ⊢[PRAAx] le (Ws p a z (quo t p)) (Ws p a z t) := Ws_mono (quo_le hp1 (quo t p))
  refine le_of_mul_le hp1 ?_
  ipra_le sl h1 + 𝔞 p * sl h2 + sl h3 + sl h7 with
    𝔞 p * e4 - e5 - e6 + 𝔞 (Ws p a z t) * e1

end LeanProofs.IPRA.AnalyticNumberTheory.DenominatorPrimeStep
