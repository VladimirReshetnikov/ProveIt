import IPRADerivations.AnalyticNumberTheory.EulerDomination
import IPRADerivations.AnalyticNumberTheory.SieveRecursion

/-!
# The prime step for truncated smooth harmonic sums

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, the proof of the
denominator bound `eq:sieve-denominator` (through `eq:radical-bound`): the smooth part of the harmonic sum is
compared prime by prime.

With `Sm(a; N) = ∑_{m < N} [m ≥ 1][m ∣ a^L] ⌊F/m⌋` (`EulerDomination.Sm`), `EulerDomination.prime_step` is
`p · Sm(ap; N) ≤ p · Sm(a; N) + Sm(ap; N)`. Here the multiples `m = k p < N` are reindexed exactly
(`SumReindex.reindex_eq`), which shortens the range of the last sum:

    p · Sm(ap; N) ≤ p · Sm(a; N) + Sm(ap; ⌈N/p⌉)                                 (**`trunc_step`**),

and for `N = t + 1` the new range is `⌊t/p⌋ + 1` (`trunc_step_succ`). This is the inequality
`S_{ap}(t) ≤ S_a(t) + p^{−1} S_{ap}(⌊t/p⌋)` that the comparison with the truncated sum `∑_{d ≤ t} μ(d)²/φ(d)`
iterates.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SmoothTruncated

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (riB reindex_eq cM)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerDomination (Sm gB par zz bT sAP sA sR leA leB)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveRecursion (cM_succ)
open LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz (add_le_add)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- **The truncated prime step**: `p · Sm(ap; N) ≤ p · Sm(a; N) + Sm(ap; ⌈N/p⌉)`. -/
theorem trunc_step {p a L F : PTm n} (hp : Γ ⊢[PRAAx] prime p) (N : PTm n) :
    Γ ⊢[PRAAx] le (p * Sm (a * p) L F N) (p * Sm a L F N + Sm (a * p) L F (cM N p)) := by
  have h1 : Γ ⊢[PRAAx] le (Sm (a * p) L F N) (Sm a L F N + ap2 (sumF bT) N (zz p a L F)) :=
    le_congr (sAP hp N) (congrAdd (sA hp N) (.eqRefl _)) (leA hp N)
  have h2 : Γ ⊢[PRAAx] le (p * ap2 (sumF bT) N (zz p a L F)) (Sm (a * p) L F (cM N p)) :=
    le_congr (.eqRefl _) ((sR hp N).eqTrans (reindex_eq gB N (prime_eq_succ_pred hp))) (leB hp N)
  refine le_trans (le_mul_mono (le_refl p) h1)
    (le_congr ?_ (.eqRefl _) (add_le_add (le_refl (p * Sm a L F N)) h2))
  apply deriveNat; ipra_simps; ring

/-- At `N = t + 1`: `p · Sm(ap; t + 1) ≤ p · Sm(a; t + 1) + Sm(ap; ⌊t/p⌋ + 1)`. -/
theorem trunc_step_succ {p a L F : PTm n} (hp : Γ ⊢[PRAAx] prime p) (t : PTm n) :
    Γ ⊢[PRAAx] le (p * Sm (a * p) L F (succ t)) (p * Sm a L F (succ t) + Sm (a * p) L F (succ (quo t p))) :=
  le_congr (.eqRefl _)
    (congrAdd (.eqRefl _) (congrAp2 (sumF gB) (cM_succ (prime_eq_succ_pred hp)) (.eqRefl _)))
    (trunc_step hp (succ t))

end LeanProofs.IPRA.AnalyticNumberTheory.SmoothTruncated
