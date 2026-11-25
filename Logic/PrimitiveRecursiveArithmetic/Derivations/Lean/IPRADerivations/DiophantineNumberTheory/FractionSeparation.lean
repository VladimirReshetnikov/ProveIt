import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.AnalyticNumberTheory.SquareReciprocal
import IPRADerivations.AnalyticNumberTheory.SumReindex
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# Separation of reduced fractions (`hurwitz_khinchin_ipra`, (K3), (K9))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "Distinct reduced fractions with
denominators at most `Q` are separated by at least `Q⁻²`: their difference has a nonzero integer numerator
over a denominator at most `Q²`."

* `frac_unique`: reduced fractions are equal only as pairs: `pq' = p'q`, `gcd(p, q) = gcd(p', q') = 1`,
  `q, q' ≥ 1` give `q = q'` and `p = p'` (`Coprime.gauss` in both directions);
* `floor_sep`: the separation, read through `x ↦ ⌊Q² x⌋`: `p/q < p'/q'` with `1 ≤ q, q' ≤ Q` gives
  `⌊Q² p/q⌋ < ⌊Q² p'/q'⌋` (since `Q²(p'q − pq') ≥ Q² ≥ qq'`);
* `floor_inj`: `⌊Q² p/q⌋ = ⌊Q² p'/q'⌋` for two reduced fractions with denominators in `[1, Q]` forces
  `q = q'` and `p = p'` — the injectivity that turns the separation into the count "an interval of length
  `λ` contains at most `λQ² + 1` of them" (`Foundations/InjectionCount`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.FractionSeparation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' gauss gcd_comm_one dvd_le')
open LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal (cancel_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `N A = N B`, `N ≥ 1` give `A = B`. -/
alias cancel_eq := Common.mul_cancel_eq

/-- Equal reduced fractions are equal pairs. -/
theorem frac_unique {p q p' q' : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hq' : Γ ⊢[PRAAx] q' ≐ succ (pred q'))
    (g1 : Γ ⊢[PRAAx] gcd p q ≐ one) (g2 : Γ ⊢[PRAAx] gcd p' q' ≐ one) (e : Γ ⊢[PRAAx] p * q' ≐ p' * q) :
    Γ ⊢[PRAAx] (q ≐ q') ⋏ (p ≐ p') := by
  have d1 : Γ ⊢[PRAAx] dvd q q' := by
    refine gauss hq (gcd_comm_one hq g1) (dvd_of_eq' (w := p') hq ?_)
    ipra_lc natEq e
  have d2 : Γ ⊢[PRAAx] dvd q' q := by
    refine gauss hq' (gcd_comm_one hq' g2) (dvd_of_eq' (w := p) hq' ?_)
    ipra_lc -natEq e
  have hqq : Γ ⊢[PRAAx] q ≐ q' := le_antisymm (dvd_le' hq d1 hq') (dvd_le' hq' d2 hq)
  refine .andI hqq ?_
  refine cancel_eq hq' ?_
  ipra_lc natEq e + 𝔞 p' * natEq hqq

/-- The separation: `p/q < p'/q'`, `1 ≤ q, q' ≤ Q` give `⌊Q²p/q⌋ < ⌊Q²p'/q'⌋`. -/
theorem floor_sep {p q p' q' Q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hq' : Γ ⊢[PRAAx] q' ≐ succ (pred q'))
    (hQq : Γ ⊢[PRAAx] le q Q) (hQq' : Γ ⊢[PRAAx] le q' Q) (hlt : Γ ⊢[PRAAx] lt (p * q') (p' * q)) :
    Γ ⊢[PRAAx] lt (quo (Q * Q * p) q) (quo (Q * Q * p') q') := by
  have dm := div_mod_at (Γ := Γ) (x := Q * Q * p) hq
  have e := natEq (Prf.andE₁ dm)
  refine le_quo_of_mul_le hq' (cancel_le hq ?_)
  ipra_le 𝔞 Q * 𝔞 Q * sl hlt + 𝔞 Q * sl hQq' + 𝔞 q' * sl hQq + 𝔞 q' * 𝔞 (rem (Q * Q * p) q) with 𝔞 q' * e

/-- Equal floors of reduced fractions with denominators in `[1, Q]` force equal pairs. -/
theorem floor_inj {p q p' q' Q : PTm n} (hq : Γ ⊢[PRAAx] q ≐ succ (pred q)) (hq' : Γ ⊢[PRAAx] q' ≐ succ (pred q'))
    (hQq : Γ ⊢[PRAAx] le q Q) (hQq' : Γ ⊢[PRAAx] le q' Q)
    (g1 : Γ ⊢[PRAAx] gcd p q ≐ one) (g2 : Γ ⊢[PRAAx] gcd p' q' ≐ one)
    (hf : Γ ⊢[PRAAx] quo (Q * Q * p) q ≐ quo (Q * Q * p') q') :
    Γ ⊢[PRAAx] (q ≐ q') ⋏ (p ≐ p') := by
  refine .orE (lt_or_le (p * q') (p' * q)) ?_ ?_
  · let Δ : List (Fm PTm n) := lt (p * q') (p' * q) :: Γ
    have s := floor_sep hq.wk hq'.wk hQq.wk hQq'.wk (Prf.hyp0 : Δ ⊢[PRAAx] lt (p * q') (p' * q))
    exact lt_irrefl _ _ (lt_congr hf.wk (.eqRefl _) s)
  · refine .orE (lt_or_le (p' * q) (p * q')) ?_ ?_
    · let Δ : List (Fm PTm n) := lt (p' * q) (p * q') :: le (p' * q) (p * q') :: Γ
      have s := floor_sep hq'.wk.wk hq.wk.wk hQq'.wk.wk hQq.wk.wk (Prf.hyp0 : Δ ⊢[PRAAx] lt (p' * q) (p * q'))
      exact lt_irrefl _ _ (lt_congr hf.wk.wk.eqSymm (.eqRefl _) s)
    · let Δ : List (Fm PTm n) := le (p * q') (p' * q) :: le (p' * q) (p * q') :: Γ
      have e : Δ ⊢[PRAAx] p * q' ≐ p' * q := le_antisymm Prf.hyp0 Prf.hyp1
      exact frac_unique hq.wk.wk hq'.wk.wk g1.wk.wk g2.wk.wk e

end LeanProofs.IPRA.DiophantineNumberTheory.FractionSeparation
