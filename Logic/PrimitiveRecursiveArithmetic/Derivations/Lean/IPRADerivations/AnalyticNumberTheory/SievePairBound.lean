import IPRADerivations.AnalyticNumberTheory.SievePairCount

/-!
# The pair count bounds with their side conditions as indicator factors

Packet: `analytic-number-theory/prime_distribution_ipra`, `paper/sections/05_sieve.tex`, proof of `thm:finite-sieve`:
the estimate `eq:crt-count` is applied to every pair `(d, e)` of indices of the sieve weights and then summed.

`SievePairCount.pair_le` and `pair_ge` hold for `d, e ≥ 1` coprime to `q ≥ 1` and `gcd(a, q) = 1`. To sum them over
all pairs below a bound (where a monotonicity lemma for double sums needs the inequality at every index), the side
conditions are carried by the 0/1 factor

  `ind d e q a = [2 ≤ q] [gcd(a, q) = 1] [d ≥ 1] [gcd(d, q) = 1] [e ≥ 1] [gcd(e, q) = 1]`:

* `eqb_factor`, `sg_factor`, `one_factor`: an inequality `R A ≤ R B` under an extra hypothesis gives the inequality
  with the indicator of that hypothesis as a further factor, with no hypothesis;
* `pw_upper`: `ind · W · (q d e · K) ≤ ind · W · (gcd(d, e) X + q d e)` for every weight `W` and all terms;
* `pw_lower`: `ind · W · (gcd(d, e) X) ≤ ind · W · (q d e · K + q d e)`,

with `K = SieveCount.cnt X q (lc d e) a`. Where an indicator vanishes both sides are zero.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.SievePairBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (sg_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.SieveCount (cnt)
open LeanProofs.IPRA.AnalyticNumberTheory.SievePairCount (lc pair_le pair_ge)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Indicator factors -/

/-- An inequality under the hypothesis `s = t` holds outright with the factor `[s = t]`. -/
theorem eqb_factor {s t R A B : PTm n} (h : ((s ≐ t) :: Γ) ⊢[PRAAx] le (R * A) (R * B)) :
    Γ ⊢[PRAAx] le ((eqb s t * R) * A) ((eqb s t * R) * B) := by
  refine .orE (eq_or_ne s t) ?_ ?_
  · have e1 : ((s ≐ t) :: Γ) ⊢[PRAAx] eqb s t ≐ one := eqb_of_eq Prf.hyp0
    have c : ∀ Y : PTm n, ((s ≐ t) :: Γ) ⊢[PRAAx] R * Y ≐ (eqb s t * R) * Y := fun Y =>
      congrMul ((one_mul R).eqSymm.eqTrans (congrMul e1.eqSymm (.eqRefl _))) (.eqRefl _)
    exact le_congr (c A) (c B) h
  · have e0 : (neg (s ≐ t) :: Γ) ⊢[PRAAx] eqb s t ≐ zero := eqb_of_ne Prf.hyp0
    have z : ∀ Y : PTm n, (neg (s ≐ t) :: Γ) ⊢[PRAAx] (eqb s t * R) * Y ≐ zero := fun Y =>
      zero_mul_l (zero_mul_l e0 R) Y
    exact le_congr (z A).eqSymm (z B).eqSymm (le_refl zero)

/-- An inequality under the hypothesis `d ≥ 1` holds outright with the factor `[d ≥ 1]`. -/
theorem sg_factor {d R A B : PTm n} (h : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] le (R * A) (R * B)) :
    Γ ⊢[PRAAx] le ((sg d * R) * A) ((sg d * R) * B) := by
  refine .orE (zero_or_succ d) ?_ ?_
  · have e0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    have z : ∀ Y : PTm n, ((d ≐ zero) :: Γ) ⊢[PRAAx] (sg d * R) * Y ≐ zero := fun Y =>
      zero_mul_l (zero_mul_l e0 R) Y
    exact le_congr (z A).eqSymm (z B).eqSymm (le_refl zero)
  · have e1 : ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] sg d ≐ one := sg_pos Prf.hyp0
    have c : ∀ Y : PTm n, ((d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] R * Y ≐ (sg d * R) * Y := fun Y =>
      congrMul ((one_mul R).eqSymm.eqTrans (congrMul e1.eqSymm (.eqRefl _))) (.eqRefl _)
    exact le_congr (c A) (c B) h

theorem one_factor {A B : PTm n} (h : Γ ⊢[PRAAx] le A B) : Γ ⊢[PRAAx] le (one * A) (one * B) :=
  le_congr (one_mul A).eqSymm (one_mul B).eqSymm h

/-! ## The pair bounds -/

/-- `[2 ≤ q] [gcd(a, q) = 1] [d ≥ 1] [gcd(d, q) = 1] [e ≥ 1] [gcd(e, q) = 1]`. -/
abbrev ind (d e q a : PTm n) : PTm n :=
  eqb (monus one q) zero * (eqb (gcd a q) one * (sg d * (eqb (gcd d q) one * (sg e * (eqb (gcd e q) one * one)))))

/-- `ind · W · (q d e · K) ≤ ind · W · (gcd(d, e) X + q d e)`. -/
theorem pw_upper (W d e q a X : PTm n) :
    Γ ⊢[PRAAx] le (ind d e q a * (W * (q * (d * e) * cnt X q (lc d e) a)))
      (ind d e q a * (W * (gcd d e * X + q * (d * e)))) := by
  refine eqb_factor (eqb_factor (sg_factor (eqb_factor (sg_factor (eqb_factor (one_factor ?_))))))
  let C1 : List (Fm PTm n) := (monus one q ≐ zero) :: Γ
  let C2 : List (Fm PTm n) := (gcd a q ≐ one) :: C1
  let C3 : List (Fm PTm n) := (d ≐ succ (pred d)) :: C2
  let C4 : List (Fm PTm n) := (gcd d q ≐ one) :: C3
  let C5 : List (Fm PTm n) := (e ≐ succ (pred e)) :: C4
  let C6 : List (Fm PTm n) := (gcd e q ≐ one) :: C5
  have hq : C6 ⊢[PRAAx] le one q := (Prf.hyp0 : C1 ⊢[PRAAx] monus one q ≐ zero).wk.wk.wk.wk.wk
  have ha : C6 ⊢[PRAAx] gcd a q ≐ one := (Prf.hyp0 : C2 ⊢[PRAAx] gcd a q ≐ one).wk.wk.wk.wk
  have hd : C6 ⊢[PRAAx] d ≐ succ (pred d) := (Prf.hyp0 : C3 ⊢[PRAAx] d ≐ succ (pred d)).wk.wk.wk
  have hdq : C6 ⊢[PRAAx] gcd d q ≐ one := (Prf.hyp0 : C4 ⊢[PRAAx] gcd d q ≐ one).wk.wk
  have he : C6 ⊢[PRAAx] e ≐ succ (pred e) := (Prf.hyp0 : C5 ⊢[PRAAx] e ≐ succ (pred e)).wk
  have heq : C6 ⊢[PRAAx] gcd e q ≐ one := Prf.hyp0
  exact le_mul_mono (le_refl W) (pair_le X hd he hq hdq heq ha)

/-- `ind · W · (gcd(d, e) X) ≤ ind · W · (q d e · K + q d e)`. -/
theorem pw_lower (W d e q a X : PTm n) :
    Γ ⊢[PRAAx] le (ind d e q a * (W * (gcd d e * X)))
      (ind d e q a * (W * (q * (d * e) * cnt X q (lc d e) a + q * (d * e)))) := by
  refine eqb_factor (eqb_factor (sg_factor (eqb_factor (sg_factor (eqb_factor (one_factor ?_))))))
  let C1 : List (Fm PTm n) := (monus one q ≐ zero) :: Γ
  let C2 : List (Fm PTm n) := (gcd a q ≐ one) :: C1
  let C3 : List (Fm PTm n) := (d ≐ succ (pred d)) :: C2
  let C4 : List (Fm PTm n) := (gcd d q ≐ one) :: C3
  let C5 : List (Fm PTm n) := (e ≐ succ (pred e)) :: C4
  let C6 : List (Fm PTm n) := (gcd e q ≐ one) :: C5
  have hq : C6 ⊢[PRAAx] le one q := (Prf.hyp0 : C1 ⊢[PRAAx] monus one q ≐ zero).wk.wk.wk.wk.wk
  have ha : C6 ⊢[PRAAx] gcd a q ≐ one := (Prf.hyp0 : C2 ⊢[PRAAx] gcd a q ≐ one).wk.wk.wk.wk
  have hd : C6 ⊢[PRAAx] d ≐ succ (pred d) := (Prf.hyp0 : C3 ⊢[PRAAx] d ≐ succ (pred d)).wk.wk.wk
  have hdq : C6 ⊢[PRAAx] gcd d q ≐ one := (Prf.hyp0 : C4 ⊢[PRAAx] gcd d q ≐ one).wk.wk
  have he : C6 ⊢[PRAAx] e ≐ succ (pred e) := (Prf.hyp0 : C5 ⊢[PRAAx] e ≐ succ (pred e)).wk
  have heq : C6 ⊢[PRAAx] gcd e q ≐ one := Prf.hyp0
  exact le_mul_mono (le_refl W) (pair_ge X hd he hq hdq heq ha)

end LeanProofs.IPRA.AnalyticNumberTheory.SievePairBound
