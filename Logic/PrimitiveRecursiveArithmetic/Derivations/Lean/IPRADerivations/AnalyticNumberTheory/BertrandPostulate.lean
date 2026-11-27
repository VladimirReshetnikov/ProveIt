import IPRADerivations.AnalyticNumberTheory.BertrandFactor
import IPRADerivations.AnalyticNumberTheory.BertrandGrowth
import IPRADerivations.AnalyticNumberTheory.BertrandCertificate

/-!
# Bertrand's postulate as a closed sentence of iPRA

Packet: `analytic-number-theory/bertrand_ipra`, `bertrand.tex`: for every `n ≥ 4` the bounded search returns a
prime `p` with `n < p < 2n − 2`.

`BertrandSearch.bertrand_of_failure_refuted` reduced the closed sentence

    ∀ x. 4 ≤ x → x < p(x) ∧ prime p(x) ∧ p(x) < 2x − 2          (`BertrandSearch.sentence`)

to the open sequent `found x = 0, 4 ≤ x ⊢ ⊥` (`BertrandSearch.failureObligation`). This module derives it:

* `large`: for `x ≥ 883`. The lower bound `4^x ≤ (2x + 1) C(2x, x)` (`CentralBinomial.central_lower`) and the
  estimate (8) after a failed search (`BertrandFactor.gap`) give `4^x ≤ u^{s+2} 4^m` with `u = 2x + 1`,
  `s = ⌊√(2x)⌋`, `m = ⌊2x/3⌋` (`assemble`); `x ≥ 883` gives `s ≥ 38`, and `BertrandGrowth.growth_absurd`
  refutes the inequality;
* `BertrandCertificate.small`: for `4 ≤ x ≤ 882`, by the table of ten primes;
* `failure_refuted : failureObligation`, and **`bertrand`**: the closed sentence.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.BertrandPostulate

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.BertrandSearch (found failureObligation sentence
  bertrand_of_failure_refuted)
open LeanProofs.IPRA.AnalyticNumberTheory.BertrandFactor (sq md gap)
open LeanProofs.IPRA.AnalyticNumberTheory.BertrandGrowth (growth_absurd)
open LeanProofs.IPRA.AnalyticNumberTheory.BertrandCertificate (small)
open LeanProofs.IPRA.Combinatorics.CentralBinomial (central_lower)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm)
open LeanProofs.IPRA.DiophantineNumberTheory.ResidueFacts (pw_two)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `y² ≤ N` gives `y ≤ ⌊√N⌋`. -/
theorem le_isqrt {y N : PTm n} (h : Γ ⊢[PRAAx] le (y * y) N) : Γ ⊢[PRAAx] le y (isqrt N) :=
  Isqrt.le_of_sq_le h

/-- `u · ((A W) u) = u^{s+2} W` when `A = u^s`. -/
theorem asm_alg {u A W PW B2 : PTm n} (p1 : Γ ⊢[PRAAx] PW ≐ A * B2) (p2 : Γ ⊢[PRAAx] B2 ≐ u * u) :
    Γ ⊢[PRAAx] u * ((A * W) * u) ≐ PW * W := by
  ipra_lc (-𝔞 W) * natEq p1 - 𝔞 W * 𝔞 A * natEq p2

/-- `4^x ≤ (2x + 1)^{s+2} 4^m` after a failed search. -/
theorem assemble {x : PTm n} (fail : Γ ⊢[PRAAx] found x ≐ zero) (h4 : Γ ⊢[PRAAx] le (two + two) x) :
    Γ ⊢[PRAAx] le (pw two (two * x)) (pw (succ (two * x)) (sq x + two) * pw two (two * md x)) := by
  have g := gap fail h4
  have cl := central_lower (Γ := Γ) x
  have a1 : Γ ⊢[PRAAx] le (two * x) (succ (two * x)) := le_succ_self _
  have a2 := pw_le_pw (sq x) a1
  have g2 := le_trans g (le_mul_mono (le_mul_mono a2 (le_refl (pw two (two * md x)))) a1)
  have g3 := le_mul_mono (le_refl (succ (two * x))) g2
  have eu := asm_alg (Γ := Γ) (W := pw two (two * md x)) (pw_add (succ (two * x)) (sq x) two)
    (pw_two (succ (two * x)))
  exact le_congr (.eqRefl _) eu (le_trans cl g3)

/-- The failure of the search is contradictory for `x ≥ 883`. -/
theorem large {x : PTm n} (fail : Γ ⊢[PRAAx] found x ≐ zero) (h4 : Γ ⊢[PRAAx] le (two + two) x)
    (hbig : Γ ⊢[PRAAx] le (num 883) x) : Γ ⊢[PRAAx] Fm.bot := by
  have G0 := assemble fail h4
  have tp : Γ ⊢[PRAAx] (succ two : PTm n) ≐ succ (pred (succ two)) := congrSucc (pred_succ _).eqSymm
  have hm : Γ ⊢[PRAAx] le (succ two * md x) (two * x) :=
    le_of_eq_add (d := rem (two * x) (succ two)) (Prf.andE₁ (dm tp (two * x)))
  have hs1 := isqrt_le (Γ := Γ) (two * x)
  have hs2 := lt_isqrt_succ_sq (Γ := Γ) (two * x)
  have h38 : Γ ⊢[PRAAx] le (num 38 * num 38) (two * x) := by
    ipra_le 2 * sl hbig + 322 using (push_cast; ring)
  have s38 := le_isqrt h38
  have es : Γ ⊢[PRAAx] sq x ≐ monus (sq x) (num 38) + num 38 := (eq_add_of_le s38).eqTrans (add_comm _ _)
  exact growth_absurd (d := monus (sq x) (num 38)) G0 hm hs1 hs2 es

/-- The failure obligation of `BertrandSearch`: `found x = 0, 4 ≤ x ⊢ ⊥`. -/
theorem failure_refuted : failureObligation := by
  have fail : ([found (var 0) ≐ zero, le (two + two) (var 0)] : List (Fm PTm 1)) ⊢[PRAAx]
      found (var 0) ≐ zero := Prf.hyp0
  have h4 : ([found (var 0) ≐ zero, le (two + two) (var 0)] : List (Fm PTm 1)) ⊢[PRAAx]
      le (two + two) (var 0) := Prf.hyp1
  refine .orE (lt_or_le (num 882) (var 0)) ?_ ?_
  · exact large fail.wk h4.wk Prf.hyp0
  · have e4 : (le (var 0) (num 882) :: [found (var 0) ≐ zero, le (two + two) (var 0)]) ⊢[PRAAx]
        (two + two : PTm 1) ≐ num 4 := by apply deriveNat; ipra_simps; push_cast; ring
    exact small fail.wk (le_congr e4 (.eqRefl _) h4.wk) Prf.hyp0

/-- **Bertrand's postulate** as a closed sentence of iPRA: for every `x ≥ 4` the least prime above `x`
found by the bounded search satisfies `x < p < 2x − 2`. -/
theorem bertrand : ([] : List (Fm PTm 0)) ⊢[PRAAx] sentence := bertrand_of_failure_refuted failure_refuted

end LeanProofs.IPRA.AnalyticNumberTheory.BertrandPostulate
