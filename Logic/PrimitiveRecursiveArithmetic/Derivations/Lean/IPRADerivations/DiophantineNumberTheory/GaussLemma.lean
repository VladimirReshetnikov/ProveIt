import IPRADerivations.DiophantineNumberTheory.GaussProduct
import IPRADerivations.DiophantineNumberTheory.WilsonProduct
import IPRADerivations.DiophantineNumberTheory.ResidueFacts
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.CommonLemmas

/-!
# Euler's criterion and Gauss's lemma

Packet: `diophantine-number-theory/quadratic_reciprocity_ipra`, `quadratic_reciprocity.tex`, `eq:euler` and
`eq:gauss`:

  "`a^h ≡ (−1)^{sgnbit_p(a)} (mod p)`" and "`sgnbit_p(a) = N_p(a) mod 2`".

For an odd prime `p = 2h + 1` and `gcd(a, p) = 1`, with the residue bit
`rb p a = exB sqB p ⟨p, a⟩ = [∃ x < p, x² ≡ a (mod p)]` of `Foundations/BoundedReflection`:

* `euler_nr`: `rb = 0` gives `a^h ≡ p − 1 (mod p)` (`PairProduct.euler_nonresidue` and
  `WilsonProduct.wilson`);
* `euler_res`: `rb = 1` gives `a^h ≡ 1 (mod p)` (the witness of the bit is a unit `x` with `x² ≡ a`, and
  `ResidueFacts.residue_pow`);
* `gauss_lemma`: `par N_p(a) = 1 − rb`, for `a ≥ 1`: Gauss's count `N_p(a) = Σ_{i ≤ h} [a i mod p > h]` is odd
  exactly when `a` is a nonresidue. It combines `GaussProduct.gauss_unit`, `(p − 1)^N a^h ≡ 1`, with the two
  cases and `ResidueFacts.neg_pow`; the two signs `1` and `p − 1` are different because `p ≥ 3`.

The identification of `1 − rb` with the sign bit `signBit p a` of `QuadraticReciprocityGoal`, and with it
Eisenstein's lemma and the reciprocity law, are not derived in this module.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.GaussLemma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ConvolutionAssoc (rem_small)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_rem_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidue (cop_of_sol)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_comm_one)
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (rem_mul_congr2)
open LeanProofs.IPRA.DiophantineNumberTheory.EisensteinParity (eB)
open LeanProofs.IPRA.DiophantineNumberTheory.GaussProduct (gauss_unit)
open LeanProofs.IPRA.DiophantineNumberTheory.PairProduct (sqB sq_at euler_nonresidue)
open LeanProofs.IPRA.DiophantineNumberTheory.WilsonProduct (wilson pred_lt)
open LeanProofs.IPRA.DiophantineNumberTheory.ResidueFacts (neg_pow residue_pow)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_cases ex_elim eqb_cases eq_of_eqb one_ne_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The residue bit `[∃ x < p, x² ≡ a (mod p)]`. -/
abbrev rb (p a : PTm n) : PTm n := exB sqB p (pairT p a)

/-! ## Euler's criterion -/

/-- A nonresidue has `a^h ≡ p − 1 (mod p)`. -/
theorem euler_nr {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (hc : Γ ⊢[PRAAx] gcd p a ≐ one) (ha : Γ ⊢[PRAAx] gcd a p ≐ one) (hnr : Γ ⊢[PRAAx] rb p a ≐ zero) :
    Γ ⊢[PRAAx] rem (pw a (half p)) p ≐ pred p :=
  (euler_nonresidue hp hodd hc ha hnr).eqSymm.eqTrans (wilson hp hodd)

/-- A residue has `a^h ≡ 1 (mod p)`. -/
theorem euler_res {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (ha : Γ ⊢[PRAAx] gcd a p ≐ one) (hr : Γ ⊢[PRAAx] rb p a ≐ one) :
    Γ ⊢[PRAAx] rem (pw a (half p)) p ≐ rem one p := by
  have hq := prime_two hp
  have hp1 := p_pos hq
  have ee := ex_elim sqB hr
  have ne : Γ ⊢[PRAAx] neg (eqb (rem (wit sqB p (pairT p a) * wit sqB p (pairT p a)) p) (rem a p) ≐ zero) :=
    .impI (.impE (Prf.andE₂ ee).wk ((sq_at _ _ _).eqTrans Prf.hyp0))
  have sq : Γ ⊢[PRAAx] rem (wit sqB p (pairT p a) * wit sqB p (pairT p a)) p ≐ rem a p := by
    refine .orE (eqb_cases (rem (wit sqB p (pairT p a) * wit sqB p (pairT p a)) p) (rem a p)) ?_ ?_
    · exact .botE _ (.impE ne.wk Prf.hyp0)
    · exact eq_of_eqb Prf.hyp0
  have hu : Γ ⊢[PRAAx] gcd (wit sqB p (pairT p a)) p ≐ one := cop_of_sol hq ha sq
  exact (pw_rem_congr hp1 sq.eqSymm (half p)).eqTrans (residue_pow hp hodd hu)

/-! ## Gauss's lemma -/

/-- `p − 1 ≠ 1` for an odd `p`. -/
theorem pred_ne_one {p : PTm n} (hp1 : Γ ⊢[PRAAx] p ≐ succ (pred p)) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (φ : Fm PTm n) (h : Γ ⊢[PRAAx] pred p ≐ one) : Γ ⊢[PRAAx] φ := by
  have e2 : Γ ⊢[PRAAx] p ≐ two := hp1.eqTrans (congrSucc h)
  have pe : Γ ⊢[PRAAx] par p ≐ zero :=
    (congrAp1 parF e2).eqTrans ((par_succ _).eqTrans ((congrMonus (.eqRefl _)
      ((par_succ _).eqTrans ((congrMonus (.eqRefl _) par_zero).eqTrans (monus_zero _)))).eqTrans (monus_self _)))
  exact one_ne_zero φ (hodd.eqSymm.eqTrans pe)

alias mul_one_r := Common.mul_one_right'

/-- `par N = 1` from `par (N + 1) = 0`. -/
theorem par_of_succ {N : PTm n} (h : Γ ⊢[PRAAx] par (succ N) ≐ zero) : Γ ⊢[PRAAx] par N ≐ one := by
  have m : Γ ⊢[PRAAx] monus one (par N) ≐ zero := (par_succ N).eqSymm.eqTrans h
  refine .orE (par_cases N) ?_ Prf.hyp0
  exact one_ne_zero _ ((monus_zero _).eqSymm.eqTrans
    ((congrMonus (.eqRefl _) (Prf.hyp0 : ((par N ≐ zero) :: Γ) ⊢[PRAAx] par N ≐ zero)).eqSymm.eqTrans m.wk))

/-- Gauss's lemma: `par N_p(a) = 1 − [a is a square mod p]` for an odd prime `p`, `a ≥ 1`, `gcd(p, a) = 1`. -/
theorem gauss_lemma {p a : PTm n} (hp : Γ ⊢[PRAAx] prime p) (hodd : Γ ⊢[PRAAx] par p ≐ one)
    (ha1 : Γ ⊢[PRAAx] a ≐ succ (pred a)) (hc : Γ ⊢[PRAAx] gcd p a ≐ one) :
    Γ ⊢[PRAAx] par (ap2 (sumF eB) (half p) (pairT p a)) ≐ monus one (rb p a) := by
  have hq := prime_two hp
  have hp1 := p_pos hq
  have ha : Γ ⊢[PRAAx] gcd a p ≐ one := gcd_comm_one ha1 hc
  have gu := gauss_unit hp hodd ha1 hc
  have r1 : Γ ⊢[PRAAx] rem one p ≐ one := rem_small hq
  have rp : Γ ⊢[PRAAx] rem (pred p) p ≐ pred p := rem_small (pred_lt hp1)
  refine .orE (ex_cases sqB p (pairT p a)) ?_ ?_
  · -- nonresidue: `(p − 1)^{N + 1} ≡ 1`, so `N + 1` is even
    let C : List (Fm PTm n) := (rb p a ≐ zero) :: Γ
    have hnr : C ⊢[PRAAx] rb p a ≐ zero := Prf.hyp0
    have en := euler_nr hp.wk hodd.wk hc.wk ha.wk hnr
    have k1 : C ⊢[PRAAx] rem (pw (pred p) (succ (ap2 (sumF eB) (half p) (pairT p a)))) p ≐ rem one p :=
      (congrAp2 remF (pw_succ _ _) (.eqRefl _)).eqTrans
        ((rem_mul_congr2 hp1.wk (.eqRefl (rem (pw (pred p) (ap2 (sumF eB) (half p) (pairT p a))) p))
          (rp.wk.eqTrans en.eqSymm)).eqTrans gu.wk)
    have goal1 : C ⊢[PRAAx] par (ap2 (sumF eB) (half p) (pairT p a)) ≐ one := by
      refine .orE (neg_pow hq.wk (succ (ap2 (sumF eB) (half p) (pairT p a)))) ?_ ?_
      · exact par_of_succ (Prf.andE₁ Prf.hyp0)
      · exact pred_ne_one hp1.wk.wk hodd.wk.wk _
          (rp.wk.wk.eqSymm.eqTrans ((Prf.andE₂ Prf.hyp0).eqSymm.eqTrans (k1.wk.eqTrans r1.wk.wk)))
    exact goal1.eqTrans ((congrMonus (.eqRefl _) hnr).eqTrans (monus_zero _)).eqSymm
  · -- residue: `(p − 1)^N ≡ 1`, so `N` is even
    let C : List (Fm PTm n) := (rb p a ≐ one) :: Γ
    have hr : C ⊢[PRAAx] rb p a ≐ one := Prf.hyp0
    have er := euler_res hp.wk hodd.wk ha.wk hr
    have k0 : C ⊢[PRAAx] rem (pw (pred p) (ap2 (sumF eB) (half p) (pairT p a))) p ≐ rem one p :=
      (congrAp2 remF (mul_one_r _) (.eqRefl _)).eqTrans
        ((rem_mul_congr2 hp1.wk (.eqRefl (rem (pw (pred p) (ap2 (sumF eB) (half p) (pairT p a))) p))
          er.eqSymm).eqTrans gu.wk)
    have goal0 : C ⊢[PRAAx] par (ap2 (sumF eB) (half p) (pairT p a)) ≐ zero := by
      refine .orE (neg_pow hq.wk (ap2 (sumF eB) (half p) (pairT p a))) ?_ ?_
      · exact Prf.andE₁ Prf.hyp0
      · exact pred_ne_one hp1.wk.wk hodd.wk.wk _
          (rp.wk.wk.eqSymm.eqTrans ((Prf.andE₂ Prf.hyp0).eqSymm.eqTrans (k0.wk.eqTrans r1.wk.wk)))
    exact goal0.eqTrans ((congrMonus (.eqRefl _) hr).eqTrans (monus_self _)).eqSymm

end LeanProofs.IPRA.DiophantineNumberTheory.GaussLemma
