import IPRADerivations.AnalyticNumberTheory.GoldbachGeometric
import IPRADerivations.AnalyticNumberTheory.ValuationMul
import IPRADerivations.Core.CertificateTactics

/-!
# A Mersenne prime has a prime exponent

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`,
`chapters/elementary.tex`, the exponent clause of `el:perfect`.
For a divisor `d ≥ 2` of `e`, the existing finite geometric sum at base
`2^d` supplies a quotient for `(2^d − 1) ∣ (2^e − 1)`. If `d < e`,
the constructed divisor lies in the properly excluded interval of a prime
`2^e − 1`. This yields primality of the exponent in the object theory.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.MersenneExponent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (prime_shift)
open LeanProofs.IPRA.AnalyticNumberTheory.GoldbachGeometric (gB geom_sum one_le_pw)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd')
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The Mersenne number `2^e − 1`. -/
abbrev mersenne (e : PTm n) : PTm n := pred (pw two e)

theorem succ_mersenne (e : PTm n) : Γ ⊢[PRAAx] succ (mersenne e) ≐ pw two e :=
  (pw_pos one e).eqSymm

theorem two_le_mersenne {d : PTm n} (hd : Γ ⊢[PRAAx] le two d) :
    Γ ⊢[PRAAx] le two (mersenne d) := by
  have three_le_four : Γ ⊢[PRAAx] le (succ two) (pw two two) := by
    refine le_of_eq_add (d := one) ?_
    ipra_lc natEq (pw_succ (Γ := Γ) (two : PTm n) one) +
      2 * natEq (pw_one (Γ := Γ) (two : PTm n))
  have bound := le_trans three_le_four (pw_le_exp (p_pos (le_refl two)) hd)
  exact (succ_monus_succ two (mersenne d)).eqSymm.eqTrans
    (le_congr (.eqRefl _) (succ_mersenne d).eqSymm bound)

theorem mersenne_lt {d e : PTm n} (h : Γ ⊢[PRAAx] lt d e) :
    Γ ⊢[PRAAx] lt (mersenne d) (mersenne e) := by
  have gain : Γ ⊢[PRAAx] le (succ (pw two d)) (pw two (succ d)) := by
    refine le_of_eq_add (d := mersenne d) ?_
    ipra_lc natEq (pw_succ (Γ := Γ) two d) - natEq (succ_mersenne (Γ := Γ) d)
  have bound := le_trans gain (pw_le_exp (p_pos (le_refl two)) h)
  exact (succ_monus_succ (succ (mersenne d)) (mersenne e)).eqSymm.eqTrans
    (le_congr (congrSucc (succ_mersenne d)).eqSymm (succ_mersenne e).eqSymm bound)

/-- A divisor `d ≥ 2` of the exponent gives a divisor `2^d − 1` of `2^e − 1`. -/
theorem mersenne_divides {d e : PTm n} (hd : Γ ⊢[PRAAx] le two d) (h : Γ ⊢[PRAAx] dvd d e) :
    Γ ⊢[PRAAx] dvd (mersenne d) (mersenne e) := by
  let q := quo e d
  let x := pw two d
  let witness := ap2 (sumF gB) q x
  have expEq : Γ ⊢[PRAAx] e ≐ d * q := eq_of_dvd' (p_pos hd) h
  have geom := geom_sum (one_le_pw (le_succ_self (Γ := Γ) one) d) q
  have monusEq : Γ ⊢[PRAAx] monus x one ≐ mersenne d := by
    exact (congrMonus (succ_mersenne d).eqSymm (.eqRefl one)).eqTrans
      ((succ_monus_succ _ _).eqTrans (monus_zero _))
  refine dvd_of_eq' (p_pos (two_le_mersenne hd)) (w := witness) (succ_inj ?_)
  exact (succ_mersenne e).eqTrans ((congrPw (.eqRefl _) expEq).eqTrans
    ((pw_mul two d q).eqSymm.eqTrans (geom.eqTrans
      ((congrAdd (congrMul monusEq (.eqRefl _)) (.eqRefl one)).eqTrans
        (succ_eq_add_one _).eqSymm))))

/-- Primality of the Mersenne number forces primality of the exponent. -/
theorem prime_exponent {e : PTm n} (he : Γ ⊢[PRAAx] le two e) (hp : Γ ⊢[PRAAx] prime (mersenne e)) :
    Γ ⊢[PRAAx] prime e := by
  unfold prime
  refine .andI he (.allI (.impI (.impI (.impI ?_))))
  let d : PTm (n + 1) := var 0
  let e' := Syn.shift e
  let Δ := dvd d e' :: lt d e' :: le two d :: Γ.map Fm.shift
  have hd : Δ ⊢[PRAAx] le two d := hyp2
  have hde : Δ ⊢[PRAAx] lt d e' := Prf.hyp1
  have hdiv : Δ ⊢[PRAAx] dvd d e' := Prf.hyp0
  have hp' : Δ ⊢[PRAAx] prime (mersenne e') := by
    have h := prime_shift hp
    rw [show Syn.shift (mersenne e) = mersenne e' by simp [Syn.shift, mersenne, e']] at h
    exact h.wk.wk.wk
  unfold prime at hp'
  have hprime := Prf.allE (mersenne d) (Prf.andE₂ hp')
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_neg, Fm.subst_eq, subst_ap2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hprime
  exact .impE (.impE (.impE hprime (two_le_mersenne hd)) (mersenne_lt hde)) (mersenne_divides hd hdiv)

def exponentFormula : Fm PTm 1 := le two (var 0) ⟶ prime (mersenne (var 0)) ⟶ prime (var 0)

theorem prime_exponent_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 exponentFormula :=
  closeUniv 1 (.impI (.impI (prime_exponent Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.AnalyticNumberTheory.MersenneExponent
