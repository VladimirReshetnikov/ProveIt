import IPRADerivations.AnalyticNumberTheory.ChebyshevUpper
import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.CommonLemmas

/-!
# Two corollaries of the Chebyshev bounds

* Packet `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/analytic.tex`, Lemma `an:binomial`,
  last assertion: `∏_{n < p ≤ 2n} p ≤ 4^n` for `n ≥ 1`. With the primorial `∏_{p ≤ r} p = PrimorialUpper.pri r`
  the product over the window is the quotient `pri (2n) / pri n`, and the assertion is stated without division:

      pri (2n) ≤ pri n · 4^n                                                   (**`window_product`**).

  For `n ≥ 2` it is `PrimorialUpper.pri_step` (which gives `4^{n−1}`); for `n = 1` it is `pri 2 ≤ 2`.

* Packet `analytic-number-theory/prime-counting-ipra`, `sections/growth.tex`, Proposition "Integer Chebyshev
  bounds", last assertion: "`π(n)/n` tends to zero with the explicit modulus `n ≥ 2^{13k+1}` for error `< 1/k`":

      k ≥ 1,  b ≥ 13k + 1,  2^b ≤ N   ⟹   k · π(N) < N                          (**`pi_density`**),

  from `ChebyshevUpper.cheb_upper_b` (`b π(N) ≤ 13 N`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevCorollaries

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (one_le_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimeRank (pc)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimorialUpper (pri pri_pos pri_step pri_two_le congrPri)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevUpper (cheb_upper_b)
open LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBounds (two_pos')
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The product of the primes of `(n, 2n]` -/

alias mul_one_r := Common.mul_one_right

theorem dbl_le (j m : PTm n) (e : Γ ⊢[PRAAx] m ≐ succ (succ j)) : Γ ⊢[PRAAx] le (two * succ j) (two * m) := by
  refine le_of_eq_add (d := two) ?_
  ipra_lc 2 * natEq e

theorem one_le_dbl (m : PTm n) (e : Γ ⊢[PRAAx] m ≐ one) : Γ ⊢[PRAAx] le one (two * m) := by
  refine le_of_eq_add (d := one) ?_
  ipra_lc 2 * natEq e

/-- **`an:binomial`, last assertion**: `∏_{p ≤ 2m} p ≤ ∏_{p ≤ m} p · 4^m` for `m ≥ 1`. -/
theorem window_product {m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) :
    Γ ⊢[PRAAx] le (pri (two * m)) (pri m * pw two (two * m)) := by
  refine .orE (zero_or_succ (pred m)) ?_ ?_
  · -- `m = 1`: `pri 2 ≤ 2 ≤ pri 1 · 4`
    let C : List (Fm PTm n) := (pred m ≐ zero) :: Γ
    have e1 : C ⊢[PRAAx] m ≐ one := hm.wk.eqTrans (congrSucc Prf.hyp0)
    have l1 : C ⊢[PRAAx] le (pri (two * m)) two :=
      le_congr (congrPri ((congrMul (.eqRefl _) e1).eqTrans (mul_one_r two)).eqSymm) (.eqRefl _) pri_two_le
    have p1 : C ⊢[PRAAx] le one (pri m) := one_le_pos (pri_pos m)
    have p2 : C ⊢[PRAAx] le two (pw two (two * m)) :=
      le_congr (pw_one two) (.eqRefl _) (PowerCleared.pw_le_exp two_pos' (one_le_dbl m e1))
    exact le_trans l1 (le_congr (one_mul two) (.eqRefl _) (le_mul_mono p1 p2))
  · -- `m = j + 2`
    let C : List (Fm PTm n) := (pred m ≐ succ (pred (pred m))) :: Γ
    have e2 : C ⊢[PRAAx] m ≐ succ (succ (pred (pred m))) := hm.wk.eqTrans (congrSucc Prf.hyp0)
    have st := pri_step (Γ := C) (pred (pred m))
    have l1 : C ⊢[PRAAx] le (pri (two * m)) (pri m * pw two (two * succ (pred (pred m)))) :=
      le_congr (congrPri (congrMul (.eqRefl _) e2).eqSymm) (congrMul (congrPri e2.eqSymm) (.eqRefl _)) st
    have l2 : C ⊢[PRAAx] le (pw two (two * succ (pred (pred m)))) (pw two (two * m)) :=
      PowerCleared.pw_le_exp two_pos' (dbl_le _ m e2)
    exact le_trans l1 (le_mul_mono (le_refl _) l2)

/-! ## The density of the primes -/

theorem two_le_of {k b : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k))
    (hb : Γ ⊢[PRAAx] le (succ (num 13 * k)) b) : Γ ⊢[PRAAx] le two b := by
  have l : Γ ⊢[PRAAx] le two (succ (num 13 * k)) := by
    refine le_of_eq_add (d := num 13 * pred k + num 12) ?_
    ipra_lc 13 * natEq hk
  exact le_trans l hb

/-- From `(13k + 1) P ≤ 13 N` and `N ≤ k P`: `P = 0`. -/
theorem zero_alg {k P N : PTm n} (h1 : Γ ⊢[PRAAx] le (succ (num 13 * k) * P) (num 13 * N))
    (h3 : Γ ⊢[PRAAx] le N (k * P)) : Γ ⊢[PRAAx] P ≐ zero := by
  have e1 := natEq (eq_add_of_le h1); have e2 := natEq (eq_add_of_le h3)
  have l : Γ ⊢[PRAAx] le P zero := by
    refine le_of_eq_add (d := monus (num 13 * N) (succ (num 13 * k) * P) + num 13 * monus (k * P) N) ?_
    ipra_lc e1 + 13 * e2
  exact (monus_zero P).eqSymm.eqTrans l

/-- **The density of the primes**: for `k ≥ 1`, `b ≥ 13k + 1` and `2^b ≤ N`, `k · π(N) < N`. -/
theorem pi_density {k b N : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k))
    (hb : Γ ⊢[PRAAx] le (succ (num 13 * k)) b) (hN : Γ ⊢[PRAAx] le (pw two b) N) :
    Γ ⊢[PRAAx] lt (k * pc N) N := by
  have h1 : Γ ⊢[PRAAx] le (succ (num 13 * k) * pc N) (b * pc N) := le_mul_mono hb (le_refl _)
  have h2 := cheb_upper_b (two_le_of hk hb) hN
  have h12 := le_trans h1 h2
  have hN1 : Γ ⊢[PRAAx] le one N := le_trans (one_le_pos (pw_pos' two_pos' b)) hN
  refine .orE (lt_or_le (k * pc N) N) Prf.hyp0 ?_
  let C : List (Fm PTm n) := le N (k * pc N) :: Γ
  have h3 : C ⊢[PRAAx] le N (k * pc N) := Prf.hyp0
  have z : C ⊢[PRAAx] pc N ≐ zero := zero_alg h12.wk h3
  have kz : C ⊢[PRAAx] k * pc N ≐ zero := (congrMul (.eqRefl _) z).eqTrans (mul_zero _)
  have l0 : C ⊢[PRAAx] le N zero := le_congr (.eqRefl _) kz h3
  have l1 : C ⊢[PRAAx] lt zero zero := le_trans hN1.wk l0
  exact lt_irrefl zero _ l1

end LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevCorollaries
