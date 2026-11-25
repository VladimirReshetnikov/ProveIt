import IPRADerivations.AnalyticNumberTheory.GcdFiber
import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# Case split on a positive divisor

Sums over the divisors of `N` are written `∑_{d ≤ N} [d ≥ 1][d ∣ N] ⋯` with the indicator
`sg d * eqb (rem N d) zero`. A pointwise statement about a summand is trivial when the indicator vanishes, so
only a positive divisor `d` of `N` has to be treated; there `N = d (N/d)`, and for `N ≥ 1` the cofactor satisfies
`1 ≤ N/d ≤ N`. The lemmas below make that reduction once:

* `quo_lt'`: `N/d ≤ N` for `d ≥ 1`;
* `divisor_orE`: either `[d ≥ 1][d ∣ N] = 0`, or `d ≥ 1` and `d ∣ N`;
* `divisor_congr`: `[d ≥ 1][d ∣ N] X A = [d ≥ 1][d ∣ N] X B` from `A = B` for positive divisors `d`;
* `divisor_quo_congr`: the same for `N ≥ 1`, with `N/d ≥ 1` and `N/d ≤ N` supplied to the proof of `A = B`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorCases

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (eq_of_dvd' pos_of_eq_mul)
open LeanProofs.IPRA.Signum (sg sg_zero)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `N/d ≤ N` for `d ≥ 1`. -/
theorem quo_lt' {d N : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) : Γ ⊢[PRAAx] lt (quo N d) (succ N) := by
  have dv := natEq (GcdFiber.div_eq (j := N) hd); have wp := natEq hd
  refine (succ_monus_succ _ _).eqTrans (le_of_eq_add (d := pred d * quo N d + rem N d) ?_)
  apply deriveNat; ipra_simps; linear_combination dv + 𝔞 (quo N d) * wp

/-- Either the divisor indicator `[d ≥ 1][d ∣ N]` vanishes, or `d` is a positive divisor of `N`. -/
theorem divisor_orE {d N : PTm n} {φ : Fm PTm n}
    (h₀ : ((sg d * eqb (rem N d) zero ≐ zero) :: Γ) ⊢[PRAAx] φ)
    (h₁ : ((rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] φ) : Γ ⊢[PRAAx] φ := by
  have h := Prf.impI h₀
  refine .orE (zero_or_succ d) (Prf.impE h.wk ?_) (.orE (eq_or_ne (rem N d) zero) h₁ (Prf.impE h.wk.wk ?_))
  · exact (congrMul ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) Prf.hyp0)).eqTrans sg_zero)
      (.eqRefl _)).eqTrans (zero_mul _)
  · exact (congrMul (.eqRefl _) (eqb_of_ne Prf.hyp0)).eqTrans (mul_zero _)

/-- An equation between multiples of the divisor indicator has to be proved only for positive divisors. -/
theorem divisor_congr {d N A B : PTm n} (X : PTm n)
    (h : ((rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ) ⊢[PRAAx] A ≐ B) :
    Γ ⊢[PRAAx] ((sg d * eqb (rem N d) zero) * X) * A ≐ ((sg d * eqb (rem N d) zero) * X) * B := by
  refine divisor_orE (d := d) (N := N) ?_ (congrMul (.eqRefl _) h)
  have z := natEq (Prf.hyp0 : ((sg d * eqb (rem N d) zero ≐ zero) :: Γ) ⊢[PRAAx] _)
  apply deriveNat; ipra_simps
  linear_combination 𝔞 X * (𝔞 A - 𝔞 B) * z

/-- `divisor_congr` for `N ≥ 1`: the cofactor of a positive divisor satisfies `1 ≤ N/d ≤ N`. -/
theorem divisor_quo_congr {d N A B : PTm n} (X : PTm n) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (h : ∀ {C : List (Fm PTm n)}, (C ⊢[PRAAx] quo N d ≐ succ (pred (quo N d))) →
      (C ⊢[PRAAx] le (succ (quo N d)) (succ N)) → (C ⊢[PRAAx] A ≐ B)) :
    Γ ⊢[PRAAx] ((sg d * eqb (rem N d) zero) * X) * A ≐ ((sg d * eqb (rem N d) zero) * X) * B := by
  refine divisor_congr X ?_
  let C : List (Fm PTm n) := (rem N d ≐ zero) :: (d ≐ succ (pred d)) :: Γ
  have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp1
  exact h (pos_of_eq_mul hN.wk.wk (eq_of_dvd' hd (Prf.hyp0 : C ⊢[PRAAx] dvd d N))) (quo_lt' hd)

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorCases
