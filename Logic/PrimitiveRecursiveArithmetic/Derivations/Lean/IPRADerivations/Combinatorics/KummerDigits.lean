import IPRADerivations.AnalyticNumberTheory.Mobius
import IPRADerivations.Combinatorics.LegendreFact
import IPRADerivations.Combinatorics.LegendreDigits
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Foundations.CrossingSearch

/-!
# Kummer's formula in digit-sum form

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/elementary.tex`, Theorem `el:kummer`,
the displayed identity `(p − 1) v_p(C(n, k)) = s_p(k) + s_p(n − k) − s_p(n)`.

With `n = a + b`, `k = a` and the digit sum `s_p(m) = ∑_{j<m} (⌊m/p^j⌋ mod p)` of `LegendreDigits`, the identity
is stated without subtraction:

    (p − 1) · v_p(C(a + b, a)) + s_p(a + b) = s_p(a) + s_p(b)                       (**`kummer_digits`**).

It follows from `C(a + b, a) · a! · b! = (a + b)!` (`BinomialIdentities.binom_eq`), additivity of the valuation
(`ValuationMul.val_mul`), and Legendre's formula in the two forms `LegendreFact.legendre_fact` and
`LegendreDigits.legendre_digits`, which together give `s_p(m) + (p − 1) v_p(m!) = m` (`legendre_sum`).

The reading of the right side as `(p − 1)` times the number of carries (the carry array of the base-`p`
addition) is not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.KummerDigits

open_ipra
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val)
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_mul val_congr)
open LeanProofs.IPRA.Combinatorics.Binomial (binom pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (qB' legendre_digits)
open LeanProofs.IPRA.Combinatorics.LegendreFact (legendre_fact)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (pos_of_eq_mul)
open LeanProofs.IPRA.Foundations.CrossingSearch (monus_of_eq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The digit sum `s_p(m)`. -/
abbrev ds (p m : PTm n) : PTm n := ap2 (sumF LegendreDigits.dB) m (pairT p m)

/-- `s_p(m) + (p − 1) v_p(m!) = m` for a prime `p`. -/
theorem legendre_sum {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (m : PTm n) :
    Γ ⊢[PRAAx] ds p m + monus p one * val p (fact m) ≐ m :=
  (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (legendre_fact hp m))).eqTrans (legendre_digits (prime_two hp) m)

theorem kummer_alg {P Va Vb Vn Vc sa sb sn a b : PTm n} (vn : Γ ⊢[PRAAx] Vn ≐ (Va + Vb) + Vc)
    (ka : Γ ⊢[PRAAx] sa + P * Va ≐ a) (kb : Γ ⊢[PRAAx] sb + P * Vb ≐ b)
    (kn : Γ ⊢[PRAAx] sn + P * Vn ≐ a + b) : Γ ⊢[PRAAx] P * Vc + sn ≐ sa + sb := by
  ipra_lc natEq kn - natEq ka - natEq kb - 𝔞 P * natEq vn

/-- **Kummer's formula**, digit-sum form: `(p − 1) v_p(C(a + b, a)) + s_p(a + b) = s_p(a) + s_p(b)`. -/
theorem kummer_digits {p : PTm n} (hp : Γ ⊢[PRAAx] prime p) (a b : PTm n) :
    Γ ⊢[PRAAx] monus p one * val p (binom (a + b) a) + ds p (a + b) ≐ ds p a + ds p b := by
  have hle : Γ ⊢[PRAAx] le a (a + b) := le_add_right a b
  have mb : Γ ⊢[PRAAx] monus (a + b) a ≐ b := monus_of_eq (.eqRefl _)
  have e1 : Γ ⊢[PRAAx] fact (a + b) ≐ (fact a * fact b) * binom (a + b) a :=
    (binom_eq hle).eqTrans (congrMul (congrMul (.eqRefl _) (congrAp2 factF mb (.eqRefl _))) (.eqRefl _))
  have fab := pos_mul (fact_pos (Γ := Γ) a) (fact_pos b)
  have bpos := pos_of_eq_mul (fact_pos (Γ := Γ) (a + b)) e1
  have vn : Γ ⊢[PRAAx] val p (fact (a + b)) ≐ (val p (fact a) + val p (fact b)) + val p (binom (a + b) a) :=
    (val_congr p e1).eqTrans ((val_mul hp fab bpos).eqTrans
      (congrAdd (val_mul hp (fact_pos a) (fact_pos b)) (.eqRefl _)))
  exact kummer_alg vn (legendre_sum hp a) (legendre_sum hp b) (legendre_sum hp (a + b))

end LeanProofs.IPRA.Combinatorics.KummerDigits
