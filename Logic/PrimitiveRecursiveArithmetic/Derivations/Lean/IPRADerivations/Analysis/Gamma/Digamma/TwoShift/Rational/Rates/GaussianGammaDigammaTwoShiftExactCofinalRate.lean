import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.Rates.GaussianGammaDigammaTwoShiftCofinalRate

/-!
# Cofinal two-shift bounds with an explicit rational denominator

The leading radius and the original Gamma input denominator are
independent. Move each exact scalar radius into the endpoints of
the interval, and remove the remaining dyadic observation slack by
named real order.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftExactCofinalRate

open_ipra
open GaussianGammaDigammaTwoShiftCofinalRate
  (finiteRateWithDenominator logRateWithDenominator cofinal_rate_with_denominator)
open GaussianStirlingGammaLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def finiteRate (a b c d K D B : PTm n) : Fm PTm n :=
  finiteRateWithDenominator a b c d K D B

ipra_subst finiteRate [finiteRateWithDenominator, Syn.subst_shift, Syn.shift_subst]

def logRate (a b c d K T : PTm n) : Fm PTm n :=
  logRateWithDenominator a b c d K T

theorem cofinal_rate (a b c d K T B : PTm n) (ha : Γ ⊢[PRAAx] source a b)
    (hc : Γ ⊢[PRAAx] source c b) (hd : Γ ⊢[PRAAx] source d b) (hT : Γ ⊢[PRAAx] le one T)
    (h : Γ ⊢[PRAAx] finiteRate a b c d K T B) : Γ ⊢[PRAAx] logRate a b c d K T :=
  cofinal_rate_with_denominator a b c d K T B ha hc hd hT h

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftExactCofinalRate
