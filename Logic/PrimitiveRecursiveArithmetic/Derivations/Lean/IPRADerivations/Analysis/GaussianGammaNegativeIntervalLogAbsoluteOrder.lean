import IPRADerivations.Analysis.GaussianGammaNegativeIntervalLogAbsolute

/-!
# Order transfer from log-absolute Gamma

Both comparisons use the original sign-adjusted negative-interval Gamma
and permit independent rational inputs, intervals, and observation clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogAbsoluteOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalGammaSign (signedF signedData)
open GaussianGammaNegativeIntervalLogAbsolute (nameF nameData expF expData name_regular name_real original_exponential)
open GaussianNameEquivalence (cross_symm)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianStirlingMultiplicativeBoundsOrder (exponential_order)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_exponential_order strict_transport)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem absolute_order (a b N c d M : PTm n)
    (hx : Γ ⊢[PRAAx] guard a b) (hy : Γ ⊢[PRAAx] guard c d)
    (h : Γ ⊢[PRAAx] realOrder nameF nameF (nameData a b N) (nameData c d M)) :
    Γ ⊢[PRAAx] realOrder signedF signedF (signedData a b N) (signedData c d M) :=
  GaussianNamedRealOrderTransport.transport signedF expF expF signedF (signedData a b N)
    (expData a b N) (expData c d M) (signedData c d M)
    (cross_symm _ _ _ _ (original_exponential a b N hx)) (original_exponential c d M hy)
    (exponential_order nameF nameF (nameData a b N) (nameData c d M)
      (name_regular a b N hx) (name_regular c d M hy) (name_real a b N) (name_real c d M) h)

theorem strict_absolute_order (a b N c d M : PTm n)
    (hx : Γ ⊢[PRAAx] guard a b) (hy : Γ ⊢[PRAAx] guard c d)
    (h : Γ ⊢[PRAAx] strictOrder nameF nameF (nameData a b N) (nameData c d M)) :
    Γ ⊢[PRAAx] strictOrder signedF signedF (signedData a b N) (signedData c d M) :=
  strict_transport signedF expF expF signedF (signedData a b N)
    (expData a b N) (expData c d M) (signedData c d M)
    (cross_symm _ _ _ _ (original_exponential a b N hx)) (original_exponential c d M hy)
    (strict_exponential_order nameF nameF (nameData a b N) (nameData c d M)
      (name_regular a b N hx) (name_regular c d M hy) (name_real a b N) (name_real c d M) h)

theorem actual_original_negative_interval_log_absolute_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((guard (var 0) (var 1) ⋏ guard (var 3) (var 4)) ⟶
        ((realOrder nameF nameF (nameData (var 0) (var 1) (var 2)) (nameData (var 3) (var 4) (var 5)) ⟶
          realOrder signedF signedF (signedData (var 0) (var 1) (var 2)) (signedData (var 3) (var 4) (var 5))) ⋏
        (strictOrder nameF nameF (nameData (var 0) (var 1) (var 2)) (nameData (var 3) (var 4) (var 5)) ⟶
          strictOrder signedF signedF (signedData (var 0) (var 1) (var 2)) (signedData (var 3) (var 4) (var 5))))) :=
  closeUniv 6 (.impI (.andI
    (.impI (absolute_order _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))
    (.impI (strict_absolute_order _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogAbsoluteOrder
