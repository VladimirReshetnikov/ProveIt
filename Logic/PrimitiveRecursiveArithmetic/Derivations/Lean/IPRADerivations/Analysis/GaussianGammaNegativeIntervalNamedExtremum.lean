import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedGamma
import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedInputRetiming
import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedStrictMinimum
import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedApartnessTransport

/-!
# Extrema of the original Gamma on negative pole intervals

At the selected offset the magnitude is a minimum. Gamma itself is a
minimum on the positive-sign intervals and a maximum on the negative-sign
intervals. Finite apartness gives a strict comparison, including after
retiming an input supplied with named interval bounds.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedExtremum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeCriticalLocation (fractionLocationF)
open GaussianGammaNegativeIntervalNamedApartness (apart)
open GaussianGammaNegativeIntervalNamedGamma (signedF signedData signed_regular actualF actualData)
open GaussianGammaNegativeIntervalNamedInput (root_source)
open GaussianGammaNegativeIntervalNamedInputRetiming (orderedWindow retimed_source)
open GaussianGammaNegativeIntervalNamedLog (nameF data name_real name_regular)
open GaussianGammaNegativeIntervalNamedMinimum (log_minimum)
open GaussianGammaNegativeIntervalNamedSign (odd_interval_sign even_interval_sign
  positive_order negative_order positive_strict_order negative_strict_order)
open GaussianGammaNegativeIntervalNamedStrictMinimum (strict_log_minimum)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedPositiveLateLogSource (retimedF retimedData original_cross)
open GaussianStirlingMultiplicativeBoundsOrder (exponential_order)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_exponential_order)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def extremumOrder (f : PR 2) (x E N : PTm n) : Fm PTm n :=
  ((par N ≐ one) ⟶
    realOrder (actualF fractionLocationF) (actualF f) (actualData fractionLocationF N (mesh N) N) (actualData f x E N)) ⋏
  ((par N ≐ zero) ⟶
    realOrder (actualF f) (actualF fractionLocationF) (actualData f x E N) (actualData fractionLocationF N (mesh N) N))

def strictExtremumOrder (f : PR 2) (x E N : PTm n) : Fm PTm n :=
  ((par N ≐ one) ⟶
    strictOrder (actualF fractionLocationF) (actualF f) (actualData fractionLocationF N (mesh N) N) (actualData f x E N)) ⋏
  ((par N ≐ zero) ⟶
    strictOrder (actualF f) (actualF fractionLocationF) (actualData f x E N) (actualData fractionLocationF N (mesh N) N))

theorem magnitude_minimum (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] realOrder (signedF fractionLocationF) (signedF f) (signedData fractionLocationF N (mesh N) N)
      (signedData f x E N) :=
  exponential_order (nameF fractionLocationF) (nameF f) (data N (mesh N) N) (data x E N)
    (name_regular fractionLocationF N (mesh N) N (root_source N)) (name_regular f x E N hs)
    (name_real fractionLocationF N (mesh N) N) (name_real f x E N) (log_minimum f x E N hs)

theorem strict_magnitude_minimum (f : PR 2) (x E N h : PTm n) (hs : Γ ⊢[PRAAx] source f x E)
    (ha : Γ ⊢[PRAAx] apart f h N x) :
    Γ ⊢[PRAAx] strictOrder (signedF fractionLocationF) (signedF f) (signedData fractionLocationF N (mesh N) N)
      (signedData f x E N) :=
  strict_exponential_order (nameF fractionLocationF) (nameF f) (data N (mesh N) N) (data x E N)
    (name_regular fractionLocationF N (mesh N) N (root_source N)) (name_regular f x E N hs)
    (name_real fractionLocationF N (mesh N) N) (name_real f x E N) (strict_log_minimum f x E N h hs ha)

theorem extremum (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] extremumOrder f x E N := by
  have left := signed_regular (Γ := Γ) fractionLocationF N (mesh N) N (root_source N)
  have right := signed_regular f x E N hs
  have order := magnitude_minimum f x E N hs
  exact .andI (.impI (positive_order _ _ N _ _ left.wk right.wk (odd_interval_sign N Prf.hyp0) order.wk))
    (.impI (negative_order _ _ N _ _ left.wk right.wk (even_interval_sign N Prf.hyp0) order.wk))

theorem strict_extremum (f : PR 2) (x E N h : PTm n) (hs : Γ ⊢[PRAAx] source f x E)
    (ha : Γ ⊢[PRAAx] apart f h N x) : Γ ⊢[PRAAx] strictExtremumOrder f x E N := by
  have left := signed_regular (Γ := Γ) fractionLocationF N (mesh N) N (root_source N)
  have right := signed_regular f x E N hs
  have order := strict_magnitude_minimum f x E N h hs ha
  exact .andI (.impI (positive_strict_order _ _ N _ _ left.wk right.wk (odd_interval_sign N Prf.hyp0) order.wk))
    (.impI (negative_strict_order _ _ N _ _ left.wk right.wk (even_interval_sign N Prf.hyp0) order.wk))

theorem ordered_extremum (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] orderedWindow f x E) :
    Γ ⊢[PRAAx] extremumOrder (retimedF f) (retimedData x E) (two*E) N :=
  extremum _ _ _ _ (retimed_source f x E hs)

theorem strict_ordered_extremum (f : PR 2) (x E N h : PTm n) (hs : Γ ⊢[PRAAx] orderedWindow f x E)
    (ha : Γ ⊢[PRAAx] apart f h N x) :
    Γ ⊢[PRAAx] strictExtremumOrder (retimedF f) (retimedData x E) (two*E) N := by
  have target := retimed_source f x E hs
  have separation := GaussianGammaNegativeIntervalNamedApartnessTransport.transport f (retimedF f) h N x
    (retimedData x E) hs.andE₁ target.andE₁ ha (original_cross f x E hs.andE₁)
  exact strict_extremum _ _ _ _ (succ h) target separation

theorem actual_named_negative_Gamma_ordered_extremum_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (orderedWindow f (var 0) (var 1) ⟶
        extremumOrder (retimedF f) (retimedData (var 0) (var 1)) (two*var 1) (var 2)) :=
  closeUniv 3 (.impI (ordered_extremum f _ _ _ Prf.hyp0))

theorem actual_named_negative_Gamma_strict_ordered_extremum_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (orderedWindow f (var 0) (var 1) ⟶ apart f (var 3) (var 2) (var 0) ⟶
        strictExtremumOrder (retimedF f) (retimedData (var 0) (var 1)) (two*var 1) (var 2)) :=
  closeUniv 4 (.impI (.impI (strict_ordered_extremum f _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedExtremum
