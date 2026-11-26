import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedDerivativeMargin
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedIncrementDerivative
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedInputRetiming
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedStationary

/-!
# Critical points of the original Gamma between negative poles

The native named increment quotient tends to zero at the selected
offset. On each certified interval, any other zero of the identified
derivative represents exactly the selected offset.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedCritical

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeCriticalLocation (fractionLocationF)
open GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient (nativeQuotientF nativeQuotientData)
open GaussianGammaNegativeIntervalNamedInput (root_source)
open GaussianGammaNegativeIntervalNamedInputRetiming (orderedWindow retimed_source)
open GaussianGammaNegativeIntervalNamedIncrementDerivative (cost native_rate)
open GaussianGammaNegativeIntervalNamedTerminalDerivative (source)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans cross_refl)
open GaussianNameRingLaws (zeroF)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveLateLogSource (retimedF retimedData original_cross)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "D" => GaussianGammaNegativeIntervalNamedDerivative.nameF
local notation "dd" => GaussianGammaNegativeIntervalNamedDerivative.data
local notation "unitSource" => GaussianNamedEulerUnitTime.source

theorem root_at_margin (N W : PTm n) (hs : Γ ⊢[PRAAx] unitSource fractionLocationF N W) :
    Γ ⊢[PRAAx] crossEquivalent (D fractionLocationF) zeroF (dd fractionLocationF N W N) zero :=
  cross_trans (D fractionLocationF) (D fractionLocationF) zeroF _ _ _
    (GaussianGammaNegativeIntervalNamedDerivativeMargin.same_input_cross fractionLocationF N W (mesh N) N hs (root_source N))
    (GaussianGammaNegativeIntervalNamedStationary.root_stationary N)

theorem original_stationary_rate (K : PR 2) (p z N a : PTm n)
    (h : Γ ⊢[PRAAx] source fractionLocationF K p N z (mesh N) a) :
    Γ ⊢[PRAAx] independentRate (nativeQuotientF fractionLocationF K) zeroF
      (nativeQuotientData fractionLocationF K N z (two*mesh N) (two*mesh N) N a) zero
      (cost fractionLocationF N (two*mesh N) N) (unit p) := by
  let F := nativeQuotientF fractionLocationF K
  let W := two*mesh N
  let u := nativeQuotientData fractionLocationF K N z W W N a
  let v := dd fractionLocationF N W N
  let H := cost fractionLocationF N W N
  have src := GaussianNamedEulerUnitTimeMargin.double fractionLocationF N (mesh N) (root_source (Γ := Γ) N)
  have rate := native_rate fractionLocationF K p N z (mesh N) N a h
  have eq := GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient.original_cross fractionLocationF K N z W W N a src
    (GaussianGammaNegativeIntervalNamedTerminalDerivative.endpoint_source fractionLocationF K p N z (mesh N) a h)
    h.andE₂.andE₂.andE₁
  have reg := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ eq) eq
  exact GaussianNamedRateTransport.transport F (D fractionLocationF) F zeroF u v u zero H (unit p)
    (unit_positive p) rate (cross_refl _ _ reg) (cross_symm _ _ _ _ (root_at_margin N W src))

theorem unique_ordered_stationary (f : PR 2) (x E N : PTm n)
    (hs : Γ ⊢[PRAAx] orderedWindow f x E)
    (hz : Γ ⊢[PRAAx] crossEquivalent (D (retimedF f)) zeroF
      (dd (retimedF f) (retimedData x E) (two*(two*E)) N) zero) :
    Γ ⊢[PRAAx] crossEquivalent fractionLocationF f N x := by
  have src := retimed_source f x E hs
  have unique := GaussianGammaNegativeIntervalNamedStationary.unique_stationary (retimedF f) (retimedData x E)
    (two*(two*E)) N (GaussianNamedEulerUnitTimeMargin.double _ _ _ src) hz
  exact cross_trans fractionLocationF (retimedF f) f N (retimedData x E) x unique
    (cross_symm _ _ _ _ (original_cross f x E hs.andE₁))

theorem ordered_stationary_of_selected (f : PR 2) (x E N : PTm n)
    (hs : Γ ⊢[PRAAx] orderedWindow f x E) (he : Γ ⊢[PRAAx] crossEquivalent fractionLocationF f N x) :
    Γ ⊢[PRAAx] crossEquivalent (D (retimedF f)) zeroF
      (dd (retimedF f) (retimedData x E) (two*(two*E)) N) zero := by
  let F := retimedF f
  let X := retimedData x E
  let W := two*(two*E)
  have src := GaussianNamedEulerUnitTimeMargin.double F X (two*E) (retimed_source f x E hs)
  have near := cross_trans fractionLocationF f F N x X he (original_cross f x E hs.andE₁)
  have moved := GaussianGammaNegativeIntervalNamedDerivativeMargin.proper fractionLocationF F N X (mesh N) W N
    (root_source N) src near
  exact cross_trans (D F) (D fractionLocationF) zeroF _ _ _ (cross_symm _ _ _ _ moved)
    (GaussianGammaNegativeIntervalNamedStationary.root_stationary N)

theorem actual_negative_interval_named_stationary_rate_closed (K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source fractionLocationF K (var 0) (var 2) (var 1) (mesh (var 2)) (var 3) ⟶
        independentRate (nativeQuotientF fractionLocationF K) zeroF
          (nativeQuotientData fractionLocationF K (var 2) (var 1) (two*mesh (var 2)) (two*mesh (var 2)) (var 2) (var 3))
          zero (cost fractionLocationF (var 2) (two*mesh (var 2)) (var 2)) (unit (var 0))) :=
  closeUniv 4 (.impI (original_stationary_rate K _ _ _ _ Prf.hyp0))

theorem actual_negative_interval_named_stationary_exactly_selected_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (orderedWindow f (var 0) (var 1) ⟶
        ((crossEquivalent (D (retimedF f)) zeroF
          (dd (retimedF f) (retimedData (var 0) (var 1)) (two*(two*var 1)) (var 2)) zero ⟶
            crossEquivalent fractionLocationF f (var 2) (var 0)) ⋏
         (crossEquivalent fractionLocationF f (var 2) (var 0) ⟶
          crossEquivalent (D (retimedF f)) zeroF
            (dd (retimedF f) (retimedData (var 0) (var 1)) (two*(two*var 1)) (var 2)) zero))) :=
  closeUniv 3 (.impI (.andI
    (.impI (unique_ordered_stationary f (var 0) (var 1) (var 2) Prf.hyp1 Prf.hyp0))
    (.impI (ordered_stationary_of_selected f (var 0) (var 1) (var 2) Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedCritical
