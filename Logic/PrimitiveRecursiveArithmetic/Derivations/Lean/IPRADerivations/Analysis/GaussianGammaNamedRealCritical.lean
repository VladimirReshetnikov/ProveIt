import IPRADerivations.Analysis.GaussianGammaNamedRealDerivative
import IPRADerivations.Analysis.GaussianGammaNamedPoleFreeIncrementSource
import IPRADerivations.Analysis.GaussianGammaNamedRealDerivativeStep
import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNamedCritical

/-!
# Derivative and critical points of the original Gamma off the real poles

One original pole-free quotient and its actual reciprocal of the
increment apply on both computed charts. The branch-selected derivative
has a uniform rate from those quotients. Its zeros are exactly the
specified positive location and the specified offset in each negative
interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedRealCritical

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaDigammaDyadicLocation (locationF)
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeCriticalLocation (fractionLocationF)
open GaussianGammaNamedPoleFreeRealAdmission (offsetF offsetData chartIndex)
open GaussianGammaNamedRealDerivative (nameF data positiveCase negativeCase branch_cases positive_cross negative_cross)
open GaussianGammaNamedRealDerivativeDemand (modulus)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (zeroF)
open GaussianNamedInverseRate (independentRate)
open GaussianRealNameExponentialInjectivity (axisSamples)
open GaussianSignedNameExponentialOrder (realSamples)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "poleSource" => GaussianGammaNamedPoleFree.source
local notation "Q" => GaussianGammaNamedHalfPlanePoleFreeQuotient.nameF
local notation "qd" => GaussianGammaNamedHalfPlanePoleFreeQuotient.data
local notation "P" => GaussianNamedPositiveDigamma.derivativeF
local notation "pd" => GaussianNamedPositiveDigamma.derivativeData
local notation "N" => GaussianGammaNamedPoleFreeNegativeChartDerivative.derivativeF
local notation "nd" => GaussianGammaNamedPoleFreeNegativeChartDerivative.derivativeData
local notation "D" => GaussianGammaNegativeIntervalNamedDerivative.nameF
local notation "dd" => GaussianGammaNegativeIntervalNamedDerivative.data

def cost (f : PR 2) (x E : PTm n) : PTm n :=
  one+GaussianGammaNamedPoleFreeNegativeChartDerivative.cost f x E

def source (f K : PR 2) (p x z R E a : PTm n) : Fm PTm n :=
  (poleSource f x R E ⋏ realSamples f x) ⋏
    (axisSamples K z ⋏ (GaussianNameReciprocal.input K a z ⋏ smallSamples K z one (modulus f p x E)))

private theorem move_target (QF F G : PR 2) (q u v A B p : PTm n) (hQ : Γ ⊢[PRAAx] pointCN QF q)
    (hb : Γ ⊢[PRAAx] le A B) (hr : Γ ⊢[PRAAx] independentRate QF F q u A (unit p))
    (he : Γ ⊢[PRAAx] crossEquivalent G F v u) :
    Γ ⊢[PRAAx] independentRate QF G q v B (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  exact GaussianNamedRateTransport.transport QF F QF G q u q v B (unit p) hp
    (GaussianNamedRateRadius.weaken QF F q u A (unit p) B (unit p) hp hp (mul_le_mul_right (unit p) hb) hr)
    (cross_refl _ _ hQ) he

theorem derivative_rate (f K : PR 2) (p x z R E a : PTm n) (hs : Γ ⊢[PRAAx] source f K p x z R E a) :
    Γ ⊢[PRAAx] independentRate (Q f K) (nameF f) (qd f K x z R E (succ R) (two*E) a)
      (data f x E) (cost f x E) (unit p) := by
  have hf := hs.andE₁.andE₁
  have hr := hs.andE₁.andE₂
  have ha := hs.andE₂.andE₁
  have hk := hs.andE₂.andE₂.andE₁
  have hm := hs.andE₂.andE₂.andE₂
  have hE := (GaussianGammaNamedPoleFree.source_at f zero x R E hf).andE₂.andE₂.andE₁
  have small := GaussianGammaNamedRealDerivativeDemand.margin_small f K p x z E hE hm
  have hUpper := GaussianGammaNamedPoleFreeIncrementSource.original_source f K x z R E hf hk.andE₁ small
  have hQ := GaussianGammaNamedHalfPlanePoleFreeQuotient.name_regular f K x z R E (succ R) (two*E) a hk hf hUpper
  refine .orE (branch_cases f x R E hf hr) ?_ ?_
  · have hp : (positiveCase f x E :: Γ) ⊢[PRAAx] positiveCase f x E := Prf.hyp0
    have pos := GaussianGammaNamedRealDerivativeDemand.positive f K p x z E a hp.andE₂.andE₁ hk.wk hm.wk
    have rate := GaussianGammaNamedHalfPlanePoleFreeQuotient.derivative_rate f K p x z (two*E) R E (succ R) (two*E) a
      pos hf.wk hUpper.wk
    exact move_target (Q f K) (P f) (nameF f) _ _ _ one (cost f x E) p hQ.wk
      (le_add_right _ _) rate (positive_cross f x E hp)
  · have hn : (negativeCase f x E :: Γ) ⊢[PRAAx] negativeCase f x E := Prf.hyp0
    have term := GaussianGammaNamedRealDerivativeDemand.negative f K p x z E a hn.andE₂ ha.wk hk.wk hm.wk
    have rate := GaussianGammaNamedPoleFreeNegativeChartDerivative.derivative_rate f K p x z R E (succ R) (two*E) a
      hn.andE₂ hf.wk hUpper.wk term
    exact move_target (Q f K) (N f) (nameF f) _ _ _ _ (cost f x E) p hQ.wk
      (le_add_left _ _) rate (negative_cross f x E hn)

def selectedLocation (f : PR 2) (x E : PTm n) : Fm PTm n :=
  (positiveCase f x E ⋏ crossEquivalent f locationF x zero) ⋎
    (negativeCase f x E ⋏ crossEquivalent fractionLocationF (offsetF f) (chartIndex f x E) (offsetData f x E))

theorem selected_of_zero (f : PR 2) (x R E : PTm n) (hf : Γ ⊢[PRAAx] poleSource f x R E)
    (hr : Γ ⊢[PRAAx] realSamples f x) (hz : Γ ⊢[PRAAx] crossEquivalent (nameF f) zeroF (data f x E) zero) :
    Γ ⊢[PRAAx] selectedLocation f x E := by
  refine .orE (branch_cases f x R E hf hr) ?_ ?_
  · have hp : (positiveCase f x E :: Γ) ⊢[PRAAx] positiveCase f x E := Prf.hyp0
    have eq := cross_trans (P f) (nameF f) zeroF (pd x (two*E)) (data f x E) zero
      (cross_symm _ _ _ _ (positive_cross f x E hp)) hz.wk
    exact .orI₁ (.andI hp (GaussianGammaPositiveNamedCritical.selected_of_derivative_zero f x zero (two*E) hp.andE₂ eq))
  · have hn : (negativeCase f x E :: Γ) ⊢[PRAAx] negativeCase f x E := Prf.hyp0
    have negSrc := GaussianNamedEulerUnitTimeMargin.double _ _ _ hn.andE₂.andE₁
    have eq := cross_trans (N f) (nameF f) zeroF (nd f x E) (data f x E) zero
      (cross_symm _ _ _ _ (negative_cross f x E hn)) hz.wk
    exact .orI₂ (.andI hn (GaussianGammaNegativeIntervalNamedStationary.unique_stationary (offsetF f) (offsetData f x E)
      (two*(two*E)) (chartIndex f x E) negSrc eq))

theorem zero_of_selected (f : PR 2) (x E : PTm n) (hs : Γ ⊢[PRAAx] selectedLocation f x E) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) zeroF (data f x E) zero := by
  refine .orE hs ?_ ?_
  · exact cross_trans (nameF f) (P f) zeroF (data f x E) (pd x (two*E)) zero
      (positive_cross f x E Prf.hyp0.andE₁)
      (GaussianGammaPositiveNamedCritical.derivative_zero_of_selected f x zero (two*E) Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂)
  · let F := offsetF f
    let X := offsetData f x E
    let J := chartIndex f x E
    let W := two*(two*E)
    let Γ' := (negativeCase f x E ⋏ crossEquivalent fractionLocationF F J X) :: Γ
    have hn : Γ' ⊢[PRAAx] negativeCase f x E := Prf.hyp0.andE₁
    have he : Γ' ⊢[PRAAx] crossEquivalent fractionLocationF F J X := Prf.hyp0.andE₂
    have moved := GaussianGammaNegativeIntervalNamedDerivativeMargin.proper F fractionLocationF X J W (mesh J) J
      (GaussianNamedEulerUnitTimeMargin.double _ _ _ hn.andE₂.andE₁)
      (GaussianGammaNegativeIntervalNamedInput.root_source J) (cross_symm _ _ _ _ he)
    exact cross_trans (nameF f) (D F) zeroF (data f x E) (dd F X W J) zero
      (negative_cross f x E hn)
      (cross_trans (D F) (D fractionLocationF) zeroF (dd F X W J) (dd fractionLocationF J (mesh J) J) zero
        moved (GaussianGammaNegativeIntervalNamedStationary.root_stationary J))

theorem actual_pole_free_real_Gamma_derivative_closed (f K : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source f K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      independentRate (Q f K) (nameF f)
        (qd f K (var 1) (var 2) (var 3) (var 4) (succ (var 3)) (two*var 4) (var 5))
        (data f (var 1) (var 4)) (cost f (var 1) (var 4)) (unit (var 0))) :=
  closeUniv 6 (.impI (derivative_rate f K _ _ _ _ _ _ Prf.hyp0))

theorem actual_pole_free_real_Gamma_critical_points_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((poleSource f (var 0) (var 1) (var 2) ⋏ realSamples f (var 0)) ⟶
      ((crossEquivalent (nameF f) zeroF (data f (var 0) (var 2)) zero ⟶ selectedLocation f (var 0) (var 2)) ⋏
       (selectedLocation f (var 0) (var 2) ⟶ crossEquivalent (nameF f) zeroF (data f (var 0) (var 2)) zero))) :=
  closeUniv 3 (.impI (.andI
    (.impI (selected_of_zero f _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))
    (.impI (zero_of_selected f _ _ Prf.hyp0))))

local notation "step" => GaussianGammaNamedRealDerivativeStep.stepData
local notation "anchor" => GaussianGammaNamedRealDerivativeStep.stepAnchor

theorem literal_step_rate (f : PR 2) (p x R E : PTm n) (hf : Γ ⊢[PRAAx] poleSource f x R E)
    (hr : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    independentRate (Q f constantF) (nameF f)
      (qd f constantF x (step f p x E) R E (succ R) (two*E) (anchor f p x E))
      (data f x E) (cost f x E) (unit p) :=
  derivative_rate f constantF p x (step f p x E) R E (anchor f p x E)
    (.andI (.andI hf hr) (GaussianGammaNamedRealDerivativeStep.step_source f p x E))

theorem actual_pole_free_real_Gamma_literal_step_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((poleSource f (var 1) (var 2) (var 3) ⋏ realSamples f (var 1)) ⟶
      (neg (step f (var 0) (var 1) (var 3) ≐ GaussianRationalHorner.qzero) ⋏
        independentRate (Q f constantF) (nameF f)
          (qd f constantF (var 1) (step f (var 0) (var 1) (var 3)) (var 2) (var 3)
            (succ (var 2)) (two*var 3) (anchor f (var 0) (var 1) (var 3)))
          (data f (var 1) (var 3)) (cost f (var 1) (var 3)) (unit (var 0)))) :=
  closeUniv 4 (.impI (.andI (GaussianGammaNamedRealDerivativeStep.step_nonzero f _ _ _)
    (literal_step_rate f _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedRealCritical
