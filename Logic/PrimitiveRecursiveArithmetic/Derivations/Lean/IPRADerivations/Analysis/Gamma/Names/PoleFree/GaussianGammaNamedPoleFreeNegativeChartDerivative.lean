import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedPoleFreeRealAdmission
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedHalfPlanePoleFreeQuotient
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.GaussianGammaNegativeIntervalNamedIncrementDerivative

/-!
# Gamma and its derivative in the computed negative chart

The affine chart is equivalent to the caller's argument after shifting
back. Its increment produces the caller's upper argument under the same
translation. Pole-free Gamma properness then transfers both values and
the original divided difference with the same named reciprocal.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeNegativeChartDerivative

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianGammaNamedPoleFreeRealAdmission (negativeChart offsetF offsetData chartIndex)
open GaussianGammaNegativeIntervalNamedGamma (actualF actualData)
open GaussianGammaNegativeIntervalNamedGammaNativeDomain (shiftF shiftData radius)
open GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding (shift_source)
open GaussianGammaNegativeIntervalNamedGammaPoleFreeQuotient (nativeQuotientF nativeQuotientData shifted_sum_source)
open GaussianGammaNegativeIntervalNamedTerminalDerivative (endpoint_source)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedInverseRate (independentRate)
open GaussianRealNameExponentialInjectivity (axisSamples)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "sumF" => GaussianNamedGammaSmallIncrementInput.sumF
local notation "sumData" => GaussianNamedGammaSmallIncrementInput.sumData
local notation "P" => GaussianGammaNamedPoleFree.nameF
local notation "pd" => GaussianGammaNamedPoleFree.data
local notation "poleSource" => GaussianGammaNamedPoleFree.source
local notation "terminalSource" => GaussianGammaNegativeIntervalNamedTerminalDerivative.source
local notation "terminalModulus" => GaussianGammaNegativeIntervalNamedTerminalDerivative.modulus
local notation "quotientF" => GaussianGammaNamedHalfPlanePoleFreeQuotient.nameF
local notation "quotientData" => GaussianGammaNamedHalfPlanePoleFreeQuotient.data

abbrev derivativeF (f : PR 2) : PR 2 := GaussianGammaNegativeIntervalNamedDerivative.nameF (offsetF f)

def derivativeData (f : PR 2) (x E : PTm n) : PTm n :=
  GaussianGammaNegativeIntervalNamedDerivative.data (offsetF f) (offsetData f x E) (two*(two*E)) (chartIndex f x E)

def cost (f : PR 2) (x E : PTm n) : PTm n :=
  GaussianGammaNegativeIntervalNamedIncrementDerivative.cost (offsetF f) (offsetData f x E) (two*(two*E)) (chartIndex f x E)

def source (f K : PR 2) (p x z R E S D a : PTm n) : Fm PTm n :=
  negativeChart f x E ⋏ (poleSource f x R E ⋏
    (poleSource (sumF f K) (sumData x z) S D ⋏ terminalSource (offsetF f) K p (offsetData f x E) z (two*E) a))

theorem terminal_source (f K : PR 2) (p x z E a : PTm n) (hChart : Γ ⊢[PRAAx] negativeChart f x E)
    (hAxis : Γ ⊢[PRAAx] axisSamples K z) (hRec : Γ ⊢[PRAAx] GaussianNameReciprocal.input K a z)
    (hSmall : Γ ⊢[PRAAx] smallSamples K z one (terminalModulus (offsetF f) p (offsetData f x E) (two*E))) :
    Γ ⊢[PRAAx] terminalSource (offsetF f) K p (offsetData f x E) z (two*E) a :=
  .andI hChart.andE₁ (.andI hAxis (.andI hRec hSmall))

theorem gamma_cross (f : PR 2) (x R E : PTm n) (hChart : Γ ⊢[PRAAx] negativeChart f x E)
    (h : Γ ⊢[PRAAx] poleSource f x R E) :
    Γ ⊢[PRAAx] crossEquivalent (actualF (offsetF f)) (P f)
      (actualData (offsetF f) (offsetData f x E) (two*E) (chartIndex f x E)) (pd x R E) := by
  let F := offsetF f
  let X := offsetData f x E
  let N := chartIndex f x E
  let R₀ := radius N
  let E₀ := two*E
  have hs := shift_source F X E₀ N hChart.andE₁
  have first := GaussianGammaNegativeIntervalNamedGammaPoleFreeBinding.original_cross F X E₀ N hChart.andE₁
  have next := GaussianGammaNamedPoleFreeProperness.proper (shiftF F) f (shiftData X N) x R₀ R E₀ E hs h hChart.andE₂
  exact cross_trans _ _ _ _ _ _ first next

theorem original_cross (f K : PR 2) (p x z R E S D a : PTm n)
    (hChart : Γ ⊢[PRAAx] negativeChart f x E)
    (hLower : Γ ⊢[PRAAx] poleSource f x R E)
    (hUpper : Γ ⊢[PRAAx] poleSource (sumF f K) (sumData x z) S D)
    (hs : Γ ⊢[PRAAx] terminalSource (offsetF f) K p (offsetData f x E) z (two*E) a) :
    Γ ⊢[PRAAx] crossEquivalent (nativeQuotientF (offsetF f) K) (quotientF f K)
      (nativeQuotientData (offsetF f) K (offsetData f x E) z (two*(two*E)) (two*(two*E)) (chartIndex f x E) a)
      (quotientData f K x z R E S D a) := by
  let F := offsetF f
  let X := offsetData f x E
  let N := chartIndex f x E
  let W := two*(two*E)
  let r := radius N
  let G := shiftF F
  let Y := shiftData X N
  let h := sumF f K
  let u := sumData x z
  let j := sumF G K
  let v := sumData Y z
  have hk := hs.andE₂.andE₂.andE₁
  have hF := GaussianNamedEulerUnitTimeMargin.double F X (two*E) hs.andE₁
  have hJ := endpoint_source F K p X z (two*E) a hs
  have hG := shift_source F X W N hF
  have hShift := shifted_sum_source F K X z W N hJ hF.andE₁ hk.andE₁
  have highArgument := add_cross G f K K Y x z z hG.andE₁ hLower.andE₁ hk.andE₁ hk.andE₁
    hChart.andE₂ (cross_refl K z hk.andE₁)
  have low := GaussianGammaNamedPoleFreeProperness.proper G f Y x r R W E hG hLower hChart.andE₂
  have high := GaussianGammaNamedPoleFreeProperness.proper j h v u r S W D hShift hUpper highArgument
  exact GaussianNamedIncrementDifferenceQuotientProperness.proper (P j) (P h) (P G) (P f) K
    (pd v r W) (pd u S D) (pd Y r W) (pd x R E) z a
    (GaussianGammaNamedPoleFree.name_regular j v r W hShift) (GaussianGammaNamedPoleFree.name_regular h u S D hUpper)
    (GaussianGammaNamedPoleFree.name_regular G Y r W hG) (GaussianGammaNamedPoleFree.name_regular f x R E hLower)
    hk high low

theorem derivative_regular (f : PR 2) (x E : PTm n) (hChart : Γ ⊢[PRAAx] negativeChart f x E) :
    Γ ⊢[PRAAx] pointCN (derivativeF f) (derivativeData f x E) :=
  GaussianGammaNegativeIntervalNamedDerivative.name_regular _ _ _ _
    (GaussianNamedEulerUnitTimeMargin.double _ _ _ hChart.andE₁)

theorem derivative_rate (f K : PR 2) (p x z R E S D a : PTm n)
    (hChart : Γ ⊢[PRAAx] negativeChart f x E)
    (hLower : Γ ⊢[PRAAx] poleSource f x R E)
    (hUpper : Γ ⊢[PRAAx] poleSource (sumF f K) (sumData x z) S D)
    (hs : Γ ⊢[PRAAx] terminalSource (offsetF f) K p (offsetData f x E) z (two*E) a) :
    Γ ⊢[PRAAx] independentRate (quotientF f K) (derivativeF f) (quotientData f K x z R E S D a)
      (derivativeData f x E) (cost f x E) (unit p) := by
  let F := offsetF f
  let X := offsetData f x E
  let N := chartIndex f x E
  let W := two*(two*E)
  have base := GaussianGammaNegativeIntervalNamedIncrementDerivative.native_rate F K p X z (two*E) N a hs
  exact GaussianNamedRateTransport.transport (nativeQuotientF F K) (derivativeF f) (quotientF f K) (derivativeF f)
    (nativeQuotientData F K X z W W N a) (derivativeData f x E) (quotientData f K x z R E S D a)
    (derivativeData f x E) (cost f x E) (unit p) (unit_positive p) base
    (cross_symm _ _ _ _ (original_cross f K p x z R E S D a hChart hLower hUpper hs))
    (cross_refl _ _ (derivative_regular f x E hChart))

theorem actual_negative_chart_Gamma_binding_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((negativeChart f (var 0) (var 2) ⋏ poleSource f (var 0) (var 1) (var 2)) ⟶
      crossEquivalent (actualF (offsetF f)) (P f)
        (actualData (offsetF f) (offsetData f (var 0) (var 2)) (two*var 2) (chartIndex f (var 0) (var 2)))
        (pd (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (gamma_cross f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_negative_chart_pole_free_Gamma_derivative_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source f K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        independentRate (quotientF f K) (derivativeF f)
          (quotientData f K (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
          (derivativeData f (var 1) (var 4)) (cost f (var 1) (var 4)) (unit (var 0))) :=
  closeUniv 8 (.impI (derivative_rate f K _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeNegativeChartDerivative
