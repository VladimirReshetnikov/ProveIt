import IPRADerivations.Analysis.GaussianEulerPowerChartNamedLogarithm
import IPRADerivations.Analysis.GaussianEulerExponentialNamedKernelRate

/-!
# The original Euler row at a frozen rational power-chart image

A literal decoded image sample gives the original rescaled Euler row,
multiplied by the decoded time. Its distance to the transformed named
kernel has a uniform compact gain times the frozen query error. The two
kernel observation indices are independent of that query.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartFrozenKernel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChart (source majorant)
open GaussianEulerPositivePowerChartImage (reciprocalMargin numerator denominator)
open GaussianEulerPowerChartNamedLogarithm (lateF lateData late_at logF logData kernelF kernelData)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianNamedInverseRate (independentRate)
open GaussianCompactLogarithmBounds (radius)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerExponentialNamedKernelRate (gain)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "K" => GaussianEulerExponentialSubstitutionIntegrand.productF
local notation "L" => GaussianPositiveRationalLogarithm.logF

def imageData (k z B e f d h Q S E T a b : PTm n) : PTm n :=
  GaussianEulerExponentialSubstitutionIntegrand.productData (scaled z f) (B*e)
    (numerator k e f d h Q S E T a b) (denominator k e f d h Q S E T a b)
def cost (R h Q S E T : PTm n) : PTm n :=
  gain R (radius (reciprocalMargin h Q E T) (majorant Q S E T))*reciprocalMargin h Q E T
def parameter (z R B e f : PTm n) : Fm PTm n :=
  le one (B*e) ⋏ ComplexLogarithmRemainder.bounded (scaled z f) (R*(B*e))

private theorem decoded_log_data (k e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.rationalData lateF k (lateData e f d h Q S E T a b) ≐
      GaussianPositiveRationalLogarithm.data (numerator k e f d h Q S E T a b) (denominator k e f d h Q S E T a b) := by
  have eq := late_at k e f d h Q S E T a b hs.andE₁.andE₁.andE₂ hs.andE₁.andE₂.andE₁.andE₂
  simpa only [GaussianNamedPositiveLogarithm.rationalData,GaussianNamedPositiveLogarithm.numerator,
    GaussianNamedPositiveLogarithm.denominator,GaussianEulerPositivePowerChartImage.numerator,GaussianEulerPositivePowerChartImage.denominator,
    GaussianPositiveRationalLogarithm.subst_data,GaussianUnitIntervalInputDecoding.subst_numerator,
    GaussianUnitIntervalInputDecoding.subst_denominator,Syn.subst_var,Syn.inst_zero] using
    Prf.eqCongr1 (GaussianPositiveRationalLogarithm.data
      (GaussianUnitIntervalInputDecoding.numerator (var 0)) (GaussianUnitIntervalInputDecoding.denominator (var 0))) eq

theorem original_frozen_image_rate (k z R B e f d h Q S E T a b : PTm n)
    (hp : Γ ⊢[PRAAx] parameter z R B e f) (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] independentRate GaussianEulerPowerScalingKernel.transformedF K
      (GaussianEulerPowerScalingKernel.transformedData z B e f d h a b) (imageData k z B e f d h Q S E T a b)
      (cost R h Q S E T) (unit k) := by
  let X := lateData e f d h Q S E T a b
  let x := logData e f d h Q S E T a b
  let a' := numerator k e f d h Q S E T a b
  let b' := denominator k e f d h Q S E T a b
  let y := GaussianNamedPositiveLogarithm.rationalData lateF k X
  let y' := GaussianPositiveRationalLogarithm.data a' b'
  let G := reciprocalMargin h Q E T
  let H := majorant Q S E T
  let w := scaled z f
  let D := B*e
  have sx := GaussianEulerPowerChartNamedLogarithm.late_source e f d h Q S E T a b hs
  have hx := GaussianNamedPositiveLogarithm.exponential_input lateF X G H sx
  have hydro := GaussianNamedPositiveLogarithm.decoded_domain lateF k X G H sx
  have hy : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input L (radius G H) y :=
    GaussianNamedPositiveLogarithmExponential.original_rational_input _ _ G H sx.andE₂.andE₁ hydro
  have frozen := GaussianNamedPositiveLogarithm.original_frozen_rate lateF k X G H sx
  have raw := GaussianEulerExponentialNamedKernelRate.original_rate logF L w R D (radius G H) x y G (unit k)
    (.andI hp (.andI (.andI hx hy) (.andI (unit_positive k) frozen)))
  let Y := GaussianEulerExponentialSubstitutionNamedKernel.data L w D y
  let Y' := GaussianEulerExponentialSubstitutionNamedKernel.data L w D y'
  have dataCode : Γ ⊢[PRAAx] Y ≐ Y' := by
    simpa only [Y,Y',GaussianEulerExponentialSubstitutionNamedKernel.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (GaussianEulerExponentialSubstitutionNamedKernel.data L (Syn.shift w) (Syn.shift D) (var 0))
        (decoded_log_data k e f d h Q S E T a b hs)
  have sr : Γ ⊢[PRAAx] GaussianEulerIntegrandName.source w D a' b' :=
    .andI hp.andE₁ (GaussianEulerPositivePowerChartImage.image_domain k e f d h Q S E T a b hs).andE₁
  have weighted := cross_trans _ _ _ _ _ _
    (GaussianEulerExponentialSubstitutionNamedKernel.original_at_log w D a' b' sr)
    (cross_symm _ _ _ _ (GaussianEulerExponentialSubstitutionIntegrand.original_pullback w D a' b' sr))
  have right := GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ Y' Y _ _ dataCode.eqSymm (.eqRefl _) weighted
  have left := GaussianEulerPowerChartNamedLogarithm.original_image_kernel z B e f d h Q S E T a b hs
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive k) raw
    (cross_symm _ _ _ _ left) (cross_symm _ _ _ _ right)

theorem actual_original_frozen_power_image_Euler_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
      ((parameter (var 1) (var 2) (var 3) (var 4) (var 5) ⋏
        source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)) ⟶
        independentRate GaussianEulerPowerScalingKernel.transformedF K
          (GaussianEulerPowerScalingKernel.transformedData (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 12) (var 13))
          (imageData (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13))
          (cost (var 2) (var 7) (var 8) (var 9) (var 10) (var 11)) (unit (var 0))) :=
  closeUniv 14 (.impI (original_frozen_image_rate _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartFrozenKernel
