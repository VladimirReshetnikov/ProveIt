import IPRADerivations.Analysis.Euler.GaussianEulerSquarePower
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositiveScalingIntegrand

/-!
# The quadratic Euler kernel at positive rational times

At u = a/b and α = c/d, the original Euler evaluator at αu²
agrees with α^(z/B-1) times the kernel u^(2z/B-2) exp(-αu²).
Multiplying that kernel by u gives the original power exponent 2z/B-1
in the same decay kernel. Both identities use the literal power and
decay observations and their named product clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareKernel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianEulerIntegrandName (powerF powerData power_regular decayF decayData nameF data)
open GaussianEulerSquarePower (doubledMinusOne)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianEulerPositiveScalingIntegrand (source dampedData decay_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl cross_at)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def doubled (z B : PTm n) : PTm n := shifted (doubledMinusOne z B) B
abbrev kernelF : PR 2 := multiplyF powerF decayF
def kernelData (z B a b c d : PTm n) : PTm n :=
  multiplyData powerF decayF (powerData z B a b) (decayData (c*(a*a)) (d*(b*b)))
abbrev factoredF : PR 2 := multiplyF powerF kernelF
def factoredData (z B a b c d : PTm n) : PTm n :=
  multiplyData powerF kernelF (powerData z B c d) (kernelData (doubledMinusOne z B) B a b c d)
abbrev weightedF : PR 2 := multiplyF constantF kernelF
def weightedData (z B a b c d : PTm n) : PTm n :=
  multiplyData constantF kernelF (fraction a b) (kernelData (doubledMinusOne z B) B a b c d)

theorem doubled_parameter_equal (z B : PTm n) : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (doubled z B) (add z z) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [doubled, shifted, GaussianGammaEulerHeadLower.translated, doubledMinusOne, GaussianRootAlgebra.re_add,
      GaussianRootAlgebra.im_add, GaussianRootAlgebra.re_sub, GaussianRootAlgebra.im_sub,
      GaussianRootAlgebra.re_scale, GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring

theorem time_source (z B a b c d : PTm n) (h : Γ ⊢[PRAAx] source B a b c d) :
    Γ ⊢[PRAAx] GaussianEulerIntegrandName.source z B a b := .andI h.andE₁ h.andE₂.andE₂

theorem square_source (B a b c d : PTm n) (h : Γ ⊢[PRAAx] source B a b c d) :
    Γ ⊢[PRAAx] source B (a*a) (b*b) c d :=
  .andI h.andE₁ (.andI h.andE₂.andE₁
    (.andI (positive_product _ _ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₁)
      (positive_product _ _ h.andE₂.andE₂.andE₂ h.andE₂.andE₂.andE₂)))

theorem kernel_regular (z B a b c d : PTm n) (h : Γ ⊢[PRAAx] source B a b c d) :
    Γ ⊢[PRAAx] pointCN kernelF (kernelData z B a b c d) :=
  multiply_fast powerF decayF _ _ (power_regular z B a b (time_source z B a b c d h)) (decay_regular _ _)

theorem original_damped_at_square (z B a b c d : PTm n) (h : Γ ⊢[PRAAx] source B a b c d) :
    Γ ⊢[PRAAx] crossEquivalent kernelF kernelF (dampedData z B (a*a) (b*b) c d)
      (kernelData (doubledMinusOne z B) B a b c d) := by
  have square := square_source B a b c d h
  have decay := decay_regular (Γ := Γ) (c*(a*a)) (d*(b*b))
  exact GaussianGammaAdjacentCutoff.multiply_cross powerF powerF decayF decayF _ _ _ _
    (power_regular z B (a*a) (b*b) (time_source z B (a*a) (b*b) c d square))
    (power_regular (doubledMinusOne z B) B a b (time_source _ B a b c d h)) decay decay
    (GaussianEulerSquarePower.original_power_at_square z B a b (time_source z B a b c d h)) (cross_refl _ _ decay)

theorem original_square_scaling (z B a b c d : PTm n) (h : Γ ⊢[PRAAx] source B a b c d) :
    Γ ⊢[PRAAx] crossEquivalent nameF factoredF (data z B (c*(a*a)) (d*(b*b))) (factoredData z B a b c d) := by
  have square := square_source B a b c d h
  have factor := power_regular z B c d (.andI h.andE₁ h.andE₂.andE₁)
  have original := GaussianEulerPositiveScalingIntegrand.original_scaling z B (a*a) (b*b) c d square
  have replace := GaussianGammaAdjacentCutoff.multiply_cross powerF powerF kernelF kernelF _ _ _ _
    factor factor (GaussianEulerPositiveScalingIntegrand.damped_regular z B (a*a) (b*b) c d square)
    (kernel_regular (doubledMinusOne z B) B a b c d h) (cross_refl _ _ factor)
    (original_damped_at_square z B a b c d h)
  exact cross_trans _ _ _ _ _ _ original replace

theorem original_weighted_kernel (z B a b c d : PTm n) (h : Γ ⊢[PRAAx] source B a b c d) :
    Γ ⊢[PRAAx] crossEquivalent weightedF kernelF (weightedData z B a b c d) (kernelData (doubled z B) B a b c d) := by
  let v := doubledMinusOne z B
  let x := powerData v B a b
  let t := fraction a b
  let y := decayData (c*(a*a)) (d*(b*b))
  have ht := constant_regular (Γ := Γ) t
  have hp := power_regular v B a b (time_source v B a b c d h)
  have hd := decay_regular (Γ := Γ) (c*(a*a)) (d*(b*b))
  have shiftPower := GaussianEulerIntegrationByPartsParameterShift.original_power_parameter_shift v B a b
    (time_source v B a b c d h)
  have assoc := GaussianNameRingLaws.multiply_associative constantF powerF decayF t x y ht hp hd
  have replaced := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF constantF powerF) powerF decayF decayF
    (multiplyData constantF powerF t x) (powerData (doubled z B) B a b) y y (multiply_fast _ _ _ _ ht hp)
    (power_regular (doubled z B) B a b (time_source _ B a b c d h)) hd hd
    (cross_symm _ _ _ _ shiftPower) (cross_refl _ _ hd)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ assoc) replaced

theorem actual_original_Euler_square_scaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ crossEquivalent nameF factoredF
      (data (var 0) (var 1) (var 4*(var 2*var 2)) (var 5*(var 3*var 3)))
      (factoredData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_square_scaling _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_quadratic_weighted_kernel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ crossEquivalent weightedF kernelF
      (weightedData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
      (kernelData (doubled (var 0) (var 1)) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_weighted_kernel _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareKernel
