import IPRADerivations.Analysis.Barnes.Growth.GaussianBarnesCanonicalDiskBound
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorInverse
import IPRADerivations.Analysis.Euler.PowerScaling.Named.GaussianEulerNamedPowerScalingPowerFrozen
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedAddRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# Disk Lipschitz bound for the original Barnes prefactor

Compare the exponent after combining its two named exponential factors.
The bound uses the zeroth observations of the same named Stirling and
Euler constants and a common certified radius depending only on the disk.
Transport the resulting rate back to the original product observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorLipschitz

open_ipra
open GaussianBarnesCanonicalDiskBound (prefactorRadius radius_le)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalPrefactor
open GaussianBarnesCanonicalPrefactorInverse (exponentF exponentData exponentRadius exponent_input)
open GaussianEuclideanDistanceName (pointCN)
open GaussianEulerNamedPowerScalingPowerFrozen (multiply_same_denominator)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData multiplyF multiplyData add_fast product_distance)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRadiusExponentialLipschitzRate (factor)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem self_at (f : PR 2) (x N : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] independentRate f f x x zero N :=
  GaussianNamedRateRadius.weaken f f x x zero one zero N (le_refl one) hN
    (le_of_eq_add (d := zero) (by ipra_ring)) (GaussianNamedDifferenceRate.self_rate f x hf)

private theorem add_at (f g : PR 2) (x y u v A C N : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] independentRate f f x u A N)
    (hC : Γ ⊢[PRAAx] independentRate g g y v C N) :
    Γ ⊢[PRAAx] independentRate (addF f g) (addF f g) (addData x y) (addData u v) (A+C) N :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hN hN) hN
    (le_of_eq_add (d := zero) (by
      dsimp only [GaussianNamedRateComposition.leadingNumerator,GaussianNamedRateComposition.leadingDenominator]
      ipra_ring))
    (GaussianNamedAddRate.independent_rate f g f g x y u v A N C N hN hN hA hC)

private theorem multiply_fixed_right (f g : PR 2) (x y c A N : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN f y) (hc : Γ ⊢[PRAAx] pointCN g c)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] independentRate f f x y A N) :
    Γ ⊢[PRAAx] independentRate (multiplyF f g) (multiplyF f g) (multiplyData f g x c) (multiplyData f g y c)
      (U g c*A) N := by
  have rate := multiply_same_denominator f g f g x c y c A zero N (U g c) (U f y)
    hN hx hc hy hc (all_samples_bounded g c hc) (all_samples_bounded f y hy) h (self_at g c N hc hN)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hN hN
    (le_of_eq_add (d := zero) (by ipra_ring)) rate

def linearGain : PTm n := U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
def quadraticGain : PTm n := U quadraticCoefficientF quadraticCoefficientData
def halfGain : PTm n := U constantF negativeHalf
def exponentGain (R : PTm n) : PTm n := linearGain+halfGain*(one+quadraticGain*(two*R))
def disk (R : PTm n) : PTm n := prefactorRadius R+prefactorRadius R
def gain (R : PTm n) : PTm n := factor (disk R)*exponentGain R

theorem exponent_rate (z w R B D A N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (hN : Γ ⊢[PRAAx] le one N)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A N) :
    Γ ⊢[PRAAx] independentRate exponentF exponentF (exponentData z B) (exponentData w D)
      (exponentGain R*A) N := by
  let x := ofGaussian z B
  let y := ofGaussian w D
  let X := qmul x x
  let Y := qmul y y
  let p := polynomialData z B
  let q := polynomialData w D
  let c : PTm n := negativeHalf
  let L : PTm n := linearGain
  let Q : PTm n := quadraticGain
  let H : PTm n := halfGain
  let T := A+Q*((two*R)*A)
  have hx := GaussianGammaEulerHead.fraction_disk z R B hz.andE₁ hz.andE₂
  have hy := GaussianGammaEulerHead.fraction_disk w R D hw.andE₁ hw.andE₂
  have hs : Γ ⊢[PRAAx] distanceBounded X Y ((two*R)*A) N :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (product_distance x y x y A A N R R hN hd hd hx hy)
  have hr := GaussianNamedAddRate.constant_rate x y A N hN hd
  have hsq := GaussianNamedAddRate.constant_rate X Y ((two*R)*A) N hN hs
  have qreg := quadratic_coefficient_regular (Γ := Γ)
  have lin := multiply_fixed_right constantF GaussianStirlingConstant.nameF x y _ A N
    (constant_regular _) (constant_regular _) (GaussianStirlingConstant.name_regular zero) hN hr
  have quad := multiply_fixed_right constantF quadraticCoefficientF X Y quadraticCoefficientData ((two*R)*A) N
    (constant_regular _) (constant_regular _) qreg hN hsq
  have poly := add_at constantF quadraticF x (quadraticData z B) y (quadraticData w D) A (Q*((two*R)*A)) N
    hN hr quad
  have hp : Γ ⊢[PRAAx] pointCN polynomialF p :=
    add_fast constantF quadraticF _ _ (constant_regular _)
      (GaussianNameArithmetic.multiply_fast constantF quadraticCoefficientF X _ (constant_regular _) qreg)
  have hq : Γ ⊢[PRAAx] pointCN polynomialF q :=
    add_fast constantF quadraticF _ _ (constant_regular _)
      (GaussianNameArithmetic.multiply_fast constantF quadraticCoefficientF Y _ (constant_regular _) qreg)
  have hc := constant_regular (Γ := Γ) c
  have corr := multiply_same_denominator constantF polynomialF constantF polynomialF c p c q zero T N (U polynomialF p) H
    hN hc hp hc hq (all_samples_bounded polynomialF p hp) (all_samples_bounded constantF c hc)
    (self_at constantF c N hc hN) poly
  have joined := add_at linearF correctionF (linearData z B) (correctionData z B)
    (linearData w D) (correctionData w D) (L*A) (U polynomialF p*zero+H*T) N hN lin corr
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hN hN
    (le_of_eq_add (d := zero) (by dsimp only [exponentGain,L,Q,H,T]; ipra_ring)) joined

theorem independent_rate (z w R B D A N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D)
    (hN : Γ ⊢[PRAAx] le one N)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A N) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data z B) (data w D) (gain R*A) N := by
  let C := exponentGain R
  let T := disk R
  let X := exponentData z B
  let Y := exponentData w D
  let F := GaussianRadiusExponentialName.nameF exponentF
  let dx := GaussianRadiusExponentialName.data T X
  let dy := GaussianRadiusExponentialName.data T Y
  have hzR := radius_le z R B hz
  have hwR := radius_le w R D hw
  have hx := GaussianExponentialRadiusIndependence.input_widen exponentF (exponentRadius z B) T X
    (exponent_input z B) (add_le_add₂ hzR hzR)
  have hy := GaussianExponentialRadiusIndependence.input_widen exponentF (exponentRadius w D) T Y
    (exponent_input w D) (add_le_add₂ hwR hwR)
  have exp := GaussianRadiusExponentialLipschitzRate.independent_rate exponentF exponentF T X Y (C*A) N
    (.andI hN (.andI hx (.andI hy (exponent_rate z w R B D A N hz hw hN hd))))
  have crossx := GaussianNameEquivalence.cross_trans nameF F F (data z B) (combinedData z B) dx (combined z B)
    (GaussianExponentialRadiusIndependence.same_input_cross exponentF (exponentRadius z B) T X (exponent_input z B) hx)
  have crossy := GaussianNameEquivalence.cross_trans nameF F F (data w D) (combinedData w D) dy (combined w D)
    (GaussianExponentialRadiusIndependence.same_input_cross exponentF (exponentRadius w D) T Y (exponent_input w D) hy)
  have transported := GaussianNamedRateTransport.transport F F nameF nameF dx dy _ _ (factor T*(C*A)) N hN exp crossx crossy
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ hN hN
    (le_of_eq_add (d := zero) (by dsimp only [gain,T,C]; ipra_ring)) transported

theorem actual_Barnes_prefactor_disk_Lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let A := var 5
     let N := var 6
     (source z R B ⋏ source w R D) ⟶
       (le one N ⋏ distanceBounded (ofGaussian z B) (ofGaussian w D) A N) ⟶
       independentRate nameF nameF (data z B) (data w D) (gain R*A) N) :=
  closeUniv 7 (.impI (.impI (independent_rate _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorLipschitz
