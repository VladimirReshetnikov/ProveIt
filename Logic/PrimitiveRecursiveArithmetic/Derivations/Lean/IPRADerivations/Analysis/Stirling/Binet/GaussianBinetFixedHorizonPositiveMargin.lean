import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetFixedHorizonFrozenRows

/-!
# Fixed-horizon sine rows bounded by a physical frequency margin

On the positive strip `B ≤ G*A` the frequency inverse costs G,
independently of the encoded frequency denominator. The actual
kernel row estimate retains that physical bound in the horizon error.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFixedHorizonPositiveMargin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentResolvent (polynomial)
open GaussianBinetFixedHorizonFrozenRows (frozen_margin uniform_source)
open GaussianBinetFixedHorizonSine (error reciprocal_value)
open GaussianBinetImaginaryExponentialIntegral (coefficient)
open GaussianBinetOscillatoryPanelFactor (polarity)
open GaussianBinetSineDampedPanels (multiplier)
open GaussianBinetSineDampedQuadrature (shiftedValue panelData quadrature_error)
open GaussianBinetSineDampedTransform (coefficient_lower)
open GaussianBinetSineFrozenPiTerm (realNumerator realDenominator exact_denominator)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (sampleBody)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalFiniteSum (sum sum_multiply)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalLowerBounds (inverse_bound)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalQuadratureDifference (differenceBody weighted_difference)
open GaussianRationalReciprocal (bound_congr bounded_product reciprocal subst_reciprocal)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBinetExponentialIntegralGrid.evaluatorF
local notation "f" => sampleBody F

theorem multiplier_bound (A B G : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hg : Γ ⊢[PRAAx] le B (G*A)) : Γ ⊢[PRAAx] bounded (multiplier A B) G one := by
  let c := coefficient A B (polarity true)
  have inv : Γ ⊢[PRAAx] bounded (reciprocal c) G one :=
    bounded_radius_mono _ _ _ _ _ hA (le_refl one) (le_congr (by ipra_ring) (.eqRefl _) hg)
      (inverse_bound c A B hA hB (coefficient_lower A B hB))
  have h₂ := le_succ_self (Γ := Γ) one
  have half : Γ ⊢[PRAAx] bounded (fraction one two) one one :=
    GaussianEulerExponentCompactBounds.fraction_bound one two one h₂
      (le_congr (.eqRefl _) (one_mul two).eqSymm h₂)
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_product _ _ G one one one (le_refl one) (le_refl one) inv half)

theorem sine_error (p X Y D sign A B G R U K T L N : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hg : Γ ⊢[PRAAx] le B (G*A)) (hU : Γ ⊢[PRAAx] le A (U*B)) (hm : Γ ⊢[PRAAx] le D (K*X))
    (hcut : Γ ⊢[PRAAx] le (L*D) (X*T)) (hL : Γ ⊢[PRAAx] le L p) (hN : Γ ⊢[PRAAx] le ((R+U)*T) N)
    (hpN : Γ ⊢[PRAAx] le (unit p) N) : Γ ⊢[PRAAx]
    distanceBounded (GaussianBinetFixedHorizonSine.value p X Y D sign A B R U T N) (reciprocal (polynomial X Y D sign A B))
      (G*(error p R U K T L+error p R U K T L)) (unit p*unit L) := by
  let E := error p R U K T L
  let H := unit p*unit L
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ (unit_positive p) (unit_positive L)
  have plus := GaussianBinetFixedHorizonPole.pole_integral_error true p X Y D sign A B R U K T L N hz hB hU hm hcut hL hN hpN
  have minus := GaussianBinetFixedHorizonPole.pole_integral_error false p X Y D sign A B R U K T L N hz hB hU hm hcut hL hN hpN
  have rate := GaussianNamedDifference.difference_distance _ _ _ _ E E H hH plus minus
  exact distance_congr (.eqRefl _) (reciprocal_value X Y D sign A B hz.andE₁ hA hB) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance (multiplier A B) _ _ G (E+E) H hH (multiplier_bound A B G hA hB hg) rate)

private theorem readback (p X D A B R U T N : PTm n) : Γ ⊢[PRAAx]
    shiftedValue (p+N) X D A B R U T N ≐ GaussianBinetFixedHorizonSine.value p X zero D zero A B R U T N := by
  let c := multiplier A B
  let w := weight T one N
  let a := panelData true (p+N) X D A B R U T N
  let b := panelData false (p+N) X D A B R U T N
  let s := sum (differenceBody f f) N (pairT a b)
  exact (qmul_congr (.eqRefl w) (sum_multiply (differenceBody f f) c N (pairT a b))).eqTrans
    ((qmul_associative w c s).eqSymm.eqTrans ((qmul_congr (qmul_commutative w c) (.eqRefl s)).eqTrans
      ((qmul_associative c w s).eqTrans (qmul_congr (.eqRefl c) (weighted_difference f f N a b T one).eqSymm))))

theorem common_horizon_kernel_error (p k i I A B G U T N : PTm n)
    (hi : Γ ⊢[PRAAx] le one i) (hI : Γ ⊢[PRAAx] le i I) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B)
    (hg : Γ ⊢[PRAAx] le B (G*A)) (hU : Γ ⊢[PRAAx] le A (U*B)) (ht : Γ ⊢[PRAAx] le T p)
    (hN : Γ ⊢[PRAAx] le ((num 10*I+U)*T) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    let H := unit p*unit T
    let Q := unit (p+N)
    let E := error p (num 10*I) U one T T
    Γ ⊢[PRAAx] distanceBounded (GaussianBinetFixedHorizonFrozenRows.value p k i A B U T N) (GaussianBinetKernelRows.value k i A B)
      (two*(T*(B*num 28))*H+(two*(G*(E+E)))*Q) (Q*H) := by
  let X := realNumerator k i
  let D := realDenominator k
  let R := num 10*I
  let H := unit p*unit T
  let Q := unit (p+N)
  let E := error p R U one T T
  let m : PTm n := fraction two one
  let a := reciprocal (polynomial X zero D zero A B)
  let b := reciprocal (GaussianBinetKernelRows.denominator A B i (GaussianBinetKernelPi.sample k))
  have h := frozen_margin k i hi
  have hm : Γ ⊢[PRAAx] le D (one*X) := le_congr (.eqRefl _) (one_mul _).eqSymm h
  have cut : Γ ⊢[PRAAx] le (T*D) (X*T) := le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right T h)
  have hz := uniform_source k i I hi hI
  have hQ : Γ ⊢[PRAAx] le one Q := unit_positive _
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ (unit_positive p) (unit_positive T)
  have hM : Γ ⊢[PRAAx] bounded m two one :=
    GaussianEulerExponentCompactBounds.fraction_bound two one two (le_refl one) (le_congr (.eqRefl _) (by ipra_ring) (le_refl two))
  have first := distance_symmetric _ _ _ _ hQ (quadrature_error (p+N) X D A B R U T N hz hA hB (le_trans (unit_positive p) hpN) hU)
  have bridge := distance_congr (.eqRefl _) (qmul_congr (.eqRefl m) (readback p X D A B R U T N)) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance m _ _ two _ Q hQ hM first)
  have eq : Γ ⊢[PRAAx] a ≐ b := by
    simpa only [subst_reciprocal,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (reciprocal (var 0)) (exact_denominator (Γ := Γ) k i A B)
  have last := distance_congr (.eqRefl _) (qmul_congr (.eqRefl m) eq) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance m _ _ two (G*(E+E)) H hH hM
      (sine_error p X zero D zero A B G R U one T T N hz hA hB hg hU hm cut ht hN hpN))
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hQ hH bridge last

end LeanProofs.IPRA.Analysis.GaussianBinetFixedHorizonPositiveMargin
