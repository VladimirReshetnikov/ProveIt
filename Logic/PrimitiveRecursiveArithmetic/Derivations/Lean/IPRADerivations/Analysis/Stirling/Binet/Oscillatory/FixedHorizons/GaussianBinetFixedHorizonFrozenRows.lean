import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.FixedHorizons.GaussianBinetFixedHorizonSine
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineDampedQuadrature

/-!
# The frozen sine rows on a common physical horizon

The damping numerator grows with the π clock but its real size is
between one and ten times the geometric index. On any fixed integer
horizon the actual real-damped sine quadrature evaluates the original
kernel row with a denominator-independent time cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFixedHorizonFrozenRows

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetFixedHorizonSine (error)
open GaussianBinetSineDampedPanels (multiplier)
open GaussianBinetSineDampedQuadrature (shiftedValue panelData quadrature_error)
open GaussianBinetSineFrozenPiTerm (realNumerator realDenominator exact_denominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleBody)
open GaussianLogGammaEulerResidualDomain (source native)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalFiniteSum (sum sum_multiply)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalQuadratureDifference (differenceBody weighted_difference)
open GaussianRationalReciprocal (reciprocal subst_reciprocal)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianStirlingConstant (piNumerator piDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBinetExponentialIntegralGrid.evaluatorF
local notation "f" => sampleBody F

def value (p k i A B U T N : PTm n) : PTm n :=
  qmul (fraction two one) (GaussianBinetSineDampedQuadrature.value (p+N) (realNumerator k i) (realDenominator k) A B U T N)

@[simp] private theorem subst_pi_numerator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (piNumerator k) = piNumerator (Syn.subst σ k) := by
  simp [piNumerator,BaselQuadrature.Q,GaussianGammaHalfPiName.clearing,GaussianGammaHalfPiName.meshAt,
    GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,GaussianGammaHalfPiName.orderIndex,
    WallisFinite.Dm,one,two]

@[simp] private theorem subst_pi_denominator {m : ℕ} (σ : Fin n → PTm m) (k : PTm n) :
    Syn.subst σ (piDenominator k) = piDenominator (Syn.subst σ k) := by
  simp [piDenominator,Products.fact,GaussianGammaHalfPiName.clearing,GaussianGammaHalfPiName.meshAt,
    GaussianGammaHalfPiName.meshIndex,GaussianGammaHalfPiName.orderAt,GaussianGammaHalfPiName.orderIndex,
    WallisFinite.Dm,one,two]

ipra_subst value [realNumerator, realDenominator, GaussianBinetKernelImaginaryRatioRows.timeNumerator, GaussianBinetKernelImaginaryRatioRows.timeDenominator, one, two]

theorem frozen_margin (k i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx] le (realDenominator k) (realNumerator k i) := by
  have num := (GaussianBinetKernelPi.sample_margins (Γ := Γ) k).andE₁
  have h₁ : Γ ⊢[PRAAx] le (realDenominator k) (two*piDenominator k) :=
    le_of_eq_add (d := piDenominator k) (by dsimp only [realDenominator,GaussianBinetKernelImaginaryRatioRows.timeDenominator]; ipra_ring)
  have h₂ : Γ ⊢[PRAAx] le (piNumerator k) (realNumerator k i) := by
    dsimp only [realNumerator,GaussianBinetKernelImaginaryRatioRows.timeNumerator]
    have h := mul_le_mul_right (piNumerator k) hi
    have hs : Γ ⊢[PRAAx] le (i*piNumerator k) (two*piNumerator k*i) :=
      le_of_eq_add (d := i*piNumerator k) (by ipra_ring)
    exact le_trans (le_congr (one_mul _) (.eqRefl _) h) hs
  exact le_trans h₁ (le_trans num h₂)

theorem uniform_source (k i I : PTm n) (hi : Γ ⊢[PRAAx] le one i) (hI : Γ ⊢[PRAAx] le i I) : Γ ⊢[PRAAx]
    source (realNumerator k i) zero (realDenominator k) zero (num 10*I) := by
  let X := realNumerator k i
  let D := realDenominator k
  have hD : Γ ⊢[PRAAx] le one D := GaussianBinetKernelImaginaryRatioRows.time_denominator_positive k one (le_refl one)
  have hX : Γ ⊢[PRAAx] le one X := le_trans hD (frozen_margin k i hi)
  have h₁ := (GaussianBinetKernelPi.sample_margins (Γ := Γ) k).andE₂
  have h₂ : Γ ⊢[PRAAx] le X (num 10*I*D) := by
    dsimp only [X,D,realNumerator,realDenominator,GaussianBinetKernelImaginaryRatioRows.timeNumerator,
      GaussianBinetKernelImaginaryRatioRows.timeDenominator]
    exact le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono (le_mul_mono (le_refl two) h₁) hI)
  have hN : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq (native X zero zero) ≐ X*X :=
    (GaussianLogGammaEulerResidualRadius.native_norm X zero zero (.orI₁ (.eqRefl _))).eqTrans (by ipra_ring)
  exact .andI (.andI (.andI hX (.orI₁ (.eqRefl _))) hD)
    (le_congr hN.eqSymm (.eqRefl _) (le_mul_mono h₂ h₂))

private theorem readback (p X D A B R U T N : PTm n) : Γ ⊢[PRAAx]
    shiftedValue (p+N) X D A B R U T N ≐ GaussianBinetFixedHorizonSine.value p X zero D zero A B R U T N := by
  let c := multiplier A B
  let w := weight T one N
  let a := panelData true (p+N) X D A B R U T N
  let b := panelData false (p+N) X D A B R U T N
  let s := sum (differenceBody f f) N (pairT a b)
  exact (qmul_congr (.eqRefl w) (sum_multiply (differenceBody f f) c N (pairT a b))).eqTrans
    ((GaussianRationalPowerAlgebra.commute_nested w c s).eqTrans
       (qmul_congr (.eqRefl c) (weighted_difference f f N a b T one).eqSymm))

theorem frozen_kernel_error (p k i A B R U K T L N : PTm n)
    (hz : Γ ⊢[PRAAx] source (realNumerator k i) zero (realDenominator k) zero R)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hU : Γ ⊢[PRAAx] le A (U*B))
    (hm : Γ ⊢[PRAAx] le (realDenominator k) (K*realNumerator k i))
    (hcut : Γ ⊢[PRAAx] le (L*realDenominator k) (realNumerator k i*T)) (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+U)*T) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    let H := unit p*unit L
    let Q := unit (p+N)
    let E := error p R U K T L
    Γ ⊢[PRAAx] distanceBounded (value p k i A B U T N) (GaussianBinetKernelRows.value k i A B)
      (two*(T*(B*num 28))*H+(two*(B*(E+E)))*Q) (Q*H) := by
  let X := realNumerator k i
  let D := realDenominator k
  let H := unit p*unit L
  let Q := unit (p+N)
  let E := error p R U K T L
  let m : PTm n := fraction two one
  let c := reciprocal (GaussianBinetArctangentResolvent.polynomial X zero D zero A B)
  let d := reciprocal (GaussianBinetKernelRows.denominator A B i (GaussianBinetKernelPi.sample k))
  have hQ : Γ ⊢[PRAAx] le one Q := unit_positive _
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ (unit_positive p) (unit_positive L)
  have hM : Γ ⊢[PRAAx] bounded m two one :=
    GaussianEulerExponentCompactBounds.fraction_bound two one two (le_refl one) (le_congr (.eqRefl _) (by ipra_ring) (le_refl two))
  have first := distance_symmetric _ _ _ _ hQ (quadrature_error (p+N) X D A B R U T N hz hA hB (le_trans (unit_positive p) hpN) hU)
  have bridge := distance_congr (.eqRefl _) (qmul_congr (.eqRefl m) (readback p X D A B R U T N)) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance m _ _ two _ Q hQ hM first)
  have eq : Γ ⊢[PRAAx] c ≐ d := by
    simpa only [subst_reciprocal,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (reciprocal (var 0)) (exact_denominator (Γ := Γ) k i A B)
  have last := distance_congr (.eqRefl _) (qmul_congr (.eqRefl m) eq) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance m _ _ two (B*(E+E)) H hH hM
      (GaussianBinetFixedHorizonSine.finite_error p X zero D zero A B R U K T L N hz hA hB hU hm hcut hL hN hpN))
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hQ hH bridge last

theorem common_horizon_kernel_error (p k i I A B U T N : PTm n)
    (hi : Γ ⊢[PRAAx] le one i) (hI : Γ ⊢[PRAAx] le i I) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le one B) (hU : Γ ⊢[PRAAx] le A (U*B)) (ht : Γ ⊢[PRAAx] le T p)
    (hN : Γ ⊢[PRAAx] le ((num 10*I+U)*T) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    let H := unit p*unit T
    let Q := unit (p+N)
    let E := error p (num 10*I) U one T T
    Γ ⊢[PRAAx] distanceBounded (value p k i A B U T N) (GaussianBinetKernelRows.value k i A B)
      (two*(T*(B*num 28))*H+(two*(B*(E+E)))*Q) (Q*H) := by
  have h := frozen_margin k i hi
  have hm : Γ ⊢[PRAAx] le (realDenominator k) (one*realNumerator k i) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm h
  have cut : Γ ⊢[PRAAx] le (T*realDenominator k) (realNumerator k i*T) :=
    le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right T h)
  exact frozen_kernel_error p k i A B (num 10*I) U one T T N (uniform_source k i I hi hI) hA hB hU hm cut ht hN hpN

end LeanProofs.IPRA.Analysis.GaussianBinetFixedHorizonFrozenRows
