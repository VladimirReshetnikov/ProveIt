import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineTransforms.GaussianBinetSineDampedTransform
import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelImaginaryRatioRows
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerPositiveAxis

/-!
# The frozen geometric sine transform is the original Binet kernel row

At positive geometric index use the original rational π observation
as the damping constant `2 i π`. Its exact squared resolvent is the
actual Binet denominator at the very same π clock. The two-exponential
sine integral therefore converges to the original frozen kernel row.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineFrozenPiTerm

open_ipra
open ComplexLogarithmRemainder (scale oneCode)
open GaussianBinetArctangentResolvent (polynomial)
open GaussianBinetKernelImaginaryRatioRows (timeNumerator timeDenominator time_denominator_positive time_value)
open GaussianBinetKernelPi (sample sample_margins)
open GaussianStirlingConstant (piNumerator piDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (fraction_congr)
open GaussianEulerDampedTimeRate (fraction_product)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal subst_reciprocal)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianReciprocalHorner (qadd_commutative qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def realNumerator (k i : PTm n) : PTm n := timeNumerator k i
def realDenominator (k : PTm n) : PTm n := timeDenominator k one

def value (p k i A B R U L N : PTm n) : PTm n :=
  qmul (fraction two one) (GaussianBinetSineDampedTransform.value p (realNumerator k i) zero (realDenominator k) zero A B R U L N)

private theorem real_argument (X D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    argument X zero D zero ≐ fraction X D :=
  GaussianGammaFiniteValueProperness.fraction_equal (native X zero zero) (scale X oneCode) D hD
    (GaussianLogGammaEulerPositiveAxis.native_axis_equal X zero (.orI₁ (.eqRefl _)))

private theorem square_shuffle (x y : PTm n) : Γ ⊢[PRAAx]
    qmul (qmul x y) (qmul x y) ≐ qmul (qmul y y) (qmul x x) := by
  have inner : Γ ⊢[PRAAx] qmul y (qmul x y) ≐ qmul x (qmul y y) :=
    (qmul_associative _ _ _).eqSymm.eqTrans
      ((qmul_congr (qmul_commutative y x) (.eqRefl _)).eqTrans (qmul_associative _ _ _))
  exact (qmul_associative _ _ _).eqTrans ((qmul_congr (.eqRefl _) inner).eqTrans
    ((qmul_associative _ _ _).eqSymm.eqTrans (qmul_commutative _ _)))

theorem exact_denominator (k i A B : PTm n) : Γ ⊢[PRAAx]
    polynomial (realNumerator k i) zero (realDenominator k) zero A B ≐ GaussianBinetKernelRows.denominator A B i (sample k) := by
  let X := realNumerator k i
  let D := realDenominator k
  let t := fraction (two*i) one
  have hD : Γ ⊢[PRAAx] le one D := time_denominator_positive k one (le_refl one)
  have e : Γ ⊢[PRAAx] argument X zero D zero ≐ qmul (sample k) t :=
    (real_argument X D hD).eqTrans (time_value k i one (le_refl one)).eqSymm
  have t₂ : Γ ⊢[PRAAx] qmul t t ≐ fraction (GaussianBinetKernelRows.weight i) one :=
    (fraction_product (two*i) one (two*i) one (le_refl one) (le_refl one)).eqTrans
      (fraction_congr _ _ _ _ (by simp only [GaussianBinetKernelRows.weight]; ipra_ring) (one_mul one))
  have eq : Γ ⊢[PRAAx] qmul (argument X zero D zero) (argument X zero D zero) ≐
      qmul (fraction (GaussianBinetKernelRows.weight i) one) (qmul (sample k) (sample k)) :=
    (qmul_congr e e).eqTrans ((square_shuffle (sample k) t).eqTrans (qmul_congr t₂ (.eqRefl _)))
  exact (qadd_congr eq (.eqRefl _)).eqTrans (qadd_commutative _ _)

theorem canonical_source (k i : PTm n) (hi : Γ ⊢[PRAAx] le one i) : Γ ⊢[PRAAx]
    source (realNumerator k i) zero (realDenominator k) zero (GaussianLogGammaEulerResidualRadius.radius (realNumerator k i) zero) := by
  have den := GaussianBinetKernelPi.denominator_positive (Γ := Γ) k
  have num : Γ ⊢[PRAAx] le one (piNumerator k) :=
    le_trans (positive_product two (piDenominator k) (le_succ_self one) den) (sample_margins k).andE₁
  have x : Γ ⊢[PRAAx] le one (realNumerator k i) := positive_product _ _ (positive_product _ _ (le_succ_self one) num) hi
  have d : Γ ⊢[PRAAx] le one (realDenominator k) := time_denominator_positive k one (le_refl one)
  exact GaussianLogGammaEulerResidualRadius.source_of_right_half_plane (realNumerator k i) zero (realDenominator k) zero
    (.andI (.andI x (.orI₁ (.eqRefl _))) d)

theorem finite_error (p k i A B R U K L N : PTm n)
    (hz : Γ ⊢[PRAAx] source (realNumerator k i) zero (realDenominator k) zero R)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hU : Γ ⊢[PRAAx] le A (U*B))
    (hm : Γ ⊢[PRAAx] le (realDenominator k) (K*realNumerator k i)) (hL : Γ ⊢[PRAAx] le L p)
    (hN : Γ ⊢[PRAAx] le ((R+U)*(realDenominator k*L)) N) (hpN : Γ ⊢[PRAAx] le (unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (value p k i A B R U L N) (GaussianBinetKernelRows.value k i A B)
      (two*(B*GaussianBinetArctangentCosineLaplace.error p R U K (realDenominator k*L) L)) (unit p*unit L) := by
  let X := realNumerator k i
  let D := realDenominator k
  let H := unit p*unit L
  have eq : Γ ⊢[PRAAx] reciprocal (polynomial X zero D zero A B) ≐ reciprocal (GaussianBinetKernelRows.denominator A B i (sample k)) := by
    simpa only [subst_reciprocal,Syn.subst_var,Syn.inst_zero] using
      Prf.eqCongr1 (reciprocal (var 0)) (exact_denominator (Γ := Γ) k i A B)
  have hH : Γ ⊢[PRAAx] le one H := positive_product _ _ (unit_positive p) (unit_positive L)
  have scaled := GaussianBinetSineDampedTransform.finite_error p X zero D zero A B R U K L N hz hA hB hU hm hL hN hpN
  exact distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) eq) (.eqRefl _) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance (fraction two one) _ _ two _ H hH
      (GaussianEulerExponentCompactBounds.fraction_bound two one two (le_refl one) (le_congr (.eqRefl _) (by ipra_ring) (le_refl two))) scaled)

theorem actual_Binet_frozen_sine_denominator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (polynomial (realNumerator (var 0) (var 1)) zero (realDenominator (var 0)) zero (var 2) (var 3) ≐
      GaussianBinetKernelRows.denominator (var 2) (var 3) (var 1) (sample (var 0))) :=
  closeUniv 4 (exact_denominator _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianBinetSineFrozenPiTerm
