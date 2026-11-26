import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingFrozenIntegrand
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartMeshJacobian

/-!
# Literal frozen power-scaling rows at their true multiplication clocks

Both nested products retain their own actual queries. The frozen output
is exactly inverse source time times an original inverse-scale observation,
multiplied by decoded image time times an original Euler observation.
Multiplication by e/f and the physical cell width then gives exactly the
original evaluated Jacobian weight, with no value or clock-alignment law
assumed. Zero physical widths are included.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingFrozenRow

open_ipra
open GaussianEulerPositivePowerChart (source)
open GaussianEulerPowerScalingFrozenIntegrand (factorF factorData frozenF frozenData)
open GaussianEulerPowerScalingKernel (scaleExpF scaleExpData)
open GaussianEulerPowerChartFrozenKernel (imageData)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalPowerAlgebra (qmul_commutative qmul_shuffle)
open GaussianPositiveRationalLogarithm (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev EulerRow : PR 2 := GaussianEulerExponentialSubstitutionIntegrand.productF
abbrev I : PR 2 := GaussianEulerIntegrandName.nameF

def outerClock (p k z B e f d h Q S E T a b : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus factorF EulerRow (factorData z B e f d h a b)
    (imageData k z B e f d h Q S E T a b)) p

def scaleClock (p k z B e f d h Q S E T a b : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus constantF scaleExpF (fraction b a) (scaleExpData z B e f d h))
    (outerClock p k z B e f d h Q S E T a b)

def decodedNumerator (k e f d h Q S E T a b : PTm n) : PTm n := GaussianEulerPositivePowerChartImage.numerator k e f d h Q S E T a b
def decodedDenominator (k e f d h Q S E T a b : PTm n) : PTm n := GaussianEulerPositivePowerChartImage.denominator k e f d h Q S E T a b

def decodedFraction (k e f d h Q S E T a b : PTm n) : PTm n :=
  fraction (decodedNumerator k e f d h Q S E T a b) (decodedDenominator k e f d h Q S E T a b)
def eulerData (k z B e f d h Q S E T a b : PTm n) : PTm n :=
  GaussianEulerIntegrandName.data (scaled z f) (B*e) (decodedNumerator k e f d h Q S E T a b) (decodedDenominator k e f d h Q S E T a b)
def eulerClock (p k z B e f d h Q S E T a b : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus constantF I (decodedFraction k e f d h Q S E T a b)
    (eulerData k z B e f d h Q S E T a b)) (outerClock p k z B e f d h Q S E T a b)
def scaleObservation (p k z B e f d h Q S E T a b : PTm n) : PTm n :=
  ap2 scaleExpF (scaleClock p k z B e f d h Q S E T a b) (scaleExpData z B e f d h)
def eulerObservation (p k z B e f d h Q S E T a b : PTm n) : PTm n :=
  ap2 I (eulerClock p k z B e f d h Q S E T a b) (eulerData k z B e f d h Q S E T a b)
def frozenObservation (p k z B e f d h Q S E T a b : PTm n) : PTm n :=
  ap2 frozenF p (frozenData k z B e f d h Q S E T a b)
def jacobianObservation (k e f d h Q S E T a b : PTm n) : PTm n :=
  GaussianEulerPositivePowerChartJacobian.run (GaussianEulerPositivePowerChartImage.query k h Q E T) e f d h S a b

/-- Exact raw normalized product readback, without a regularity premise. -/
theorem multiply_readback (F G : PR 2) (p x y : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyF F G) p (multiplyData F G x y) ≐
      qmul (ap2 F (GaussianFastValueCut.exponent (multiplyModulus F G x y) p) x)
        (ap2 G (GaussianFastValueCut.exponent (multiplyModulus F G x y) p) y) :=
  (GaussianNameArithmetic.multiply_at F G x y p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))

theorem original_raw_readback (p k z B e f d h Q S E T a b : PTm n) : Γ ⊢[PRAAx]
    frozenObservation p k z B e f d h Q S E T a b ≐
      qmul (qmul (fraction b a) (scaleObservation p k z B e f d h Q S E T a b))
        (qmul (decodedFraction k e f d h Q S E T a b) (eulerObservation p k z B e f d h Q S E T a b)) := by
  let t := outerClock p k z B e f d h Q S E T a b
  have factor : Γ ⊢[PRAAx] ap2 factorF t (factorData z B e f d h a b) ≐
      qmul (fraction b a) (scaleObservation p k z B e f d h Q S E T a b) :=
    (multiply_readback constantF scaleExpF t (fraction b a) (scaleExpData z B e f d h)).eqTrans
      (qmul_congr (constant_at _ _) (.eqRefl _))
  have image : Γ ⊢[PRAAx] ap2 EulerRow t (imageData k z B e f d h Q S E T a b) ≐
      qmul (decodedFraction k e f d h Q S E T a b) (eulerObservation p k z B e f d h Q S E T a b) :=
    (multiply_readback constantF I t (decodedFraction k e f d h Q S E T a b) (eulerData k z B e f d h Q S E T a b)).eqTrans
      (qmul_congr (constant_at _ _) (.eqRefl _))
  exact (multiply_readback factorF EulerRow p (factorData z B e f d h a b) (imageData k z B e f d h Q S E T a b)).eqTrans
    (qmul_congr factor image)

private theorem swap_first (a b c : PTm n) : Γ ⊢[PRAAx] qmul a (qmul b c) ≐ qmul b (qmul a c) :=
  (qmul_associative a b c).eqSymm.eqTrans ((qmul_congr (qmul_commutative a b) (.eqRefl _)).eqTrans (qmul_associative b a c))

/-- Only true normalized multiplication laws; no canonical raw operands
or cancellation of a possibly zero cell width is needed. -/
theorem six_factor_reorder (r t s u v w : PTm n) : Γ ⊢[PRAAx]
    qmul (qmul r (qmul (qmul t s) (qmul u v))) w ≐
      qmul s (qmul (qmul (qmul u (qmul r t)) w) v) := by
  have first : Γ ⊢[PRAAx] qmul r (qmul (qmul t s) (qmul u v)) ≐ qmul (qmul u (qmul r t)) (qmul s v) :=
    (qmul_associative r (qmul t s) (qmul u v)).eqSymm.eqTrans
      ((qmul_congr (qmul_associative r t s).eqSymm (.eqRefl _)).eqTrans
        ((qmul_shuffle (qmul r t) s u v).eqTrans (qmul_congr (qmul_commutative _ _) (.eqRefl _))))
  exact (qmul_congr first (.eqRefl _)).eqTrans
    ((qmul_associative _ _ w).eqTrans
      ((qmul_congr (.eqRefl _) ((qmul_associative s v w).eqTrans
        (qmul_congr (.eqRefl _) (qmul_commutative v w)))).eqTrans
          ((swap_first _ s _).eqTrans (qmul_congr (.eqRefl _) (qmul_associative _ w v).eqSymm))))

/-- Literal evaluated-Jacobian readback of the frozen image. -/
theorem original_image_Jacobian (k e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    qmul (decodedFraction k e f d h Q S E T a b) (qmul (fraction e f) (fraction b a)) ≐
      jacobianObservation k e f d h Q S E T a b :=
  (qmul_congr (GaussianEulerPositivePowerChartImage.fraction_exact k e f d h Q S E T a b hs)
    (GaussianEulerDampedTimeRate.fraction_product e f b a hs.andE₁.andE₁.andE₂ hs.andE₂.andE₂.andE₁.andE₁)).eqTrans
      (GaussianEulerPositivePowerChartJacobian.program_at _ _ _ _ _ _ _ _).eqSymm

/-- The exact finite row equation at independent frozen-output and chart
queries. All three original nested multiply clocks remain displayed. -/
theorem original_weighted_row (p k z B e f d h Q S E T a b C D : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    qmul (qmul (fraction e f) (frozenObservation p k z B e f d h Q S E T a b)) (fraction C D) ≐
      qmul (scaleObservation p k z B e f d h Q S E T a b)
        (qmul (qmul (jacobianObservation k e f d h Q S E T a b) (fraction C D)) (eulerObservation p k z B e f d h Q S E T a b)) :=
  (qmul_congr (qmul_congr (.eqRefl _) (original_raw_readback p k z B e f d h Q S E T a b)) (.eqRefl _)).eqTrans
    ((six_factor_reorder _ _ _ _ _ _).eqTrans
      (qmul_congr (.eqRefl _) (qmul_congr (qmul_congr (original_image_Jacobian k e f d h Q S E T a b hs) (.eqRefl _)) (.eqRefl _))))

theorem original_mesh_weighted_row (p k i z B e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPositivePowerChartMesh.source e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    qmul (qmul (fraction e f) (frozenObservation p k z B e f d h Q S E T (GaussianEulerPositivePowerChartMesh.timeNumerator i N a C)
      (GaussianEulerPositivePowerChartMesh.timeDenominator N E))) (fraction C (GaussianEulerPositivePowerChartMesh.timeDenominator N E)) ≐
      qmul (scaleObservation p k z B e f d h Q S E T (GaussianEulerPositivePowerChartMesh.timeNumerator i N a C)
        (GaussianEulerPositivePowerChartMesh.timeDenominator N E))
        (qmul (GaussianEulerPositivePowerChartMeshJacobian.linearTerm k i e f d h Q S E T a C N)
          (eulerObservation p k z B e f d h Q S E T (GaussianEulerPositivePowerChartMesh.timeNumerator i N a C)
            (GaussianEulerPositivePowerChartMesh.timeDenominator N E))) :=
  original_weighted_row _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GaussianEulerPositivePowerChartMesh.node_source i e f d h Q S E T a C N hs hi)

theorem actual_original_frozen_scaling_row_readback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    (frozenObservation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ≐
      qmul (qmul (fraction (var 13) (var 12)) (scaleObservation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)))
        (qmul (decodedFraction (var 1) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13))
          (eulerObservation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)))) :=
  closeUniv 14 (original_raw_readback _ _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem actual_original_frozen_scaling_Jacobian_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
    (source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⟶
      qmul (qmul (fraction (var 4) (var 5)) (frozenObservation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)))
        (fraction (var 14) (var 15)) ≐
      qmul (scaleObservation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13))
        (qmul (qmul (jacobianObservation (var 1) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)) (fraction (var 14) (var 15)))
          (eulerObservation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13)))) :=
  closeUniv 16 (.impI (original_weighted_row _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingFrozenRow
