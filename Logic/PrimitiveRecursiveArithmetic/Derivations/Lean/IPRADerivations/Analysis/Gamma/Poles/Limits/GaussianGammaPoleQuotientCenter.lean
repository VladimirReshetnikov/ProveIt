import IPRADerivations.Analysis.Gamma.Poles.LocalFactors.GaussianGammaPoleCenterValue
import IPRADerivations.Analysis.Gamma.Poles.LocalFactors.GaussianGammaPoleReciprocalFactor

/-!
# Exact center coefficient of the original reciprocal Gamma pole quotient

The SAME actual quotient in the original P factorization has center
value (-1)^j*j!. Its original finite correction product is exactly one
at zero, and its actual terminal P name is normalized by native input
properness, radius overlap and the checked P(1)=1. This center identity
does not assume or claim the remaining quotient continuity theorem.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleQuotientCenter

open_ipra
open GaussianGammaPoleCenterValue (inverse_product_at_zero terminal_at_zero center_terminal_source zero_scaled_bound)
open GaussianGammaPoleFiniteFactors (factorProduct signedFactorial)
open GaussianGammaPoleReciprocalFactor (quotientF quotientData)
open GaussianGammaLocalPoleGuards (terminal)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianRationalHorner (qmul)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open ComplexLogarithmRemainder (zeroCode oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_factor_product_at_zero (B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    factorProduct zeroCode B j ≐ qone := by
  have upper : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (ComplexLogarithmRemainder.scale one zeroCode) (zero*B) :=
    le_congr (.eqRefl _) (by ipra_ring) (zero_scaled_bound (one : PTm n))
  have old := GaussianGammaPoleMultiplier.product_inverse zeroCode B one zero one j hB (le_refl one) (le_refl one)
    (le_of_eq_add (d := zero) (by ipra_ring)) upper
  have unit := GaussianReciprocalHorner.qmul_one_right (Γ := Γ) (factorProduct zeroCode B j)
    (GaussianRationalFiniteProduct.product_canonical _ _ _)
  exact unit.eqSymm.eqTrans ((qmul_congr (.eqRefl _) (inverse_product_at_zero B j hB).eqSymm).eqTrans old)

def centerMultiplier (j : PTm n) : PTm n := qmul (signedFactorial j) (factorProduct zeroCode one j)
def centerData (j : PTm n) : PTm n := quotientData zeroCode one j
ipra_subst centerMultiplier
ipra_subst centerData [quotientData, terminal]

theorem center_multiplier_code (j : PTm n) : Γ ⊢[PRAAx] centerMultiplier j ≐ signedFactorial j :=
  (qmul_congr (.eqRefl _) (original_factor_product_at_zero one j (le_refl one))).eqTrans
    (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.qmul_canonical _ _))

theorem terminal_P_one (j : PTm n) : Γ ⊢[PRAAx] crossEquivalent GaussianGammaC7Name.nameF GaussianNameRingLaws.oneF
    (GaussianGammaC7Name.data (terminal zeroCode one j) two one) zero := by
  have here := (center_terminal_source j one (le_refl (Γ := Γ) one)).andE₁
  have eq := terminal_at_zero (Γ := Γ) j
  have proper := GaussianGammaInputProperness.original_C7_proper (terminal zeroCode one j) oneCode two one here eq
  have overlap := GaussianGammaRadiusOverlap.original_P_overlap oneCode two one one
    (GaussianGammaFiniteValueProperness.source_equal _ _ _ _ here eq) GaussianGammaNormalization.unit_source
  exact cross_trans _ _ _ _ _ _ proper (cross_trans _ _ _ _ _ _ overlap GaussianRobinMeshExponential.C20_P_one)

theorem center_regular (j : PTm n) : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN quotientF (centerData j) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (constant_regular _)
    (GaussianGammaC7Name.name_regular _ _ _ (center_terminal_source j one (le_refl (Γ := Γ) one)).andE₁)

/-- Exact center value of the SAME original C23 factored quotient. -/
theorem original_C23_quotient_center (j : PTm n) : Γ ⊢[PRAAx] crossEquivalent quotientF constantF (centerData j) (signedFactorial j) := by
  let a := centerMultiplier j
  let z := GaussianGammaC7Name.data (terminal zeroCode one j) two one
  have ha := constant_regular (Γ := Γ) a
  have hz := GaussianGammaC7Name.name_regular _ _ _ (center_terminal_source j one (le_refl (Γ := Γ) one)).andE₁
  have unitName := cross_trans (Γ := Γ) _ _ _ _ _ _ (terminal_P_one j) (GaussianBoundedInverseApartness.ones_equivalent zero a)
  have replace := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF GaussianGammaC7Name.nameF GaussianNameRingLaws.oneF
    a a z a ha ha hz (GaussianNameRingLaws.one_fast a) (GaussianNameEquivalence.cross_refl _ _ ha) unitName
  have unit := GaussianNameRingLaws.multiply_one constantF a ha
  have value := GaussianGammaWeierstrassApproximant.constant_data_cross (Γ := Γ) a (signedFactorial j) (center_multiplier_code j)
  exact cross_trans _ _ _ _ _ _ replace (cross_trans _ _ _ _ _ _ unit value)
/-- The actual quotient observation, exact signed factorial and independent constant observation. -/
def output (p q j : PTm n) : PTm n := pairT (ap2 quotientF p (centerData j))
  (pairT (signedFactorial j) (ap2 constantF q (signedFactorial j)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (p q j : PTm n) : PTm n := PTm.app outputF ![p,q,j]
ipra_subst output
ipra_subst run

theorem program_at (p q j : PTm n) : Γ ⊢[PRAAx] run p q j ≐ output p q j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![p,q,j]
theorem returned_quotient (p q j : PTm n) : Γ ⊢[PRAAx]
    fstT (run p q j) ≐ ap2 quotientF p (centerData j) := (program_at p q j).fstE
theorem returned_coefficient (p q j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run p q j)) ≐ signedFactorial j :=
  (program_at p q j).sndE.fstE
theorem returned_constant (p q j : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run p q j)) ≐ ap2 constantF q (signedFactorial j) :=
  (program_at p q j).sndE.sndE
theorem returned_center_distance (p q j : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (fstT (run p q j)) (sndT (sndT (run p q j)))
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_quotient p q j).eqSymm (returned_constant p q j).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.cross_at _ _ _ _ p q (original_C23_quotient_center j))

theorem actual_original_correction_product_center_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ factorProduct zeroCode (var 0) (var 1) ≐ qone) := closeUniv 2 (.impI (original_factor_product_at_zero _ _ Prf.hyp0))
theorem original_P_pole_quotient_center_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (GaussianEuclideanDistanceName.pointCN quotientF (quotientData zeroCode one (var 0))) := closeUniv 1 (center_regular _)
theorem original_C23_exact_pole_quotient_center_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent quotientF constantF (quotientData zeroCode one (var 0)) (signedFactorial (var 0))) :=
  closeUniv 1 (original_C23_quotient_center _)
theorem actual_original_P_pole_center_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_original_P_pole_center_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalMetric.distanceBounded (fstT (run (var 0) (var 1) (var 2))) (sndT (sndT (run (var 0) (var 1) (var 2))))
      (GaussianCoefficientNameBounds.unit (var 0)+GaussianCoefficientNameBounds.unit (var 1))
      (GaussianCoefficientNameBounds.unit (var 0)*GaussianCoefficientNameBounds.unit (var 1))) := closeUniv 3 (returned_center_distance _ _ _)


end LeanProofs.IPRA.Analysis.GaussianGammaPoleQuotientCenter
