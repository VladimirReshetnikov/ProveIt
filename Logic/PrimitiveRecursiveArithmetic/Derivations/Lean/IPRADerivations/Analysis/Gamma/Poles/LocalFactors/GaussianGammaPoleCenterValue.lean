import IPRADerivations.Analysis.Gamma.Poles.LocalFactors.GaussianGammaLocalPoleFormula
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianRobinMeshExponential
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaInputProperness

/-!
# Exact center value of the original local Gamma regular part

At the center every actual normalized inverse factor is literally one.
The original terminal argument has native value one and its actual Gamma
name is normalized using checked input and radius properness. Thus the
actual regular part has center value (-1)^j/j!, independently of any
continuity or analyticity claim for that regular part.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleCenterValue

open_ipra
open GaussianGammaPoleMultiplier (inverseFactorProduct inverseFactorBody signedInverseFactorial)
open GaussianGammaLocalPoleFormula (regularMultiplier regularData resultF)
open GaussianGammaLocalPoleGuards (terminal)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr)
open GaussianRationalReciprocal (reciprocal)
open GaussianRootAlgebra (equal equal_of_values equal_trans)
open ComplexLogarithmRemainder (zeroCode oneCode scale normSq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem factor_at_zero (B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    GaussianGammaPoleFiniteFactors.factor zeroCode B k ≐ qone := by
  let E := B*k
  have hE := positive_product _ _ hB hk
  have same : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.neg (GaussianGammaLocalPoleGuards.center zeroCode B k))
      (scale E oneCode) := by
    apply equal_of_values <;>
      simp only [GaussianGammaLocalPoleGuards.center,GaussianGammaPoleZeros.poleNumerator,
        GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.im_neg,
        GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,
        GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero] <;> ring
  exact GaussianRationalHorner.canonical_unique _ _ _ E (GaussianRationalHorner.ofGaussian_canonical _ _ hE) qone_canonical hE
    (GaussianRationalHorner.represents_congr (.eqRefl _) same (.eqRefl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ hE)) (GaussianRationalReciprocal.qone_represents_scaled E)

theorem reciprocal_one : Γ ⊢[PRAAx] reciprocal (qone : PTm n) ≐ qone := by
  have low : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower (qone : PTm n) one one :=
    GaussianRationalLowerBounds.lower_from_representation qone oneCode one one one (le_refl _) (le_refl _)
      (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))
      (le_congr (by ipra_ring) ((congrMul (one_mul one) ComplexLogarithmRemainder.normSq_one).eqTrans (one_mul _)).eqSymm (le_refl one))
  have positive := GaussianNameReciprocal.lower_norm_positive (qone : PTm n) one (le_refl _)
    (GaussianRationalLowerBounds.name_lower qone one one (le_refl _) (le_refl _) low)
  have old := GaussianRationalReciprocal.reciprocal_identity (qone : PTm n) positive
  have unit : Γ ⊢[PRAAx] qmul qone (reciprocal (qone : PTm n)) ≐ reciprocal qone :=
    (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalReciprocal.reciprocal_canonical _))
  exact unit.eqSymm.eqTrans old

theorem reciprocal_congr {q r : PTm n} (e : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] reciprocal q ≐ reciprocal r := by
  ipra_congr (reciprocal (var 0) : PTm 1) with [e]

def inverseZeroLaw (B j : PTm n) : Fm PTm n := inverseFactorProduct zeroCode B j ≐ qone
ipra_subst inverseZeroLaw

theorem inverse_product_at_zero (B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] inverseZeroLaw B j := by
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have hall : Γ ⊢[PRAAx] .all (inverseZeroLaw (Syn.shift B) (var 0)) := by
    ipra_qfind [subst_inverseZeroLaw]
    · exact GaussianRationalFiniteProduct.product_zero inverseFactorBody (pairT zeroCode B)
    · exact (GaussianGammaPoleMultiplier.inverseFactorProduct_succ zeroCode _ _).eqTrans
        ((qmul_congr Prf.hyp0 ((reciprocal_congr (factor_at_zero _ _ bs.wk (zero_lt_succ _))).eqTrans reciprocal_one)).eqTrans
          (GaussianReciprocalHorner.qmul_one_right qone qone_canonical))
  simpa only [subst_inverseZeroLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE j

theorem regular_multiplier_at_zero (B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    regularMultiplier zeroCode B j ≐ signedInverseFactorial j :=
  (qmul_congr (.eqRefl _) (inverse_product_at_zero B j hB)).eqTrans
    (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.qmul_canonical _ _))

theorem terminal_at_zero (j : PTm n) : Γ ⊢[PRAAx] equal (terminal zeroCode one j) oneCode := by
  apply equal_trans (GaussianGammaLocalPoleGuards.terminal_native zeroCode one j)
  apply equal_of_values <;>
    simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring
def centerData (j D : PTm n) : PTm n := regularData zeroCode one j D
def centerValue (j : PTm n) : PTm n := signedInverseFactorial j
ipra_subst centerData [regularData, regularMultiplier, signedInverseFactorial, GaussianGammaReciprocalInverse.gammaData, GaussianGammaReciprocalInverse.gammaHeight, terminal]
ipra_subst centerValue [signedInverseFactorial]

theorem zero_scaled_bound (D : PTm n) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (scale D zeroCode) (zero*one) := by
  have eq : Γ ⊢[PRAAx] normSq (scale D zeroCode) ≐ zero :=
    (ComplexLogarithmRemainder.normSq_scale D zeroCode).eqTrans
      ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_zero).eqTrans (mul_zero _))
  exact le_congr eq.eqSymm (by ipra_ring) (le_refl zero)

/-- The terminal argument is in the original Gamma domain even at h=0.
Only D>=1 is needed; the punctured-center margin is not used. -/
theorem center_terminal_source (j D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (terminal zeroCode one j) two one one D :=
  GaussianGammaLocalPoleGuards.terminal_Gamma_domain zeroCode one one zero D j (le_refl _) (le_refl _) hD
    (le_congr (add_zero one).eqSymm (.eqRefl _) hD) (zero_scaled_bound D)

theorem terminal_Gamma_one (j D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent GaussianGammaReciprocalInverse.gammaF GaussianNameRingLaws.oneF
      (GaussianGammaReciprocalInverse.gammaData (terminal zeroCode one j) two one D) zero := by
  have here := center_terminal_source j D hD
  have eq := terminal_at_zero (Γ := Γ) j
  have proper := GaussianGammaInputProperness.original_Gamma_proper (terminal zeroCode one j) oneCode two one one D here eq
  have overlap := GaussianGammaRadiusOverlap.original_Gamma_overlap oneCode two one one one D one one
    (GaussianGammaInputProperness.gamma_source_equal (terminal zeroCode one j) oneCode two one one D here eq)
    GaussianGammaNormalization.unit_gamma_source
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ proper
    (GaussianNameEquivalence.cross_trans _ _ _ _ _ _ overlap GaussianRobinMeshExponential.C21_Gamma_one)

theorem center_regular (j D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN resultF (centerData j D) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (GaussianGammaCanonicalExponent.constant_regular _)
    (GaussianGammaReciprocalInverse.gamma_regular _ _ _ _ _ (center_terminal_source j D hD))

/-- C25 exact center coefficient of the SAME original regular-part name.
The original signed factorial reciprocal is literally (-1)^j/j!. -/
theorem original_C25_center_value (j D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent resultF GaussianGammaCanonicalExponent.constantF (centerData j D) (centerValue j) := by
  let a := regularMultiplier zeroCode one j
  let g := GaussianGammaReciprocalInverse.gammaData (terminal zeroCode one j) two one D
  have ha := GaussianGammaCanonicalExponent.constant_regular (Γ := Γ) a
  have hg := GaussianGammaReciprocalInverse.gamma_regular _ _ _ _ _ (center_terminal_source j D hD)
  have unitName := GaussianNameEquivalence.cross_trans _ _ _ _ _ _ (terminal_Gamma_one j D hD)
    (GaussianBoundedInverseApartness.ones_equivalent zero a)
  have replace := GaussianGammaAdjacentCutoff.multiply_cross GaussianGammaCanonicalExponent.constantF GaussianGammaCanonicalExponent.constantF
    GaussianGammaReciprocalInverse.gammaF GaussianNameRingLaws.oneF a a g a ha ha hg (GaussianNameRingLaws.one_fast a)
    (GaussianNameEquivalence.cross_refl _ _ ha) unitName
  have unit := GaussianNameRingLaws.multiply_one GaussianGammaCanonicalExponent.constantF a ha
  have value := GaussianGammaWeierstrassApproximant.constant_data_cross (Γ := Γ) a (centerValue j) (regular_multiplier_at_zero one j (le_refl one))
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ replace
    (GaussianNameEquivalence.cross_trans _ _ _ _ _ _ unit value)

/-- Actual regular-part observation, exact center coefficient, independent constant observation. -/
def output (p q j D : PTm n) : PTm n := pairT (ap2 resultF p (centerData j D))
  (pairT (centerValue j) (ap2 GaussianGammaCanonicalExponent.constantF q (centerValue j)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (p q j D : PTm n) : PTm n := PTm.app outputF ![p,q,j,D]
ipra_subst output
ipra_subst run

theorem program_at (p q j D : PTm n) : Γ ⊢[PRAAx] run p q j D ≐ output p q j D := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![p,q,j,D]
theorem returned_regular_part (p q j D : PTm n) : Γ ⊢[PRAAx]
    fstT (run p q j D) ≐ ap2 resultF p (centerData j D) :=
  (program_at p q j D).fstE
theorem returned_center_coefficient (p q j D : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run p q j D)) ≐ centerValue j :=
  (program_at p q j D).sndE.fstE
theorem returned_constant (p q j D : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run p q j D)) ≐ ap2 GaussianGammaCanonicalExponent.constantF q (centerValue j) :=
  (program_at p q j D).sndE.sndE
theorem returned_center_distance (p q j D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (fstT (run p q j D)) (sndT (sndT (run p q j D)))
      (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) :=
  GaussianRationalDistanceOrder.distance_congr (returned_regular_part p q j D).eqSymm (returned_constant p q j D).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianNameEquivalence.cross_at _ _ _ _ p q (original_C25_center_value j D hD))

theorem actual_center_inverse_factor_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ inverseFactorProduct zeroCode (var 0) (var 1) ≐ qone) := closeUniv 2 (.impI (inverse_product_at_zero _ _ Prf.hyp0))
theorem actual_regular_multiplier_center_code_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ regularMultiplier zeroCode (var 0) (var 1) ≐ signedInverseFactorial (var 1)) :=
  closeUniv 2 (.impI (regular_multiplier_at_zero _ _ Prf.hyp0))
theorem original_Gamma_regular_center_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ GaussianEuclideanDistanceName.pointCN resultF (centerData (var 0) (var 1))) := closeUniv 2 (.impI (center_regular _ _ Prf.hyp0))
theorem original_C25_exact_regular_center_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ GaussianNameEquivalence.crossEquivalent resultF GaussianGammaCanonicalExponent.constantF
      (regularData zeroCode one (var 0) (var 1)) (signedInverseFactorial (var 0))) := closeUniv 2 (.impI (original_C25_center_value _ _ Prf.hyp0))
theorem actual_original_pole_center_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_original_C25_center_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ GaussianRationalMetric.distanceBounded
      (fstT (run (var 0) (var 1) (var 2) (var 3))) (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))
      (GaussianCoefficientNameBounds.unit (var 0)+GaussianCoefficientNameBounds.unit (var 1))
      (GaussianCoefficientNameBounds.unit (var 0)*GaussianCoefficientNameBounds.unit (var 1))) := closeUniv 4 (.impI (returned_center_distance _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleCenterValue
