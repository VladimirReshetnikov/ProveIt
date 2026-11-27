import IPRADerivations.Analysis.Logarithm.FiniteSeries.Composition.GaussianFiniteLogarithmDyadicTail
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameEquivalence
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GammaLogarithmFactorBridge

/-!
# The actual cofinal finite C4 composition as a regular Gaussian name

The PR2 samples evaluate the original stored composition at logarithm
degree10(p+8)+2 and exponential cutoff10(p+8). The proved dyadic tail
gives genuine point regularity and equivalence to the constant1+w name.
At original integer source data the SAME samples are exactly the finite
exponential of z/N plus the original finite Gamma logarithm factor.
This is the cofinal finite-composition interpretation; a general
exponential operation on arbitrary equivalent names is not asserted.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmCompositionName

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (evaluate ofGaussian ofGaussian_represents positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (diagonalEquivalent crossEquivalent)
open GaussianFiniteLogarithmDyadicTail (clock precisionDenominator)
open GaussianFiniteLogarithmPolynomial (composition)
open GaussianFiniteLogarithmCompositionTail (linearValue)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def degree (p : PTm n) : PTm n := clock p+two
def value (p w : PTm n) : PTm n := evaluate (composition (degree p) (clock p)) w
def nameF : PR 2 := PTm.toPR (value (var 0) (var 1))
def sample (p w : PTm n) : PTm n := ap2 nameF p w
def constantF : PR 2 := PTm.toPR (linearValue (var 1) : PTm 2)
def constant (p w : PTm n) : PTm n := ap2 constantF p w
ipra_subst degree
ipra_subst value
ipra_subst sample
ipra_subst constant

theorem sample_at (p w : PTm n) : Γ ⊢[PRAAx] sample p w ≐ value p w := by
  simpa [sample,nameF,ap2] using toPR_eq (Γ := Γ) (value (var 0) (var 1) : PTm 2) ![p,w]
theorem constant_at (p w : PTm n) : Γ ⊢[PRAAx] constant p w ≐ linearValue w := by
  simpa [constant,constantF,ap2] using toPR_eq (Γ := Γ) (linearValue (var 1) : PTm 2) ![p,w]

theorem precise_error (p w : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (sample p w) (linearValue w) one (precisionDenominator p) :=
  distance_congr (sample_at p w).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianFiniteLogarithmDyadicTail.composition_error (degree p) (clock p) p w
      (le_add_right _ _) (le_refl _) hw)

theorem precision_factor (p : PTm n) : Γ ⊢[PRAAx] precisionDenominator p ≐ unit p*num 16 :=
  (pw_add two p (num 4)).eqTrans (congrMul (.eqRefl _) GaussianFiniteLogarithmDyadicTail.two_four)

theorem sample_error (p w : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (sample p w) (linearValue w) one (unit p) := by
  have radius : Γ ⊢[PRAAx] le (one*unit p) (one*precisionDenominator p) := by
    refine le_of_eq_add (d := num 15*unit p) ?_
    have e := natEq (precision_factor (Γ := Γ) p)
    apply deriveNat; ipra_simps; rw [e]; ring
  exact distance_radius_mono _ _ _ _ _ _ (GaussianFiniteLogarithmDyadicTail.precision_positive p)
    (unit_positive p) radius (precise_error p w hw)

/-- Independent precision regularity follows from two actual finite tail
bounds at the SAME fixed original rational point. -/
theorem sample_regularity (w s t : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (sample s w) (sample t w) (unit s+unit t) (unit s*unit t) :=
  distance_congr (.eqRefl _) (.eqRefl _)
    (by ipra_ring) (.eqRefl _)
    (GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (unit_positive s) (unit_positive t)
      (sample_error s w hw) (distance_symmetric _ _ _ _ (unit_positive t) (sample_error t w hw)))

theorem name_regular (w : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx] pointCN nameF w := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] bounded (Syn.shift (Syn.shift w)) one two := by
    simpa [Fm.shift,Syn.shift] using hw.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,sample,unit,Syn.shift] using
    sample_regularity (Syn.shift (Syn.shift w)) (var 1) (var 0) hs

theorem constant_regularity (w s t : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (constant s w) (constant t w) (unit s+unit t) (unit s*unit t) :=
  distance_congr (constant_at s w).eqSymm (constant_at t w).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bound_congr (GaussianCoefficientNormOrder.qsub_self (linearValue w)).eqSymm
      (.eqRefl _) (.eqRefl _)
      (GaussianMonicResidualRadius.zero_bounded _ _ (positive_product _ _ (unit_positive s) (unit_positive t))))

theorem constant_regular (w : PTm n) : Γ ⊢[PRAAx] pointCN constantF w := by
  refine .allI (.allI ?_)
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,constant,unit,Syn.shift] using
    constant_regularity (Γ := (Γ.map Fm.shift).map Fm.shift) (Syn.shift (Syn.shift w)) (var 1) (var 0)

theorem constant_comparison (w s t : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    distanceBounded (sample s w) (constant t w) (unit s+unit t) (unit s*unit t) :=
  distance_congr (.eqRefl _) (constant_at t w).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (unit_positive s) (positive_product _ _ (unit_positive s) (unit_positive t))
      (le_of_eq_add (d := unit s*unit s) (by ipra_ring)) (sample_error s w hw))

theorem name_cross_equivalent (w : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    crossEquivalent nameF constantF w w := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] bounded (Syn.shift (Syn.shift w)) one two := by
    simpa [Fm.shift,Syn.shift] using hw.shift.shift
  simpa only [crossEquivalent,sample,constant,Syn.shift] using
    constant_comparison (Syn.shift (Syn.shift w)) (var 1) (var 0) hs

theorem name_diagonal_equivalent (w : PTm n) (hw : Γ ⊢[PRAAx] bounded w one two) : Γ ⊢[PRAAx]
    diagonalEquivalent nameF constantF w w :=
  GaussianNameEquivalence.cross_to_diagonal _ _ _ _ (name_cross_equivalent w hw)

/-- Original integer-source disk assumptions imply the actual rational
query belongs to the same Euclidean half disk, including raw/R=0 cases. -/
theorem original_half_disk (z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    bounded (ofGaussian z N) one two :=
  GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hN (le_succ_self one)
    (ofGaussian_represents z N hN)
    (le_trans (le_mul_mono (le_refl (two*two)) hz)
      (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono hR hR)))

/-- Literal link to the ORIGINAL finite Gamma logarithm argument, with
both numerical truncation indices computed by the actual name clock. -/
theorem original_sample (p z N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    sample p (ofGaussian z N) ≐ GaussianRationalPolynomialExponential.scalarSum
      (GammaLogarithmFactorBridge.sumArgument z N (clock p)) (clock p) :=
  (sample_at p (ofGaussian z N)).eqTrans
    (GammaLogarithmFactorBridge.composition_at_original_factor z N (clock p) (clock p) hN)

theorem sample_canonical (p w : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample p w) :=
  GaussianRationalHorner.canonical_congr (sample_at p w) (GaussianRationalHorner.horner_canonical _ _ _)

theorem original_name_regular (z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    pointCN nameF (ofGaussian z N) := name_regular _ (original_half_disk z R N hN hz hR)

theorem original_name_equivalent (z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    crossEquivalent nameF constantF (ofGaussian z N) (ofGaussian z N) :=
  name_cross_equivalent _ (original_half_disk z R N hN hz hR)

theorem original_precise_error (p z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    distanceBounded (sample p (ofGaussian z N)) (linearValue (ofGaussian z N)) one (precisionDenominator p) :=
  precise_error p _ (original_half_disk z R N hN hz hR)

/-! Actual PR3 source payload retains the actual original query, its
finite-composition sample, the old finite logarithm argument and clock. -/
def output (p z N : PTm n) : PTm n := pairT (sample p (ofGaussian z N))
  (pairT (GammaLogarithmFactorBridge.sumArgument z N (clock p)) (pairT (clock p) (ofGaussian z N)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (p z N : PTm n) : PTm n := ap3 outputF p z N
ipra_subst output
ipra_subst run

theorem program_at (p z N : PTm n) : Γ ⊢[PRAAx] run p z N ≐ output p z N := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![p,z,N]
theorem returned_sample (p z N : PTm n) : Γ ⊢[PRAAx] fstT (run p z N) ≐ sample p (ofGaussian z N) :=
  (program_at _ _ _).fstE
theorem returned_tail (p z N : PTm n) : Γ ⊢[PRAAx] sndT (run p z N) ≐
    pairT (GammaLogarithmFactorBridge.sumArgument z N (clock p)) (pairT (clock p) (ofGaussian z N)) :=
  (program_at _ _ _).sndE
theorem returned_argument (p z N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p z N)) ≐
    GammaLogarithmFactorBridge.sumArgument z N (clock p) :=
  (returned_tail _ _ _).fstE
theorem returned_pair (p z N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p z N)) ≐ pairT (clock p) (ofGaussian z N) :=
  (returned_tail _ _ _).sndE
theorem returned_clock (p z N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p z N))) ≐ clock p :=
  (returned_pair _ _ _).fstE
theorem returned_query (p z N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p z N))) ≐ ofGaussian z N :=
  (returned_pair _ _ _).sndE
theorem returned_original_evaluation (p z N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    fstT (run p z N) ≐ GaussianRationalPolynomialExponential.scalarSum
      (GammaLogarithmFactorBridge.sumArgument z N (clock p)) (clock p) :=
  (returned_sample _ _ _).eqTrans (original_sample p z N hN)
theorem returned_error (p z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z R) (hR : Γ ⊢[PRAAx] le (two*R) N) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p z N)) (linearValue (ofGaussian z N)) one (precisionDenominator p) :=
  distance_congr (returned_sample _ _ _).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (original_precise_error p z R N hN hz hR)

theorem actual_finite_composition_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sample (var 0) (var 1) ≐ value (var 0) (var 1)) := closeUniv 2 (sample_at _ _)
theorem actual_finite_composition_sample_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalHorner.canonical (sample (var 0) (var 1))) := closeUniv 2 (sample_canonical _ _)
theorem original_half_disk_finite_composition_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (bounded (var 0) one two ⟶ pointCN nameF (var 0)) := closeUniv 1 (.impI (name_regular _ Prf.hyp0))
theorem actual_constant_linear_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN constantF (var 0)) := closeUniv 1 (constant_regular _)
theorem original_half_disk_finite_composition_cross_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (bounded (var 0) one two ⟶ crossEquivalent nameF constantF (var 0) (var 0)) :=
  closeUniv 1 (.impI (name_cross_equivalent _ Prf.hyp0))
theorem original_half_disk_finite_composition_diagonal_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (bounded (var 0) one two ⟶ diagonalEquivalent nameF constantF (var 0) (var 0)) :=
  closeUniv 1 (.impI (name_diagonal_equivalent _ Prf.hyp0))
theorem original_integer_source_named_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ ComplexLogarithmRemainder.bounded (var 0) (var 1) ⟶ le (two*var 1) (var 2) ⟶
      (pointCN nameF (ofGaussian (var 0) (var 2)) ⋏
        crossEquivalent nameF constantF (ofGaussian (var 0) (var 2)) (ofGaussian (var 0) (var 2)))) :=
  closeUniv 3 (.impI (.impI (.impI (.andI
    (original_name_regular _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)
    (original_name_equivalent _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem original_gamma_factor_finite_exponential_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ sample (var 0) (ofGaussian (var 1) (var 2)) ≐
      GaussianRationalPolynomialExponential.scalarSum
        (GammaLogarithmFactorBridge.sumArgument (var 1) (var 2) (clock (var 0))) (clock (var 0))) :=
  closeUniv 3 (.impI (original_sample _ _ _ Prf.hyp0))
theorem actual_named_composition_source_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem original_named_composition_returned_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ ComplexLogarithmRemainder.bounded (var 1) (var 2) ⟶ le (two*var 2) (var 3) ⟶
      distanceBounded (fstT (run (var 0) (var 1) (var 3))) (linearValue (ofGaussian (var 1) (var 3)))
        one (precisionDenominator (var 0))) :=
  closeUniv 4 (.impI (.impI (.impI (returned_error _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianFiniteLogarithmCompositionName
