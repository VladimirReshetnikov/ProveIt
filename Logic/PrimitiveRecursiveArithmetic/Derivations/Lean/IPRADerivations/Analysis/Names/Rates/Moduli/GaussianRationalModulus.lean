import IPRADerivations.Analysis.Geometry.Distances.GaussianEuclideanDistanceName
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalRelativeTwoTerm
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianRationalMonicReduction

/-!
# Actual nonnegative modulus samples of original Gaussian rational points

The existing Euclidean integer-square-root sampler is applied to the actual
singleton containing zero. Its two rational endpoints bracket the original
point norm and have a dyadic width. Original Euclidean point comparisons
give the scalar sample variation with the same radius plus sample errors.
No square-root, interval, Lipschitz or output law is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalModulus

open_ipra
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (qsub qnormSq distanceBounded)
open GaussianEuclideanPointDistance (unit unit_positive)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMonicReduction (singleton singleton_length singleton_lookup)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (add multiply negative)
open RationalSupMetric (numeratorOf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def zeroList : PTm n := singleton qzero
def lower (q s : PTm n) : PTm n := GaussianEuclideanPointDistance.lower q zeroList s
def upper (q s : PTm n) : PTm n := GaussianEuclideanPointDistance.upper q zeroList s
def denominator (q : PTm n) : PTm n := GaussianEuclideanPointDistance.denominator q zeroList
def root (q s : PTm n) : PTm n := GaussianEuclideanPointDistance.root q zeroList s

ipra_subst zeroList
ipra_subst lower
ipra_subst upper
ipra_subst denominator
ipra_subst root

theorem zero_list_nonempty : Γ ⊢[PRAAx] le one (length (zeroList : PTm n)) :=
  le_congr (.eqRefl _) (singleton_length qzero).eqSymm (le_refl one)

theorem selected_zero (q : PTm n) :
    Γ ⊢[PRAAx] GaussianEuclideanPointDistance.selected q zeroList ≐ zero := by
  have bound := lt_congr (.eqRefl _) (singleton_length (Γ := Γ) qzero)
    (GaussianEuclideanPointDistance.selected_range q zeroList zero_list_nonempty)
  exact le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans bound) (zero_le _)

theorem selected_point_zero (q : PTm n) : Γ ⊢[PRAAx]
    entry zeroList (GaussianEuclideanPointDistance.selected q zeroList) ≐ qzero :=
  (entry_congr (.eqRefl _) (selected_zero q)).eqTrans (singleton_lookup qzero)

theorem norm_sub_zero (q : PTm n) : Γ ⊢[PRAAx] qnormSq (qsub q qzero) ≐ qnormSq q := by
  apply GaussianRationalRelativeTwoTerm.norm_of_representations _ _ _ _ (rawDen q) (raw_den_positive q)
    (GaussianRationalMetric.qsub_represents _ _ _ _ _ (raw_den_positive q)
      (raw_represents q) (GaussianRationalHorner.zero_represents _)) (raw_represents q)
  apply GaussianRootAlgebra.normSq_equal
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
    GaussianRootAlgebra.re_zero,GaussianRootAlgebra.im_zero]; ring

theorem squared_minimum (q : PTm n) : Γ ⊢[PRAAx]
    GaussianEuclideanPointDistance.squaredDistance q zeroList ≐ qnormSq q :=
  (GaussianRationalProductWitness.qnormSq_congr
    (GaussianRationalSyntheticDivision.qsub_congr (.eqRefl q) (selected_point_zero q))).eqTrans (norm_sub_zero q)

theorem denominator_positive (q : PTm n) : Γ ⊢[PRAAx] le one (denominator q) :=
  GaussianEuclideanPointDistance.denominator_positive q zeroList
theorem sample_denominator_positive (q s : PTm n) : Γ ⊢[PRAAx] le one (denominator q*unit s) :=
  positive_product _ _ (denominator_positive q) (unit_positive s)
theorem lower_represents (q s : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (lower q s) (ZT.ofNat (root q s)) (denominator q*unit s) :=
  GaussianEuclideanPointDistance.lower_represents q zeroList s
theorem upper_represents (q s : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (upper q s) (ZT.ofNat (succ (root q s))) (denominator q*unit s) :=
  GaussianEuclideanPointDistance.upper_represents q zeroList s
theorem lower_canonical (q s : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (lower q s) :=
  RationalNormalForm.normalize_well_formed _ _ (sample_denominator_positive q s)
theorem upper_canonical (q s : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (upper q s) :=
  RationalNormalForm.normalize_well_formed _ _ (sample_denominator_positive q s)
theorem lower_nonnegative (q s : PTm n) : Γ ⊢[PRAAx] le (numeratorOf (lower q s)).neg (numeratorOf (lower q s)).pos :=
  GaussianEuclideanPointDistance.lower_nonnegative q zeroList s
theorem upper_nonnegative (q s : PTm n) : Γ ⊢[PRAAx] le (numeratorOf (upper q s)).neg (numeratorOf (upper q s)).pos :=
  GaussianEuclideanPointDistance.upper_nonnegative q zeroList s

theorem lower_square (q s : PTm n) : Γ ⊢[PRAAx] rationalLE (multiply (lower q s) (lower q s)) (qnormSq q) :=
  rationalLE_congr (.eqRefl _) (squared_minimum q) (GaussianEuclideanPointDistance.lower_square q zeroList s)
theorem upper_square (q s : PTm n) : Γ ⊢[PRAAx] rationalLE (qnormSq q) (multiply (upper q s) (upper q s)) :=
  rationalLE_congr (squared_minimum q) (.eqRefl _) (GaussianEuclideanPointDistance.upper_square q zeroList s)

theorem interval_order (q s : PTm n) : Γ ⊢[PRAAx] rationalLE (lower q s) (upper q s) :=
  GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (sample_denominator_positive q s)
    (sample_denominator_positive q s) (lower_represents q s) (upper_represents q s)
    (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (denominator q*unit s) (le_succ_self _)))

theorem interval_width (q s : PTm n) : Γ ⊢[PRAAx]
    add (upper q s) (negative (lower q s)) ≐ fraction one (denominator q*unit s) := by
  have hp := sample_denominator_positive (Γ := Γ) q s
  have rep := GaussianRationalHorner.scalar_add_same _ _ _ _ _ hp (upper_represents q s)
    (RationalRepresentations.represents_negative _ _ _ (lower_represents q s))
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hp) rep (fraction_represents _ _ hp) hp hp
  ipra_lc

theorem interval_width_bound (q s : PTm n) : Γ ⊢[PRAAx]
    rationalLE (add (upper q s) (negative (lower q s))) (fraction one (unit s)) :=
  rationalLE_congr (interval_width q s).eqSymm (.eqRefl _)
    (GaussianEuclideanDistanceName.fraction_order _ _ _ _ (sample_denominator_positive q s) (unit_positive s)
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (unit s) (denominator_positive q))))

/-- The original Euclidean radius is preserved; only the other endpoint's
actual square-root precision contributes the one-sided sampling error. -/
theorem sample_upper (q r s t A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (lower q s) (lower r t) (A*unit t+B) (B*unit t) :=
  GaussianEuclideanDistanceName.lower_variation q r zeroList s t A B zero_list_nonempty hB h

def errorNumerator (A B s t : PTm n) : PTm n := A*unit s*unit t+B*(unit s+unit t)
def errorDenominator (B s t : PTm n) : PTm n := B*unit s*unit t
ipra_subst errorNumerator
ipra_subst errorDenominator

theorem sample_radius (q r s t A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (lower q s) (lower r t) (errorNumerator A B s t) (errorDenominator B s t) := by
  have first := RationalValueBounds.upper_mono (lower q s) (lower r t) (A*unit t+B) (B*unit t)
    (errorNumerator A B s t) (errorDenominator B s t) (positive_product _ _ hB (unit_positive t))
    (sample_upper q r s t A B hB h)
    (le_of_eq_add (d := B*B*unit t*unit t) (by unfold errorNumerator errorDenominator; ipra_ring))
  have second := RationalValueBounds.upper_mono (lower r t) (lower q s) (A*unit s+B) (B*unit s)
    (errorNumerator A B s t) (errorDenominator B s t) (positive_product _ _ hB (unit_positive s))
    (sample_upper r q t s A B hB (GaussianRationalDistanceOrder.distance_symmetric q r A B hB h))
    (le_of_eq_add (d := B*B*unit s*unit s) (by unfold errorNumerator errorDenominator; ipra_ring))
  exact RationalValueBounds.radius_of_upper _ _ _ _ first second

def sampleF : PR 2 := PTm.toPR (lower (var 0) (var 1))
def evaluatorF : PR 3 := PTm.toPR (lower (var 0) (var 1))
def output (q s : PTm n) : PTm n := pairT (lower q s) (pairT (upper q s) (qnormSq q))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (q s : PTm n) : PTm n := ap2 outputF q s
ipra_subst output
ipra_subst run

theorem sample_at (q s : PTm n) : Γ ⊢[PRAAx] ap2 sampleF q s ≐ lower q s := by
  simpa [sampleF,ap2] using toPR_eq (Γ := Γ) (lower (var 0) (var 1) : PTm 2) ![q,s]
theorem evaluator_at (q s x : PTm n) : Γ ⊢[PRAAx] ap3 evaluatorF q s x ≐ lower q s := by
  simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (lower (var 0) (var 1) : PTm 3) ![q,s,x]
theorem program_at (q s : PTm n) : Γ ⊢[PRAAx] run q s ≐ output q s := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![q,s]
theorem returned_lower (q s : PTm n) : Γ ⊢[PRAAx] fstT (run q s) ≐ lower q s :=
  (program_at q s).fstE
theorem returned_upper (q s : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run q s)) ≐ upper q s :=
  (program_at q s).sndE.fstE
theorem returned_norm_square (q s : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run q s)) ≐ qnormSq q :=
  (program_at q s).sndE.sndE
theorem returned_bracket (q s : PTm n) : Γ ⊢[PRAAx]
    rationalLE (multiply (fstT (run q s)) (fstT (run q s))) (sndT (sndT (run q s))) ⋏
      rationalLE (sndT (sndT (run q s))) (multiply (fstT (sndT (run q s))) (fstT (sndT (run q s)))) :=
  .andI (rationalLE_congr (RationalAlgebra.multiply_congr (returned_lower q s) (returned_lower q s)).eqSymm
    (returned_norm_square q s).eqSymm (lower_square q s))
    (rationalLE_congr (returned_norm_square q s).eqSymm
      (RationalAlgebra.multiply_congr (returned_upper q s) (returned_upper q s)).eqSymm (upper_square q s))

theorem actual_modulus_bracket_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (multiply (lower (var 0) (var 1)) (lower (var 0) (var 1))) (qnormSq (var 0)) ⋏
      rationalLE (qnormSq (var 0)) (multiply (upper (var 0) (var 1)) (upper (var 0) (var 1)))) :=
  closeUniv 2 (.andI (lower_square _ _) (upper_square _ _))
theorem actual_modulus_nonnegative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le (numeratorOf (lower (var 0) (var 1))).neg (numeratorOf (lower (var 0) (var 1))).pos ⋏
      le (numeratorOf (upper (var 0) (var 1))).neg (numeratorOf (upper (var 0) (var 1))).pos) :=
  closeUniv 2 (.andI (lower_nonnegative _ _) (upper_nonnegative _ _))
theorem actual_modulus_interval_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (add (upper (var 0) (var 1)) (negative (lower (var 0) (var 1))) ≐ fraction one (denominator (var 0)*unit (var 1))) :=
  closeUniv 2 (interval_width _ _)
theorem actual_modulus_dyadic_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (add (upper (var 0) (var 1)) (negative (lower (var 0) (var 1)))) (fraction one (unit (var 1)))) :=
  closeUniv 2 (interval_width_bound _ _)
theorem actual_modulus_sample_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 5) ⟶ distanceBounded (var 0) (var 1) (var 4) (var 5) ⟶
      RationalValueBounds.radius (lower (var 0) (var 2)) (lower (var 1) (var 3))
        (errorNumerator (var 4) (var 5) (var 2) (var 3)) (errorDenominator (var 5) (var 2) (var 3))) :=
  closeUniv 6 (.impI (.impI (sample_radius _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_modulus_sample_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 sampleF (var 0) (var 1) ≐ lower (var 0) (var 1)) := closeUniv 2 (sample_at _ _)
theorem actual_modulus_evaluator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 evaluatorF (var 0) (var 1) (var 2) ≐ lower (var 0) (var 1)) := closeUniv 3 (evaluator_at _ _ _)
theorem actual_modulus_interval_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)
theorem actual_returned_modulus_bracket_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (rationalLE (multiply (fstT (run (var 0) (var 1))) (fstT (run (var 0) (var 1)))) (sndT (sndT (run (var 0) (var 1)))) ⋏
      rationalLE (sndT (sndT (run (var 0) (var 1))))
        (multiply (fstT (sndT (run (var 0) (var 1)))) (fstT (sndT (run (var 0) (var 1)))))) :=
  closeUniv 2 (returned_bracket _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalModulus
