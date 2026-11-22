import IPRADerivations.Analysis.GaussianRationalModulus
import IPRADerivations.Analysis.AggregateOptimization
import IPRADerivations.Analysis.GaussianCoefficientNormEntries
import IPRADerivations.Foundations.GuardedTotalization

/-!
# The original modulus sampler satisfies the aggregate scalar-map contract

The first two original rational coordinates decode a Gaussian point. Their
actual sup-radius gives a Euclidean radius with the source safe constant
two. The existing modulus samples therefore satisfy the original packed
aggregate approximation contract. A true two-coordinate list constructor
retains the original real and imaginary scalar observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianModulusAggregateMap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalHausdorff (pointRadius coordinateRadius pointRadius_at crossNumerator denominatorProduct)
open RationalSupMetric (numeratorOf denominatorOf rationalNumerator rationalDenominator)
open GaussianRationalHorner (represents scalar_congr scalar_rescale represents_congr positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalL1 (qL1 qL1_represents)
open GaussianL1 (norm1 abs_scale)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianEuclideanPointDistance (unit)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def point (v : PTm n) : PTm n := pairT (entry v zero) (entry v one)
def coordinateBody : PTm 2 := sel (eqb (var 0) zero) (fstT (var 1)) (sndT (var 1))
def vector (z : PTm n) : PTm n := sequence coordinateBody two z
def common (v w : PTm n) : PTm n := denominatorProduct v w zero*denominatorProduct v w one
def scaledValue (v w : PTm n) : PTm n := ComplexLogarithmRemainder.code
  (rationalNumerator v zero*ZT.ofNat (rationalDenominator w zero*denominatorProduct v w one))
  (rationalNumerator v one*ZT.ofNat (rationalDenominator w one*denominatorProduct v w zero))
def differenceValue (v w : PTm n) : PTm n := ComplexLogarithmRemainder.code
  (ZT.ofNat (denominatorProduct v w one)*crossNumerator v w zero)
  (ZT.ofNat (denominatorProduct v w zero)*crossNumerator v w one)
def evaluatorF : PR 3 := PTm.toPR (GaussianRationalModulus.lower (point (var 0)) (var 1))

@[simp] theorem subst_point {l : ℕ} (σ : Fin n → PTm l) (v : PTm n) :
    Syn.subst σ (point v) = point (Syn.subst σ v) := by simp [point]
@[simp] theorem subst_vector {l : ℕ} (σ : Fin n → PTm l) (z : PTm n) :
    Syn.subst σ (vector z) = vector (Syn.subst σ z) := by simp [vector]
@[simp] theorem subst_common {l : ℕ} (σ : Fin n → PTm l) (v w : PTm n) :
    Syn.subst σ (common v w) = common (Syn.subst σ v) (Syn.subst σ w) := by simp [common]

theorem vector_length (z : PTm n) : Γ ⊢[PRAAx] length (vector z) ≐ two := sequence_length _ _ _
theorem vector_zero (z : PTm n) : Γ ⊢[PRAAx] entry (vector z) zero ≐ fstT z := by
  have e := sequence_decode (Γ := Γ) coordinateBody (x := z) (zero_lt_succ one)
  have decoded : Γ ⊢[PRAAx] entry (vector z) zero ≐ sel (eqb zero zero) (fstT z) (sndT z) := by
    simpa [vector,coordinateBody,inst2,sel,one,two] using e
  exact decoded.eqTrans (sel_one (eqb_of_eq (.eqRefl zero)))
theorem vector_one (z : PTm n) : Γ ⊢[PRAAx] entry (vector z) one ≐ sndT z := by
  have e := sequence_decode (Γ := Γ) coordinateBody (x := z) (le_refl two)
  have different : Γ ⊢[PRAAx] neg (one ≐ (zero : PTm n)) := .impI (succ_ne_zero Prf.hyp0)
  have decoded : Γ ⊢[PRAAx] entry (vector z) one ≐ sel (eqb one zero) (fstT z) (sndT z) := by
    simpa [vector,coordinateBody,inst2,sel,one,two] using e
  exact decoded.eqTrans (sel_zero (eqb_of_ne different))

theorem common_positive (v w : PTm n) : Γ ⊢[PRAAx] le one (common v w) :=
  positive_product _ _ (RationalHausdorff.denominatorProduct_one_le v w zero)
    (RationalHausdorff.denominatorProduct_one_le v w one)

theorem point_represents (v w : PTm n) : Γ ⊢[PRAAx] represents (point v) (scaledValue v w) (common v w) := by
  refine .andI ?_ ?_
  · apply scalar_congr (fst_pair _ _).eqSymm ?_ ?_
      (scalar_rescale (entry v zero) (rationalNumerator v zero) (rationalDenominator v zero)
        (rationalDenominator w zero*denominatorProduct v w one) (RationalRepresentations.represents_self _))
    · apply ZT.derive
      simp only [scaledValue,ComplexLogarithmRemainder.eval_re_code]
    · unfold common denominatorProduct
      ipra_ring
  · apply scalar_congr (snd_pair _ _).eqSymm ?_ ?_
      (scalar_rescale (entry v one) (rationalNumerator v one) (rationalDenominator v one)
        (rationalDenominator w one*denominatorProduct v w zero) (RationalRepresentations.represents_self _))
    · apply ZT.derive
      simp only [scaledValue,ComplexLogarithmRemainder.eval_im_code]
    · unfold common denominatorProduct
      ipra_ring

theorem difference_represents (v w : PTm n) : Γ ⊢[PRAAx]
    represents (qsub (point v) (point w)) (differenceValue v w) (common v w) := by
  have right : Γ ⊢[PRAAx] represents (point w) (scaledValue w v) (common v w) :=
    represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_of_values rfl rfl)
      (by unfold common denominatorProduct; ipra_ring) (point_represents w v)
  have raw := GaussianRationalMetric.qsub_represents _ _ _ _ _ (common_positive v w) (point_represents v w) right
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) raw
  apply GaussianRootAlgebra.equal_of_values
  all_goals
    simp only [differenceValue,scaledValue,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,
      ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat,
      crossNumerator,denominatorProduct]
    ipra_simps
    ring

theorem difference_norm1 (v w : PTm n) : Γ ⊢[PRAAx] norm1 (differenceValue v w) ≐
    denominatorProduct v w one*zabs (crossNumerator v w zero)+denominatorProduct v w zero*zabs (crossNumerator v w one) := by
  have re := zabs_congr (Γ := Γ) (ComplexLogarithmRemainder.eval_re_code
    (ZT.ofNat (denominatorProduct v w one)*crossNumerator v w zero)
    (ZT.ofNat (denominatorProduct v w zero)*crossNumerator v w one))
  have im := zabs_congr (Γ := Γ) (ComplexLogarithmRemainder.eval_im_code
    (ZT.ofNat (denominatorProduct v w one)*crossNumerator v w zero)
    (ZT.ofNat (denominatorProduct v w zero)*crossNumerator v w one))
  exact congrAdd (re.eqTrans (abs_scale _ _)) (im.eqTrans (abs_scale _ _))

theorem coordinate_to_euclidean (v w A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] pointRadius v w two A B) : Γ ⊢[PRAAx]
    distanceBounded (point v) (point w) (two*A) B := by
  have real := pointRadius_at v w two A B zero h (zero_lt_succ one)
  have imag := pointRadius_at v w two A B one h (le_refl two)
  have sum := add_le_add₂ (mul_le_mul_right (denominatorProduct v w one) real)
    (mul_le_mul_right (denominatorProduct v w zero) imag)
  have left : Γ ⊢[PRAAx] B*norm1 (differenceValue v w) ≐
      (B*zabs (crossNumerator v w zero))*denominatorProduct v w one+
        (B*zabs (crossNumerator v w one))*denominatorProduct v w zero :=
    (congrMul (.eqRefl B) (difference_norm1 v w)).eqTrans (by ipra_ring)
  have bound : Γ ⊢[PRAAx] le (B*norm1 (differenceValue v w)) ((two*A)*common v w) :=
    le_congr left.eqSymm (by unfold common; ipra_ring) sum
  have l1 := GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ (common_positive v w) hB
    (qL1_represents _ _ _ (common_positive v w) (difference_represents v w)) (fraction_represents _ _ hB) bound
  exact GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ hB l1

theorem evaluator_at (v s x : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF v s x ≐ GaussianRationalModulus.lower (point v) s := by
  simpa [evaluatorF,ap3] using
    toPR_eq (Γ := Γ) (GaussianRationalModulus.lower (point (var 0)) (var 1) : PTm 3) ![v,s,x]

theorem map_instance (x v w s t A B : PTm n) : Γ ⊢[PRAAx]
    AggregateOptimization.mapInstance evaluatorF two two one x v w s t A B := by
  refine .impI ?_
  let Δ := pointRadius v w two A B :: Γ
  refine .orE (zero_or_succ B) ?_ ?_
  · have zero : (B ≐ zero) :: Δ ⊢[PRAAx] AggregateOptimization.errorDenominator one B s t ≐ zero :=
      (congrMul (congrMul (congrMul (.eqRefl one) Prf.hyp0) (.eqRefl _)) (.eqRefl _)).eqTrans (by ipra_ring)
    exact le_congr ((congrMul zero (.eqRefl _)).eqTrans (by ipra_ring)).eqSymm (.eqRefl _) (zero_le _)
  · have positive : (B ≐ succ (LeanProofs.IPRA.PTm.pred B)) :: Δ ⊢[PRAAx] le one B :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (le_of_eq_add (d := LeanProofs.IPRA.PTm.pred B) (by ipra_ring))
    have variation := GaussianRationalModulus.sample_radius _ _ s t (two*A) B positive
      (coordinate_to_euclidean v w A B positive Prf.hyp1)
    exact RationalValueBounds.radius_congr (evaluator_at v s x).eqSymm (evaluator_at w t x).eqSymm
      (by unfold GaussianRationalModulus.errorNumerator AggregateOptimization.errorNumerator GaussianEuclideanPointDistance.unit AggregateEquality.unit; ipra_ring)
      (by unfold GaussianRationalModulus.errorDenominator AggregateOptimization.errorDenominator GaussianEuclideanPointDistance.unit AggregateEquality.unit; ipra_ring) variation

theorem map_contract (x : PTm n) : Γ ⊢[PRAAx] AggregateOptimization.mapContract evaluatorF two two one x := by
  refine .allI ?_
  simpa [Syn.shift,one,two] using map_instance (Γ := Γ.map Fm.shift) (Syn.shift x)
    (AggregateOptimization.argument 0 (var 0)) (AggregateOptimization.argument 1 (var 0))
    (AggregateOptimization.argument 2 (var 0)) (AggregateOptimization.argument 3 (var 0))
    (AggregateOptimization.argument 4 (var 0)) (AggregateOptimization.argument 5 (var 0))

/-! The original Gaussian point is connected through its actual two
scalar observations, rather than a raw outer-code eta assertion. -/

theorem point_vector_fst (z : PTm n) : Γ ⊢[PRAAx] fstT (point (vector z)) ≐ fstT z :=
  (fst_pair _ _).eqTrans (vector_zero z)
theorem point_vector_snd (z : PTm n) : Γ ⊢[PRAAx] sndT (point (vector z)) ≐ sndT z :=
  (snd_pair _ _).eqTrans (vector_one z)
theorem point_vector_represents (z : PTm n) : Γ ⊢[PRAAx]
    represents (point (vector z)) (GaussianRationalL1.rawGaussian z) (GaussianRationalL1.rawDen z) :=
  .andI (scalar_congr (point_vector_fst z).eqSymm (.eqRefl _) (.eqRefl _)
    (.andE₁ (GaussianRationalL1.raw_represents z)))
    (scalar_congr (point_vector_snd z).eqSymm (.eqRefl _) (.eqRefl _)
      (.andE₂ (GaussianRationalL1.raw_represents z)))
theorem point_vector_norm (z : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalMetric.qnormSq (point (vector z)) ≐ GaussianRationalMetric.qnormSq z :=
  GaussianRationalRelativeTwoTerm.norm_of_representations _ _ _ _ (GaussianRationalL1.rawDen z)
    (GaussianRationalL1.raw_den_positive z) (point_vector_represents z) (GaussianRationalL1.raw_represents z) (.eqRefl _)

theorem encoded_modulus_bracket (z s : PTm n) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE
      (RationalArithmetic.multiply (GaussianRationalModulus.lower (point (vector z)) s) (GaussianRationalModulus.lower (point (vector z)) s))
      (GaussianRationalMetric.qnormSq z) ⋏
    RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq z)
      (RationalArithmetic.multiply (GaussianRationalModulus.upper (point (vector z)) s) (GaussianRationalModulus.upper (point (vector z)) s)) :=
  .andI (RationalArgmin.rationalLE_congr (.eqRefl _) (point_vector_norm z) (GaussianRationalModulus.lower_square _ _))
    (RationalArgmin.rationalLE_congr (point_vector_norm z) (.eqRefl _) (GaussianRationalModulus.upper_square _ _))

def vectorF : PR 1 := PTm.toPR (vector (var 0))
theorem vector_at (z : PTm n) : Γ ⊢[PRAAx] ap1 vectorF z ≐ vector z := by
  simpa [vectorF,ap1] using toPR_eq (Γ := Γ) (vector (var 0) : PTm 1) ![z]

theorem actual_gaussian_vector_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (length (vector (var 0)) ≐ two ⋏
      (entry (vector (var 0)) zero ≐ fstT (var 0) ⋏ entry (vector (var 0)) one ≐ sndT (var 0))) :=
  closeUniv 1 (.andI (vector_length _) (.andI (vector_zero _) (vector_one _)))
theorem actual_gaussian_vector_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 vectorF (var 0) ≐ vector (var 0)) := closeUniv 1 (vector_at _)
theorem actual_coordinate_euclidean_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ pointRadius (var 0) (var 1) two (var 2) (var 3) ⟶
      distanceBounded (point (var 0)) (point (var 1)) (two*var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (coordinate_to_euclidean _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_modulus_aggregate_evaluator_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 evaluatorF (var 0) (var 1) (var 2) ≐ GaussianRationalModulus.lower (point (var 0)) (var 1)) :=
  closeUniv 3 (evaluator_at _ _ _)
theorem actual_modulus_map_instance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (AggregateOptimization.mapInstance evaluatorF two two one (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (map_instance _ _ _ _ _ _ _)
theorem actual_modulus_aggregate_contract_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (AggregateOptimization.mapContract evaluatorF two two one (var 0)) := closeUniv 1 (map_contract _)
theorem actual_encoded_point_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (GaussianRationalMetric.qnormSq (point (vector (var 0))) ≐ GaussianRationalMetric.qnormSq (var 0)) :=
  closeUniv 1 (point_vector_norm _)
theorem actual_encoded_modulus_bracket_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (RationalArgmin.rationalLE
      (RationalArithmetic.multiply (GaussianRationalModulus.lower (point (vector (var 0))) (var 1))
        (GaussianRationalModulus.lower (point (vector (var 0))) (var 1))) (GaussianRationalMetric.qnormSq (var 0)) ⋏
      RationalArgmin.rationalLE (GaussianRationalMetric.qnormSq (var 0))
        (RationalArithmetic.multiply (GaussianRationalModulus.upper (point (vector (var 0))) (var 1))
          (GaussianRationalModulus.upper (point (vector (var 0))) (var 1)))) :=
  closeUniv 2 (encoded_modulus_bracket _ _)

end LeanProofs.IPRA.Analysis.GaussianModulusAggregateMap
