import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalDerivativeSum
import IPRADerivations.Analysis.Polynomials.Division.GaussianRationalSyntheticCoefficientValues
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaPolynomialPrimitive

/-!
# A genuine first-order estimate for actual rational Horner polynomials

The ORIGINAL synthetic quotient Q_t satisfies P(t+h)-P(t)=h Q_t(t+h).
Its value Q_t(t) is the actual slope program. The checked finite derivative
sum of the quotient, left-padded by one zero, bounds its variation. This
gives a quadratic remainder with the actual computed rational constant.
Padding retains degree N even for N=0, so no exceptional quotient degree
or nonzero increment is required. All raw point codes are retained.
The unchanged stored Beta primitive is an immediate actual specialization.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalFirstOrderPolynomial

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qmul qadd evaluate canonical)
open GaussianRationalMetric (qsub bounded distanceBounded)
open GaussianRationalSyntheticDivision (quotient qmul_congr qsub_congr)
open GaussianRationalPolynomialBuffers (leftPad)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def paddedQuotient (C t N : PTm n) : PTm n := leftPad (quotient C t N) one
def slope (C t N : PTm n) : PTm n := evaluate (quotient C t N) t
def remainder (C t h N : PTm n) : PTm n :=
  qsub (qsub (evaluate C (qadd t h)) (evaluate C t)) (qmul h (slope C t N))
def numerator (C t N U : PTm n) : PTm n := GaussianRationalDerivativeSum.numerator (paddedQuotient C t N) N U
def denominator (C t N : PTm n) : PTm n := GaussianRationalVariableHornerBudget.denominator (paddedQuotient C t N)
def sizeNumerator (C U : PTm n) : PTm n := GaussianRationalVariableHornerBudget.size C U (length C)
def betaSlope (z B N t : PTm n) : PTm n := slope (GaussianEulerBetaPolynomialPrimitive.primitive z B N) t N
def betaRemainder (z B N t h : PTm n) : PTm n := remainder (GaussianEulerBetaPolynomialPrimitive.primitive z B N) t h N

@[simp] theorem subst_paddedQuotient {m : ℕ} (σ : Fin n → PTm m) (C t N : PTm n) :
    Syn.subst σ (paddedQuotient C t N) = paddedQuotient (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ N) := by simp [paddedQuotient]
@[simp] theorem subst_slope {m : ℕ} (σ : Fin n → PTm m) (C t N : PTm n) :
    Syn.subst σ (slope C t N) = slope (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ N) := by simp [slope]
@[simp] theorem subst_remainder {m : ℕ} (σ : Fin n → PTm m) (C t h N : PTm n) :
    Syn.subst σ (remainder C t h N) = remainder (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ h) (Syn.subst σ N) := by simp [remainder]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (C t N U : PTm n) :
    Syn.subst σ (numerator C t N U) = numerator (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ N) (Syn.subst σ U) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (C t N : PTm n) :
    Syn.subst σ (denominator C t N) = denominator (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ N) := by simp [denominator]

theorem padded_length (C t N : PTm n) : Γ ⊢[PRAAx] length (paddedQuotient C t N) ≐ succ N :=
  (GaussianRationalPolynomialBuffers.pad_length _ _).eqTrans
    ((congrAdd (.eqRefl _) (GaussianRationalSyntheticDivision.quotient_length C t N)).eqTrans (by ipra_ring))
theorem denominator_positive (C t N : PTm n) : Γ ⊢[PRAAx] le one (denominator C t N) :=
  GaussianRationalVariableHornerBudget.denominator_positive _
theorem numerator_positive (C t N U : PTm n) : Γ ⊢[PRAAx] le one (numerator C t N U) :=
  GaussianRationalDerivativeSum.numerator_positive _ _ _
theorem slope_canonical (C t N : PTm n) : Γ ⊢[PRAAx] canonical (slope C t N) := GaussianRationalHorner.horner_canonical _ _ _

/-- Exact actual increment identity, including arbitrary raw h. -/
theorem increment_identity (C t h N : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    qsub (evaluate C (qadd t h)) (evaluate C t) ≐ qmul h (evaluate (quotient C t N) (qadd t h)) :=
  (qsub_congr (GaussianRationalSyntheticDivision.division_evaluation C t (qadd t h) N hLen) (.eqRefl _)).eqTrans
    ((qsub_congr (GaussianReciprocalHorner.qadd_commutative _ _) (.eqRefl _)).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
        ((qmul_congr (GaussianRationalSyntheticCoefficientValues.qadd_sub_recode t h) (.eqRefl _)).eqTrans
          (GaussianRationalSyntheticCoefficientValues.qmul_recode_left _ _))))

theorem remainder_identity (C t h N : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    remainder C t h N ≐ qmul h (qsub (evaluate (quotient C t N) (qadd t h)) (evaluate (quotient C t N) t)) :=
  (qsub_congr (increment_identity C t h N hLen) (.eqRefl _)).eqTrans
    (GaussianRationalRoundedPower.multiplication_difference _ _ _)

theorem increment_distance (t h A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hh : Γ ⊢[PRAAx] bounded h A B) : Γ ⊢[PRAAx]
    distanceBounded (qadd t h) t A B := by
  have old := GaussianRationalMetric.bounded_iff h (GaussianRationalL1.rawGaussian h) (GaussianRationalL1.rawDen h) A B
    (GaussianRationalL1.raw_den_positive h) hB (GaussianRationalL1.raw_represents h)
  have fresh := GaussianRationalMetric.bounded_iff (GaussianTranslatedNonconstant.recode h)
    (GaussianRationalL1.rawGaussian h) (GaussianRationalL1.rawDen h) A B
    (GaussianRationalL1.raw_den_positive h) hB (GaussianTranslatedNonconstant.recode_represents h)
  have recoded : Γ ⊢[PRAAx] bounded (GaussianTranslatedNonconstant.recode h) A B := fresh.iffMpr (old.iffMp hh)
  have actual : Γ ⊢[PRAAx] qsub (qadd t h) t ≐ GaussianTranslatedNonconstant.recode h :=
    GaussianRationalSyntheticCoefficientValues.qadd_sub_recode t h
  exact GaussianRationalReciprocal.bound_congr actual.eqSymm (.eqRefl _) (.eqRefl _) recoded

/-- The actual old derivative-sum constant of the padded original
quotient bounds its true observation variation. -/
theorem quotient_variation (C t h N U A B : PTm n)
    (ht : Γ ⊢[PRAAx] bounded t U one) (hx : Γ ⊢[PRAAx] bounded (qadd t h) U one)
    (hB : Γ ⊢[PRAAx] le one B) (hh : Γ ⊢[PRAAx] bounded h A B) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (quotient C t N) (qadd t h)) (evaluate (quotient C t N) t)
      (numerator C t N U*A) (denominator C t N*B) := by
  let D := paddedQuotient C t N
  have raw := GaussianRationalDerivativeWeights.evaluation_bound D N U (qadd t h) t A B (padded_length C t N) hx ht hB (increment_distance t h A B hB hh)
  have actual := distance_congr (GaussianRationalPolynomialBuffers.pad_evaluation _ one (qadd t h))
    (GaussianRationalPolynomialBuffers.pad_evaluation _ one t) (.eqRefl _) (.eqRefl _) raw
  have den := positive_product (Γ := Γ) _ _ (denominator_positive C t N) hB
  have comparison : Γ ⊢[PRAAx] le
      ((GaussianRationalDerivativeWeights.total D N U*A)*(GaussianRationalVariableHornerBudget.denominator D*B))
      ((GaussianRationalDerivativeSum.numerator D N U*A)*(GaussianRationalVariableHornerBudget.denominator D*B)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (mul_le_mul_right (A*(GaussianRationalVariableHornerBudget.denominator D*B)) (GaussianRationalDerivativeSum.total_le_numerator D N U))
  exact distance_radius_mono _ _ _ _ (GaussianRationalDerivativeSum.numerator D N U*A)
    (GaussianRationalVariableHornerBudget.denominator D*B) den den comparison actual

/-- First-order finite Taylor estimate, with an actual rational constant
and a quadratic increment. No canonical input or nonzero h is required. -/
theorem first_order_bound (C t h N U A B : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (ht : Γ ⊢[PRAAx] bounded t U one) (hx : Γ ⊢[PRAAx] bounded (qadd t h) U one)
    (hB : Γ ⊢[PRAAx] le one B) (hh : Γ ⊢[PRAAx] bounded h A B) : Γ ⊢[PRAAx]
    bounded (remainder C t h N) (numerator C t N U*A*A) (denominator C t N*B*B) := by
  have den := positive_product (Γ := Γ) _ _ (denominator_positive C t N) hB
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hB den hh (quotient_variation C t h N U A B ht hx hB hh)
  exact GaussianRationalReciprocal.bound_congr (remainder_identity C t h N hLen).eqSymm (by ipra_ring) (by ipra_ring) product

/-- Actual finite value and slope budgets on the requested compact disk. -/
theorem value_bound (C t U : PTm n) (ht : Γ ⊢[PRAAx] bounded t U one) : Γ ⊢[PRAAx]
    bounded (evaluate C t) (sizeNumerator C U) (GaussianRationalVariableHornerBudget.denominator C) :=
  GaussianRationalVariableHornerBudget.size_prefix C U t (length C) ht (le_refl _)
theorem slope_bound (C t N U : PTm n) (ht : Γ ⊢[PRAAx] bounded t U one) : Γ ⊢[PRAAx]
    bounded (slope C t N) (sizeNumerator (paddedQuotient C t N) U) (denominator C t N) :=
  GaussianRationalReciprocal.bound_congr (GaussianRationalPolynomialBuffers.pad_evaluation _ one t) (.eqRefl _) (.eqRefl _)
    (value_bound (paddedQuotient C t N) t U ht)

/-- SAME unchanged Beta primitive and SAME raw increment/query programs. -/
theorem beta_first_order_bound (z B N t h U A D : PTm n)
    (ht : Γ ⊢[PRAAx] bounded t U one) (hx : Γ ⊢[PRAAx] bounded (qadd t h) U one)
    (hD : Γ ⊢[PRAAx] le one D) (hh : Γ ⊢[PRAAx] bounded h A D) : Γ ⊢[PRAAx]
    bounded (betaRemainder z B N t h) (numerator (GaussianEulerBetaPolynomialPrimitive.primitive z B N) t N U*A*A) (denominator (GaussianEulerBetaPolynomialPrimitive.primitive z B N) t N*D*D) := by
  exact first_order_bound (GaussianEulerBetaPolynomialPrimitive.primitive z B N) t h N U A D
    (GaussianEulerBetaPolynomialPrimitive.primitive_length z B N) ht hx hD hh

/-- The actual slope, exact remainder, and old computed constant are
returned together, with no additional recursive evaluator. -/
def output (C t h N U : PTm n) : PTm n := pairT (slope C t N)
  (pairT (remainder C t h N) (pairT (numerator C t N U) (denominator C t N)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (C t h N U : PTm n) : PTm n := PTm.app outputF ![C,t,h,N,U]
theorem program_at (C t h N U : PTm n) : Γ ⊢[PRAAx] run C t h N U ≐ output C t h N U := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![C,t,h,N,U]

theorem actual_polynomial_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 3) ⟶
      qsub (evaluate (var 0) (qadd (var 1) (var 2))) (evaluate (var 0) (var 1)) ≐
        qmul (var 2) (evaluate (quotient (var 0) (var 1) (var 3)) (qadd (var 1) (var 2)))) :=
  closeUniv 4 (.impI (increment_identity _ _ _ _ Prf.hyp0))
theorem actual_polynomial_quadratic_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((length (var 0) ≐ succ (var 3) ⋏ bounded (var 1) (var 4) one ⋏ bounded (qadd (var 1) (var 2)) (var 4) one ⋏
      le one (var 6) ⋏ bounded (var 2) (var 5) (var 6)) ⟶
      bounded (remainder (var 0) (var 1) (var 2) (var 3))
        (numerator (var 0) (var 1) (var 3) (var 4)*var 5*var 5)
        (denominator (var 0) (var 1) (var 3)*var 6*var 6)) :=
  closeUniv 7 (.impI (first_order_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))
theorem original_Beta_primitive_quadratic_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((bounded (var 3) (var 5) one ⋏ bounded (qadd (var 3) (var 4)) (var 5) one ⋏ le one (var 7) ⋏ bounded (var 4) (var 6) (var 7)) ⟶
      bounded (betaRemainder (var 0) (var 1) (var 2) (var 3) (var 4))
        (numerator (GaussianEulerBetaPolynomialPrimitive.primitive (var 0) (var 1) (var 2)) (var 3) (var 2) (var 5)*var 6*var 6)
        (denominator (GaussianEulerBetaPolynomialPrimitive.primitive (var 0) (var 1) (var 2)) (var 3) (var 2)*var 7*var 7)) :=
  closeUniv 8 (.impI (beta_first_order_bound _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_first_order_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalFirstOrderPolynomial
