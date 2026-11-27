import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaShift
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianGammaShiftTrajectory
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScale

/-!
# Actual Gamma factorial values by a numerical error induction

The same native successor trajectory retains the literal original
shift constructor. Every stage has its original positive-integer pole
guard. A fixed-precision numerical QF error invariant propagates the
actual multiplication-normalizer loss; no name predicate is inducted.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFactorialValues

open_ipra
open GaussianGammaReciprocalInverse (gammaF gammaData gammaHeight gamma_regular)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerHeadShift (shifted)
open GaussianRationalHorner (ofGaussian canonical_unique represents_congr)
open GaussianRationalNaturalScale (naturalPoint natural_point_represents)
open GaussianRationalMetric (distanceBounded bounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent)
open ComplexLogarithmRemainder (oneCode scale normSq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def argument (i : PTm n) : PTm n := GaussianGammaShiftTrajectory.point oneCode one i
def radius (i : PTm n) : PTm n := one+i
def data (i : PTm n) : PTm n := gammaData (argument i) (radius i) one one
def value (p i : PTm n) : PTm n := ap2 gammaF p (data i)
def scalarArgument (i : PTm n) : PTm n := ofGaussian (argument i) one
def factorialValue (i : PTm n) : PTm n := naturalPoint (Products.fact i)
def modulus (i : PTm n) : PTm n := GaussianNameArithmetic.multiplyModulus constantF gammaF (scalarArgument i) (data i)
def errorF : PR 2 := rec2 (two : PTm 1) (succ (var 0)*var 1+two+(modulus (var 0)+one))
def error (i : PTm n) : PTm n := ap2 errorF i zero
def errorLaw (p i : PTm n) : Fm PTm n := distanceBounded (value p i) (factorialValue i) (error i) (unit p)
ipra_subst argument
ipra_subst radius
ipra_subst data [gammaData, gammaHeight]
ipra_subst value
ipra_subst scalarArgument
ipra_subst factorialValue [Products.fact]
ipra_subst modulus
ipra_subst error
ipra_subst errorLaw

theorem scalar_argument (i : PTm n) : Γ ⊢[PRAAx] scalarArgument i ≐ naturalPoint (succ i) := by
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (argument i) (GaussianGammaEulerHeadLower.translated oneCode one i) :=
    GaussianGammaShiftTrajectory.point_native oneCode one i
  apply canonical_unique _ _ _ one (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _))
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (le_refl _) _ (natural_point_represents _)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) (GaussianRationalHorner.ofGaussian_represents (argument i) one (le_refl _))
  apply GaussianRootAlgebra.equal_of_values
  · rw [GaussianRootAlgebra.equal_re native]
    simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.re_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
    ipra_simps
    ring
  · rw [GaussianRootAlgebra.equal_im native]
    simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.im_add,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.im_one]
    ring

theorem integer_pole_norm (i k : PTm n) : Γ ⊢[PRAAx]
    normSq (GaussianGammaEulerHeadLower.translated (argument i) one k) ≐ succ (i+k)*succ (i+k) := by
  have native : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (argument i) (GaussianGammaEulerHeadLower.translated oneCode one i) :=
    GaussianGammaShiftTrajectory.point_native oneCode one i
  apply deriveNat
  ipra_simps
  rw [ComplexLogarithmRemainder.normSq_eval]
  simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  rw [GaussianRootAlgebra.equal_re native,GaussianRootAlgebra.equal_im native]
  simp only [GaussianGammaEulerHeadLower.translated,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
    GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  ipra_simps
  ring

theorem integer_pole_at (i k : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaEulerHeadLower.poleAt (argument i) one one one k :=
  le_congr (by ipra_ring) ((congrMul (.eqRefl _) (integer_pole_norm i k)).eqTrans (by ipra_ring)).eqSymm
    (sq_le_sq (zero_lt_succ (i+k)))

theorem integer_pole_guard (i N : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaEulerHeadLower.poleGuard (argument i) one one one N := by
  refine .allI (.impI ?_)
  simpa only [GaussianGammaEulerHeadLower.poleGuard,Syn.shift,subst_argument,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    integer_pole_at (Γ := le (var 0) (Syn.shift N) :: Γ.map Fm.shift) (Syn.shift i) (var 0)

theorem integer_source (i : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaReciprocalInverse.source (argument i) (radius i) one one one :=
  .andI (GaussianGammaShiftTrajectory.point_source oneCode one one i GaussianGammaNormalization.unit_source)
    (.andI (le_refl _) (.andI (le_refl _) (integer_pole_guard i _)))

theorem gamma_fields_congr {z R B d a S C e : PTm n} (hz : Γ ⊢[PRAAx] z ≐ a) (hR : Γ ⊢[PRAAx] R ≐ S)
    (hB : Γ ⊢[PRAAx] B ≐ C) (hd : Γ ⊢[PRAAx] d ≐ e) : Γ ⊢[PRAAx]
    gammaData z R B d ≐ gammaData a S C e := by
  ipra_congr (gammaData (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hz, hR, hB, hd] using [gammaData, gammaHeight]

theorem data_zero : Γ ⊢[PRAAx] data (zero : PTm n) ≐ gammaData oneCode one one one :=
  gamma_fields_congr (GaussianGammaShiftTrajectory.point_zero oneCode one) (by unfold radius; ipra_ring) (.eqRefl _) (.eqRefl _)
theorem data_succ (i : PTm n) : Γ ⊢[PRAAx]
    data (succ i) ≐ gammaData (shifted (argument i) one) (radius i+one) one one :=
  gamma_fields_congr (GaussianGammaShiftTrajectory.point_succ oneCode one i) (by unfold radius; ipra_ring) (.eqRefl _) (.eqRefl _)

theorem integer_shift_input (i : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaShift.input (argument i) (radius i) one one one one one := by
  refine .andI (integer_source i) (.andI (le_refl _) (.andI (le_refl _) ?_))
  have old := integer_pole_guard (Γ := Γ) (succ i) (two*(radius i+one))
  have transported := Prf.eqSubst (Γ := Γ) (Ax := PRAAx)
    (GaussianGammaEulerHeadLower.poleGuard (var 0) one one one (var 1) : Fm PTm 2)
    ![argument (succ i),two*(radius i+one)] ![shifted (argument i) one,two*(radius i+one)]
    (fun j => by fin_cases j; exact GaussianGammaShiftTrajectory.point_succ oneCode one i; exact .eqRefl _)
    (by simpa using old)
  simpa using transported

theorem value_regular (i : PTm n) : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN gammaF (data i) :=
  gamma_regular _ _ _ _ _ (integer_source i)

theorem error_zero : Γ ⊢[PRAAx] error (zero : PTm n) ≐ two := by
  simpa only [error,errorF,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    rec2_zero (Γ := Γ) (two : PTm 1) (succ (var 0)*var 1+two+(modulus (var 0)+one)) zero

theorem error_succ (i : PTm n) : Γ ⊢[PRAAx] error (succ i) ≐ succ i*error i+two+(modulus i+one) := by
  have h := rec2_succ (Γ := Γ) (two : PTm 1) (succ (var 0)*var 1+two+(modulus (var 0)+one)) i zero
  simp only [PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,subst_modulus,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    one,two,ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem natural_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] naturalPoint a ≐ naturalPoint b :=
  GaussianRationalHorner.real_fraction_congr h (.eqRefl _)

theorem natural_one : Γ ⊢[PRAAx] naturalPoint (one : PTm n) ≐ GaussianRationalSyntheticDivision.qone := by
  apply canonical_unique _ _ _ one (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _))
    GaussianRationalSyntheticDivision.qone_canonical (le_refl _) _ (GaussianRationalHorner.ofGaussian_represents _ _ (le_refl _))
  apply represents_congr (.eqRefl _) _ (.eqRefl _) (natural_point_represents one)
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals ipra_simps; ring

theorem natural_product (a b : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.qmul (naturalPoint a) (naturalPoint b) ≐ naturalPoint (a*b) := by
  have rep := GaussianRationalHorner.qmul_represents (Γ := Γ) _ _ _ _ _ _ (le_refl one) (le_refl one)
    (natural_point_represents a) (natural_point_represents b)
  apply canonical_unique _ _ _ one (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)) (le_refl _) _ (natural_point_represents _)
  apply represents_congr (.eqRefl _) _ (one_mul one) rep
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_mul,GaussianRootAlgebra.im_mul,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
      GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one]
  all_goals ipra_simps; ring

theorem factorial_zero : Γ ⊢[PRAAx] factorialValue (zero : PTm n) ≐ GaussianRationalSyntheticDivision.qone :=
  (natural_congr (fact_zero zero)).eqTrans natural_one

theorem factorial_multiply (i : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.qmul (scalarArgument i) (factorialValue i) ≐ factorialValue (succ i) :=
  (GaussianRationalSyntheticDivision.qmul_congr (scalar_argument i) (.eqRefl _)).eqTrans
    ((natural_product (succ i) (Products.fact i)).eqTrans
      (natural_congr ((mul_comm _ _).eqTrans (fact_succ i zero).eqSymm)))

theorem factorial_bound (i : PTm n) : Γ ⊢[PRAAx] bounded (factorialValue i) (Products.fact i) one :=
  GaussianNamedNaturalScale.natural_point_bound _
theorem argument_bound (i : PTm n) : Γ ⊢[PRAAx] bounded (scalarArgument i) (succ i) one :=
  GaussianRationalReciprocal.bound_congr (scalar_argument i).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianNamedNaturalScale.natural_point_bound _)

theorem successor_product_error (p i : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (value p (succ i)) (GaussianRationalHorner.qmul (scalarArgument i) (value p i))
      (two+(modulus i+one)) (unit p) := by
  let X := GaussianGammaShift.shiftData (argument i) (radius i) one one
  have hshift := GaussianGammaShift.C21_Gamma_shift (Γ := Γ) (argument i) (radius i) one one one one one (integer_shift_input i)
  have hcross := GaussianNameEquivalence.cross_diagonal_at p hshift
  have left : Γ ⊢[PRAAx] value p (succ i) ≐ ap2 gammaF p (gammaData (shifted (argument i) one) (radius i+one) one one) :=
    congrAp2 gammaF (.eqRefl _) (data_succ i)
  have first : Γ ⊢[PRAAx] distanceBounded (value p (succ i)) (ap2 GaussianGammaShift.shiftF p X) two (unit p) :=
    distance_congr left.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) hcross
  have raw := GaussianNameRingLaws.multiply_sample_error (Γ := Γ) constantF gammaF (scalarArgument i) (data i) p
    (constant_regular _) (value_regular i)
  have second : Γ ⊢[PRAAx] distanceBounded (ap2 GaussianGammaShift.shiftF p X)
      (GaussianRationalHorner.qmul (scalarArgument i) (value p i)) (modulus i+one) (unit p) :=
    distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p (scalarArgument i)) (.eqRefl _))
      (.eqRefl _) (.eqRefl _) raw
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second

theorem error_base (p : PTm n) : Γ ⊢[PRAAx] errorLaw p zero := by
  have original := GaussianNameEquivalence.cross_diagonal_at (Γ := Γ) p GaussianRobinMeshExponential.C21_Gamma_one
  have left : Γ ⊢[PRAAx] value p zero ≐ ap2 gammaF p (gammaData oneCode one one one) := congrAp2 gammaF (.eqRefl _) data_zero
  have right : Γ ⊢[PRAAx] ap2 GaussianNameRingLaws.oneF p zero ≐ factorialValue zero :=
    (GaussianNameRingLaws.one_at p zero).eqTrans factorial_zero.eqSymm
  exact distance_congr left.eqSymm right error_zero.eqSymm (.eqRefl _) original

theorem error_step (p i : PTm n) (ih : Γ ⊢[PRAAx] errorLaw p i) : Γ ⊢[PRAAx] errorLaw p (succ i) := by
  have raw := GaussianNameRingLaws.product_right_error (scalarArgument i) (value p i) (factorialValue i)
    (error i) (unit p) (GaussianNameBounds.U gammaF (data i)) (succ i) (unit_positive p) ih
    (GaussianNameBounds.sample_bound gammaF (data i) p (value_regular i)) (argument_bound i)
  have next := distance_congr (.eqRefl _) (factorial_multiply i) (.eqRefl _) (.eqRefl _) raw
  have joined := distance_triangle_same _ _ _ _ _ _ (unit_positive p) (successor_product_error p i) next
  have budget : Γ ⊢[PRAAx] two+(modulus i+one)+succ i*error i ≐ error (succ i) :=
    (by ipra_ring : Γ ⊢[PRAAx] two+(modulus i+one)+succ i*error i ≐ succ i*error i+two+(modulus i+one)).eqTrans
      (error_succ i).eqSymm
  exact distance_congr (.eqRefl _) (.eqRefl _) budget (.eqRefl _) joined

/-- Every induction instance fixes the original observation p. The
inducted formula is one actual numerical Euclidean error predicate. -/
theorem prefix_error (p i : PTm n) : Γ ⊢[PRAAx] errorLaw p i := by
  have hall : Γ ⊢[PRAAx] .all (errorLaw (Syn.shift p) (var 0)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using error_base (Γ := Γ) p
    · simpa only [subst_errorLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using error_step (Syn.shift p) (var 0) Prf.hyp0
  simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i

theorem factorial_envelope (i : PTm n) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal gammaF constantF (data i) (factorialValue i) (error i) := by
  refine .allI ?_
  have finite := prefix_error (Γ := Γ.map Fm.shift) (var 0) (Syn.shift i)
  have actual := distance_congr (.eqRefl _) (constant_at (var 0) (factorialValue (Syn.shift i))).eqSymm (.eqRefl _) (.eqRefl _) finite
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,value,subst_data,subst_factorialValue,subst_error,Syn.shift] using actual

theorem original_C21_factorial (i : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent gammaF constantF (data i) (factorialValue i) :=
  GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (error i) (value_regular i) (constant_regular _) (factorial_envelope i)


/-- The same numerical index returns its actual original argument code,
original Gamma observation, actual factorial value and actual error budget. -/
def output (p i : PTm n) : PTm n := pairT (argument i)
  (pairT (value p i) (pairT (factorialValue i) (error i)))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (p i : PTm n) : PTm n := ap2 outputF p i
ipra_subst output
ipra_subst run

theorem program_at (p i : PTm n) : Γ ⊢[PRAAx] run p i ≐ output p i := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![p,i]
theorem returned_argument (p i : PTm n) : Γ ⊢[PRAAx] fstT (run p i) ≐ argument i :=
  (program_at p i).fstE
theorem returned_Gamma (p i : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p i)) ≐ value p i :=
  ((congrFst (congrSnd (program_at p i))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_factorial (p i : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p i))) ≐ factorialValue i :=
  (((congrFst (congrSnd (congrSnd (program_at p i)))).eqTrans
    (congrFst (congrSnd (snd_pair _ _)))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_budget (p i : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p i))) ≐ error i :=
  (((congrSnd (congrSnd (congrSnd (program_at p i)))).eqTrans
    (congrSnd (congrSnd (snd_pair _ _)))).eqTrans (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_numerical_error (p i : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (fstT (sndT (run p i))) (fstT (sndT (sndT (run p i)))) (sndT (sndT (sndT (run p i)))) (unit p) :=
  distance_congr (returned_Gamma p i).eqSymm (returned_factorial p i).eqSymm (returned_budget p i).eqSymm (.eqRefl _)
    (prefix_error p i)

theorem actual_original_positive_integer_argument_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (scalarArgument (var 0) ≐ naturalPoint (succ (var 0))) := closeUniv 1 (scalar_argument _)

theorem original_positive_integer_pole_guards_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianGammaEulerHeadLower.poleGuard (argument (var 0)) one one one (var 1)) := closeUniv 2 (integer_pole_guard _ _)

theorem actual_original_Gamma_successor_data_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (data (succ (var 0)) ≐ gammaData (shifted (argument (var 0)) one) (radius (var 0)+one) one one) :=
  closeUniv 1 (data_succ _)

theorem actual_factorial_error_budget_recursion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (error zero ≐ two ⋏ error (succ (var 0)) ≐ succ (var 0)*error (var 0)+two+(modulus (var 0)+one)) :=
  closeUniv 1 (.andI error_zero (error_succ _))

theorem original_Gamma_factorial_numerical_prefix_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (distanceBounded (value (var 0) (var 1)) (factorialValue (var 1)) (error (var 1)) (unit (var 0))) :=
  closeUniv 2 (prefix_error _ _)

theorem original_C21_Gamma_factorial_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (crossEquivalent gammaF constantF (data (var 0)) (naturalPoint (Products.fact (var 0)))) :=
  closeUniv 1 (original_C21_factorial _)

theorem actual_Gamma_factorial_value_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (run (var 0) (var 1) ≐ output (var 0) (var 1)) := closeUniv 2 (program_at _ _)

theorem actual_returned_original_factorial_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (fstT (run (var 0) (var 1)) ≐ argument (var 1) ⋏
      distanceBounded (fstT (sndT (run (var 0) (var 1)))) (fstT (sndT (sndT (run (var 0) (var 1)))))
        (sndT (sndT (sndT (run (var 0) (var 1))))) (unit (var 0))) :=
  closeUniv 2 (.andI (returned_argument _ _) (returned_numerical_error _ _))

end LeanProofs.IPRA.Analysis.GaussianGammaFactorialValues
