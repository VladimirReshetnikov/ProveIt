import IPRADerivations.Analysis.Euler.Integration.Incomplete.IntegerValues.GaussianEulerIncompleteIntegerStep
import IPRADerivations.Analysis.Euler.Integration.Incomplete.IntegerValues.GaussianEulerIncompleteFactorialCombination
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteUnitUpper

/-!
# The original upper incomplete Gamma factorial formula

At fixed precision, the numerical residual propagates through the
actual normalized recurrence with coefficient i+1. Quantifier-free
induction bounds that residual for every internal index. The exact
independent-precision identity follows by removing its fixed error
coefficient. The scalar polynomial is the actual factorial sum.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteIntegerFormula

open_ipra
open GaussianEulerIncompleteIntegerDomain (source data data_zero original_regular_names)
open GaussianEulerIncompleteIntegerStep (value decay stepCost original_upper_step)
open GaussianEulerIncompleteName (upperF)
open GaussianEulerIncompleteFactorialPolynomial (polynomial)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianGammaFactorialValues (argument_bound scalarArgument)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast sum_distance)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalHorner (positive_product qadd qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev formulaF : PR 2 := multiplyF constantF decayF
def formulaData (i a b : PTm n) : PTm n := multiplyData constantF decayF (polynomial i a b) (decayData a b)
def rawFormula (p i a b : PTm n) : PTm n := qmul (polynomial i a b) (decay p a b)
def errorBody : PTm 3 := succ (var 0)*var 1+stepCost (var 0) (fstT (var 2)) (sndT (var 2))
def errorF : PR 2 := rec2 (two : PTm 1) errorBody
def error (i a b : PTm n) : PTm n := ap2 errorF i (pairT a b)
def errorLaw (p i a b : PTm n) : Fm PTm n := distanceBounded (value p i a b) (rawFormula p i a b) (error i a b) (unit p)

ipra_subst formulaData
ipra_subst rawFormula
ipra_subst error
ipra_subst errorLaw

theorem error_zero (a b : PTm n) : Γ ⊢[PRAAx] error zero a b ≐ two := by
  simpa only [error,errorF,two,PTm.subst_succ,PTm.subst_zero] using
    rec2_zero (Γ := Γ) (two : PTm 1) errorBody (pairT a b)

theorem error_succ (i a b : PTm n) : Γ ⊢[PRAAx] error (succ i) a b ≐ succ i*error i a b+stepCost i a b := by
  have recEq := rec2_succ (Γ := Γ) (two : PTm 1) errorBody i (pairT a b)
  have stepEq : Γ ⊢[PRAAx]
      stepCost i (fstT (pairT a b)) (sndT (pairT a b)) ≐ stepCost i a b := by
    ipra_congr (stepCost (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl i, fst_pair _ _, snd_pair _ _]
  have raw : Γ ⊢[PRAAx] error (succ i) a b ≐ succ i*error i a b+
      stepCost i (fstT (pairT a b)) (sndT (pairT a b)) := by
    simpa only [error,errorF,errorBody,PTm.subst_add,PTm.subst_mul,PTm.subst_succ,subst_fstT,subst_sndT,
      GaussianEulerIncompleteIntegerStep.subst_stepCost,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using recEq
  exact raw.eqTrans (congrAdd (.eqRefl _) stepEq)

theorem decay_regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN decayF (decayData a b) :=
  GaussianRadiusExponentialName.name_regular constantF _ _
    (GaussianGammaFiniteApproximantName.exponential_input constantF (decayPoint a b) (constant_regular _))

theorem formula_regular (i a b : PTm n) : Γ ⊢[PRAAx] pointCN formulaF (formulaData i a b) :=
  multiply_fast constantF decayF (polynomial i a b) (decayData a b) (constant_regular _) (decay_regular a b)

theorem error_base (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] errorLaw p zero a b := by
  have hu := unit_positive (Γ := Γ) p
  have unitEq := GaussianEulerIncompleteUnitUpper.original_upper_at_one a b h
  have old := cross_at _ _ _ _ p p unitEq
  have left := congrAp2 upperF (.eqRefl p) (data_zero (Γ := Γ) a b)
  have hcan : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (decay p a b) :=
    GaussianRadiusExponentialName.sample_canonical constantF _ _ _
  have right := GaussianEulerIncompleteFactorialCombination.base (GaussianPositiveRationalLogarithm.fraction a b) (decay p a b) hcan
  have diag := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hu hu) hu
    (le_of_eq_add (d := zero) (by ipra_ring)) old
  exact distance_congr left.eqSymm right.eqSymm (error_zero a b).eqSymm (.eqRefl _) diag

theorem error_step (p i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) (ih : Γ ⊢[PRAAx] errorLaw p i a b) :
    Γ ⊢[PRAAx] errorLaw p (succ i) a b := by
  let d := decay p a b
  let w := qmul (GaussianEulerIntegerBoundary.monomial (succ i) a b) d
  have hu := unit_positive (Γ := Γ) p
  have scaled := GaussianApproximateInverseDistance.multiply_distance (scalarArgument i) _ _ (succ i) (error i a b) (unit p)
    hu (argument_bound i) ih
  have trivial := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) w (unit p) hu
  have sum := sum_distance _ _ _ _ _ _ _ hu scaled trivial
  have exactValue := GaussianEulerIncompleteFactorialCombination.rational_step (Γ := Γ) i a b d
  have moved := distance_congr (.eqRefl _) exactValue (.eqRefl _) (.eqRefl _) sum
  have amount : Γ ⊢[PRAAx] stepCost i a b+(succ i*error i a b+zero) ≐ error (succ i) a b :=
    (by ipra_ring : Γ ⊢[PRAAx] stepCost i a b+(succ i*error i a b+zero) ≐ succ i*error i a b+stepCost i a b).eqTrans
      (error_succ i a b).eqSymm
  exact distance_congr (.eqRefl _) (.eqRefl _) amount (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu (original_upper_step p i a b h) moved)

theorem prefix_error (p i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] errorLaw p i a b := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift, Syn.shift, GaussianEulerIncompleteIntegerDomain.subst_source] using h.shift
  have hall : Γ ⊢[PRAAx] .all (errorLaw (Syn.shift p) (var 0) (Syn.shift a) (Syn.shift b)) := by
    refine PRA.qfInd _ (by trivial) ?_ ?_
    · simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using error_base p a b h
    · simpa only [subst_errorLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        error_step (Syn.shift p) (var 0) (Syn.shift a) (Syn.shift b) hs.wk Prf.hyp0
  simpa only [subst_errorLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i

private def gain (i a b : PTm n) : PTm n := error i a b+(multiplyModulus constantF decayF (polynomial i a b) (decayData a b)+one)

theorem original_upper_integer_formula (i a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent upperF formulaF (data i a b) (formulaData i a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope upperF formulaF (data i a b) (formulaData i a b) (gain i a b)
    (original_regular_names i a b h).andE₂ (formula_regular i a b)
  unfold GaussianValueNormalizerExtensionality.rawDiagonal
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift, Syn.shift, GaussianEulerIncompleteIntegerDomain.subst_source] using h.shift
  let j := Syn.shift i
  let x := Syn.shift a
  let y := Syn.shift b
  let p : PTm (n+1) := var 0
  have finite := prefix_error p j x y hs
  have raw := GaussianNameRingLaws.multiply_sample_error (Γ := Γ.map Fm.shift) constantF decayF
    (polynomial j x y) (decayData x y) p (constant_regular _) (decay_regular x y)
  have named := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p _) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) raw
  have hu := unit_positive (Γ := Γ.map Fm.shift) p
  have proof := distance_triangle_same _ _ _ _ _ _ hu finite (distance_symmetric _ _ _ _ hu named)
  simpa [j,x,y,p,gain,Syn.shift,errorLaw,value,formulaF,formulaData,rawFormula,decay] using proof

theorem actual_original_upper_incomplete_Gamma_integer_formula_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 1) (var 2) ⟶ crossEquivalent upperF formulaF (data (var 0) (var 1) (var 2))
        (formulaData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_upper_integer_formula _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteIntegerFormula
