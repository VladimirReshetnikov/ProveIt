import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.Distances.GaussianRootRadius
import IPRADerivations.Analysis.Polynomials.Horner.Perturbation.GaussianRationalHornerPerturbation

/-!
# Exact finite evaluation budget for the actual root-support product

Source04 (FE). The true factorization error and the original coefficient
name condition give the actual product-to-sample coefficient comparisons.
Actual rational Horner perturbation then compares their evaluations. The
only residual premise is the normalized root-equation observation at the
specified finite sample. No coefficient or evaluation discrepancy, common
radius or common denominator is supplied. All numerical data are internal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootFiniteEvaluation

open_ipra
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (CN R unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRootRadius (product)
open LeanProofs.IPRA.Analysis.GaussianFactorParameters (monicRD)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (bound_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder
  (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open LeanProofs.IPRA.Analysis.GaussianRootSchedule (coefficientConstant)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def denominator (a : PR 3) (N t x : PTm n) : PTm n := GaussianRootSchedule.toleranceDenominator N (R a N x) t
def coefficientNumerator (a : PR 3) (N t s x : PTm n) : PTm n := two*unit s+denominator a N t x
def coefficientDenominator (a : PR 3) (N t s x : PTm n) : PTm n := denominator a N t x*unit s
def evaluationNumerator (a : PR 3) (N U t s x T : PTm n) : PTm n :=
  two*coefficientConstant N U*unit s+(coefficientConstant N U+T)*denominator a N t x

ipra_subst denominator
ipra_subst coefficientNumerator
ipra_subst coefficientDenominator
ipra_subst evaluationNumerator

theorem denominator_positive (a : PR 3) (N t x : PTm n) : Γ ⊢[PRAAx] le one (denominator a N t x) :=
  GaussianRootSchedule.tolerance_positive _ _ _
theorem coefficient_denominator_positive (a : PR 3) (N t s x : PTm n) : Γ ⊢[PRAAx]
    le one (coefficientDenominator a N t s x) :=
  GaussianRationalHorner.positive_product _ _ (denominator_positive a N t x) (unit_positive s)

/-- Actual AF error and the true CN instance at E(t),s give the exact
original coefficient distance (2*2^s+2^E)/(2^E*2^s). -/
theorem coefficient_distance (step a : PR 3) (N t s x j : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] lt j N) : Γ ⊢[PRAAx]
    distanceBounded (entry (product step a N t x) (succ j)) (entry (GaussianRootSamples.sample a N s x) (succ j))
      (coefficientNumerator a N t s x) (coefficientDenominator a N t s x) := by
  have Dpos := denominator_positive (Γ := Γ) a N t x
  have Ddpos := coefficient_denominator_positive (Γ := Γ) a N t s x
  have af := GaussianRootSamples.coefficient_error step a N (R a N x) t x (succ j) hRD hN hj
  have reverse := distance_symmetric _ _ _ _ Dpos af
  have fraction : Γ ⊢[PRAAx] le (one*coefficientDenominator a N t s x) (unit s*denominator a N t x) :=
    le_of_eq_add (d := zero) (by unfold coefficientDenominator; ipra_ring)
  have first := distance_radius_mono _ _ one (denominator a N t x) (unit s) (coefficientDenominator a N t s x)
    Dpos Ddpos fraction reverse
  have actualCN := GaussianCoefficientNameBounds.CN_at a N x (PTm.monus N (succ j))
    (GaussianRootSchedule.precision N (R a N x) t) s hCN (GaussianApproximateFactorization.remaining_active N j hj)
  have second : Γ ⊢[PRAAx] distanceBounded
      (entry (GaussianRootSamples.polynomial a N (R a N x) t x) (succ j))
      (entry (GaussianRootSamples.sample a N s x) (succ j))
      (denominator a N t x+unit s) (coefficientDenominator a N t s x) :=
    distance_congr (GaussianRootSamples.polynomial_coefficient a N (R a N x) t x j hj).eqSymm
      (GaussianRootSamples.sample_coefficient a N s x j hj).eqSymm (.eqRefl _) (.eqRefl _) actualCN
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold coefficientNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ (unit s) (denominator a N t x+unit s) (coefficientDenominator a N t s x) Ddpos first second)

/-- All needed lower coefficients refer to the actual two produced lists.
The CN and AF hypotheses are instantiated, not replaced by an error law. -/
theorem coefficient_errors (step a : PR 3) (N t s x : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianRationalHornerPerturbation.coefficientErrors (product step a N t x) (GaussianRootSamples.sample a N s x) N
      (coefficientNumerator a N t s x) (coefficientDenominator a N t s x) := by
  refine .allI (.impI ?_)
  have rdShift : Γ.map Fm.shift ⊢[PRAAx] monicRD step := by
    simpa only [Fm.shift,GaussianFactorParameters.subst_monicRD] using hRD.shift
  have cnShift : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have nShift : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hN.shift
  simpa only [Syn.shift,GaussianRootRadius.subst_product,GaussianRootSamples.subst_sample,
    subst_coefficientNumerator,subst_coefficientDenominator] using
    coefficient_distance step a (Syn.shift N) (Syn.shift t) (Syn.shift s) (Syn.shift x) (var 0)
      rdShift.wk cnShift.wk nShift.wk Prf.hyp0

/-- The actual Horner perturbation estimate has precisely C_U times the
just-derived original rational coefficient budget. -/
theorem evaluation_distance (step a : PR 3) (N U t s x z : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le one U)
    (hz : Γ ⊢[PRAAx] bounded z U one) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (product step a N t x) z) (evaluate (GaussianRootSamples.sample a N s x) z)
      (coefficientConstant N U*coefficientNumerator a N t s x) (coefficientDenominator a N t s x) :=
  GaussianRationalHornerPerturbation.monic_evaluation_bound _ _ _ _ _ _ _
    (GaussianRootRadius.product_length step a N t x) (GaussianRootSamples.sample_length a N s x)
    (GaussianRootRadius.product_leading step a N t x) (GaussianRootSamples.sample_leading a N s x)
    hU (coefficient_denominator_positive a N t s x) (coefficient_errors step a N t s x hRD hCN hN) hz

/-- Exact source (FE), derived from the actual normalized root-residual
observation and the actual finite sample/factorization constructions. -/
theorem finite_evaluation_bound (step a : PR 3) (N U t s x z T : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le one U)
    (hz : Γ ⊢[PRAAx] bounded z U one)
    (hResidual : Γ ⊢[PRAAx] bounded (evaluate (GaussianRootSamples.sample a N s x) z) T (unit s)) : Γ ⊢[PRAAx]
    bounded (evaluate (product step a N t x) z) (evaluationNumerator a N U t s x T) (coefficientDenominator a N t s x) := by
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _
    (coefficient_denominator_positive a N t s x) (unit_positive s)
    (evaluation_distance step a N U t s x z hRD hCN hN hU hz) hResidual
  have scaled : Γ ⊢[PRAAx] bounded (evaluate (product step a N t x) z)
      (evaluationNumerator a N U t s x T*unit s) (coefficientDenominator a N t s x*unit s) := bound_congr (.eqRefl _)
    (by unfold coefficientNumerator coefficientDenominator evaluationNumerator; ipra_ring)
    (.eqRefl _) raw
  exact GaussianMonicResidualRadius.bounded_cancel _ _ _ _
    (coefficient_denominator_positive a N t s x) (unit_positive s) scaled


/-- Actual program returning the true evaluation and its computed FE radius. -/
def output (step a : PR 3) (N U t s x z T : PTm n) : PTm n :=
  pairT (evaluate (product step a N t x) z)
    (pairT (evaluationNumerator a N U t s x T) (coefficientDenominator a N t s x))
def outputF (step a : PR 3) : PR 7 := PTm.toPR
  (output step a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (step a : PR 3) (N U t s x z T : PTm n) : PTm n := PTm.app (outputF step a) ![N,U,t,s,x,z,T]

ipra_subst output
ipra_subst run

theorem program_at (step a : PR 3) (N U t s x z T : PTm n) : Γ ⊢[PRAAx]
    run step a N U t s x z T ≐ output step a N U t s x z T := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output step a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![N,U,t,s,x,z,T]

theorem output_value (step a : PR 3) (N U t s x z T : PTm n) : Γ ⊢[PRAAx]
    fstT (run step a N U t s x z T) ≐ evaluate (product step a N t x) z :=
  (program_at step a N U t s x z T).fstE
theorem output_numerator (step a : PR 3) (N U t s x z T : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run step a N U t s x z T)) ≐ evaluationNumerator a N U t s x T :=
  (program_at step a N U t s x z T).sndE.fstE
theorem output_denominator (step a : PR 3) (N U t s x z T : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run step a N U t s x z T)) ≐ coefficientDenominator a N t s x :=
  (program_at step a N U t s x z T).sndE.sndE

theorem program_certificate (step a : PR 3) (N U t s x z T : PTm n)
    (hRD : Γ ⊢[PRAAx] monicRD step) (hCN : Γ ⊢[PRAAx] CN a N x)
    (hN : Γ ⊢[PRAAx] le one N) (hU : Γ ⊢[PRAAx] le one U)
    (hz : Γ ⊢[PRAAx] bounded z U one)
    (hResidual : Γ ⊢[PRAAx] bounded (evaluate (GaussianRootSamples.sample a N s x) z) T (unit s)) : Γ ⊢[PRAAx]
    le one (sndT (sndT (run step a N U t s x z T))) ⋏
      bounded (fstT (run step a N U t s x z T))
        (fstT (sndT (run step a N U t s x z T))) (sndT (sndT (run step a N U t s x z T))) :=
  .andI (le_congr (.eqRefl _) (output_denominator step a N U t s x z T).eqSymm
    (coefficient_denominator_positive a N t s x))
    (bound_congr (output_value step a N U t s x z T).eqSymm (output_numerator step a N U t s x z T).eqSymm
      (output_denominator step a N U t s x z T).eqSymm
      (finite_evaluation_bound step a N U t s x z T hRD hCN hN hU hz hResidual))

theorem finite_coefficient_distance_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (monicRD step ⟶ CN a (var 0) (var 3) ⟶ le one (var 0) ⟶ lt (var 4) (var 0) ⟶
      distanceBounded (entry (product step a (var 0) (var 1) (var 3)) (succ (var 4)))
        (entry (GaussianRootSamples.sample a (var 0) (var 2) (var 3)) (succ (var 4)))
        (coefficientNumerator a (var 0) (var 1) (var 2) (var 3)) (coefficientDenominator a (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (coefficient_distance _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem finite_evaluation_distance_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (monicRD step ⟶ CN a (var 0) (var 4) ⟶ le one (var 0) ⟶ le one (var 1) ⟶ bounded (var 5) (var 1) one ⟶
      distanceBounded (evaluate (product step a (var 0) (var 2) (var 4)) (var 5))
        (evaluate (GaussianRootSamples.sample a (var 0) (var 3) (var 4)) (var 5))
        (coefficientConstant (var 0) (var 1)*coefficientNumerator a (var 0) (var 2) (var 3) (var 4))
        (coefficientDenominator a (var 0) (var 2) (var 3) (var 4))) := by
  apply closeUniv 6
  refine .impI (.impI (.impI (.impI (.impI ?_))))
  exact evaluation_distance _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk
    Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem finite_root_evaluation_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (monicRD step ⟶ CN a (var 0) (var 4) ⟶ le one (var 0) ⟶ le one (var 1) ⟶ bounded (var 5) (var 1) one ⟶
      bounded (evaluate (GaussianRootSamples.sample a (var 0) (var 3) (var 4)) (var 5)) (var 6) (unit (var 3)) ⟶
      bounded (evaluate (product step a (var 0) (var 2) (var 4)) (var 5))
        (evaluationNumerator a (var 0) (var 1) (var 2) (var 3) (var 4) (var 6))
        (coefficientDenominator a (var 0) (var 2) (var 3) (var 4))) := by
  apply closeUniv 7
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact finite_evaluation_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

theorem finite_evaluation_program_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run step a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output step a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) :=
  closeUniv 7 (program_at _ _ _ _ _ _ _ _ _)

theorem finite_evaluation_certificate_closed (step a : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (monicRD step ⟶ CN a (var 0) (var 4) ⟶ le one (var 0) ⟶ le one (var 1) ⟶ bounded (var 5) (var 1) one ⟶
      bounded (evaluate (GaussianRootSamples.sample a (var 0) (var 3) (var 4)) (var 5)) (var 6) (unit (var 3)) ⟶
      (le one (sndT (sndT (run step a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))) ⋏
        bounded (fstT (run step a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
          (fstT (sndT (run step a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))
          (sndT (sndT (run step a (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))) := by
  apply closeUniv 7
  refine .impI (.impI (.impI (.impI (.impI (.impI ?_)))))
  exact program_certificate _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianRootFiniteEvaluation
