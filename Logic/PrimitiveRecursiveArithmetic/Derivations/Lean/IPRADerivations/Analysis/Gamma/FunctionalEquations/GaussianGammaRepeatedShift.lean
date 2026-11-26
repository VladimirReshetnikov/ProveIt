import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaShiftTrajectory
import IPRADerivations.Analysis.Exponential.GaussianRobinMeshExponential
import IPRADerivations.Analysis.Names.Rates.GaussianApproximateInverseDistance
import IPRADerivations.Core.CongruenceTactic

/-!
# Repeated shift of the original entire reciprocal Gamma name

The finite factor risingProduct is the original Gaussian rational product of
z/B+j. A fixed-observation numerical error invariant iterates the checked
C20 equation along the actual native shift trajectory. It never inducts
over names or assumes nonzero factors.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRepeatedShift

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaShiftTrajectory (point point_zero point_succ point_source point_linear)
open GaussianGammaEulerHeadShift (linear shifted)
open GaussianGammaCanonicalExponent (source constantF constant_regular)
open GaussianRationalHorner (qmul canonical ofGaussian positive_product)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteProduct (qprod product_zero product_canonical)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def linearBody : PTm 2 := linear (fstT (var 1)) (sndT (var 1)) (var 0)
def risingProduct (z B i : PTm n) : PTm n := qprod linearBody i (GaussianGammaShiftTrajectory.data z B)
def stageData (z R B i : PTm n) : PTm n := GaussianGammaC7Name.data (point z B i) (R+i) B
def stage (p z R B i : PTm n) : PTm n := ap2 GaussianGammaC7Name.nameF p (stageData z R B i)
def factorBound (R E : PTm n) : PTm n := R+E+one
def stepCost (R E : PTm n) : PTm n := two+two*factorBound R E
def error (R E i : PTm n) : PTm n := i*stepCost R E*pw (factorBound R E) E

def resultF : PR 2 := GaussianNameArithmetic.multiplyF constantF GaussianGammaC7Name.nameF
def resultData (z R B E : PTm n) : PTm n := GaussianNameArithmetic.multiplyData constantF GaussianGammaC7Name.nameF
  (risingProduct z B E) (stageData z R B E)

@[simp] theorem subst_prefix {l : ℕ} (σ : Fin n → PTm l) (z B i : PTm n) :
    Syn.subst σ (risingProduct z B i) = risingProduct (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ i) := by simp [risingProduct]
@[simp] theorem subst_stageData {l : ℕ} (σ : Fin n → PTm l) (z R B i : PTm n) :
    Syn.subst σ (stageData z R B i) = stageData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ i) := by simp [stageData]
@[simp] theorem subst_stage {l : ℕ} (σ : Fin n → PTm l) (p z R B i : PTm n) :
    Syn.subst σ (stage p z R B i) = stage (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ i) := by simp [stage]
@[simp] theorem subst_factorBound {l : ℕ} (σ : Fin n → PTm l) (R E : PTm n) :
    Syn.subst σ (factorBound R E) = factorBound (Syn.subst σ R) (Syn.subst σ E) := by simp [factorBound]
@[simp] theorem subst_stepCost {l : ℕ} (σ : Fin n → PTm l) (R E : PTm n) :
    Syn.subst σ (stepCost R E) = stepCost (Syn.subst σ R) (Syn.subst σ E) := by simp [stepCost]
@[simp] theorem subst_error {l : ℕ} (σ : Fin n → PTm l) (R E i : PTm n) :
    Syn.subst σ (error R E i) = error (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ i) := by simp [error]
@[simp] theorem subst_resultData {l : ℕ} (σ : Fin n → PTm l) (z R B E : PTm n) :
    Syn.subst σ (resultData z R B E) = resultData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) := by simp [resultData]

theorem linear_at (z B i : PTm n) : Γ ⊢[PRAAx]
    inst2 linearBody i (GaussianGammaShiftTrajectory.data z B) ≐ linear z B i := by
  ipra_congr (linear (var 0) (var 1) (var 2) : PTm 3) with
    [fst_pair _ _, snd_pair _ _, .eqRefl i] using [linearBody, inst2, GaussianGammaShiftTrajectory.data]

theorem prefix_zero (z B : PTm n) : Γ ⊢[PRAAx] risingProduct z B zero ≐ qone := product_zero _ _
theorem prefix_succ (z B i : PTm n) : Γ ⊢[PRAAx]
    risingProduct z B (succ i) ≐ qmul (risingProduct z B i) (linear z B i) :=
  (GaussianRationalFiniteProduct.product_succ _ _ _).eqTrans (qmul_congr (.eqRefl _) (linear_at z B i))
theorem prefix_canonical (z B i : PTm n) : Γ ⊢[PRAAx] canonical (risingProduct z B i) := product_canonical _ _ _

theorem factor_bound (z R B E i : PTm n) (h : Γ ⊢[PRAAx] source z R B) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    bounded (linear z B i) (factorBound R E) one := by
  have here := point_source z R B i h
  have native := GaussianGammaFunctionalEquation.input_point_bound (point z B i) (R+i) B here
  have grow : Γ ⊢[PRAAx] le (R+i) (factorBound R E) :=
    le_trans (add_le_add₂ (le_refl R) hi) (le_add_right _ one)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring) grow)
    (GaussianRationalReciprocal.bound_congr (point_linear z B i h.andE₂.andE₁) (.eqRefl _) (.eqRefl _) native)

theorem prefix_bound_step (z R B E i : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hi : Γ ⊢[PRAAx] le (succ i) E) (ih : Γ ⊢[PRAAx] bounded (risingProduct z B i) (pw (factorBound R E) i) one) : Γ ⊢[PRAAx]
    bounded (risingProduct z B (succ i)) (pw (factorBound R E) (succ i)) one :=
  GaussianRationalReciprocal.bound_congr (prefix_succ z B i).eqSymm (pw_succ _ _).eqSymm (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) ih
      (factor_bound z R B E i h (le_trans (le_succ_self i) hi)))

theorem prefix_bound (z R B E i : PTm n) (h : Γ ⊢[PRAAx] source z R B) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    bounded (risingProduct z B i) (pw (factorBound R E) i) one := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  have hall : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift E) ⟶
      bounded (risingProduct (Syn.shift z) (Syn.shift B) (var 0)) (pw (factorBound (Syn.shift R) (Syn.shift E)) (var 0)) one) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [Fm.subst_imp,subst_le,GaussianRationalMetric.subst_bounded,subst_prefix,subst_factorBound,subst_ap2,
        ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (GaussianRationalReciprocal.bound_congr (prefix_zero z B).eqSymm (pw_zero _).eqSymm (.eqRefl _)
        GaussianRationalReciprocal.qone_bounded)
    · simp only [Fm.subst_imp,subst_le,GaussianRationalMetric.subst_bounded,subst_prefix,subst_factorBound,subst_ap2,
        ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact prefix_bound_step _ _ _ _ _ hs.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have gate : Γ ⊢[PRAAx] le i E ⟶ bounded (risingProduct z B i) (pw (factorBound R E) i) one := by
    simpa only [Fm.subst_imp,subst_le,GaussianRationalMetric.subst_bounded,subst_prefix,subst_factorBound,subst_ap2,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i
  exact .impE gate hi

theorem factor_bound_positive (R E : PTm n) : Γ ⊢[PRAAx] le one (factorBound R E) :=
  le_congr (.eqRefl _) (by unfold factorBound; ipra_ring) (le_add_right one (R+E))
theorem prefix_uniform_bound (z R B E i : PTm n) (h : Γ ⊢[PRAAx] source z R B) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    bounded (risingProduct z B i) (pw (factorBound R E) E) one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (le_congr (by ipra_ring) (by ipra_ring)
      (GaussianFactorBudget.power_monotone_length _ _ _ (factor_bound_positive R E) hi))
    (prefix_bound z R B E i h hi)

theorem stage_regular (z R B i : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN GaussianGammaC7Name.nameF (stageData z R B i) :=
  GaussianGammaC7Name.name_regular _ _ _ (point_source z R B i h)

theorem C7_data_congr {z w R S B C : PTm n} (hz : Γ ⊢[PRAAx] z ≐ w)
    (hR : Γ ⊢[PRAAx] R ≐ S) (hB : Γ ⊢[PRAAx] B ≐ C) : Γ ⊢[PRAAx]
    GaussianGammaC7Name.data z R B ≐ GaussianGammaC7Name.data w S C := by
  ipra_congr (GaussianGammaC7Name.data (var 0) (var 1) (var 2) : PTm 3) with [hz, hR, hB]

theorem stage_zero (p z R B : PTm n) : Γ ⊢[PRAAx] stage p z R B zero ≐ GaussianGammaC7Name.sample p z R B :=
  congrAp2 GaussianGammaC7Name.nameF (.eqRefl _) (C7_data_congr (point_zero z B) (add_zero R) (.eqRefl _))

theorem stage_successor (p z R B i : PTm n) : Γ ⊢[PRAAx]
    stage p z R B (succ i) ≐ GaussianGammaC7Name.sample p (shifted (point z B i) B) ((R+i)+one) B :=
  congrAp2 GaussianGammaC7Name.nameF (.eqRefl _) (C7_data_congr (point_succ z B i) (by ipra_ring) (.eqRefl _))

/-- The old C20 name equality and its actual product clock yield a
same-p recurrence with an explicit error, before any iteration. -/
theorem stage_step_error (p z R B E i : PTm n) (h : Γ ⊢[PRAAx] source z R B) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    distanceBounded (stage p z R B i) (qmul (linear z B i) (stage p z R B (succ i))) (stepCost R E) (unit p) := by
  have here := point_source z R B i h
  have eqn := GaussianGammaFunctionalEquation.original_C20_shift (point z B i) (R+i) B here
    GaussianRobinMeshExponential.all_mesh_exponential_inverses
  have cross := distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p))
    (cross_at _ _ _ _ p p eqn)
  have first : Γ ⊢[PRAAx] distanceBounded (stage p z R B i)
      (ap2 GaussianGammaFunctionalEquation.leftLimitF p
        (GaussianGammaFunctionalEquation.leftLimitData (point z B i) (R+i) B)) two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
      (le_of_eq_add (d := zero) (by ipra_ring)) cross
  have raw := GaussianGammaFunctionalEquation.left_raw_error p (point z B i) (R+i) B here
  have second := distance_congr (.eqRefl _)
    (qmul_congr (point_linear z B i h.andE₂.andE₁).eqSymm (stage_successor p z R B i)).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  have chain := distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second
  apply distance_radius_mono _ _ _ _ _ _ (unit_positive p) (unit_positive p) _ chain
  have grow : Γ ⊢[PRAAx] le (R+i) (factorBound R E) :=
    le_trans (add_le_add₂ (le_refl R) hi) (le_add_right _ one)
  ipra_le 2*𝔞(unit p)*sl grow using
    unfold stepCost
    ipra_simps
    ring

def prefixLaw (p z R B E i : PTm n) : Fm PTm n := le i E ⟶
  distanceBounded (GaussianGammaC7Name.sample p z R B) (qmul (risingProduct z B i) (stage p z R B i)) (error R E i) (unit p)
@[simp] theorem subst_prefixLaw {l : ℕ} (σ : Fin n → PTm l) (p z R B E i : PTm n) :
    (prefixLaw p z R B E i).subst σ = prefixLaw (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ E) (Syn.subst σ i) := by simp [prefixLaw]

theorem prefix_error_zero (p z R B E : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (qmul (risingProduct z B zero) (stage p z R B zero))
      (error R E zero) (unit p) := by
  have base : Γ ⊢[PRAAx] qmul (risingProduct z B zero) (stage p z R B zero) ≐ GaussianGammaC7Name.sample p z R B :=
    (qmul_congr (prefix_zero z B) (stage_zero p z R B)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (GaussianGammaC7Name.sample_canonical p z R B)))
  exact distance_congr (.eqRefl _) base.eqSymm (by unfold error; ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero _ _ (unit_positive p))

/-- The sole recursive hypothesis is the fixed-p numerical distance. -/
theorem prefix_error_step (p z R B E i : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hi : Γ ⊢[PRAAx] le (succ i) E)
    (ih : Γ ⊢[PRAAx] distanceBounded (GaussianGammaC7Name.sample p z R B)
      (qmul (risingProduct z B i) (stage p z R B i)) (error R E i) (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B)
      (qmul (risingProduct z B (succ i)) (stage p z R B (succ i))) (error R E (succ i)) (unit p) := by
  have ii := le_trans (le_succ_self i) hi
  have lifted := GaussianApproximateInverseDistance.multiply_distance (risingProduct z B i) _ _
    (pw (factorBound R E) E) (stepCost R E) (unit p) (unit_positive p)
    (prefix_uniform_bound z R B E i h ii) (stage_step_error p z R B E i h ii)
  have right : Γ ⊢[PRAAx] qmul (risingProduct z B i) (qmul (linear z B i) (stage p z R B (succ i))) ≐
      qmul (risingProduct z B (succ i)) (stage p z R B (succ i)) :=
    (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      (qmul_congr (prefix_succ z B i).eqSymm (.eqRefl _))
  exact distance_congr (.eqRefl _) right (by unfold error; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) ih lifted)

/-- A genuine guarded QF induction at the fixed requested precision. -/
theorem prefix_error (p z R B E i : PTm n) (h : Γ ⊢[PRAAx] source z R B) (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (qmul (risingProduct z B i) (stage p z R B i)) (error R E i) (unit p) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  have hall : Γ ⊢[PRAAx] .all (prefixLaw (Syn.shift p) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial,trivial⟩ ?_ ?_
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (prefix_error_zero p z R B E)
    · simp only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      exact prefix_error_step _ _ _ _ _ _ hs.wk.wk Prf.hyp0
        (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))
  have gate : Γ ⊢[PRAAx] prefixLaw p z R B E i := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i
  exact .impE gate hi

def finalError (R E : PTm n) : PTm n := (E*stepCost R E+two)*pw (factorBound R E) E
@[simp] theorem subst_finalError {l : ℕ} (σ : Fin n → PTm l) (R E : PTm n) :
    Syn.subst σ (finalError R E) = finalError (Syn.subst σ R) (Syn.subst σ E) := by simp [finalError]

theorem result_regular (z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN resultF (resultData z R B E) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (constant_regular _) (stage_regular z R B E h)

/-- The final actual multiplication retains its own late normalizer query.
Only the original C7 regularity and the finite factor bound are needed. -/
theorem result_same_precision (p z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 resultF p (resultData z R B E))
      (qmul (risingProduct z B E) (stage p z R B E)) (two*pw (factorBound R E) E) (unit p) := by
  let t := GaussianGammaFunctionalEquation.clock GaussianGammaC7Name.nameF (risingProduct z B E) (stageData z R B E) p
  have close := GaussianGammaFunctionalEquation.earlier_C7_error p t (point z B E) (R+E) B
    (point_source z R B E h) (GaussianGammaFunctionalEquation.clock_later _ _ _ _)
  have lifted := GaussianApproximateInverseDistance.multiply_distance (risingProduct z B E) _ _
    (pw (factorBound R E) E) two (unit p) (unit_positive p) (prefix_bound z R B E E h (le_refl _)) close
  exact distance_congr (GaussianGammaFunctionalEquation.constant_product_at GaussianGammaC7Name.nameF
    (risingProduct z B E) (stageData z R B E) p).eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _) lifted

theorem final_diagonal_error (p z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (ap2 resultF p (resultData z R B E)) (finalError R E) (unit p) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by unfold error finalError; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) (prefix_error p z R B E E h (le_refl _))
      (distance_symmetric _ _ _ _ (unit_positive p) (result_same_precision p z R B E h)))

theorem final_envelope (z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal GaussianGammaC7Name.nameF resultF
      (GaussianGammaC7Name.data z R B) (resultData z R B E) (finalError R E) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianGammaC7Name.sample,GaussianGammaC7Name.subst_data,
    subst_resultData,subst_finalError,Syn.shift] using final_diagonal_error (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) hs

/-- Arbitrarily many original shifts, with no pole or nonzero condition. -/
theorem repeated_shift (z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF resultF (GaussianGammaC7Name.data z R B) (resultData z R B E) :=
  GaussianNameRingLaws.equivalent_of_envelope GaussianGammaC7Name.nameF resultF _ _ (finalError R E)
    (GaussianGammaC7Name.name_regular z R B h) (result_regular z R B E h) (final_envelope z R B E h)

/-- Source C22 uses n+1 literal linear factors and the actual native
point obtained after n+1 original shifts, at its derived disk R+n+1. -/
theorem original_C22 (z R B J : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent GaussianGammaC7Name.nameF resultF (GaussianGammaC7Name.data z R B) (resultData z R B (succ J)) :=
  repeated_shift z R B (succ J) h
/-- Actual independent observations and the exact polynomial multiplier. -/
def output (p q z R B E : PTm n) : PTm n := pairT (GaussianGammaC7Name.sample p z R B)
  (pairT (risingProduct z B E) (ap2 resultF q (resultData z R B E)))
def outputF : PR 6 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
def run (p q z R B E : PTm n) : PTm n := PTm.app outputF ![p,q,z,R,B,E]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (p q z R B E : PTm n) :
    Syn.subst σ (output p q z R B E) = output (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (p q z R B E : PTm n) :
    Syn.subst σ (run p q z R B E) = run (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem program_at (p q z R B E : PTm n) : Γ ⊢[PRAAx] run p q z R B E ≐ output p q z R B E := by
  simpa [run,outputF] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) ![p,q,z,R,B,E]

theorem returned_original (p q z R B E : PTm n) : Γ ⊢[PRAAx]
    fstT (run p q z R B E) ≐ GaussianGammaC7Name.sample p z R B :=
  (congrFst (program_at p q z R B E)).eqTrans (fst_pair _ _)
theorem returned_product (p q z R B E : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run p q z R B E)) ≐ risingProduct z B E :=
  (congrFst ((congrSnd (program_at p q z R B E)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_shifted (p q z R B E : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run p q z R B E)) ≐ ap2 resultF q (resultData z R B E) :=
  (congrSnd ((congrSnd (program_at p q z R B E)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_distance (p q z R B E : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (fstT (run p q z R B E)) (sndT (sndT (run p q z R B E))) (unit p+unit q) (unit p*unit q) :=
  distance_congr (returned_original p q z R B E).eqSymm (returned_shifted p q z R B E).eqSymm (.eqRefl _) (.eqRefl _)
    (cross_at _ _ _ _ p q (repeated_shift z R B E h))

theorem actual_rising_linear_product_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (risingProduct (var 0) (var 1) zero ≐ qone) := closeUniv 2 (prefix_zero _ _)
theorem actual_rising_linear_product_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (risingProduct (var 0) (var 1) (succ (var 2)) ≐ qmul (risingProduct (var 0) (var 1) (var 2))
      (linear (var 0) (var 1) (var 2))) := closeUniv 3 (prefix_succ _ _ _)
theorem original_rising_product_prefix_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 0) (var 1) (var 2) ⋏ le (var 4) (var 3)) ⟶
      bounded (risingProduct (var 0) (var 2) (var 4)) (pw (factorBound (var 1) (var 3)) (var 4)) one) :=
  closeUniv 5 (.impI (prefix_bound _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_C22_fixed_observation_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 1) (var 2) (var 3) ⋏ le (var 5) (var 4)) ⟶
      distanceBounded (GaussianGammaC7Name.sample (var 0) (var 1) (var 2) (var 3))
        (qmul (risingProduct (var 1) (var 3) (var 5)) (stage (var 0) (var 1) (var 2) (var 3) (var 5)))
        (error (var 2) (var 4) (var 5)) (unit (var 0))) :=
  closeUniv 6 (.impI (prefix_error _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem original_entire_repeated_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent GaussianGammaC7Name.nameF resultF
      (GaussianGammaC7Name.data (var 0) (var 1) (var 2)) (resultData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (repeated_shift _ _ _ _ Prf.hyp0))
theorem original_Gamma_C22_entire_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent GaussianGammaC7Name.nameF resultF
      (GaussianGammaC7Name.data (var 0) (var 1) (var 2)) (resultData (var 0) (var 1) (var 2) (succ (var 3)))) :=
  closeUniv 4 (.impI (original_C22 _ _ _ _ Prf.hyp0))
theorem actual_original_C22_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (program_at _ _ _ _ _ _)
theorem actual_returned_original_C22_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) ⟶ distanceBounded
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)))
      (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))
      (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (returned_distance _ _ _ _ _ _ Prf.hyp0))


end LeanProofs.IPRA.Analysis.GaussianGammaRepeatedShift
