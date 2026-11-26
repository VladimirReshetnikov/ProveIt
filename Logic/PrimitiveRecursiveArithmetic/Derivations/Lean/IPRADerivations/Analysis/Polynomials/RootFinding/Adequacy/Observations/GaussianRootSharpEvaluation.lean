import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.Observations.GaussianRootSharpErrorSamples
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootAdequacy

/-!
# Sharp represented polynomial evaluation error

Source04 root-eval-error: the actual normalized PR2 name of the sampled
difference F_t(point_s)-P_s(point_s) has norm at most 2 C_Z/2^E(t).
Its raw observations, derived modulus and finite sample envelope are
bound to actual programs. Only genuine source inputs are assumed; finite
dyadic slack removal gives the sharp Z constant, rather than Z+1.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootSharpEvaluation

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRootAdequacy (inputContract)
open LeanProofs.IPRA.Analysis.GaussianRootSharpErrorSamples (observation cost)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (A R unit unit_positive)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRootSchedule (coefficientConstant)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N t x : PTm n) : PTm n := pairT N (pairT t x)
def rawBody (step a : PR 3) (point : PR 2) : PTm 2 :=
  observation step a point (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def rawF (step a : PR 3) (point : PR 2) : PR 2 := PTm.toPR (rawBody step a point)
def modulus (a : PR 3) (N Z x : PTm n) : PTm n :=
  GaussianRationalHornerLipschitz.constant N (Z+one) (A a N x)+GaussianRootApproximationWitness.T a N (Z+one) x

ipra_subst data
ipra_subst modulus

theorem raw_at (step a : PR 3) (point : PR 2) (N t x s : PTm n) : Γ ⊢[PRAAx]
    ap2 (rawF step a point) s (data N t x) ≐ observation step a point N t x s := by
  have fields := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (observation step a point (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (data N t x),fstT (sndT (data N t x)),sndT (sndT (data N t x)),s])
    (σ' := ![N,t,x,s]) (fun j => by
      fin_cases j
      · exact fst_pair _ _
      · exact (snd_pair _ _).fstE
      · exact (snd_pair _ _).sndE
      · exact .eqRefl _)
  exact (toPR_eq (rawBody step a point) ![s,data N t x]).eqTrans (by
    simpa only [rawBody,GaussianRootSharpErrorSamples.subst_observation,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons] using fields)

theorem observation_regular_at (step a : PR 3) (point : PR 2) (N Z t x s r : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    distanceBounded (observation step a point N t x s) (observation step a point N t x r)
      (modulus a N Z x*(unit s+unit r)) (unit s*unit r) := by
  have core := GaussianRootAdequacy.source_sample_contract step a point N Z x h
  have rd := Prf.andE₁ core
  have cn := Prf.andE₁ (Prf.andE₂ core)
  have hn := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ core))
  have ru := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ core)))
  have pointData := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ core)))
  have hu := le_trans (GaussianRootSupport.radius_positive a N x) ru
  have positive := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive r)
  have product := GaussianRationalHornerLipschitz.evaluation_bound (GaussianRootRadius.product step a N t x)
    (ap2 point s x) (ap2 point r x) N (Z+one) (A a N x) (unit s+unit r) (unit s*unit r)
    (GaussianRootRadius.product_length step a N t x) (GaussianRootRadius.product_coefficients step a N t x rd cn hn)
    (GaussianRootApproximationWitness.point_at point (Z+one) x s (Prf.andE₂ pointData))
    (GaussianRootApproximationWitness.point_at point (Z+one) x r (Prf.andE₂ pointData)) positive
    (GaussianEuclideanDistanceName.point_cn_at point x s r (Prf.andE₁ pointData))
  have original := GaussianPolynomialValueName.observation_regular_at a point N (Z+one) x s r cn
    (Prf.andE₁ pointData) (Prf.andE₂ pointData) hu
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold modulus; ipra_ring) (.eqRefl _)
    (GaussianFastValueCut.distance_difference_same _ _ _ _ _ _ _ positive product original)

theorem raw_regular (step a : PR 3) (point : PR 2) (N Z t x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.regular (rawF step a point) (modulus a N Z x) (data N t x) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] inputContract step a point
      (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift Z)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianRootAdequacy.subst_inputContract,Syn.shift] using h.shift.shift
  have actual := observation_regular_at step a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift Z))
    (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift x)) (var 1) (var 0) hs
  simpa only [Syn.shift,subst_data,subst_modulus] using distance_congr
    (raw_at step a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift x)) (var 1)).eqSymm
    (raw_at step a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift x)) (var 0)).eqSymm
    (.eqRefl _) (.eqRefl _) actual

theorem raw_envelope (step a : PR 3) (point : PR 2) (N Z t x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.rawEnvelope (rawF step a point) (data N t x)
      (two*coefficientConstant N Z) (GaussianRootFiniteEvaluation.denominator a N t x) (cost N Z) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] inputContract step a point (Syn.shift N) (Syn.shift Z) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRootAdequacy.subst_inputContract,Syn.shift] using h.shift
  have rd := Prf.andE₁ hs
  have cn := Prf.andE₁ (Prf.andE₂ hs)
  have hn := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hs))
  have rz := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hs)))
  have norm := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ hs))))
  have hz := le_trans (GaussianRootSupport.radius_positive a (Syn.shift N) (Syn.shift x)) rz
  have result := GaussianRootSharpErrorSamples.observation_bound step a point (Syn.shift N) (Syn.shift Z)
    (Syn.shift t) (Syn.shift x) (var 0) rd cn hn hz norm
  simpa only [Syn.shift,subst_data,GaussianRootSchedule.subst_coefficientConstant,GaussianRootSharpErrorSamples.subst_cost,
    GaussianRootFiniteEvaluation.subst_denominator,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    GaussianRationalReciprocal.bound_congr (raw_at step a point (Syn.shift N) (Syn.shift t) (Syn.shift x) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _) result

def errorNameF (step a : PR 3) (point : PR 2) : PR 2 := GaussianFastValueCut.nameF (rawF step a point)
def errorNameData (a : PR 3) (N Z t x : PTm n) : PTm n := GaussianFastValueCut.nameData (modulus a N Z x) (data N t x)

theorem error_program_at (step a : PR 3) (point : PR 2) (N Z t x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (errorNameF step a point) k (errorNameData a N Z t x) ≐ GaussianFastValueCut.recode
      (observation step a point N t x (GaussianFastValueCut.exponent (modulus a N Z x) k)) := by
  have e := raw_at (Γ := Γ) step a point N t x (GaussianFastValueCut.exponent (modulus a N Z x) k)
  have recoded := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (GaussianFastValueCut.recode (var 0) : PTm 1)
    (σ := ![ap2 (rawF step a point) (GaussianFastValueCut.exponent (modulus a N Z x) k) (data N t x)])
    (σ' := ![observation step a point N t x (GaussianFastValueCut.exponent (modulus a N Z x) k)])
    (fun j => by fin_cases j; exact e)
  exact (GaussianFastValueCut.name_at (rawF step a point) (modulus a N Z x) (data N t x) k).eqTrans
    (by simpa only [GaussianFastValueCut.value,GaussianFastValueCut.subst_recode,Syn.subst_var,Matrix.cons_val_zero] using recoded)

theorem error_name_fast (step a : PR 3) (point : PR 2) (N Z t x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN (errorNameF step a point) (errorNameData a N Z t x) :=
  GaussianFastValueCut.name_fast _ _ _ (raw_regular _ _ _ _ _ _ _ h)

/-- The source sharp bound, as the literal PR2 difference-name norm cut. -/
theorem sharp_evaluation_error (step a : PR 3) (point : PR 2) (N Z t x : PTm n)
    (h : Γ ⊢[PRAAx] inputContract step a point N Z x) : Γ ⊢[PRAAx]
    GaussianFastValueCut.radiusCut (rawF step a point) (modulus a N Z x) (data N t x)
      (two*coefficientConstant N Z) (GaussianRootFiniteEvaluation.denominator a N t x) :=
  GaussianFastValueCut.envelope_to_cut _ _ _ _ _ _ (raw_regular _ _ _ _ _ _ _ h)
    (GaussianRootFiniteEvaluation.denominator_positive a N t x) (raw_envelope _ _ _ _ _ _ _ h)

theorem sharp_root_evaluation_error_closed (step a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract step a point (var 0) (var 1) (var 3) ⟶
      GaussianFastValueCut.radiusCut (rawF step a point) (modulus a (var 0) (var 1) (var 3)) (data (var 0) (var 2) (var 3))
        (two*coefficientConstant (var 0) (var 1)) (GaussianRootFiniteEvaluation.denominator a (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (sharp_evaluation_error _ _ _ _ _ _ _ Prf.hyp0))

theorem sharp_error_name_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (inputContract step a point (var 0) (var 1) (var 3) ⟶
      GaussianEuclideanDistanceName.pointCN (errorNameF step a point) (errorNameData a (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (error_name_fast _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_error_name_query_closed (step a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (ap2 (errorNameF step a point) (var 4) (errorNameData a (var 0) (var 1) (var 2) (var 3)) ≐
      GaussianFastValueCut.recode (observation step a point (var 0) (var 2) (var 3)
        (GaussianFastValueCut.exponent (modulus a (var 0) (var 1) (var 3)) (var 4)))) :=
  closeUniv 5 (error_program_at _ _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRootSharpEvaluation
