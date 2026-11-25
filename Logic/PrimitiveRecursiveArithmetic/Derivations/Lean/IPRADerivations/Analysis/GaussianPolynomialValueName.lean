import IPRADerivations.Analysis.GaussianRootResidualFromHit
import IPRADerivations.Analysis.GaussianRootApproximationWitness
import IPRADerivations.Analysis.GaussianEuclideanDistanceName
import IPRADerivations.Analysis.GaussianRationalSlackRemoval
import IPRADerivations.Core.CongruenceTactic

/-!
# The actual Gaussian polynomial value name

The samples are literal Horner evaluations of the sampled coefficient list
at the given point samples. Coefficient CN and point CN imply their exact
T-weighted regularity. A computed precision shift produces a genuine fast
Gaussian name. Its zero predicate is equivalent to the source normalized
residual predicate, using only finite rational slack removal.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialValueName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate positive_product)
open LeanProofs.IPRA.Analysis.GaussianCoefficientNameBounds (CN A unit unit_positive subst_unit)
open LeanProofs.IPRA.Analysis.GaussianRootApproximationWitness (C T pointBounds normalizedZero)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (pointCN)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def observation (a : PR 3) (point : PR 2) (N x s : PTm n) : PTm n :=
  evaluate (GaussianRootSamples.sample a N s x) (ap2 point s x)
def normalizer (a : PR 3) (N U x : PTm n) : PTm n := GaussianRootSchedule.binaryLength (T a N U x)+two
def exponent (a : PR 3) (N U x k : PTm n) : PTm n := k+normalizer a N U x
def value (a : PR 3) (point : PR 2) (N U x k : PTm n) : PTm n :=
  observation a point N x (exponent a N U x k)

@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2) (N x s : PTm n) :
    Syn.subst σ (observation a point N x s) = observation a point (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ s) := by simp [observation]
@[simp] theorem subst_normalizer {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N U x : PTm n) :
    Syn.subst σ (normalizer a N U x) = normalizer a (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) := by simp [normalizer]
@[simp] theorem subst_exponent {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (N U x k : PTm n) :
    Syn.subst σ (exponent a N U x k) = exponent a (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) (Syn.subst σ k) := by simp [exponent]
@[simp] theorem subst_value {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2) (N U x k : PTm n) :
    Syn.subst σ (value a point N U x k) = value a point (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) (Syn.subst σ k) := by simp [value]

theorem sample_errors (a : PR 3) (N x s t : PTm n) (hCN : Γ ⊢[PRAAx] CN a N x) : Γ ⊢[PRAAx]
    GaussianRationalHornerPerturbation.coefficientErrors (GaussianRootSamples.sample a N s x)
      (GaussianRootSamples.sample a N t x) N (unit s+unit t) (unit s*unit t) := by
  refine .allI (.impI ?_)
  have cn : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have actual := GaussianCoefficientNameBounds.CN_at a (Syn.shift N) (Syn.shift x)
    (PTm.monus (Syn.shift N) (succ (var 0))) (Syn.shift s) (Syn.shift t) cn.wk
    (GaussianApproximateFactorization.remaining_active _ _ Prf.hyp0)
  simpa only [Syn.shift,GaussianRootSamples.subst_sample,subst_unit,PTm.subst_add,PTm.subst_mul] using
    distance_congr (GaussianRootSamples.sample_coefficient a (Syn.shift N) (Syn.shift s) (Syn.shift x) (var 0) Prf.hyp0).eqSymm
      (GaussianRootSamples.sample_coefficient a (Syn.shift N) (Syn.shift t) (Syn.shift x) (var 0) Prf.hyp0).eqSymm
      (.eqRefl _) (.eqRefl _) actual

/-- Actual coefficient variation and actual point variation give the exact
source T-weighted regularity; no value-name law is an input. -/
theorem observation_regular_at (a : PR 3) (point : PR 2) (N U x s t : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U x) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    distanceBounded (observation a point N x s) (observation a point N x t)
      (T a N U x*(unit s+unit t)) (unit s*unit t) := by
  have pos := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive t)
  have first := GaussianRationalHornerPerturbation.monic_evaluation_bound
    (GaussianRootSamples.sample a N s x) (GaussianRootSamples.sample a N t x) (ap2 point s x)
    N U (unit s+unit t) (unit s*unit t)
    (GaussianRootSamples.sample_length a N s x) (GaussianRootSamples.sample_length a N t x)
    (GaussianRootSamples.sample_leading a N s x) (GaussianRootSamples.sample_leading a N t x)
    hU pos (sample_errors a N x s t hCN) (GaussianRootApproximationWitness.point_at point U x s hBounds)
  have second := GaussianRationalHornerLipschitz.evaluation_bound (GaussianRootSamples.sample a N t x)
    (ap2 point s x) (ap2 point t x) N U (A a N x) (unit s+unit t) (unit s*unit t)
    (GaussianRootSamples.sample_length a N t x) (GaussianRootResidualFromHit.sample_coefficients a N t x hCN)
    (GaussianRootApproximationWitness.point_at point U x s hBounds)
    (GaussianRootApproximationWitness.point_at point U x t hBounds) pos
    (GaussianEuclideanDistanceName.point_cn_at point x s t hPoint)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by
    unfold T C GaussianRootSchedule.coefficientConstant
    ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ pos first second)

theorem exponent_ge_index (a : PR 3) (N U x k : PTm n) : Γ ⊢[PRAAx] le k (exponent a N U x k) :=
  le_add_right _ _

theorem exponent_unit (a : PR 3) (N U x k : PTm n) : Γ ⊢[PRAAx]
    unit (exponent a N U x k) ≐ unit k*unit (normalizer a N U x) := pw_add _ _ _

theorem normalizer_budget (a : PR 3) (N U x : PTm n) : Γ ⊢[PRAAx]
    le (T a N U x) (unit (normalizer a N U x)) :=
  le_trans (Prf.andE₁ (GaussianRootSchedule.binary_length_correct _))
    (GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (le_add_right _ _))

theorem unit_exponent_ge (a : PR 3) (N U x k : PTm n) : Γ ⊢[PRAAx]
    le (unit k) (unit (exponent a N U x k)) :=
  GaussianFactorBudget.power_monotone_length _ _ _ (le_succ_self one) (exponent_ge_index a N U x k)

theorem normalized_regularity_budget (a : PR 3) (N U x s t : PTm n) : Γ ⊢[PRAAx]
    le ((T a N U x*(unit (exponent a N U x s)+unit (exponent a N U x t)))*(unit s*unit t))
      ((unit s+unit t)*(unit (exponent a N U x s)*unit (exponent a N U x t))) := by
  have h := le_mul_mono (normalizer_budget (Γ := Γ) a N U x)
    (le_refl ((unit s+unit t)*unit (normalizer a N U x)*unit s*unit t))
  have hs := natEq (exponent_unit (Γ := Γ) a N U x s)
  have ht := natEq (exponent_unit (Γ := Γ) a N U x t)
  apply le_congr ?_ ?_ h
  · apply deriveNat
    ipra_simps
    rw [hs,ht]
    ring
  · apply deriveNat
    ipra_simps
    rw [hs,ht]
    ring

theorem value_regular_at (a : PR 3) (point : PR 2) (N U x s t : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U x) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    distanceBounded (value a point N U x s) (value a point N U x t)
      (unit s+unit t) (unit s*unit t) :=
  distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _))
    (positive_product _ _ (unit_positive _) (unit_positive _))
    (normalized_regularity_budget a N U x s t)
    (observation_regular_at a point N U x (exponent a N U x s) (exponent a N U x t) hCN hPoint hBounds hU)

def valueZero (a : PR 3) (point : PR 2) (N U x : PTm n) : Fm PTm n :=
  .all (bounded (value a point (Syn.shift N) (Syn.shift U) (Syn.shift x) (var 0)) one (unit (var 0)))

@[simp] theorem subst_valueZero {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2) (N U x : PTm n) :
    (valueZero a point N U x).subst σ = valueZero a point (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) := by
  simp [valueZero,Syn.subst_shift,Syn.shift_subst]

theorem value_zero_at (a : PR 3) (point : PR 2) (N U x k : PTm n)
    (h : Γ ⊢[PRAAx] valueZero a point N U x) : Γ ⊢[PRAAx] bounded (value a point N U x k) one (unit k) := by
  simpa [valueZero] using h.allE k

theorem normalized_zero_value_at (a : PR 3) (point : PR 2) (N U x k : PTm n)
    (h : Γ ⊢[PRAAx] normalizedZero a point N U x) : Γ ⊢[PRAAx] bounded (value a point N U x k) one (unit k) := by
  have raw := GaussianRootApproximationWitness.zero_at a point N U x (exponent a N U x k) h
  have budget : Γ ⊢[PRAAx] le (T a N U x*unit k) (one*unit (exponent a N U x k)) := by
    have h := le_mul_mono (normalizer_budget (Γ := Γ) a N U x) (le_refl (unit k))
    apply le_congr (.eqRefl _) ?_ h
    apply deriveNat
    have e := natEq (exponent_unit (Γ := Γ) a N U x k)
    ipra_simps
    rw [e]
    ring
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (unit_positive _) (unit_positive _) budget raw

theorem normalized_zero_to_value_zero (a : PR 3) (point : PR 2) (N U x : PTm n)
    (h : Γ ⊢[PRAAx] normalizedZero a point N U x) : Γ ⊢[PRAAx] valueZero a point N U x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] normalizedZero a point (Syn.shift N) (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRootApproximationWitness.subst_normalizedZero,Syn.shift] using h.shift
  exact normalized_zero_value_at a point _ _ _ (var 0) hs

/-- Every original observation has the claimed residual plus an explicitly
vanishing dyadic slack, derived from the actual value name. -/
theorem observation_slack_at (a : PR 3) (point : PR 2) (N U x s k : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U x) (hU : Γ ⊢[PRAAx] le one U)
    (hZero : Γ ⊢[PRAAx] valueZero a point N U x) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (observation a point N x s) (T a N U x) (unit s) (T a N U x+one) k := by
  have regular := observation_regular_at a point N U x s (exponent a N U x k) hCN hPoint hBounds hU
  have near := value_zero_at a point N U x k hZero
  have den := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive (exponent a N U x k))
  have norm := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ den (unit_positive k) regular near
  have targetDen := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive k)
  have gap := natEq (eq_add_of_le (unit_exponent_ge (Γ := Γ) a N U x k))
  have cross : Γ ⊢[PRAAx]
      le ((T a N U x*(unit s+unit (exponent a N U x k))*unit k+one*(unit s*unit (exponent a N U x k)))*(unit s*unit k))
        ((T a N U x*unit k+(T a N U x+one)*unit s)*((unit s*unit (exponent a N U x k))*unit k)) := by
    apply le_of_eq_add (d := T a N U x*unit s*unit s*unit k*PTm.monus (unit (exponent a N U x k)) (unit k))
    apply deriveNat
    ipra_simps
    rw [gap]
    ring
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ den (unit_positive k)) targetDen cross norm

theorem observation_from_value_zero (a : PR 3) (point : PR 2) (N U x s : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U x) (hU : Γ ⊢[PRAAx] le one U)
    (hZero : Γ ⊢[PRAAx] valueZero a point N U x) : Γ ⊢[PRAAx]
    bounded (observation a point N x s) (T a N U x) (unit s) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (T a N U x+one) (unit_positive s)
  refine .allI ?_
  have cn : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have pc : Γ.map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift x) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hPoint.shift
  have bounds : Γ.map Fm.shift ⊢[PRAAx] pointBounds point (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRootApproximationWitness.subst_pointBounds,Syn.shift] using hBounds.shift
  have u : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift U) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hU.shift
  have hz : Γ.map Fm.shift ⊢[PRAAx] valueZero a point (Syn.shift N) (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,subst_valueZero,Syn.shift] using hZero.shift
  simpa only [Syn.shift,subst_observation,GaussianRootApproximationWitness.subst_T,subst_unit,
    PTm.subst_add,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    observation_slack_at a point (Syn.shift N) (Syn.shift U) (Syn.shift x) (Syn.shift s) (var 0) cn pc bounds u hz

theorem value_zero_to_normalized_zero (a : PR 3) (point : PR 2) (N U x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U x) (hU : Γ ⊢[PRAAx] le one U)
    (hZero : Γ ⊢[PRAAx] valueZero a point N U x) : Γ ⊢[PRAAx] normalizedZero a point N U x := by
  refine .allI ?_
  have cn : Γ.map Fm.shift ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift
  have pc : Γ.map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift x) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hPoint.shift
  have bounds : Γ.map Fm.shift ⊢[PRAAx] pointBounds point (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRootApproximationWitness.subst_pointBounds,Syn.shift] using hBounds.shift
  have u : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift U) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hU.shift
  have hz : Γ.map Fm.shift ⊢[PRAAx] valueZero a point (Syn.shift N) (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,subst_valueZero,Syn.shift] using hZero.shift
  exact observation_from_value_zero a point _ _ _ (var 0) cn pc bounds u hz

theorem zero_iff (a : PR 3) (point : PR 2) (N U x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U x) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    Fm.iff (normalizedZero a point N U x) (valueZero a point N U x) :=
  .andI (.impI (normalized_zero_to_value_zero a point _ _ _ Prf.hyp0))
    (.impI (value_zero_to_normalized_zero a point _ _ _ hCN.wk hPoint.wk hBounds.wk hU.wk Prf.hyp0))

def nameData (N U x : PTm n) : PTm n := pairT N (pairT U x)
def nameBody (a : PR 3) (point : PR 2) : PTm 2 :=
  value a point (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def nameF (a : PR 3) (point : PR 2) : PR 2 := PTm.toPR (nameBody a point)

@[simp] theorem subst_nameData {m : ℕ} (σ : Fin n → PTm m) (N U x : PTm n) :
    Syn.subst σ (nameData N U x) = nameData (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) := by simp [nameData]

theorem value_congr (a : PR 3) (point : PR 2) {N N' U U' x x' k k' : PTm n}
    (hN : Γ ⊢[PRAAx] N ≐ N') (hU : Γ ⊢[PRAAx] U ≐ U')
    (hx : Γ ⊢[PRAAx] x ≐ x') (hk : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx]
    value a point N U x k ≐ value a point N' U' x' k' := by
  ipra_congr (value a point (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hN, hU, hx, hk]

theorem name_at (a : PR 3) (point : PR 2) (N U x k : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF a point) k (nameData N U x) ≐ value a point N U x k := by
  have program : Γ ⊢[PRAAx] ap2 (nameF a point) k (nameData N U x) ≐
      value a point (fstT (nameData N U x)) (fstT (sndT (nameData N U x)))
        (sndT (sndT (nameData N U x))) k := by
    simpa [nameF,nameBody,ap2] using toPR_eq (Γ := Γ) (nameBody a point) ![k,nameData N U x]
  have tail : Γ ⊢[PRAAx] sndT (nameData N U x) ≐ pairT U x := snd_pair _ _
  exact program.eqTrans (value_congr a point (fst_pair _ _)
    ((congrFst tail).eqTrans (fst_pair _ _)) ((congrSnd tail).eqTrans (snd_pair _ _)) (.eqRefl _))

theorem value_canonical (a : PR 3) (point : PR 2) (N U x k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (value a point N U x k) :=
  GaussianRationalHorner.horner_canonical _ _ _

/-- The returned PR2 schema is a genuine fast Gaussian point name. Degree,
radius and persistent coefficient/point data are numerical packed inputs. -/
theorem name_fast (a : PR 3) (point : PR 2) (N U x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U x) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    pointCN (nameF a point) (nameData N U x) := by
  refine .allI (.allI ?_)
  have cn : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] CN a (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianCoefficientNameBounds.subst_CN,Syn.shift] using hCN.shift.shift
  have pc : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN point (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianEuclideanDistanceName.subst_pointCN,Syn.shift] using hPoint.shift.shift
  have bounds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      pointBounds point (Syn.shift (Syn.shift U)) (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,GaussianRootApproximationWitness.subst_pointBounds,Syn.shift] using hBounds.shift.shift
  have u : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift U)) := by
    simpa only [Fm.shift,subst_le,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using hU.shift.shift
  simpa only [Syn.shift,subst_nameData,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit] using
    distance_congr (name_at a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift U)) (Syn.shift (Syn.shift x)) (var 1)).eqSymm
      (name_at a point (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift U)) (Syn.shift (Syn.shift x)) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _) (value_regular_at a point _ _ _ (var 1) (var 0) cn pc bounds u)

theorem name_canonical (a : PR 3) (point : PR 2) (N U x k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (nameF a point) k (nameData N U x)) :=
  GaussianRationalHorner.canonical_congr (name_at a point N U x k) (value_canonical a point N U x k)

def nameZero (a : PR 3) (point : PR 2) (N U x : PTm n) : Fm PTm n :=
  .all (bounded (ap2 (nameF a point) (var 0) (nameData (Syn.shift N) (Syn.shift U) (Syn.shift x))) one (unit (var 0)))

@[simp] theorem subst_nameZero {m : ℕ} (σ : Fin n → PTm m) (a : PR 3) (point : PR 2) (N U x : PTm n) :
    (nameZero a point N U x).subst σ = nameZero a point (Syn.subst σ N) (Syn.subst σ U) (Syn.subst σ x) := by
  simp [nameZero,Syn.subst_shift,Syn.shift_subst]

theorem name_zero_to_value_zero (a : PR 3) (point : PR 2) (N U x : PTm n)
    (h : Γ ⊢[PRAAx] nameZero a point N U x) : Γ ⊢[PRAAx] valueZero a point N U x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] nameZero a point (Syn.shift N) (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,subst_nameZero,Syn.shift] using h.shift
  have observed : Γ.map Fm.shift ⊢[PRAAx]
      bounded (ap2 (nameF a point) (var 0) (nameData (Syn.shift N) (Syn.shift U) (Syn.shift x))) one (unit (var 0)) := by
    simpa [nameZero] using hs.allE (var 0)
  exact GaussianRationalReciprocal.bound_congr (name_at a point _ _ _ (var 0)) (.eqRefl _) (.eqRefl _) observed

theorem value_zero_to_name_zero (a : PR 3) (point : PR 2) (N U x : PTm n)
    (h : Γ ⊢[PRAAx] valueZero a point N U x) : Γ ⊢[PRAAx] nameZero a point N U x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] valueZero a point (Syn.shift N) (Syn.shift U) (Syn.shift x) := by
    simpa only [Fm.shift,subst_valueZero,Syn.shift] using h.shift
  simpa only [Syn.shift,subst_nameData] using
    GaussianRationalReciprocal.bound_congr (name_at a point (Syn.shift N) (Syn.shift U) (Syn.shift x) (var 0)).eqSymm
      (.eqRefl _) (.eqRefl _) (value_zero_at a point _ _ _ (var 0) hs)

theorem computed_zero_iff (a : PR 3) (point : PR 2) (N U x : PTm n)
    (hCN : Γ ⊢[PRAAx] CN a N x) (hPoint : Γ ⊢[PRAAx] pointCN point x)
    (hBounds : Γ ⊢[PRAAx] pointBounds point U x) (hU : Γ ⊢[PRAAx] le one U) : Γ ⊢[PRAAx]
    Fm.iff (normalizedZero a point N U x) (nameZero a point N U x) :=
  .andI (.impI (value_zero_to_name_zero a point _ _ _ (normalized_zero_to_value_zero a point _ _ _ Prf.hyp0)))
    (.impI (value_zero_to_normalized_zero a point _ _ _ hCN.wk hPoint.wk hBounds.wk hU.wk
      (name_zero_to_value_zero a point _ _ _ Prf.hyp0)))

theorem actual_value_regularity_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (CN a (var 0) (var 2) ⟶ pointCN point (var 2) ⟶ pointBounds point (var 1) (var 2) ⟶ le one (var 1) ⟶
      distanceBounded (observation a point (var 0) (var 2) (var 3)) (observation a point (var 0) (var 2) (var 4))
        (T a (var 0) (var 1) (var 2)*(unit (var 3)+unit (var 4))) (unit (var 3)*unit (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (observation_regular_at _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem polynomial_value_name_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (CN a (var 0) (var 2) ⟶ pointCN point (var 2) ⟶ pointBounds point (var 1) (var 2) ⟶ le one (var 1) ⟶
      pointCN (nameF a point) (nameData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI
    (name_fast _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem polynomial_value_zero_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (CN a (var 0) (var 2) ⟶ pointCN point (var 2) ⟶ pointBounds point (var 1) (var 2) ⟶ le one (var 1) ⟶
      Fm.iff (normalizedZero a point (var 0) (var 1) (var 2)) (valueZero a point (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI
    (zero_iff _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem polynomial_value_program_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (ap2 (nameF a point) (var 3) (nameData (var 0) (var 1) (var 2)) ≐ value a point (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (name_at _ _ _ _ _ _)

theorem polynomial_computed_zero_closed (a : PR 3) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (CN a (var 0) (var 2) ⟶ pointCN point (var 2) ⟶ pointBounds point (var 1) (var 2) ⟶ le one (var 1) ⟶
      Fm.iff (normalizedZero a point (var 0) (var 1) (var 2)) (nameZero a point (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI
    (computed_zero_iff _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianPolynomialValueName
