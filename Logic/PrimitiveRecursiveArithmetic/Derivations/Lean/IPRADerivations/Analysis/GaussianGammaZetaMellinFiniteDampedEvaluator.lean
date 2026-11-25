import IPRADerivations.Analysis.GaussianGammaZetaMellinDampedPoint
import IPRADerivations.Analysis.GaussianEulerDampedCompactName

/-!
# An evaluator for the original finite damped prefix

Every row is an unchanged positive-scale Euler observation. The
evaluator reads them at one sufficiently late clock. Its comparison
with the finite reciprocal geometric identity pays only observation
errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedEvaluator

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerCompactPowerMajorant (majorant original_power_observation)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaZetaMellinDampedPoint (point_error cost)
open GaussianGammaZetaMellinDecayPrefix (weighted_sum_at weighted_term_at powerSample prefix_error roundingCost)
open GaussianGammaZetaMellinIntegrand (factorClock)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono distance_triangle_same)
open GaussianRationalFiniteSum (sum multiplyBody)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Damped" => GaussianEulerPositiveScalingIntegrand.evaluatorF
local notation "dampData" => GaussianEulerPositiveScalingIntegrand.fixedData

def rawData (p t z B : PTm n) : PTm n := pairT p (pairT t (pairT z B))

def rawBody : PTm 2 :=
  let x := var 1
  let d := sndT (sndT x)
  ap3 Damped (fstT x) (fstT (sndT x)) (dampData (fstT d) (sndT d) (succ (var 0)) one)

def raw (p t z B N : PTm n) : PTm n := sum rawBody N (rawData p t z B)

def data (z B N Q : PTm n) : PTm n := pairT Q (pairT N (pairT z B))
def evaluatorTerm (p t x : PTm n) : PTm n :=
  let d := sndT (sndT x)
  raw (exponent (fstT x) p) t (fstT d) (sndT d) (fstT (sndT x))
def evaluatorF : PR 3 := PTm.toPR (evaluatorTerm (var 0) (var 1) (var 2))

def budget (R H T N : PTm n) : PTm n := N*(cost R H T+one)

@[simp] theorem subst_rawData {m : ℕ} (σ : Fin n → PTm m) (p t z B : PTm n) :
    Syn.subst σ (rawData p t z B) = rawData (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ B) := by simp [rawData]
@[simp] theorem subst_raw {m : ℕ} (σ : Fin n → PTm m) (p t z B N : PTm n) :
    Syn.subst σ (raw p t z B N) = raw (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by simp [raw]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z B N Q : PTm n) :
    Syn.subst σ (data z B N Q) = data (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ Q) := by simp [data]
@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (R H T N : PTm n) :
    Syn.subst σ (budget R H T N) = budget (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ T) (Syn.subst σ N) := by simp [budget,one]

theorem raw_term_at (j p t z B : PTm n) :
    Γ ⊢[PRAAx] inst2 rawBody j (rawData p t z B) ≐ ap3 Damped p t (dampData z B (succ j) one) := by
  let x := rawData p t z B
  have first := snd_pair (Γ := Γ) p (pairT t (pairT z B))
  have last := (congrSnd first).eqTrans (snd_pair t (pairT z B))
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (ap3 Damped (var 0) (var 1) (dampData (var 2) (var 3) (succ (var 4)) one) : PTm 5)
    (σ := ![fstT x,fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x)),j]) (σ' := ![p,t,z,B,j])
    (fun i => by fin_cases i
                 · exact fst_pair p _
                 · exact (congrFst first).eqTrans (fst_pair t _)
                 · exact (congrFst last).eqTrans (fst_pair z B)
                 · exact (congrSnd last).eqTrans (snd_pair z B)
                 · exact .eqRefl j)
  simpa only [rawBody,inst2,subst_ap3,GaussianEulerPositiveScalingIntegrand.subst_fixedData,
    subst_fstT,subst_sndT,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one,Syn.subst_var,Matrix.cons_val,x] using eq

theorem evaluator_at (p t z B N Q : PTm n) :
    Γ ⊢[PRAAx] ap3 evaluatorF p t (data z B N Q) ≐ raw (exponent Q p) t z B N := by
  let x := data z B N Q
  have read : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ evaluatorTerm p t x := by
    simpa [evaluatorF,evaluatorTerm,ap3] using toPR_eq (Γ := Γ) (evaluatorTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]
  have first := snd_pair (Γ := Γ) Q (pairT N (pairT z B))
  have last := (congrSnd first).eqTrans (snd_pair N (pairT z B))
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (raw (exponent (var 0) (var 1)) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![fstT x,p,t,fstT (sndT (sndT x)),sndT (sndT (sndT x)),fstT (sndT x)])
    (σ' := ![Q,p,t,z,B,N])
    (fun i => by fin_cases i
                 · exact fst_pair Q _
                 · exact .eqRefl p
                 · exact .eqRefl t
                 · exact (congrFst last).eqTrans (fst_pair z B)
                 · exact (congrSnd last).eqTrans (snd_pair z B)
                 · exact (congrFst first).eqTrans (fst_pair N _))
  exact read.eqTrans (by simpa only [evaluatorTerm,subst_raw,GaussianFastValueCut.subst_exponent,Syn.subst_var,Matrix.cons_val] using eq)

theorem raw_native_term_at (j q z B a b : PTm n) :
    Γ ⊢[PRAAx] inst2 rawBody j (rawData q (pairT a b) z B) ≐
      GaussianEulerPositiveScalingIntegrand.sample q z B a b (succ j) one := by
  have read := GaussianEulerDampedCompactName.evaluator_raw_at (Γ := Γ) q (pairT a b) z B (succ j) one
  have code := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (GaussianEulerPositiveScalingIntegrand.sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) one : PTm 6)
    (σ := ![q,z,B,fstT (pairT a b),sndT (pairT a b),succ j]) (σ' := ![q,z,B,a,b,succ j])
    (fun i => by fin_cases i
                 · exact .eqRefl q
                 · exact .eqRefl z
                 · exact .eqRefl B
                 · exact fst_pair a b
                 · exact snd_pair a b
                 · exact .eqRefl (succ j))
  have decode := GaussianEulerPositiveScalingIntegrand.sample_at (Γ := Γ) q z B
    (fstT (pairT a b)) (sndT (pairT a b)) (succ j) one
  exact (raw_term_at j q (pairT a b) z B).eqTrans (read.eqTrans (decode.eqSymm.eqTrans (by
    simpa only [GaussianEulerPositiveScalingIntegrand.subst_sample,Syn.subst_var,Matrix.cons_val,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using code)))

private theorem subst_factorClock {m : ℕ} (σ : Fin n → PTm m) (p z B a b : PTm n) :
    Syn.subst σ (factorClock p z B a b) =
      factorClock (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [factorClock]

theorem original_raw_error (p q z R B a b H T N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B H)
    (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b H T)
    (hq : Γ ⊢[PRAAx] le q p) : Γ ⊢[PRAAx]
    distanceBounded (raw q (pairT a b) z B N)
      (GaussianGammaZetaMellinDecayPrefix.weightedValue p z B a b N)
      (N*cost R H T) (unit q) := by
  let x := rawData q (pairT a b) z B
  let f := multiplyBody GaussianGammaZetaMellinDecayPrefix.body
  let y := pairT (powerSample p z B a b) (GaussianGammaZetaMellinDecayPrefix.parameters (factorClock p z B a b) a b)
  have rows : Γ ⊢[PRAAx] termsDistance rawBody f N x y (cost R H T) (unit q) := by
    refine .allI (.impI ?_)
    let s (u : PTm n) := Syn.shift u
    let Δ := lt (var 0) (s N) :: Γ.map Fm.shift
    have hz' : Δ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source (s z) (s R) (s B) (s H) := by
      simpa [s,Δ,Fm.shift,Syn.shift] using hz.shift.wk
    have ht' : Δ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (s a) (s b) (s H) (s T) := by
      simpa [s,Δ,Fm.shift,Syn.shift] using ht.shift.wk
    have hq' : Δ ⊢[PRAAx] le (s q) (s p) := by simpa [s,Δ,Fm.shift,Syn.shift] using hq.shift.wk
    have e := point_error (var 0) (s p) (s q) (s z) (s R) (s B) (s a) (s b) (s H) (s T) hz' ht' hq'
    have a' := raw_native_term_at (Γ := Δ) (var 0) (s q) (s z) (s B) (s a) (s b)
    have b' := weighted_term_at (Γ := Δ) (var 0) (s p) (s z) (s B) (s a) (s b)
    simpa only [s,Δ,Syn.shift,x,f,y,subst_rawData,subst_pairT,GaussianGammaZetaMellinDecayPrefix.subst_powerSample,
      GaussianGammaZetaMellinDecayPrefix.subst_parameters,subst_factorClock,GaussianGammaZetaMellinDampedPoint.subst_cost,
      GaussianCoefficientNameBounds.subst_unit] using
      distance_congr a'.eqSymm b'.eqSymm (.eqRefl _) (.eqRefl _) (distance_symmetric _ _ _ _ (unit_positive (s q)) e)
  exact distance_congr (.eqRefl _) (weighted_sum_at p z B a b N).eqSymm (.eqRefl _) (.eqRefl _)
    (sum_distance _ _ N x y _ _ (unit_positive q) rows)

def comparisonClock (p R H T N a b : PTm n) :=
  exponent (majorant R H T*roundingCost N a b) (exponent (budget R H T N) p)

theorem geometric_point_error (p z R B a b H T N : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B H)
    (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b H T) : Γ ⊢[PRAAx]
    distanceBounded (ap3 evaluatorF p (pairT a b) (data z B N (budget R H T N)))
      (GaussianGammaZetaMellinGeometric.weightedValue (comparisonClock p R H T N a b) z B a b N) two (unit p) := by
  let q := exponent (budget R H T N) p
  let h := comparisonClock p R H T N a b
  let k := factorClock h z B a b
  let r := GaussianGammaZetaMellinDecayRows.clock k b
  let A := majorant R H T
  let C := roundingCost N a b
  have hq : Γ ⊢[PRAAx] le q h := le_add_right _ _
  have hp : Γ ⊢[PRAAx] le p q := le_add_right _ _
  have hk : Γ ⊢[PRAAx] le h k := le_add_right _ _
  have hr : Γ ⊢[PRAAx] le k r := le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_add_right _ _))
  have bq := query_budget (Γ := Γ) (budget R H T N) p
  have cap : Γ ⊢[PRAAx] le (N*cost R H T*unit p) (unit q) :=
    le_trans (le_congr (.eqRefl _) (by unfold budget; ipra_ring)
      (le_add_right (N*cost R H T*unit p) (N*unit p))) bq
  have cmp := original_raw_error h q z R B a b H T N hz ht hq
  have first := distance_radius_mono _ _ _ _ one (unit p) (unit_positive q) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm cap) cmp
  have hPower := original_power_observation k z R B H T a b hz ht
  have raw := GaussianApproximateInverseDistance.multiply_distance (powerSample h z B a b) _ _ A C (unit r)
    (unit_positive r) hPower (prefix_error k N a b ht.andE₁.andE₂)
  have gap : Γ ⊢[PRAAx] le (A*C*unit p) (unit r) :=
    le_trans (le_mul_mono (le_refl (A*C)) (GaussianExponentialReference.unit_monotone hp))
      (le_trans (query_budget (A*C) q) (GaussianExponentialReference.unit_monotone (le_trans hk hr)))
  have second : Γ ⊢[PRAAx] distanceBounded
      (GaussianGammaZetaMellinDecayPrefix.weightedValue h z B a b N)
      (GaussianGammaZetaMellinGeometric.weightedValue h z B a b N) one (unit p) :=
    distance_radius_mono _ _ _ _ one (unit p) (unit_positive r) (unit_positive p)
      (le_congr (.eqRefl _) (one_mul _).eqSymm gap) raw
  exact distance_congr (evaluator_at p (pairT a b) z B N (budget R H T N)).eqSymm (.eqRefl _)
    (by ipra_ring) (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second)

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedEvaluator
