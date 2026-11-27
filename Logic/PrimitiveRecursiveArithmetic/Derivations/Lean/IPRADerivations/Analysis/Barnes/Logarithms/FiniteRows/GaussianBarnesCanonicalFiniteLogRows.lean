import IPRADerivations.Analysis.Barnes.Logarithms.FiniteRows.GaussianBarnesCanonicalFiniteLog
import IPRADerivations.Analysis.Barnes.Logarithms.FiniteRows.GaussianBarnesCanonicalLogFactor
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHead
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.Families.GaussianNamedFiniteSumFamily

/-!
# The actual finite Barnes logarithm and its original row names

The synchronized rounded interval and the normalized finite sum of
naturally scaled row names use the very same cubic observations.
A common late clock compares all the rows without changing either
name or its actual query schedule.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteLogRows

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalHead (parameters subst_parameters)
open GaussianBarnesCanonicalLogTail (source row_source)
open GaussianBarnesCanonicalLogRow (roundedValue)
open GaussianBarnesCanonicalLogRoundedTail (value)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedFiniteProductFamily (regularRows)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rowF" => GaussianBarnesCanonicalLogFactor.nameF
local notation "rowData" => GaussianBarnesCanonicalLogFactor.data
local notation "finiteF" => GaussianBarnesCanonicalFiniteLog.nameF
local notation "finiteData" => GaussianBarnesCanonicalFiniteLog.data
local notation "scaleClock" => GaussianNamedNaturalScale.clock

def body : PTm 2 :=
  let x := var 1
  rowData (fstT x) (fstT (sndT x)) (fstT (sndT (sndT x))) (succ (sndT (sndT (sndT x))+var 0))

abbrev nameF : PR 2 := GaussianNamedFiniteSumFamily.nameF rowF body

def data (z R B N r : PTm n) : PTm n := GaussianNamedFiniteSumFamily.data r (parameters z R B N)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B N r : PTm n) :
    Syn.subst σ (data z R B N r) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ r) := by
  simp [data]

theorem body_at (i z R B N : PTm n) : Γ ⊢[PRAAx]
    inst2 body i (parameters z R B N) ≐ rowData z R B (succ (N+i)) := by
  let x := parameters z R B N
  let t : PTm 5 := rowData (var 1) (var 2) (var 3) (succ (var 4+var 0))
  have tail := snd_pair (Γ := Γ) z (pairT R (pairT B N))
  have tail₂ := (congrSnd tail).eqTrans (snd_pair R (pairT B N))
  have read := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) t
    (σ := ![i,fstT x,fstT (sndT x),fstT (sndT (sndT x)),sndT (sndT (sndT x))])
    (σ' := ![i,z,R,B,N]) (fun j => by
      fin_cases j
      · exact .eqRefl i
      · exact fst_pair _ _
      · exact (congrFst tail).eqTrans (fst_pair _ _)
      · exact (congrFst tail₂).eqTrans (fst_pair _ _)
      · exact (congrSnd tail₂).eqTrans (snd_pair _ _))
  simpa only [body,inst2,t,x,GaussianBarnesCanonicalLogFactor.subst_data,subst_fstT,subst_sndT,
    PTm.subst_add,PTm.subst_succ,Syn.subst_var,Matrix.cons_val] using read

theorem rows_regular (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] regularRows rowF body r (parameters z R B N) := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
  have rr := GaussianBarnesCanonicalLogFactor.regular (sh z) (sh R) (sh B) (succ (sh N+var 0))
    (row_source (sh z) (sh R) (sh B) (sh N) (var 0) hs)
  simpa only [Syn.shift,sh,Δ,subst_parameters] using
    GaussianGammaCompactCutoffSplit.point_data_congr rowF _ _
      (body_at (var 0) (sh z) (sh R) (sh B) (sh N)).eqSymm rr

private theorem row_clock_budget (p k : PTm n) :
    Γ ⊢[PRAAx] le ((num 5*k)*unit p) (one*DyadicComplexLogarithm.unit (scaleClock p k)) := by
  let M := GaussianNamedNaturalScale.amplification k
  let D := DyadicComplexLogarithm.unit (scaleClock p k)
  have hM := GaussianNamedNaturalScale.cap_budget (Γ := Γ) k k (le_refl _)
  have h := le_mul_mono
    (le_mul_mono (le_of_eq_add (d := num 11) (by ipra_ring : Γ ⊢[PRAAx] (num 16 : PTm n) ≐ num 5+num 11)) hM)
    (le_refl (unit p))
  have e : Γ ⊢[PRAAx] D ≐ unit p*M*num 16 :=
    (GaussianLocalLogarithmName.unit_factor (scaleClock p k)).eqTrans
      (congrMul (GaussianNamedNaturalScale.clock_unit p k) (.eqRefl _))
  exact le_congr (.eqRefl _) ((by ipra_ring : Γ ⊢[PRAAx] num 16*M*unit p ≐ unit p*M*num 16).eqTrans
    (e.eqSymm.eqTrans (one_mul D).eqSymm)) h

private theorem later_row (s v z R B N r i : PTm n) (h : Γ ⊢[PRAAx] source z R B N)
    (hi : Γ ⊢[PRAAx] lt i r) (hv : Γ ⊢[PRAAx] le (scaleClock s (N+r)) v) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 rowF s (inst2 body i (parameters z R B N))) (roundedValue v z R B (succ (N+i))) one (unit s) := by
  let k := succ (N+i)
  let t := scaleClock s k
  have hk : Γ ⊢[PRAAx] le k (N+r) := le_congr (add_succ _ _) (.eqRefl _) (add_le_add₂ (le_refl N) hi)
  have ht : Γ ⊢[PRAAx] le t (scaleClock s (N+r)) :=
    add_le_add₂ (add_le_add₂ (le_refl s) hk) (le_refl two)
  have raw := GaussianBarnesCanonicalLogObservation.ordered_distance t v z R B k (row_source z R B N i h)
    (le_trans ht hv)
  have hU := GaussianLocalLogarithmName.unit_positive (Γ := Γ) t
  have eq := (congrAp2 (Γ := Γ) rowF (.eqRefl s) (body_at i z R B N)).eqTrans (GaussianBarnesCanonicalLogFactor.sample_at s z R B k)
  exact distance_congr eq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hU (unit_positive s) (row_clock_budget s k)
      (distance_symmetric _ _ _ _ hU raw))

theorem observations (p z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B N r)) (ap2 finiteF p (finiteData z R B N r)) two (unit p) := by
  let s := exponent r p
  let c := GaussianBarnesCanonicalFiniteLog.clock p N r
  let v := c+scaleClock s (N+r)
  let b := GaussianNamedFiniteSumFamily.body rowF body
  let x := parameters z R B N
  let y := GaussianBarnesCanonicalLogRoundedTail.data v z R B N
  let U := unit s
  have hU : Γ ⊢[PRAAx] le one U := unit_positive s
  have rows : Γ ⊢[PRAAx] termsDistance b GaussianBarnesCanonicalLogRoundedTail.body r (pairT s x) y one U := by
    refine .allI (.impI ?_)
    let sh (a : PTm n) := Syn.shift a
    let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
    have hv : Δ ⊢[PRAAx] le (scaleClock (sh s) (sh N+sh r)) (sh v) := by
      simpa only [Syn.shift,sh,v,PTm.subst_add,GaussianNamedNaturalScale.subst_clock] using
        (le_add_left (Γ := Δ) (scaleClock (sh s) (sh N+sh r)) (sh c))
    have near := later_row (sh s) (sh v) (sh z) (sh R) (sh B) (sh N) (sh r) (var 0) hs Prf.hyp0 hv
    simpa only [termsDistance,b,x,y,U,Syn.shift,sh,Δ,subst_pairT,subst_parameters,
      GaussianBarnesCanonicalLogRoundedTail.subst_data,GaussianCoefficientNameBounds.subst_unit,one,
      PTm.subst_succ,PTm.subst_zero] using
      distance_congr (GaussianNamedFiniteSumFamily.term_at rowF body (var 0) (sh s) (parameters (sh z) (sh R) (sh B) (sh N))).eqSymm
        (GaussianBarnesCanonicalLogRoundedTail.body_at (sh v) (sh z) (sh R) (sh B) (sh N) (var 0)).eqSymm
        (.eqRefl _) (.eqRefl _) near
  have raw := sum_distance _ _ _ _ _ _ _ hU rows
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B N r)) (value v z R B N r) one (unit p) :=
    distance_congr (GaussianNamedFiniteSumFamily.sample_at rowF body p r x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (distance_radius_mono _ _ _ _ _ _ hU (unit_positive p)
        (le_congr (.eqRefl _) (one_mul _).eqSymm (query_budget r p)) (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) raw))
  have second := GaussianBarnesCanonicalFiniteLog.later_rounding p v z R B N r h (le_add_right _ _)
  exact distance_congr (.eqRefl _) (GaussianBarnesCanonicalFiniteLog.sample_at p z R B N r).eqSymm (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second)

theorem finite_cross (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] crossEquivalent nameF finiteF (data z R B N r) (finiteData z R B N r) := by
  apply GaussianNameRingLaws.equivalent_of_envelope nameF finiteF (data z R B N r) (finiteData z R B N r) two
    (GaussianNamedFiniteSumFamily.regular rowF body r _ (rows_regular z R B N r h))
    (GaussianBarnesCanonicalFiniteLog.regular z R B N r h)
  refine .allI ?_
  let sh (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh N) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,sh,subst_data,
    GaussianBarnesCanonicalFiniteLog.subst_data,two,one,PTm.subst_succ,PTm.subst_zero] using
      observations (var 0) (sh z) (sh R) (sh B) (sh N) (sh r) hs

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteLogRows
