import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianCharacteristicAggregateDecoding
import IPRADerivations.Analysis.LinearAlgebra.GaussianSpectralRadius

/-!
# Original Gaussian roots witnessing approximate spectral maxima

The numerical accuracy parameter is kept beside the original matrix data.
The actual finite maximizer seeds the original least-neighbor chain. Its
one-bit Gaussian decoding is a point name supported by the original roots.
The split-data membership formula retains those literal original root lists;
it specializes to the existing member formula when the data coincide.
No coherence is asserted as the accuracy parameter varies.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSpectralRootWitness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCharacteristicAggregate (stageF sample_nonempty stage_regular sample_entry sample_length)
open GaussianCharacteristicRootSupport (roots roots_length)
open GaussianModulusAggregateMap (point vector evaluatorF)
open GaussianSpectralRadius (witnessShift radiusName)
open AggregateEquality (sample unit unit_positive)
open AggregateOptimization (witnessName negateEvaluator pointRegular supportZero)
open GaussianRationalHorner (positive_product)
open GaussianEuclideanDistanceName (pointCN distanceLE)
open GaussianCharacteristicAggregateDecoding (distance_point_vector)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (N k x : PTm n) : PTm n := pairT k (GaussianCharacteristicRootSupport.data N x)
def sourceBody (a : PR 4) : PTm 2 := sample (stageF a) (var 0) (sndT (var 1))
def sourceF (a : PR 4) : PR 2 := PTm.toPR (sourceBody a)
def vectorBody (a : PR 4) : PTm 2 := RationalHausdorff.apply5
  (AggregateOptimization.witnessNameF (stageF a) (negateEvaluator evaluatorF))
  (fstT (var 1)) (var 0) witnessShift two (sndT (var 1))
def vectorF (a : PR 4) : PR 2 := PTm.toPR (vectorBody a)
def rootF (a : PR 4) : PR 2 := GaussianCharacteristicAggregateDecoding.decodedF (vectorF a)
def observation (a : PR 4) (N k t x : PTm n) : PTm n := ap2 (rootF a) t (data N k x)

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (N k x : PTm n) :
    Syn.subst σ (data N k x) = data (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ x) := by simp [data]
@[simp] theorem subst_observation {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N k t x : PTm n) :
    Syn.subst σ (observation a N k t x) = observation a (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ t) (Syn.subst σ x) := by simp [observation]

theorem source_at (a : PR 4) (N k t x : PTm n) : Γ ⊢[PRAAx]
    sample (sourceF a) t (data N k x) ≐ sample (stageF a) t (GaussianCharacteristicRootSupport.data N x) := by
  have h : Γ ⊢[PRAAx] sample (sourceF a) t (data N k x) ≐
      sample (stageF a) t (sndT (data N k x)) := by
    let body := sourceBody a
    change Γ ⊢[PRAAx] PTm.app (PTm.toPR body) ![t,data N k x] ≐
      sample (stageF a) t (sndT (data N k x))
    simpa [body,sourceBody] using toPR_eq (Γ := Γ) body ![t,data N k x]
  exact h.eqTrans (congrAp2 (stageF a) (.eqRefl _) (snd_pair _ _))

theorem vector_at (a : PR 4) (N k t x : PTm n) : Γ ⊢[PRAAx]
    sample (vectorF a) t (data N k x) ≐
      witnessName (stageF a) (negateEvaluator evaluatorF) k t witnessShift two (GaussianCharacteristicRootSupport.data N x) := by
  have h := toPR_eq (Γ := Γ) (vectorBody a) ![t,data N k x]
  have h' : Γ ⊢[PRAAx] sample (vectorF a) t (data N k x) ≐ RationalHausdorff.apply5
      (AggregateOptimization.witnessNameF (stageF a) (negateEvaluator evaluatorF))
      (fstT (data N k x)) t witnessShift two (sndT (data N k x)) := by
    simpa [vectorBody,vectorF,sample,ap2,GaussianSpectralRadius.witnessShift] using h
  exact h'.eqTrans ((congrApp (AggregateOptimization.witnessNameF (stageF a) (negateEvaluator evaluatorF))
    (fun i => by fin_cases i; exact fst_pair _ _; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact snd_pair _ _)).eqTrans
      (AggregateOptimization.witness_program_at _ _ _ _ _ _ _))

theorem point_code_congr {v w : PTm n} (h : Γ ⊢[PRAAx] v ≐ w) : Γ ⊢[PRAAx] point v ≐ point w :=
  congrPairT (Foundations.SequenceComposition.entry_congr h (.eqRefl _))
    (Foundations.SequenceComposition.entry_congr h (.eqRefl _))

theorem observation_at (a : PR 4) (N k t x : PTm n) : Γ ⊢[PRAAx]
    observation a N k t x ≐ point
      (witnessName (stageF a) (negateEvaluator evaluatorF) k (t+one) witnessShift two (GaussianCharacteristicRootSupport.data N x)) :=
  (GaussianCharacteristicAggregateDecoding.decoded_at (vectorF a) t (data N k x)).eqTrans
    (point_code_congr (vector_at a N k (t+one) x))

theorem vector_regular_pair (a : PR 4) (N k x s t : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    RationalHausdorff.pointRadius (sample (vectorF a) s (data N k x)) (sample (vectorF a) t (data N k x))
      two (unit s+unit t) (unit s*unit t) :=
  AggregateChain.point_congr (vector_at a N k s x).eqSymm (vector_at a N k t x).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (AggregateOptimization.witness_name_regular (stageF a) (negateEvaluator evaluatorF) k s t witnessShift two
      (GaussianCharacteristicRootSupport.data N x) (sample_nonempty a N x hn) (stage_regular a N x hn hc))

theorem vector_regular (a : PR 4) (N k x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] pointRegular (vectorF a) two (data N k x) := by
  refine .allI (.allI ?_)
  let M := Syn.shift (Syn.shift N)
  let K := Syn.shift (Syn.shift k)
  let y := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have n' : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift,one] using hn.shift.shift
  have c' : Δ ⊢[PRAAx] GaussianMatrixNames.CN a M y := by simpa [Δ,M,y,Fm.shift,Syn.shift] using hc.shift.shift
  simpa [Δ,M,K,y,Syn.shift,one,two] using vector_regular_pair a M K y (var 1) (var 0) n' c'

theorem root_point_cn (a : PR 4) (N k x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] pointCN (rootF a) (data N k x) :=
  GaussianCharacteristicAggregateDecoding.decoded_point_cn (vectorF a) (data N k x) (vector_regular a N k x hn hc)

/-- The original chain supplies a genuine same-stage point hit. -/
theorem vector_hit (a : PR 4) (N k x t : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    RationalPointDistance.pointHit (sample (vectorF a) (succ t) (data N k x))
      (sample (stageF a) (succ t) (GaussianCharacteristicRootSupport.data N x)) two (num 5) (num 8*unit t) := by
  let S := stageF a
  let d := GaussianCharacteristicRootSupport.data N x
  let s := k+witnessShift
  let i := AggregateOptimization.minimumIndex S (negateEvaluator evaluatorF) s d
  let j := AggregateChain.distanceNeighbor S t s i two d
  have ne : Γ ⊢[PRAAx] AggregateEquality.nonempty S d := sample_nonempty a N x hn
  have reg : Γ ⊢[PRAAx] AggregateEquality.regular S two d := stage_regular a N x hn hc
  have hi : Γ ⊢[PRAAx] lt i (length (sample S s d)) := AggregateOptimization.minimum_index_range S (negateEvaluator evaluatorF) s d ne
  have hj : Γ ⊢[PRAAx] lt j (length (sample S (succ t) d)) := AggregateChain.distance_neighbor_range S t s i two d ne
  have radius : Γ ⊢[PRAAx] RationalHausdorff.pointRadius
      (sample (vectorF a) (succ t) (data N k x)) (entry (sample S (succ t) d) j) two (num 5) (num 8*unit t) :=
    RationalPointDistance.radius_point_congr _ _ _ _ (vector_at a N k (succ t) x).eqSymm
      (AggregateChain.distance_neighbor_radius S t s i two d ne reg hi)
  refine .exI j ?_
  simpa [RationalPointDistance.pointHit] using Prf.andI hj radius

theorem vector_support_bound (a : PR 4) (N k x t : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    le (unit t*RationalPointDistance.numerator (sample (vectorF a) (succ t) (data N k x))
      (sample (sourceF a) (succ t) (data N k x)) two)
      (RationalPointDistance.denominator (sample (vectorF a) (succ t) (data N k x))
        (sample (sourceF a) (succ t) (data N k x)) two) := by
  have original := RationalPointDistance.bound_of_point_hit _ _ _ _ _ (vector_hit a N k x t hn hc)
  have hB : Γ ⊢[PRAAx] le one (num 8*unit t) :=
    positive_product _ _ (le_of_eq_add (d := num 7) (by ipra_ring)) (unit_positive t)
  have relaxed : Γ ⊢[PRAAx] le
      (unit t*RationalPointDistance.numerator (sample (vectorF a) (succ t) (data N k x))
        (sample (stageF a) (succ t) (GaussianCharacteristicRootSupport.data N x)) two)
      (one*RationalPointDistance.denominator (sample (vectorF a) (succ t) (data N k x))
        (sample (stageF a) (succ t) (GaussianCharacteristicRootSupport.data N x)) two) :=
    AggregateChain.fraction_mono hB original
      (le_of_eq_add (d := num 3*unit t) (by ipra_ring))
  let formula : Fm PTm 3 := le (unit (var 2)*RationalPointDistance.numerator (var 0) (var 1) two)
    (one*RationalPointDistance.denominator (var 0) (var 1) two)
  have before : Γ ⊢[PRAAx] formula.subst
      ![sample (vectorF a) (succ t) (data N k x),sample (stageF a) (succ t) (GaussianCharacteristicRootSupport.data N x),t] := by
    simpa [formula] using relaxed
  have after := Prf.eqSubst formula
    ![sample (vectorF a) (succ t) (data N k x),sample (stageF a) (succ t) (GaussianCharacteristicRootSupport.data N x),t]
    ![sample (vectorF a) (succ t) (data N k x),sample (sourceF a) (succ t) (data N k x),t]
    (fun i => by fin_cases i; exact .eqRefl _; exact (source_at a N k (succ t) x).eqSymm; exact .eqRefl _) before
  exact le_congr (.eqRefl _) (one_mul _) (by simpa [formula] using after)

theorem vector_support (a : PR 4) (N k x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] supportZero (vectorF a) (sourceF a) two (data N k x) := by
  refine .allI ?_
  let M := Syn.shift N
  let K := Syn.shift k
  let y := Syn.shift x
  let Δ := Γ.map Fm.shift
  have n' : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift,one] using hn.shift
  have c' : Δ ⊢[PRAAx] GaussianMatrixNames.CN a M y := by simpa [Δ,M,y,Fm.shift,Syn.shift] using hc.shift
  simpa [Δ,M,K,y,Syn.shift,one,two] using vector_support_bound a M K y (var 0) n' c'

def stageAt (a : PR 4) (p : PR 2) (N x y r t : PTm n) : Fm PTm n :=
  le r t ⋏ distanceLE p (roots a N t x) y one (unit r)
def precisionAt (a : PR 4) (p : PR 2) (N x y r : PTm n) : Fm PTm n :=
  .ex (stageAt a p (Syn.shift N) (Syn.shift x) (Syn.shift y) (Syn.shift r) (var 0))
def memberAt (a : PR 4) (p : PR 2) (N x y : PTm n) : Fm PTm n :=
  .all (precisionAt a p (Syn.shift N) (Syn.shift x) (Syn.shift y) (var 0))

@[simp] theorem subst_stageAt {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (p : PR 2) (N x y r t : PTm n) :
    (stageAt a p N x y r t).subst σ = stageAt a p (Syn.subst σ N) (Syn.subst σ x)
      (Syn.subst σ y) (Syn.subst σ r) (Syn.subst σ t) := by simp [stageAt]
@[simp] theorem subst_precisionAt {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (p : PR 2) (N x y r : PTm n) :
    (precisionAt a p N x y r).subst σ = precisionAt a p (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ r) := by
  simp [precisionAt,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_memberAt {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (p : PR 2) (N x y : PTm n) :
    (memberAt a p N x y).subst σ = memberAt a p (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) := by
  simp [memberAt,Syn.subst_shift,Syn.shift_subst]

/-- This is exactly the existing membership formula with independent point data. -/
theorem member_same_data (a : PR 4) (p : PR 2) (N x : PTm n) :
    memberAt a p N x (GaussianCharacteristicRootSupport.data N x) =
      GaussianMonicRootAdequacy.member (GaussianCharacteristicNames.coefficientF a) p N
        (GaussianCharacteristicRootSupport.data N x) := by
  simp only [memberAt,precisionAt,stageAt,GaussianMonicRootAdequacy.member,
    GaussianRootMembership.member,GaussianRootMembership.atPrecision,GaussianRootMembership.stageCondition,
    roots,GaussianMonicRootSupport.roots,unit,GaussianCoefficientNameBounds.unit,
    Syn.shift,GaussianCharacteristicRootSupport.data,subst_pairT]

theorem root_distance_at (a : PR 4) (N k x t j : PTm n) (hj : Γ ⊢[PRAAx] lt j N)
    (hd : Γ ⊢[PRAAx] RationalHausdorff.pointRadius (sample (vectorF a) (succ t) (data N k x))
      (entry (sample (stageF a) (succ t) (GaussianCharacteristicRootSupport.data N x)) j) two (num 5) (num 8*unit t)) :
    Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded (observation a N k t x)
      (entry (roots a N (succ t) x) j) (num 10) (num 8*unit t) := by
  have hb : Γ ⊢[PRAAx] le one (num 8*unit t) :=
    positive_product _ _ (le_of_eq_add (d := num 7) (by ipra_ring)) (unit_positive t)
  have stored : Γ ⊢[PRAAx] RationalHausdorff.pointRadius (sample (vectorF a) (succ t) (data N k x))
      (vector (entry (roots a N (succ t) x) j)) two (num 5) (num 8*unit t) :=
    GaussianAggregateCoverTransport.point_radius_congr _ _ (.eqRefl _) (sample_entry a N (succ t) x j hj) hd
  have gaussian := GaussianModulusAggregateMap.coordinate_to_euclidean _ _ _ _ hb stored
  have original : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (point (sample (vectorF a) (succ t) (data N k x))) (entry (roots a N (succ t) x) j)
      (two*num 5) (num 8*unit t) := distance_point_vector _ _ _ _ gaussian
  have code : Γ ⊢[PRAAx] observation a N k t x ≐ point (sample (vectorF a) (succ t) (data N k x)) :=
    (GaussianCharacteristicAggregateDecoding.decoded_at (vectorF a) t (data N k x)).eqTrans
      (point_code_congr (congrAp2 (vectorF a) (by ipra_ring) (.eqRefl _)))
  exact GaussianRationalDistanceOrder.distance_congr code.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _) original

theorem root_hit (a : PR 4) (N k x t : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    GaussianRationalCover.hit (observation a N k t x) (roots a N (succ t) x) (num 10) (num 8*unit t) := by
  refine .exE (vector_hit a N k x t hn hc) ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (sample (stageF a) (succ (Syn.shift t))
      (GaussianCharacteristicRootSupport.data (Syn.shift N) (Syn.shift x)))) ⋏
    RationalHausdorff.pointRadius (sample (vectorF a) (succ (Syn.shift t)) (data (Syn.shift N) (Syn.shift k) (Syn.shift x)))
      (entry (sample (stageF a) (succ (Syn.shift t)) (GaussianCharacteristicRootSupport.data (Syn.shift N) (Syn.shift x))) (var 0))
      two (num 5) (num 8*unit (Syn.shift t))
  let Δ := E :: Γ.map Fm.shift
  have found : Δ ⊢[PRAAx] E := Prf.hyp0
  have j : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) :=
    lt_congr (.eqRefl _) (sample_length a (Syn.shift N) (succ (Syn.shift t)) (Syn.shift x)) (.andE₁ found)
  have bound := root_distance_at a (Syn.shift N) (Syn.shift k) (Syn.shift x) (Syn.shift t) (var 0) j (.andE₂ found)
  have hit : Δ ⊢[PRAAx] GaussianRationalCover.hit
      (observation a (Syn.shift N) (Syn.shift k) (Syn.shift t) (Syn.shift x))
      (roots a (Syn.shift N) (succ (Syn.shift t)) (Syn.shift x)) (num 10) (num 8*unit (Syn.shift t)) :=
    GaussianRationalCover.hit_intro _ _ _ _ (var 0)
      (lt_congr (.eqRefl _) (roots_length a (Syn.shift N) (succ (Syn.shift t)) (Syn.shift x)).eqSymm j) bound
  simpa [Δ,E,Fm.shift,Syn.shift,one,two] using hit

def memberPrecision (r : PTm n) : PTm n := GaussianCharacteristicAggregateDecoding.memberStage r
@[simp] theorem subst_memberPrecision {l : ℕ} (σ : Fin n → PTm l) (r : PTm n) :
    Syn.subst σ (memberPrecision r) = memberPrecision (Syn.subst σ r) := by simp [memberPrecision]

theorem root_cut_budget (r : PTm n) : Γ ⊢[PRAAx] le
    ((num 10*unit (memberPrecision r)+num 8*unit (memberPrecision r))*unit r)
    (one*((num 8*unit (memberPrecision r))*unit (memberPrecision r))) := by
  have h := natEq (GaussianCharacteristicAggregateDecoding.member_stage_value (Γ := Γ) r)
  apply le_of_eq_add (d := num 14*unit (memberPrecision r)*unit r)
  apply deriveNat
  simp only [memberPrecision]
  ipra_simps
  rw [h]
  ring

theorem root_stage (a : PR 4) (N k x r : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    stageAt a (rootF a) N x (data N k x) r (succ (memberPrecision r)) := by
  refine .andI (le_trans (le_add_right r two) (le_succ_self _)) ?_
  have hb : Γ ⊢[PRAAx] le one (num 8*unit (memberPrecision r)) :=
    positive_product _ _ (le_of_eq_add (d := num 7) (by ipra_ring)) (unit_positive _)
  exact GaussianEuclideanDistanceName.finite_hit_to_cut (rootF a) (roots a N (succ (memberPrecision r)) x)
    (data N k x) (memberPrecision r) (num 10) (num 8*unit (memberPrecision r)) one (unit r)
    (root_point_cn a N k x hn hc) hb (unit_positive r) (root_hit a N k x (memberPrecision r) hn hc) (root_cut_budget r)

theorem root_member (a : PR 4) (N k x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] memberAt a (rootF a) N x (data N k x) := by
  refine .allI ?_
  let M := Syn.shift N
  let K := Syn.shift k
  let y := Syn.shift x
  let Δ := Γ.map Fm.shift
  have n' : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift,one] using hn.shift
  have c' : Δ ⊢[PRAAx] GaussianMatrixNames.CN a M y := by simpa [Δ,M,y,Fm.shift,Syn.shift] using hc.shift
  have stage : Δ ⊢[PRAAx] stageAt a (rootF a) M y (data M K y) (var 0) (succ (memberPrecision (var 0))) :=
    root_stage a M K y (var 0) n' c'
  have precise : Δ ⊢[PRAAx] precisionAt a (rootF a) M y (data M K y) (var 0) := by
    refine .exI (succ (memberPrecision (var 0))) ?_
    simpa [precisionAt] using stage
  simpa [Δ,M,K,y,Syn.shift] using precise

def value (a : PR 4) (N k t x : PTm n) : PTm n :=
  GaussianRationalModulus.lower (observation a N k (t+one) x) (t+two)
@[simp] theorem subst_value {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N k t x : PTm n) :
    Syn.subst σ (value a N k t x) = value a (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ t) (Syn.subst σ x) := by simp [value]

theorem value_at (a : PR 4) (N k t x : PTm n) : Γ ⊢[PRAAx]
    value a N k t x ≐ AggregateOptimization.supremumWitnessValue (stageF a) evaluatorF k t witnessShift two two
      (GaussianCharacteristicRootSupport.data N x) := by
  have observed : Γ ⊢[PRAAx] sample (vectorF a) ((t+one)+one) (data N k x) ≐
      witnessName (stageF a) (negateEvaluator evaluatorF) k (t+two) witnessShift two (GaussianCharacteristicRootSupport.data N x) :=
    (congrAp2 (vectorF a) (by ipra_ring) (.eqRefl _)).eqTrans (vector_at a N k (t+two) x)
  have lower := GaussianCharacteristicAggregateDecoding.decoded_modulus (Γ := Γ) (vectorF a) (t+one) (data N k x) (t+two)
  exact lower.eqTrans ((congrAp3 evaluatorF observed (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianModulusAggregateMap.evaluator_at _ _ _).eqTrans (GaussianModulusAggregateMap.evaluator_at _ _ _).eqSymm))

theorem value_regular (a : PR 4) (N k x t u : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (value a N k t x) (value a N k u x) (unit t+unit u) (unit t*unit u) :=
  RationalValueBounds.radius_congr (value_at a N k t x).eqSymm (value_at a N k u x).eqSymm (.eqRefl _) (.eqRefl _)
    (AggregateOptimization.supremum_witness_regular (stageF a) evaluatorF k t u witnessShift two two two one
      (GaussianCharacteristicRootSupport.data N x) (le_refl one) GaussianSpectralRadius.value_budget
      (sample_nonempty a N x hn) (stage_regular a N x hn hc) (GaussianModulusAggregateMap.map_contract _))

theorem near_maximum (a : PR 4) (N k t l x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (radiusName a N l x) (value a N k t x)
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) :=
  RationalValueBounds.upper_congr (.eqRefl _) (value_at a N k t x).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianSpectralRadius.approximate_maximum a N k t l x hn hc)

/-- Every Gaussian observation comes from an actual original root-list entry. -/
theorem root_disk (a : PR 4) (N k t x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (observation a N k t x) (GaussianCharacteristicRootSupport.radius a N x) one := by
  let S := stageF a
  let d := GaussianCharacteristicRootSupport.data N x
  let s := k+witnessShift
  let r := succ (succ (t+one))
  let i := AggregateOptimization.minimumIndex S (negateEvaluator evaluatorF) s d
  let j := AggregateChain.index S r s i two d
  have ne : Γ ⊢[PRAAx] AggregateEquality.nonempty S d := sample_nonempty a N x hn
  have seed : Γ ⊢[PRAAx] lt i (length (sample S s d)) := AggregateOptimization.minimum_index_range S (negateEvaluator evaluatorF) s d ne
  have index : Γ ⊢[PRAAx] lt j N :=
    lt_congr (.eqRefl _) (sample_length a N (s+r) x) (AggregateChain.index_in_range S r s i two d ne seed)
  have stored : Γ ⊢[PRAAx] witnessName S (negateEvaluator evaluatorF) k (t+one) witnessShift two d ≐
      vector (entry (roots a N (s+r) x) j) := sample_entry a N (s+r) x j index
  have code : Γ ⊢[PRAAx] observation a N k t x ≐ point (vector (entry (roots a N (s+r) x) j)) :=
    (observation_at a N k t x).eqTrans (point_code_congr stored)
  have original := GaussianCharacteristicRootSupport.root_radius a N (s+r) x j hc hn index
  have encoded : Γ ⊢[PRAAx] GaussianRationalMetric.bounded (point (vector (entry (roots a N (s+r) x) j)))
      (GaussianCharacteristicRootSupport.radius a N x) one :=
    RationalArgmin.rationalLE_congr (GaussianModulusAggregateMap.point_vector_norm _).eqSymm (.eqRefl _) original
  exact GaussianRationalReciprocal.bound_congr code.eqSymm (.eqRefl _) (.eqRefl _) encoded

def output (a : PR 4) (N k t x : PTm n) : PTm n := pairT (observation a N k (t+one) x) (value a N k t x)
def outputF (a : PR 4) : PR 4 := PTm.toPR (output a (var 0) (var 1) (var 2) (var 3))
def run (a : PR 4) (N k t x : PTm n) : PTm n := PTm.app (outputF a) ![N,k,t,x]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N k t x : PTm n) :
    Syn.subst σ (output a N k t x) = output a (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ t) (Syn.subst σ x) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N k t x : PTm n) :
    Syn.subst σ (run a N k t x) = run a (Syn.subst σ N) (Syn.subst σ k) (Syn.subst σ t) (Syn.subst σ x) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (a : PR 4) (N k t x : PTm n) : Γ ⊢[PRAAx] run a N k t x ≐ output a N k t x := by
  simpa only [run,outputF,subst_output,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    toPR_eq (Γ := Γ) (output a (var 0) (var 1) (var 2) (var 3) : PTm 4) ![N,k,t,x]
theorem returned_root (a : PR 4) (N k t x : PTm n) : Γ ⊢[PRAAx]
    fstT (run a N k t x) ≐ observation a N k (t+one) x :=
  (congrFst (program_at a N k t x)).eqTrans (fst_pair _ _)
theorem returned_value (a : PR 4) (N k t x : PTm n) : Γ ⊢[PRAAx]
    sndT (run a N k t x) ≐ value a N k t x :=
  (congrSnd (program_at a N k t x)).eqTrans (snd_pair _ _)

theorem returned_modulus (a : PR 4) (N k t x : PTm n) : Γ ⊢[PRAAx]
    sndT (run a N k t x) ≐ GaussianRationalModulus.lower (fstT (run a N k t x)) (t+two) :=
  (returned_value a N k t x).eqTrans
    ((GaussianRationalModulus.sample_at _ _).eqSymm.eqTrans
      ((congrAp2 GaussianRationalModulus.sampleF (returned_root a N k t x).eqSymm (.eqRefl _)).eqTrans
        (GaussianRationalModulus.sample_at _ _)))

theorem returned_near_maximum (a : PR 4) (N k t l x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (radiusName a N l x) (sndT (run a N k t x))
      (unit t*unit l+unit k*unit l+unit k*unit t) (unit k*unit t*unit l) :=
  RationalValueBounds.upper_congr (.eqRefl _) (returned_value a N k t x).eqSymm (.eqRefl _) (.eqRefl _)
    (near_maximum a N k t l x hn hc)

theorem source_certificate (a : PR 4) (N k x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    pointCN (rootF a) (data N k x) ⋏
      (memberAt a (rootF a) N x (data N k x) ⋏ supportZero (vectorF a) (sourceF a) two (data N k x)) :=
  .andI (root_point_cn a N k x hn hc) (.andI (root_member a N k x hn hc) (vector_support a N k x hn hc))

theorem actual_spectral_witness_data_relabel_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sample (sourceF a) (var 2) (data (var 0) (var 1) (var 3)) ≐
      sample (stageF a) (var 2) (GaussianCharacteristicRootSupport.data (var 0) (var 3))) :=
  closeUniv 4 (source_at a _ _ _ _)

theorem actual_spectral_witness_vector_program_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sample (vectorF a) (var 2) (data (var 0) (var 1) (var 3)) ≐
      witnessName (stageF a) (negateEvaluator evaluatorF) (var 1) (var 2) witnessShift two
        (GaussianCharacteristicRootSupport.data (var 0) (var 3))) := closeUniv 4 (vector_at a _ _ _ _)

theorem actual_spectral_witness_root_program_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (observation a (var 0) (var 1) (var 2) (var 3) ≐ point
      (witnessName (stageF a) (negateEvaluator evaluatorF) (var 1) (var 2+one) witnessShift two
        (GaussianCharacteristicRootSupport.data (var 0) (var 3)))) := closeUniv 4 (observation_at a _ _ _ _)

theorem actual_spectral_root_witness_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 2) ⟶
      (pointCN (rootF a) (data (var 0) (var 1) (var 2)) ⋏
        (memberAt a (rootF a) (var 0) (var 2) (data (var 0) (var 1) (var 2)) ⋏
          supportZero (vectorF a) (sourceF a) two (data (var 0) (var 1) (var 2))))) :=
  closeUniv 3 (.impI (.impI (source_certificate a _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_spectral_root_disk_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 3) ⟶
      GaussianRationalMetric.bounded (observation a (var 0) (var 1) (var 2) (var 3))
        (GaussianCharacteristicRootSupport.radius a (var 0) (var 3)) one) :=
  closeUniv 4 (.impI (.impI (root_disk a _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_spectral_witness_modulus_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (value a (var 0) (var 1) (var 2) (var 3) ≐
      AggregateOptimization.supremumWitnessValue (stageF a) evaluatorF (var 1) (var 2) witnessShift two two
        (GaussianCharacteristicRootSupport.data (var 0) (var 3))) := closeUniv 4 (value_at a _ _ _ _)

theorem actual_spectral_witness_value_regular_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 4) ⟶
      RationalValueBounds.radius (value a (var 0) (var 1) (var 2) (var 4)) (value a (var 0) (var 1) (var 3) (var 4))
        (unit (var 2)+unit (var 3)) (unit (var 2)*unit (var 3))) :=
  closeUniv 5 (.impI (.impI (value_regular a _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_spectral_witness_near_maximum_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 4) ⟶
      RationalValueBounds.upper (radiusName a (var 0) (var 3) (var 4)) (sndT (run a (var 0) (var 1) (var 2) (var 4)))
        (unit (var 2)*unit (var 3)+unit (var 1)*unit (var 3)+unit (var 1)*unit (var 2))
        (unit (var 1)*unit (var 2)*unit (var 3))) :=
  closeUniv 5 (.impI (.impI (returned_near_maximum a _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_spectral_root_witness_output_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((fstT (run a (var 0) (var 1) (var 2) (var 3)) ≐ observation a (var 0) (var 1) (var 2+one) (var 3)) ⋏
      sndT (run a (var 0) (var 1) (var 2) (var 3)) ≐
        GaussianRationalModulus.lower (fstT (run a (var 0) (var 1) (var 2) (var 3))) (var 2+two)) :=
  closeUniv 4 (.andI (returned_root a _ _ _ _) (returned_modulus a _ _ _ _))

end LeanProofs.IPRA.Analysis.GaussianSpectralRootWitness
