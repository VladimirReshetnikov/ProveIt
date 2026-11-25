import IPRADerivations.Analysis.GaussianAggregateCoverTransport
import IPRADerivations.Analysis.GaussianCharacteristicRootSupport
import IPRADerivations.Analysis.GaussianRootSynchronizedHit
import IPRADerivations.Core.CongruenceTactic

/-!
# The original characteristic root lists as a rational aggregate

The stored vector list is exactly the list of pairs of coordinates of the
characteristic root stage. Its finite covers prove regularity in the
sup-coordinate metric. Every represented characteristic root has
vanishing distance to these actual vector samples at the same stage.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCharacteristicAggregate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCharacteristicRootSupport (data roots roots_length root_support)
open GaussianAggregateCoverTransport (vectorList vector_list_length vector_list_lookup)
open GaussianModulusAggregateMap (vector)
open AggregateEquality (sample unit unit_positive nonempty regular)
open AggregateOptimization (pointRegular supportZero)
open GaussianRootSupport (coverDenominator cover_denominator_positive)
open GaussianEuclideanDistanceName (pointCN point_cn_at)
open RationalHausdorff (originalClose original_close_of_bound bound_of_original_close pointRadius)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def stages (a : PR 4) (N t x : PTm n) : PTm n := vectorList (roots a N t x)
def stageBody (a : PR 4) : PTm 2 := stages a (fstT (var 1)) (var 0) (sndT (var 1))
def stageF (a : PR 4) : PR 2 := PTm.toPR (stageBody a)
def pointF (point : PR 2) : PR 2 := PTm.toPR (vector (ap2 point (var 0) (var 1)))

@[simp] theorem subst_stages {l : ℕ} (σ : Fin n → PTm l) (a : PR 4) (N t x : PTm n) :
    Syn.subst σ (stages a N t x) = stages a (Syn.subst σ N) (Syn.subst σ t) (Syn.subst σ x) := by
  simp [stages]

theorem stages_congr (a : PR 4) {N N' t t' x x' : PTm n} (hn : Γ ⊢[PRAAx] N ≐ N')
    (ht : Γ ⊢[PRAAx] t ≐ t') (hx : Γ ⊢[PRAAx] x ≐ x') :
    Γ ⊢[PRAAx] stages a N t x ≐ stages a N' t' x' := by
  ipra_congr (stages a (var 0) (var 1) (var 2) : PTm 3) with [hn, ht, hx]

theorem stage_at (a : PR 4) (N t x : PTm n) : Γ ⊢[PRAAx] sample (stageF a) t (data N x) ≐ stages a N t x := by
  have reified : Γ ⊢[PRAAx] sample (stageF a) t (data N x) ≐
      stages a (fstT (data N x)) t (sndT (data N x)) := by
    simpa [sample,stageF,stageBody,ap2] using toPR_eq (Γ := Γ) (stageBody a) ![t,data N x]
  exact reified.eqTrans (stages_congr a (fst_pair _ _) (.eqRefl _) (snd_pair _ _))

theorem point_at (point : PR 2) (p d : PTm n) : Γ ⊢[PRAAx]
    sample (pointF point) p d ≐ vector (ap2 point p d) := by
  let body : PTm 2 := vector (ap2 point (var 0) (var 1))
  change Γ ⊢[PRAAx] PTm.app (PTm.toPR body) ![p,d] ≐ vector (ap2 point p d)
  simpa [body] using toPR_eq (Γ := Γ) body ![p,d]

theorem sample_length (a : PR 4) (N t x : PTm n) : Γ ⊢[PRAAx] length (sample (stageF a) t (data N x)) ≐ N :=
  (congrFst (stage_at a N t x)).eqTrans ((vector_list_length _).eqTrans (roots_length a N t x))

theorem sample_entry (a : PR 4) (N t x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    entry (sample (stageF a) t (data N x)) i ≐ vector (entry (roots a N t x) i) :=
  (entry_congr (stage_at a N t x) (.eqRefl _)).eqTrans
    (vector_list_lookup _ _ (lt_congr (.eqRefl _) (roots_length a N t x).eqSymm hi))

theorem sample_nonempty (a : PR 4) (N x : PTm n) (hn : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] nonempty (stageF a) (data N x) := by
  refine .allI ?_
  have pos : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift,one] using hn.shift
  simpa [Syn.shift,one] using le_congr (.eqRefl _) (sample_length a (Syn.shift N) (var 0) (Syn.shift x)).eqSymm pos

theorem sample_shaped (a : PR 4) (N x : PTm n) : Γ ⊢[PRAAx] AggregateChain.shaped (stageF a) two (data N x) := by
  refine .allI (.allI (.impI ?_))
  let M := Syn.shift (Syn.shift N)
  let y := Syn.shift (Syn.shift x)
  let Δ := lt (var 0) (length (sample (stageF a) (var 1) (data M y))) :: (Γ.map Fm.shift).map Fm.shift
  have j : Δ ⊢[PRAAx] lt (var 0) M := lt_congr (.eqRefl _) (sample_length a M (var 1) y) Prf.hyp0
  have shape := (congrFst (sample_entry a M (var 1) y (var 0) j)).eqTrans (GaussianModulusAggregateMap.vector_length _)
  simpa [Δ,M,y,Syn.shift,two,one,length] using shape

private theorem close_lists {S S' T T' : PTm n} (A B : PTm n) (hS : Γ ⊢[PRAAx] S ≐ S')
    (hT : Γ ⊢[PRAAx] T ≐ T') (h : Γ ⊢[PRAAx] originalClose S T two A B) :
    Γ ⊢[PRAAx] originalClose S' T' two A B := by
  have source : Γ ⊢[PRAAx] (originalClose (var 0) (var 1) two (var 2) (var 3) : Fm PTm 4).subst ![S,T,A,B] := by
    simpa using h
  have target := Prf.eqSubst (originalClose (var 0) (var 1) two (var 2) (var 3) : Fm PTm 4)
    ![S,T,A,B] ![S',T',A,B] (fun i => by fin_cases i; exact hS; exact hT; exact .eqRefl _; exact .eqRefl _) source
  simpa using target

theorem regular_pair_ordered (a : PR 4) (N s t x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) (hst : Γ ⊢[PRAAx] le s t) :
    Γ ⊢[PRAAx] originalClose (sample (stageF a) s (data N x)) (sample (stageF a) t (data N x))
      two (unit s+unit t) (unit s*unit t) := by
  let S := sample (stageF a) s (data N x)
  let T := sample (stageF a) t (data N x)
  have hD := cover_denominator_positive (Γ := Γ) s
  have same : Γ ⊢[PRAAx] originalClose S T two one (coverDenominator s) :=
    close_lists _ _ (stage_at a N s x).eqSymm (stage_at a N t x).eqSymm
      (GaussianAggregateCoverTransport.close_transport _ _ _ _ hD (root_support a N s t x hc hn hst))
  have ds : Γ ⊢[PRAAx] le (unit s) (coverDenominator s) :=
    GaussianRootMembershipBudget.unit_monotone s (s+two) (le_add_right _ _)
  have product := AnalyticNumberTheory.PhiLower.le_mul_mono (le_add_left (unit t) (unit s)) ds
  have budget : Γ ⊢[PRAAx] le (one*(unit s*unit t)) ((unit s+unit t)*coverDenominator s) :=
    le_congr (by ipra_ring) (.eqRefl _) product
  exact original_close_of_bound S T two _ _
    (le_congr (.eqRefl _) (sample_length a N s x).eqSymm hn)
    (le_congr (.eqRefl _) (sample_length a N t x).eqSymm hn)
    (AggregateChain.fraction_mono hD (bound_of_original_close S T _ _ _ same) budget)

theorem regular_pair (a : PR 4) (N s t x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) : Γ ⊢[PRAAx]
    originalClose (sample (stageF a) s (data N x)) (sample (stageF a) t (data N x))
      two (unit s+unit t) (unit s*unit t) := by
  refine .orE (le_total s t) (regular_pair_ordered a N s t x hn.wk hc.wk Prf.hyp0) ?_
  have rev := regular_pair_ordered a N t s x hn.wk hc.wk Prf.hyp0
  exact AggregateEquality.close_radius_congr _ _ _ (add_comm _ _) (mul_comm _ _) (.andI (.andE₂ rev) (.andE₁ rev))

theorem stage_regular (a : PR 4) (N x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x) :
    Γ ⊢[PRAAx] regular (stageF a) two (data N x) := by
  refine .allI (.allI ?_)
  let M := Syn.shift (Syn.shift N)
  let y := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have n' : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift,one] using hn.shift.shift
  have c' : Δ ⊢[PRAAx] GaussianMatrixNames.CN a M y := by simpa [Δ,M,y,Fm.shift,Syn.shift] using hc.shift.shift
  simpa [Δ,M,y,Syn.shift,two,one] using regular_pair a M (var 1) (var 0) y n' c'

theorem vector_point_regular (point : PR 2) (d : PTm n) (hp : Γ ⊢[PRAAx] pointCN point d) :
    Γ ⊢[PRAAx] pointRegular (pointF point) two d := by
  refine .allI (.allI ?_)
  let x := Syn.shift (Syn.shift d)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have h' : Δ ⊢[PRAAx] pointCN point x := by simpa [Δ,x,Fm.shift,Syn.shift] using hp.shift.shift
  have radius : Δ ⊢[PRAAx] pointRadius (vector (ap2 point (var 1) x)) (vector (ap2 point (var 0) x))
      two (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0)) :=
    GaussianAggregateCoverTransport.vector_radius _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive (var 1)) (unit_positive (var 0)))
    (point_cn_at point x (var 1) (var 0) h')
  simpa [Δ,x,Syn.shift,two,one] using AggregateChain.point_congr (point_at point (var 1) x).eqSymm
    (point_at point (var 0) x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) radius

theorem member_support_bound (a : PR 4) (point : PR 2) (N k x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hp : Γ ⊢[PRAAx] pointCN point (data N x))
    (hm : Γ ⊢[PRAAx] GaussianMonicRootAdequacy.member (GaussianCharacteristicNames.coefficientF a) point N (data N x)) :
    Γ ⊢[PRAAx] le
      (unit k*RationalPointDistance.numerator (sample (pointF point) (succ k) (data N x))
        (sample (stageF a) (succ k) (data N x)) two)
      (RationalPointDistance.denominator (sample (pointF point) (succ k) (data N x))
        (sample (stageF a) (succ k) (data N x)) two) := by
  let oldPoint := vector (ap2 point (k+one) (data N x))
  let oldList := stages a N (k+one) x
  let newPoint := sample (pointF point) (succ k) (data N x)
  let newList := sample (stageF a) (succ k) (data N x)
  have original := GaussianRootSynchronizedHit.member_hit (GaussianCharacteristicNames.coefficientF a) point
    N (data N x) k hn (GaussianCharacteristicRootSupport.coefficient_name a N x hc) hp hm
  have projected : Γ ⊢[PRAAx] RationalPointDistance.pointHit oldPoint oldList two one (unit k) :=
    GaussianAggregateCoverTransport.hit_transport _ _ _ _ (unit_positive k) original
  have fused := RationalPointDistance.bound_of_point_hit _ _ _ _ _ projected
  have time : Γ ⊢[PRAAx] k+one ≐ succ k := by ipra_ring
  have pv : Γ ⊢[PRAAx] oldPoint ≐ newPoint :=
    ((point_at point _ _).eqSymm.eqTrans (congrAp2 (pointF point) time (.eqRefl _)))
  have lv : Γ ⊢[PRAAx] oldList ≐ newList :=
    ((stage_at a N _ x).eqSymm.eqTrans (congrAp2 (stageF a) time (.eqRefl _)))
  let target : Fm PTm 3 := le (unit (var 2)*RationalPointDistance.numerator (var 0) (var 1) two)
    (one*RationalPointDistance.denominator (var 0) (var 1) two)
  have before : Γ ⊢[PRAAx] target.subst ![oldPoint,oldList,k] := by simpa [target] using fused
  have after := Prf.eqSubst target ![oldPoint,oldList,k] ![newPoint,newList,k]
    (fun i => by fin_cases i; exact pv; exact lv; exact .eqRefl _) before
  exact le_congr (.eqRefl _) (one_mul _) (by simpa [target,newPoint,newList] using after)

theorem member_support (a : PR 4) (point : PR 2) (N x : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] GaussianMatrixNames.CN a N x)
    (hp : Γ ⊢[PRAAx] pointCN point (data N x))
    (hm : Γ ⊢[PRAAx] GaussianMonicRootAdequacy.member (GaussianCharacteristicNames.coefficientF a) point N (data N x)) :
    Γ ⊢[PRAAx] supportZero (pointF point) (stageF a) two (data N x) := by
  refine .allI ?_
  let M := Syn.shift N
  let y := Syn.shift x
  let Δ := Γ.map Fm.shift
  have n' : Δ ⊢[PRAAx] le one M := by simpa [Δ,M,Fm.shift,Syn.shift,one] using hn.shift
  have c' : Δ ⊢[PRAAx] GaussianMatrixNames.CN a M y := by simpa [Δ,M,y,Fm.shift,Syn.shift] using hc.shift
  have p' : Δ ⊢[PRAAx] pointCN point (data M y) := by simpa [Δ,M,y,Fm.shift,Syn.shift] using hp.shift
  have m' : Δ ⊢[PRAAx] GaussianMonicRootAdequacy.member (GaussianCharacteristicNames.coefficientF a) point M (data M y) := by
    simpa [Δ,M,y,Fm.shift,Syn.shift] using hm.shift
  simpa [Δ,M,y,Syn.shift,one,two] using member_support_bound a point M (var 0) y n' c' p' m'

theorem actual_characteristic_aggregate_closed (a : PR 4) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 1) ⟶
      (nonempty (stageF a) (data (var 0) (var 1)) ⋏
        regular (stageF a) two (data (var 0) (var 1)) ⋏ AggregateChain.shaped (stageF a) two (data (var 0) (var 1)))) :=
  closeUniv 2 (.impI (.impI (.andI (sample_nonempty a _ _ Prf.hyp1)
    (.andI (stage_regular a _ _ Prf.hyp1 Prf.hyp0) (sample_shaped a _ _)))))

theorem actual_characteristic_member_support_closed (a : PR 4) (point : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ GaussianMatrixNames.CN a (var 0) (var 1) ⟶ pointCN point (data (var 0) (var 1)) ⟶
      GaussianMonicRootAdequacy.member (GaussianCharacteristicNames.coefficientF a) point (var 0) (data (var 0) (var 1)) ⟶
      supportZero (pointF point) (stageF a) two (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (.impI (.impI (member_support a point _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianCharacteristicAggregate
