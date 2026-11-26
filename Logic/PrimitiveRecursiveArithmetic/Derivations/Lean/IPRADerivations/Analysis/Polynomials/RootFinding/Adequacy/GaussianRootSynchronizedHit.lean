import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianMonicRootAdequacy
import IPRADerivations.AnalyticNumberTheory.RobinThreePos

/-!
# A fixed-stage hit for every represented monic root

The completed root membership supplies a later support stage. Its cut yields
an actual closest root on that stage. The earlier root cover then carries
that witness to stage k+1. The original point sample at k+1 is within 2^-k
of an actual entry at the same stage.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRootSynchronizedHit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (CN unit unit_positive)
open GaussianMonicRootSupport (roots roots_length root_support)
open GaussianMonicRootAdequacy (member)
open GaussianRootMembership (stageCondition member_at subst_stageCondition)
open GaussianEuclideanDistanceName (pointCN distanceLE shifted cut_to_hit hit_radius_mono hit_triangle point_cn_at subst_hit)
open GaussianEuclideanPointDistance (selected selected_range minimum_of_hit)
open GaussianRationalCover (cover hit hit_intro)
open GaussianRationalMetric (distanceBounded)
open GaussianRootSupport (coverDenominator)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem cover_at (S T A B j : PTm n) (h : Γ ⊢[PRAAx] cover S T A B)
    (hj : Γ ⊢[PRAAx] lt j (length S)) :
    Γ ⊢[PRAAx] hit (entry S j) T A B := by
  have shape : cover S T A B = .all (lt (var 0) (length (Syn.shift S)) ⟶
      hit (entry (Syn.shift S) (var 0)) (Syn.shift T) (Syn.shift A) (Syn.shift B)) := by
    simp only [cover,hit,Syn.shift,Foundations.MasterCertificate.subst_entry,Syn.subst_var,Fin.succ_zero_eq_one]
  rw [shape] at h
  have h' : Γ ⊢[PRAAx] lt j (length S) ⟶ hit (entry S j) T A B := by
    simpa only [Fm.subst_imp,subst_lt,Foundations.SequenceComposition.subst_length,
      subst_hit,Foundations.MasterCertificate.subst_entry,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE j
  exact .impE h' hj

private theorem unit_offset (k : PTm n) (j : ℕ) : Γ ⊢[PRAAx] unit (k+num j) ≐ unit k*num (2^j) := by
  refine (pw_add two k (num j)).eqTrans (congrMul (.eqRefl _) ?_)
  apply deriveNat
  have two_eq : Γ ⊢[PRAAx] (two : PTm n) ≐ num 2 := by ipra_ring
  rw [AnalyticNumberTheory.RobinThreePos.pw_lit, natEq two_eq]
  simp only [Q.mk_num, Nat.cast_pow, Nat.cast_ofNat, map_pow]

def fine (k : PTm n) : PTm n := k+num 4
def resolution (k : PTm n) : PTm n := coverDenominator (k+one)

@[simp] theorem subst_fine {l : ℕ} (σ : Fin n → PTm l) (k : PTm n) :
    Syn.subst σ (fine k) = fine (Syn.subst σ k) := by simp [fine]

theorem resolution_value (k : PTm n) : Γ ⊢[PRAAx] resolution k ≐ unit k*num 8 :=
  (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] k+one+two ≐ k+num 3) (.eqRefl _)).eqTrans (unit_offset k 3)

theorem fine_value (k : PTm n) : Γ ⊢[PRAAx] unit (fine k) ≐ unit k*num 16 :=
  unit_offset k 4

theorem query_value (k : PTm n) : Γ ⊢[PRAAx] unit (shifted (fine k)) ≐ unit k*num 64 :=
  (congrAp2 powF (by unfold shifted fine; ipra_ring : Γ ⊢[PRAAx] shifted (fine k) ≐ k+num 6) (.eqRefl _)).eqTrans
    (unit_offset k 6)

theorem point_budget (k : PTm n) : Γ ⊢[PRAAx] le
    ((unit (k+one)+unit (shifted (fine k)))*resolution k)
    (num 5*(unit (k+one)*unit (shifted (fine k)))) := by
  have s := natEq (GaussianRootMembershipBudget.unit_add_one (Γ := Γ) k)
  have r := natEq (resolution_value (Γ := Γ) k)
  have q := natEq (query_value (Γ := Γ) k)
  apply le_of_eq_add (d := (num 7*num 16)*unit k*unit k)
  apply deriveNat
  ipra_simps
  rw [s,q,r]
  ring

theorem cut_budget (k : PTm n) : Γ ⊢[PRAAx] le
    ((one*unit (fine k)+two*unit (fine k))*resolution k)
    (two*(unit (fine k)*unit (fine k))) := by
  have f := natEq (fine_value (Γ := Γ) k)
  have r := natEq (resolution_value (Γ := Γ) k)
  apply le_of_eq_add (d := (num 8*num 16)*unit k*unit k)
  apply deriveNat
  ipra_simps
  rw [f,r]
  ring

theorem combine_budget (k : PTm n) : Γ ⊢[PRAAx] le
    ((num 7*resolution k+one*resolution k)*unit k) (one*(resolution k*resolution k)) := by
  have r := natEq (resolution_value (Γ := Γ) k)
  apply le_of_eq_add (d := ConciseIPRA.PTm.zero)
  apply deriveNat
  ipra_simps
  rw [r]
  ring

theorem stage_hit (a : PR 3) (point : PR 2) (N x k t : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] CN a N x)
    (hp : Γ ⊢[PRAAx] pointCN point x)
    (hs : Γ ⊢[PRAAx] stageCondition GaussianMonicRD.step a point N x (fine k) t) :
    Γ ⊢[PRAAx] hit (ap2 point (k+one) x) (roots a N (k+one) x) one (unit k) := by
  let earlier := roots a N (k+one) x
  let later := roots a N t x
  let observation := ap2 point (k+one) x
  let query := ap2 point (shifted (fine k)) x
  let D := resolution k
  have hD : Γ ⊢[PRAAx] le one D := GaussianRootSupport.cover_denominator_positive (k+one)
  have hL : Γ ⊢[PRAAx] le one (length later) := le_congr (.eqRefl _) (roots_length a N t x).eqSymm hn
  have time : Γ ⊢[PRAAx] le (k+one) (fine k) := le_of_eq_add (d := num 3) (by unfold fine; ipra_ring)
  have hcovers := root_support a N (k+one) t x hc hn (le_trans time (.andE₁ hs))
  have original : Γ ⊢[PRAAx] hit query later (one*unit (fine k)+two*unit (fine k)) (unit (fine k)*unit (fine k)) :=
    cut_to_hit point later x one (unit (fine k)) (fine k) hL (unit_positive _) (.andE₂ hs)
  have hitLater := hit_radius_mono query later _ _ two D
    (positive_product _ _ (unit_positive _) (unit_positive _)) hD (cut_budget k) original
  let j := selected query later
  have hj : Γ ⊢[PRAAx] lt j (length later) := selected_range query later hL
  have closeQuery : Γ ⊢[PRAAx] distanceBounded query (entry later j) two D :=
    minimum_of_hit query later two D hitLater
  have closeObservation := GaussianRationalDistanceOrder.distance_radius_mono observation query _ _ (num 5) D
    (positive_product _ _ (unit_positive _) (unit_positive _)) hD (point_budget k)
    (point_cn_at point x (k+one) (shifted (fine k)) hp)
  have first : Γ ⊢[PRAAx] distanceBounded observation (entry later j) (num 7) D :=
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ (num 5) two D hD closeObservation closeQuery)
  have hitEarlier : Γ ⊢[PRAAx] hit (entry later j) earlier one D :=
    cover_at later earlier one D j (.andE₂ hcovers) hj
  exact hit_radius_mono _ _ _ _ _ _ (positive_product _ _ hD hD) (unit_positive k) (combine_budget k)
    (hit_triangle observation (entry later j) earlier (num 7) D one D hD hD first hitEarlier)

theorem member_hit (a : PR 3) (point : PR 2) (N x k : PTm n)
    (hn : Γ ⊢[PRAAx] le one N) (hc : Γ ⊢[PRAAx] CN a N x)
    (hp : Γ ⊢[PRAAx] pointCN point x) (hm : Γ ⊢[PRAAx] member a point N x) :
    Γ ⊢[PRAAx] hit (ap2 point (k+one) x) (roots a N (k+one) x) one (unit k) := by
  refine .exE (member_at GaussianMonicRD.step a point N x (fine k) hm) ?_
  let E := stageCondition GaussianMonicRD.step a point (Syn.shift N) (Syn.shift x) (Syn.shift (fine k)) (var 0)
  let Δ := E :: Γ.map Fm.shift
  have n' : Δ ⊢[PRAAx] le one (Syn.shift N) := by simpa [Δ,Fm.shift,Syn.shift,one] using hn.shift.wk
  have c' : Δ ⊢[PRAAx] CN a (Syn.shift N) (Syn.shift x) := by simpa [Δ,Fm.shift,Syn.shift] using hc.shift.wk
  have p' : Δ ⊢[PRAAx] pointCN point (Syn.shift x) := by simpa [Δ,Fm.shift,Syn.shift] using hp.shift.wk
  have stage : Δ ⊢[PRAAx] stageCondition GaussianMonicRD.step a point (Syn.shift N) (Syn.shift x)
      (fine (Syn.shift k)) (var 0) := by simpa [Δ,E,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] E)
  simpa [Δ,E,Fm.shift,Syn.shift,one] using stage_hit a point (Syn.shift N) (Syn.shift x) (Syn.shift k) (var 0) n' c' p' stage

theorem actual_member_synchronized_hit_closed (a : PR 3) (point : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 0) ⟶ CN a (var 0) (var 1) ⟶ pointCN point (var 1) ⟶ member a point (var 0) (var 1) ⟶
        hit (ap2 point (var 2+one) (var 1)) (roots a (var 0) (var 2+one) (var 1)) one (unit (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI
    (member_hit a point _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRootSynchronizedHit
