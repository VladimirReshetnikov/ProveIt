import IPRADerivations.Analysis.Names.Rates.GaussianModulusAggregateMap
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianCoordinateRadius
import IPRADerivations.Analysis.Geometry.GaussianEuclideanDistanceVariation

/-!
# Original Gaussian covers transport to actual rational-coordinate lists

The actual two-coordinate vectors retain the original scalar observations.
Original Euclidean radii give the same coordinate radii; actual hit indices
then witness the rational point/list and two-sided cover contracts. Empty
lists remain permitted, and no target cover or shape law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianAggregateCoverTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianModulusAggregateMap (vector vector_length vector_zero vector_one)
open GaussianRationalMetric (distanceBounded)
open RationalHausdorff (pointRadius coordinateRadius originalCover originalClose)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def listBody : PTm 2 := vector (entry (var 1) (var 0))
def vectorList (T : PTm n) : PTm n := sequence listBody (length T) T
def listShape (T : PTm n) : Fm PTm n := .all
  (lt (var 0) (length (Syn.shift T)) ⟶ length (entry (Syn.shift T) (var 0)) ≐ two)

@[simp] theorem subst_vectorList {l : ℕ} (σ : Fin n → PTm l) (T : PTm n) :
    Syn.subst σ (vectorList T) = vectorList (Syn.subst σ T) := by simp [vectorList]
@[simp] theorem subst_listShape {l : ℕ} (σ : Fin n → PTm l) (T : PTm n) :
    (listShape T).subst σ = listShape (Syn.subst σ T) := by simp [listShape,Syn.subst_shift,Syn.shift_subst]

theorem two_cases (i : PTm n) (hi : Γ ⊢[PRAAx] lt i two) : Γ ⊢[PRAAx] i ≐ zero ⋎ i ≐ one := by
  have small : Γ ⊢[PRAAx] le i one := (succ_monus_succ _ _).eqSymm.eqTrans hi
  refine .orE (lt_or_eq_of_le small) (.orI₁ ?_) (.orI₂ Prf.hyp0)
  exact le_antisymm ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0) (zero_le _)

theorem coordinate_of_entries (v w a b i A B : PTm n) (hv : Γ ⊢[PRAAx] entry v i ≐ a)
    (hw : Γ ⊢[PRAAx] entry w i ≐ b) (h : Γ ⊢[PRAAx] RationalValueBounds.radius a b A B) :
    Γ ⊢[PRAAx] coordinateRadius v w i A B := by
  have actual := RationalValueBounds.radius_congr hv.eqSymm hw.eqSymm (.eqRefl A) (.eqRefl B) h
  change Γ ⊢[PRAAx] le (B*Foundations.GapDecision.zabs (RationalValueBounds.cross (entry v i) (entry w i)))
    (A*(RationalSupMetric.denominatorOf (entry v i)*RationalSupMetric.denominatorOf (entry w i)))
  exact le_congr (.eqRefl _) (by ipra_ring) actual

theorem vector_coordinate (z w A B i : PTm n)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius (fstT z) (fstT w) A B ⋏ RationalValueBounds.radius (sndT z) (sndT w) A B)
    (hi : Γ ⊢[PRAAx] lt i two) : Γ ⊢[PRAAx] coordinateRadius (vector z) (vector w) i A B := by
  refine .orE (two_cases i hi) ?_ ?_
  · exact coordinate_of_entries _ _ _ _ i A B
      ((entry_congr (.eqRefl _) Prf.hyp0).eqTrans (vector_zero z))
      ((entry_congr (.eqRefl _) Prf.hyp0).eqTrans (vector_zero w)) (.andE₁ h.wk)
  · exact coordinate_of_entries _ _ _ _ i A B
      ((entry_congr (.eqRefl _) Prf.hyp0).eqTrans (vector_one z))
      ((entry_congr (.eqRefl _) Prf.hyp0).eqTrans (vector_one w)) (.andE₂ h.wk)

theorem vector_radius (z w A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded z w A B) : Γ ⊢[PRAAx] pointRadius (vector z) (vector w) two A B := by
  refine .allI (.impI ?_)
  have bp : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,one] using hB.shift
  have dist : Γ.map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift z) (Syn.shift w) (Syn.shift A) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa [Syn.shift,one,two] using vector_coordinate (Syn.shift z) (Syn.shift w) (Syn.shift A) (Syn.shift B) (var 0)
    (GaussianCoordinateRadius.coordinates _ _ _ _ bp dist).wk
    (by simpa [Syn.shift,one,two] using (Prf.hyp0 : lt (var 0) (Syn.shift two) :: Γ.map Fm.shift ⊢[PRAAx] _))

theorem vector_list_length (T : PTm n) : Γ ⊢[PRAAx] length (vectorList T) ≐ length T := sequence_length _ _ _
theorem vector_list_lookup (T i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length T)) :
    Γ ⊢[PRAAx] entry (vectorList T) i ≐ vector (entry T i) := by
  simpa [vectorList,listBody,inst2] using sequence_decode (Γ := Γ) listBody (x := T) hi
theorem vector_list_shape (T : PTm n) : Γ ⊢[PRAAx] listShape (vectorList T) := by
  refine .allI (.impI ?_)
  have index : lt (var 0) (length (Syn.shift (vectorList T))) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (length (Syn.shift T)) :=
    lt_congr (.eqRefl _) (by simpa [Syn.shift] using vector_list_length (Syn.shift T)) Prf.hyp0
  simpa [listShape,Syn.shift,one,two,length] using
    (congrFst (vector_list_lookup (Syn.shift T) (var 0) index)).eqTrans (vector_length _)

theorem point_radius_congr {v v' w w' : PTm n} (A B : PTm n)
    (hv : Γ ⊢[PRAAx] v ≐ v') (hw : Γ ⊢[PRAAx] w ≐ w') (h : Γ ⊢[PRAAx] pointRadius v w two A B) :
    Γ ⊢[PRAAx] pointRadius v' w' two A B := by
  have out := Prf.eqSubst (pointRadius (var 0) (var 1) two (var 2) (var 3) : Fm PTm 4)
    ![v,w,A,B] ![v',w',A,B] (fun i => by fin_cases i; exact hv; exact hw; exact .eqRefl _; exact .eqRefl _)
    (by simpa using h)
  simpa using out

theorem hit_transport (z T A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] GaussianRationalCover.hit z T A B) :
    Γ ⊢[PRAAx] RationalPointDistance.pointHit (vector z) (vectorList T) two A B := by
  refine .exE h ?_
  let E : Fm PTm (n+1) := lt (var 0) (length (Syn.shift T)) ⋏
    distanceBounded (Syn.shift z) (entry (Syn.shift T) (var 0)) (Syn.shift A) (Syn.shift B)
  have bp : E :: Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,one] using hB.shift.wk
  have j : E :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (length (Syn.shift T)) := .andE₁ Prf.hyp0
  have dist := vector_radius (Syn.shift z) (entry (Syn.shift T) (var 0)) (Syn.shift A) (Syn.shift B)
    bp (Prf.andE₂ (Prf.hyp0 : E :: Γ.map Fm.shift ⊢[PRAAx] E))
  have moved := point_radius_congr (Syn.shift A) (Syn.shift B) (.eqRefl (vector (Syn.shift z)))
    (vector_list_lookup (Syn.shift T) (var 0) j).eqSymm dist
  have result := RationalPointDistance.pointHit_intro (vector (Syn.shift z)) (vectorList (Syn.shift T)) two
    (Syn.shift A) (Syn.shift B) (var 0) (lt_congr (.eqRefl _) (vector_list_length _).eqSymm j) moved
  simpa [E,Fm.shift,Syn.shift] using result

theorem cover_hit_at (S T A B i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] GaussianRationalCover.cover S T A B) (hi : Γ ⊢[PRAAx] lt i (length S)) :
    Γ ⊢[PRAAx] RationalHausdorff.originalHit .left .right (vectorList S) (vectorList T) two A B i := by
  have original := GaussianEuclideanDistanceVariation.cover_at S T A B i h hi
  have transported := hit_transport _ _ _ _ hB original
  have current := RationalPointDistance.pointHit_point_congr _ _ _ _ (vector_list_lookup S i hi).eqSymm transported
  simpa only [RationalHausdorff.originalHit,RationalPointDistance.pointHit,RationalHausdorff.source,
    Syn.shift,Foundations.MasterCertificate.subst_entry] using current

theorem cover_transport (S T A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] GaussianRationalCover.cover S T A B) :
    Γ ⊢[PRAAx] originalCover .left .right (vectorList S) (vectorList T) two A B := by
  refine .allI (.impI ?_)
  have bp : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,one] using hB.shift
  have cov : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalCover.cover (Syn.shift S) (Syn.shift T) (Syn.shift A) (Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have i : lt (var 0) (length (Syn.shift (vectorList S))) :: Γ.map Fm.shift ⊢[PRAAx] lt (var 0) (length (Syn.shift S)) :=
    lt_congr (.eqRefl _) (by simpa [Syn.shift] using vector_list_length (Syn.shift S)) Prf.hyp0
  simpa [Syn.shift,one,two,RationalHausdorff.source] using
    cover_hit_at (Syn.shift S) (Syn.shift T) (Syn.shift A) (Syn.shift B) (var 0) bp.wk cov.wk i

theorem reverse_cover_formula (S T d A B : PTm n) :
    originalCover .right .left S T d A B = originalCover .left .right T S d A B := rfl

theorem close_transport (S T A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] GaussianRationalCover.close S T A B) :
    Γ ⊢[PRAAx] originalClose (vectorList S) (vectorList T) two A B := by
  have originalForward : Γ ⊢[PRAAx] GaussianRationalCover.cover S T A B := Prf.andE₁ h
  have originalBackward : Γ ⊢[PRAAx] GaussianRationalCover.cover T S A B := Prf.andE₂ h
  have forward : Γ ⊢[PRAAx] originalCover .left .right (vectorList S) (vectorList T) two A B :=
    cover_transport S T A B hB originalForward
  have backward : Γ ⊢[PRAAx] originalCover .left .right (vectorList T) (vectorList S) two A B :=
    cover_transport T S A B hB originalBackward
  have reverse : Γ ⊢[PRAAx] originalCover .right .left (vectorList S) (vectorList T) two A B := by
    exact Eq.mpr (congrArg (fun F => Γ ⊢[PRAAx] F) (reverse_cover_formula (vectorList S) (vectorList T) two A B)) backward
  exact .andI forward reverse

def vectorListF : PR 1 := PTm.toPR (vectorList (var 0))
theorem program_at (T : PTm n) : Γ ⊢[PRAAx] ap1 vectorListF T ≐ vectorList T := by
  simpa [vectorListF,ap1] using toPR_eq (Γ := Γ) (vectorList (var 0) : PTm 1) ![T]
theorem returned_length (T : PTm n) : Γ ⊢[PRAAx] length (ap1 vectorListF T) ≐ length T :=
  (congrFst (program_at T)).eqTrans (vector_list_length T)
theorem returned_lookup (T i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length T)) :
    Γ ⊢[PRAAx] entry (ap1 vectorListF T) i ≐ vector (entry T i) :=
  (entry_congr (program_at T) (.eqRefl _)).eqTrans (vector_list_lookup T i hi)
theorem returned_close (S T A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] GaussianRationalCover.close S T A B) :
    Γ ⊢[PRAAx] originalClose (ap1 vectorListF S) (ap1 vectorListF T) two A B := by
  have actual := close_transport S T A B hB h
  have result := Prf.eqSubst (Γ := Γ) (originalClose (var 0) (var 1) two (var 2) (var 3) : Fm PTm 4)
    ![vectorList S,vectorList T,A,B] ![ap1 vectorListF S,ap1 vectorListF T,A,B]
    (fun i => by fin_cases i; exact (program_at S).eqSymm; exact (program_at T).eqSymm; exact .eqRefl _; exact .eqRefl _)
    (by simpa using actual)
  simpa using result

theorem actual_gaussian_vector_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
      pointRadius (vector (var 0)) (vector (var 1)) two (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (vector_radius _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_vector_list_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (length (vectorList (var 0)) ≐ length (var 0) ⋏ listShape (vectorList (var 0))) :=
  closeUniv 1 (.andI (vector_list_length _) (vector_list_shape _))
theorem actual_vector_list_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (length (var 0)) ⟶ entry (vectorList (var 0)) (var 1) ≐ vector (entry (var 0) (var 1))) :=
  closeUniv 2 (.impI (vector_list_lookup _ _ Prf.hyp0))
theorem actual_gaussian_hit_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ GaussianRationalCover.hit (var 0) (var 1) (var 2) (var 3) ⟶
      RationalPointDistance.pointHit (vector (var 0)) (vectorList (var 1)) two (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (hit_transport _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_gaussian_cover_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ GaussianRationalCover.cover (var 0) (var 1) (var 2) (var 3) ⟶
      originalCover .left .right (vectorList (var 0)) (vectorList (var 1)) two (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (cover_transport _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_gaussian_close_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ GaussianRationalCover.close (var 0) (var 1) (var 2) (var 3) ⟶
      originalClose (vectorList (var 0)) (vectorList (var 1)) two (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (close_transport _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_vector_list_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (ap1 vectorListF (var 0) ≐ vectorList (var 0)) := closeUniv 1 (program_at _)
theorem actual_returned_vector_list_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (length (ap1 vectorListF (var 0)) ≐ length (var 0)) := closeUniv 1 (returned_length _)
theorem actual_returned_close_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ GaussianRationalCover.close (var 0) (var 1) (var 2) (var 3) ⟶
      originalClose (ap1 vectorListF (var 0)) (ap1 vectorListF (var 1)) two (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (returned_close _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianAggregateCoverTransport
