import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalNearest

/-!
# Actual rational point-to-list distance and a selected original witness

Finite-demand Section 3, the point-to-aggregate distance used in
`eq:distance-name` and the support lower-bound argument. The common pool
is the actual singleton point appended to the supplied finite target list.
All original coordinate denominators are retained through the proved exact
normalization adapter. A cleared distance bound returns one actual nearest
target index valid for every coordinate; no finite-hit premise is assumed
in that direction. Target nonemptiness remains explicit.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalPointDistance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalHausdorff
  (grid parameter pointRadius subst_pointRadius originalHit source minimum_bound_of_original_hit metric_to_point_radius)
open LeanProofs.IPRA.Analysis.RationalSupMetric (metricF)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.FiniteHausdorff (distanceTo subst_distanceTo)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def singleton (z : PTm n) : PTm n := sequence (var 1 : PTm 2) one z

@[simp] theorem subst_singleton {m : ℕ} (σ : Fin n → PTm m) (z : PTm n) :
    Syn.subst σ (singleton z) = singleton (Syn.subst σ z) := by simp [singleton, one]

theorem singleton_length (z : PTm n) : Γ ⊢[PRAAx] length (singleton z) ≐ one := sequence_length _ _ _
theorem singleton_zero (z : PTm n) : Γ ⊢[PRAAx] entry (singleton z) zero ≐ z := by
  simpa [singleton,inst2] using sequence_decode (Γ := Γ) (var 1 : PTm 2) (x := z) (zero_lt_succ zero)
theorem singleton_index (z : PTm n) : Γ ⊢[PRAAx] lt zero (length (singleton z)) :=
  lt_congr (.eqRefl _) (singleton_length z).eqSymm (zero_lt_succ zero)

def numerator (z T d : PTm n) : PTm n :=
  distanceTo metricF (entry (grid .left (singleton z) T d) zero)
    (grid .right (singleton z) T d) (parameter (singleton z) T d)
def denominator (z T d : PTm n) : PTm n := RationalHausdorff.denominator (singleton z) T d
def rationalDistance (z T d : PTm n) : PTm n := pairT (numerator z T d) (denominator z T d)
def selected (z T d : PTm n) : PTm n := RationalNearest.selected (singleton z) T d zero

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (z T d : PTm n) :
    Syn.subst σ (numerator z T d) = numerator (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ d) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (z T d : PTm n) :
    Syn.subst σ (denominator z T d) = denominator (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ d) := by simp [denominator]
@[simp] theorem subst_rationalDistance {m : ℕ} (σ : Fin n → PTm m) (z T d : PTm n) :
    Syn.subst σ (rationalDistance z T d) = rationalDistance (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ d) := by simp [rationalDistance]
@[simp] theorem subst_selected {m : ℕ} (σ : Fin n → PTm m) (z T d : PTm n) :
    Syn.subst σ (selected z T d) = selected (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ d) := by simp [selected]

theorem denominator_positive (z T d : PTm n) : Γ ⊢[PRAAx] le one (denominator z T d) :=
  RationalSupMetric.commonDenominator_one_le _ _

/-- One original target index witnesses all original coordinate bounds. -/
def pointHit (z T d A B : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (length (Syn.shift T)) ⋏
    pointRadius (Syn.shift z) (entry (Syn.shift T) (var 0)) (Syn.shift d) (Syn.shift A) (Syn.shift B))

@[simp] theorem subst_pointHit {m : ℕ} (σ : Fin n → PTm m) (z T d A B : PTm n) :
    (pointHit z T d A B).subst σ = pointHit (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ d)
      (Syn.subst σ A) (Syn.subst σ B) := by
  simp only [pointHit,Fm.subst_ex,Fm.subst_and,subst_lt,Foundations.SequenceComposition.subst_length,
    Foundations.MasterCertificate.subst_entry,subst_pointRadius,Syn.subst_var,Syn.up_zero,Syn.up_succ,
    Syn.subst_shift,Syn.shift_subst]

theorem pointHit_point_congr {z z' : PTm n} (T d A B : PTm n) (hz : Γ ⊢[PRAAx] z ≐ z')
    (h : Γ ⊢[PRAAx] pointHit z T d A B) : Γ ⊢[PRAAx] pointHit z' T d A B := by
  have hin : Γ ⊢[PRAAx] (pointHit (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5).subst ![z,T,d,A,B] := by simpa using h
  have out := Prf.eqSubst (pointHit (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5)
    ![z,T,d,A,B] ![z',T,d,A,B] (fun i => by fin_cases i <;> first | exact hz | exact .eqRefl _) hin
  simpa using out

theorem radius_point_congr {z z' : PTm n} (y d A B : PTm n) (hz : Γ ⊢[PRAAx] z ≐ z')
    (h : Γ ⊢[PRAAx] pointRadius z y d A B) : Γ ⊢[PRAAx] pointRadius z' y d A B := by
  have hin : Γ ⊢[PRAAx] (pointRadius (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5).subst ![z,y,d,A,B] := by simpa using h
  have out := Prf.eqSubst (pointRadius (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5)
    ![z,y,d,A,B] ![z',y,d,A,B] (fun i => by fin_cases i <;> first | exact hz | exact .eqRefl _) hin
  simpa using out

theorem singleton_hit_eq (z T d A B : PTm n) :
    originalHit .left .right (singleton z) T d A B zero = pointHit (entry (singleton z) zero) T d A B := by
  simp only [originalHit,pointHit,source,Syn.shift,Foundations.MasterCertificate.subst_entry,ConciseIPRA.PTm.subst_zero]

theorem pointHit_intro (z T d A B j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length T))
    (h : Γ ⊢[PRAAx] pointRadius z (entry T j) d A B) : Γ ⊢[PRAAx] pointHit z T d A B := by
  refine .exI j ?_
  simpa only [pointHit,Fm.subst_and,subst_lt,Foundations.SequenceComposition.subst_length,
    Foundations.MasterCertificate.subst_entry,subst_pointRadius,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI hj h

theorem bound_of_point_hit (z T d A B : PTm n) (h : Γ ⊢[PRAAx] pointHit z T d A B) :
    Γ ⊢[PRAAx] le (B*numerator z T d) (A*denominator z T d) := by
  have raw : Γ ⊢[PRAAx] originalHit .left .right (singleton z) T d A B zero := by
    rw [singleton_hit_eq]
    exact pointHit_point_congr T d A B (singleton_zero z).eqSymm h
  exact minimum_bound_of_original_hit .left .right (singleton z) T d zero A B (singleton_index z) raw

theorem selected_spec (z T d : PTm n) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] lt (selected z T d) (length T) := RationalNearest.selected_spec _ _ _ _ hT

/-- A proved comparison against the actual minimum returns the actual
least nearest index, without assuming a prior hit or a chosen witness. -/
theorem selected_radius (z T d A B : PTm n) (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] le (B*numerator z T d) (A*denominator z T d)) :
    Γ ⊢[PRAAx] pointRadius z (entry T (selected z T d)) d A B := by
  have metric := le_congr (congrMul (.eqRefl _) (RationalNearest.selected_distance (singleton z) T d zero hT)).eqSymm
    (.eqRefl _) h
  have point := metric_to_point_radius .left .right (singleton z) T d zero (selected z T d) A B
    (singleton_index z) (selected_spec z T d hT) metric
  exact radius_point_congr _ _ _ _ (singleton_zero z) point

theorem point_hit_of_bound (z T d A B : PTm n) (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] le (B*numerator z T d) (A*denominator z T d)) : Γ ⊢[PRAAx] pointHit z T d A B :=
  pointHit_intro z T d A B (selected z T d) (selected_spec z T d hT) (selected_radius z T d A B hT h)

theorem point_hit_iff (z T d A B : PTm n) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] Fm.iff (pointHit z T d A B) (le (B*numerator z T d) (A*denominator z T d)) :=
  .iffI (.impI (bound_of_point_hit _ _ _ _ _ Prf.hyp0))
    (.impI (point_hit_of_bound _ _ _ _ _ hT.wk Prf.hyp0))

/-! ## Fixed PR programs, positive rational code and a radius checker -/

def numeratorF : PR 3 := PTm.toPR (numerator (var 0) (var 1) (var 2))
def denominatorF : PR 3 := PTm.toPR (denominator (var 0) (var 1) (var 2))
def codeF : PR 3 := PTm.toPR (rationalDistance (var 0) (var 1) (var 2))
def selectedF : PR 3 := PTm.toPR (selected (var 0) (var 1) (var 2))

theorem numerator_at (z T d : PTm n) : Γ ⊢[PRAAx] ap3 numeratorF z T d ≐ numerator z T d := by
  simpa [numeratorF,ap3] using toPR_eq (Γ := Γ) (numerator (var 0) (var 1) (var 2) : PTm 3) ![z,T,d]
theorem denominator_at (z T d : PTm n) : Γ ⊢[PRAAx] ap3 denominatorF z T d ≐ denominator z T d := by
  simpa [denominatorF,ap3] using toPR_eq (Γ := Γ) (denominator (var 0) (var 1) (var 2) : PTm 3) ![z,T,d]
theorem code_at (z T d : PTm n) :
    Γ ⊢[PRAAx] ap3 codeF z T d ≐ pairT (numerator z T d) (denominator z T d) := by
  simpa [codeF,ap3,rationalDistance] using toPR_eq (Γ := Γ) (rationalDistance (var 0) (var 1) (var 2) : PTm 3) ![z,T,d]
theorem selected_at (z T d : PTm n) : Γ ⊢[PRAAx] ap3 selectedF z T d ≐ selected z T d := by
  simpa [selectedF,ap3] using toPR_eq (Γ := Γ) (selected (var 0) (var 1) (var 2) : PTm 3) ![z,T,d]

theorem code_numerator (z T d : PTm n) : Γ ⊢[PRAAx] fstT (ap3 codeF z T d) ≐ numerator z T d :=
  (congrFst (code_at z T d)).eqTrans (fst_pair _ _)
theorem code_denominator (z T d : PTm n) : Γ ⊢[PRAAx] sndT (ap3 codeF z T d) ≐ denominator z T d :=
  (congrSnd (code_at z T d)).eqTrans (snd_pair _ _)
theorem code_positive (z T d : PTm n) : Γ ⊢[PRAAx] le one (sndT (ap3 codeF z T d)) :=
  le_congr (.eqRefl _) (code_denominator z T d).eqSymm (denominator_positive z T d)

theorem code_point_hit_iff (z T d A B : PTm n) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] Fm.iff (pointHit z T d A B)
      (le (B*fstT (ap3 codeF z T d)) (A*sndT (ap3 codeF z T d))) :=
  .iffI (.impI (le_congr (congrMul (.eqRefl _) (code_numerator z T d).eqSymm)
    (congrMul (.eqRefl _) (code_denominator z T d).eqSymm) (bound_of_point_hit _ _ _ _ _ Prf.hyp0)))
    (.impI (point_hit_of_bound _ _ _ _ _ hT.wk
      (le_congr (congrMul (.eqRefl _) (code_numerator z T d))
        (congrMul (.eqRefl _) (code_denominator z T d)) Prf.hyp0)))

def checkerTerm (z T d A B : PTm n) : PTm n :=
  eqb (monus (B*fstT (ap3 codeF z T d)) (A*sndT (ap3 codeF z T d))) zero
def checkerF : PR 5 := PTm.toPR (checkerTerm (var 0) (var 1) (var 2) (var 3) (var 4))

@[simp] theorem subst_checkerTerm {m : ℕ} (σ : Fin n → PTm m) (z T d A B : PTm n) :
    Syn.subst σ (checkerTerm z T d A B) = checkerTerm (Syn.subst σ z) (Syn.subst σ T) (Syn.subst σ d)
      (Syn.subst σ A) (Syn.subst σ B) := by simp [checkerTerm]

theorem checker_at (z T d A B : PTm n) :
    Γ ⊢[PRAAx] RationalHausdorff.apply5 checkerF z T d A B ≐ checkerTerm z T d A B := by
  simpa [checkerF,RationalHausdorff.apply5] using
    toPR_eq (Γ := Γ) (checkerTerm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![z,T,d,A,B]

theorem checker_cases (z T d A B : PTm n) :
    Γ ⊢[PRAAx] (RationalHausdorff.apply5 checkerF z T d A B ≐ zero) ⋎
      (RationalHausdorff.apply5 checkerF z T d A B ≐ one) := by
  refine .orE (Foundations.BoundedReflection.eqb_cases
    (monus (B*fstT (ap3 codeF z T d)) (A*sndT (ap3 codeF z T d))) zero) ?_ ?_
  · exact .orI₁ ((checker_at z T d A B).eqTrans Prf.hyp0)
  · exact .orI₂ ((checker_at z T d A B).eqTrans Prf.hyp0)

theorem checker_sound (z T d A B : PTm n) (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] RationalHausdorff.apply5 checkerF z T d A B ≐ one) : Γ ⊢[PRAAx] pointHit z T d A B := by
  have bound := Foundations.BoundedReflection.eq_of_eqb ((checker_at z T d A B).eqSymm.eqTrans h)
  exact point_hit_of_bound _ _ _ _ _ hT
    (le_congr (congrMul (.eqRefl _) (code_numerator z T d)) (congrMul (.eqRefl _) (code_denominator z T d)) bound)

theorem checker_complete (z T d A B : PTm n) (h : Γ ⊢[PRAAx] pointHit z T d A B) :
    Γ ⊢[PRAAx] RationalHausdorff.apply5 checkerF z T d A B ≐ one := by
  have bound := le_congr (congrMul (.eqRefl _) (code_numerator z T d).eqSymm)
    (congrMul (.eqRefl _) (code_denominator z T d).eqSymm) (bound_of_point_hit z T d A B h)
  exact (checker_at z T d A B).eqTrans (eqb_of_eq bound)

theorem checker_reflection (z T d A B : PTm n) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] Fm.iff (RationalHausdorff.apply5 checkerF z T d A B ≐ one) (pointHit z T d A B) :=
  .iffI (.impI (checker_sound _ _ _ _ _ hT.wk Prf.hyp0)) (.impI (checker_complete _ _ _ _ _ Prf.hyp0))

theorem singleton_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    ((length (singleton (var 0)) ≐ one) ⋏ (entry (singleton (var 0)) zero ≐ var 0)) :=
  closeUniv 1 (.andI (singleton_length _) (singleton_zero _))

theorem point_distance_programs : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((ap3 numeratorF (var 0) (var 1) (var 2) ≐ numerator (var 0) (var 1) (var 2)) ⋏
      ((ap3 denominatorF (var 0) (var 1) (var 2) ≐ denominator (var 0) (var 1) (var 2)) ⋏
        ((ap3 codeF (var 0) (var 1) (var 2) ≐ rationalDistance (var 0) (var 1) (var 2)) ⋏
          ((ap3 selectedF (var 0) (var 1) (var 2) ≐ selected (var 0) (var 1) (var 2)) ⋏
            le one (sndT (ap3 codeF (var 0) (var 1) (var 2))))))) :=
  closeUniv 3 (.andI (numerator_at _ _ _) (.andI (denominator_at _ _ _) (.andI (code_at _ _ _)
    (.andI (selected_at _ _ _) (code_positive _ _ _)))))

theorem point_hit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 1)) ⟶
      Fm.iff (pointHit (var 0) (var 1) (var 2) (var 3) (var 4))
        (le (var 4*numerator (var 0) (var 1) (var 2)) (var 3*denominator (var 0) (var 1) (var 2)))) :=
  closeUniv 5 (.impI (point_hit_iff _ _ _ _ _ Prf.hyp0))

theorem selected_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 1)) ⟶
      le (var 4*numerator (var 0) (var 1) (var 2)) (var 3*denominator (var 0) (var 1) (var 2)) ⟶
        (lt (selected (var 0) (var 1) (var 2)) (length (var 1)) ⋏
          pointRadius (var 0) (entry (var 1) (selected (var 0) (var 1) (var 2))) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (.andI (selected_spec _ _ _ Prf.hyp1) (selected_radius _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

theorem checker_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((RationalHausdorff.apply5 checkerF (var 0) (var 1) (var 2) (var 3) (var 4) ≐
      checkerTerm (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      ((RationalHausdorff.apply5 checkerF (var 0) (var 1) (var 2) (var 3) (var 4) ≐ zero) ⋎
        (RationalHausdorff.apply5 checkerF (var 0) (var 1) (var 2) (var 3) (var 4) ≐ one))) :=
  closeUniv 5 (.andI (checker_at _ _ _ _ _) (checker_cases _ _ _ _ _))

theorem checker_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 1)) ⟶
      Fm.iff (RationalHausdorff.apply5 checkerF (var 0) (var 1) (var 2) (var 3) (var 4) ≐ one)
        (pointHit (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (checker_reflection _ _ _ _ _ Prf.hyp0))

#print axioms bound_of_point_hit
#print axioms selected_radius
#print axioms point_hit_iff
#print axioms code_positive
#print axioms code_point_hit_iff
#print axioms checker_sound
#print axioms checker_complete
#print axioms singleton_closed
#print axioms point_distance_programs
#print axioms point_hit_closed
#print axioms selected_radius_closed
#print axioms checker_program_closed
#print axioms checker_reflection_closed

end LeanProofs.IPRA.Analysis.RationalPointDistance
