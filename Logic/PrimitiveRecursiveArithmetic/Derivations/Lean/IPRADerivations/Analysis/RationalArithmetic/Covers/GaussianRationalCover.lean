import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalMetric
import IPRADerivations.Analysis.FiniteOperations.GaussianProductStability

/-!
# Original Gaussian-rational point-list covers

The actual common-denominator pool produces integer point lists. A proved
raw cover transports to the original rational point codes at exactly the
same computed indices. The returned point is an actual original-list lookup.
Both directions use the same computed pool, allowing repeated entries and
independently reduced scalar denominators. No original cover, output distance
or clearing identity is supplied as an input contract.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalCover

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (distanceBounded bounded_difference_iff boundedSyntax)
open LeanProofs.IPRA.Analysis.GaussianRationalNormalization
  (sourceNumerators targetNumerators commonD commonD_positive source_clearing target_clearing
    source_length target_length subst_sourceNumerators subst_targetNumerators subst_commonD)
open LeanProofs.IPRA.Analysis.GaussianProductStability (squaredDistanceF squared_distance_at)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open LeanProofs.IPRA.Foundations.BoundedSyntax
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Fixed choices of the two directed programs; not external numerical data. -/
inductive Side | source | target

def other : Side → Side | .source => .target | .target => .source
def original (s : Side) (S T : PTm n) : PTm n := match s with
  | .source => S
  | .target => T
def numerators (s : Side) (S T z : PTm n) : PTm n := match s with
  | .source => sourceNumerators S T z
  | .target => targetNumerators S T z

@[simp] theorem subst_original {m : ℕ} (σ : Fin n → PTm m) (s : Side) (S T : PTm n) :
    Syn.subst σ (original s S T) = original s (Syn.subst σ S) (Syn.subst σ T) := by cases s <;> rfl
@[simp] theorem subst_numerators {m : ℕ} (σ : Fin n → PTm m) (s : Side) (S T z : PTm n) :
    Syn.subst σ (numerators s S T z) = numerators s (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) := by cases s <;> simp [numerators]

theorem numerators_length (s : Side) (S T z : PTm n) : Γ ⊢[PRAAx]
    length (numerators s S T z) ≐ length (original s S T) := by
  cases s
  · exact source_length S T z
  · exact target_length S T z

theorem entry_represents (s : Side) (S T z i : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length (original s S T))) : Γ ⊢[PRAAx]
    GaussianRationalHorner.represents (entry (original s S T) i) (entry (numerators s S T z) i) (commonD S T z) := by
  cases s
  · exact source_clearing S T z i hi
  · exact target_clearing S T z i hi

def cover (S T A B : PTm n) : Fm PTm n :=
  .all (lt (var 0) (length (Syn.shift S)) ⟶
    .ex (lt (var 0) (length (Syn.shift (Syn.shift T))) ⋏
      distanceBounded (entry (Syn.shift (Syn.shift S)) (var 1))
        (entry (Syn.shift (Syn.shift T)) (var 0)) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B))))
def close (S T A B : PTm n) : Fm PTm n := cover S T A B ⋏ cover T S A B

@[simp] theorem subst_cover {m : ℕ} (σ : Fin n → PTm m) (S T A B : PTm n) :
    (cover S T A B).subst σ = cover (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ A) (Syn.subst σ B) := by
  simp only [cover,Fm.subst_all,Fm.subst_imp,Fm.subst_ex,Fm.subst_and,subst_lt,subst_length,
    GaussianRationalMetric.subst_distanceBounded,subst_entry,Syn.subst_var,Syn.up_zero,Syn.up_succ,
    Syn.subst_shift,Syn.shift_subst,Syn.up_one,Syn.shift_var,Fin.succ_zero_eq_one]
@[simp] theorem subst_close {m : ℕ} (σ : Fin n → PTm m) (S T A B : PTm n) :
    (close S T A B).subst σ = close (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ A) (Syn.subst σ B) := by simp [close]

def rawBudget (S T z A : PTm n) : PTm n := (A*commonD S T z)*(A*commonD S T z)
def rawCover (s : Side) (S T z A B : PTm n) : Fm PTm n :=
  Foundations.FiniteHausdorff.cover squaredDistanceF (numerators s S T z) (numerators (other s) S T z) (rawBudget S T z A) B
def rawClose (S T z A B : PTm n) : Fm PTm n :=
  Foundations.FiniteHausdorff.close squaredDistanceF (sourceNumerators S T z) (targetNumerators S T z) (rawBudget S T z A) B

def selected (s : Side) (S T z i B : PTm n) : PTm n := Foundations.FiniteHausdorff.nearest
  squaredDistanceF (entry (numerators s S T z) i) (numerators (other s) S T z) B

@[simp] theorem subst_rawBudget {m : ℕ} (σ : Fin n → PTm m) (S T z A : PTm n) :
    Syn.subst σ (rawBudget S T z A) = rawBudget (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) (Syn.subst σ A) := by simp [rawBudget]
@[simp] theorem subst_rawCover {m : ℕ} (σ : Fin n → PTm m) (s : Side) (S T z A B : PTm n) :
    (rawCover s S T z A B).subst σ = rawCover s (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) := by simp [rawCover]
@[simp] theorem subst_rawClose {m : ℕ} (σ : Fin n → PTm m) (S T z A B : PTm n) :
    (rawClose S T z A B).subst σ = rawClose (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) := by simp [rawClose,Foundations.FiniteHausdorff.close]
@[simp] theorem subst_selected {m : ℕ} (σ : Fin n → PTm m) (s : Side) (S T z i B : PTm n) :
    Syn.subst σ (selected s S T z i B) = selected s (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ z) (Syn.subst σ i) (Syn.subst σ B) := by simp [selected]

/-- The raw nearest index is valid in the original target list, and its actual
original point satisfies the original Euclidean rational comparison. -/
theorem selected_certificate (s : Side) (S T z A B i : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length (original (other s) S T)))
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] rawCover s S T z A B)
    (hi : Γ ⊢[PRAAx] lt i (length (original s S T))) : Γ ⊢[PRAAx]
    lt (selected s S T z i B) (length (original (other s) S T)) ⋏
      distanceBounded (entry (original s S T) i)
        (entry (original (other s) S T) (selected s S T z i B)) A B := by
  have targetPositive : Γ ⊢[PRAAx] le one (length (numerators (other s) S T z)) :=
    le_congr (.eqRefl _) (numerators_length (other s) S T z).eqSymm hT
  have rawIndex : Γ ⊢[PRAAx] lt i (length (numerators s S T z)) :=
    lt_congr (.eqRefl _) (numerators_length s S T z).eqSymm hi
  have near := Foundations.FiniteHausdorff.nearest_spec squaredDistanceF
    (entry (numerators s S T z) i) (numerators (other s) S T z) B targetPositive
  have bound := Foundations.FiniteHausdorff.minimum_of_hit squaredDistanceF
    (Foundations.FiniteHausdorff.cover_at squaredDistanceF hc rawIndex)
  have j : Γ ⊢[PRAAx] lt (selected s S T z i B) (length (original (other s) S T)) :=
    lt_congr (.eqRefl _) (numerators_length (other s) S T z) (Prf.andE₁ near)
  have raw : Γ ⊢[PRAAx] le
      ((B*B)*ComplexLogarithmRemainder.normSq (GaussianRootAlgebra.sub
        (entry (numerators s S T z) i) (entry (numerators (other s) S T z) (selected s S T z i B))))
      ((A*A)*(commonD S T z*commonD S T z)) :=
    le_congr (squared_distance_at _ _ _) (by unfold rawBudget; ipra_ring)
      (le_congr (Prf.andE₂ near).eqSymm (.eqRefl _) bound)
  exact .andI j ((bounded_difference_iff _ _ _ _ _ _ _ (commonD_positive S T z) hB
    (entry_represents s S T z i hi) (entry_represents (other s) S T z _ j)).iffMpr raw)

def hit (q T A B : PTm n) : Fm PTm n :=
  .ex (lt (var 0) (length (Syn.shift T)) ⋏
    distanceBounded (Syn.shift q) (entry (Syn.shift T) (var 0)) (Syn.shift A) (Syn.shift B))

theorem hit_intro (q T A B j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length T))
    (hd : Γ ⊢[PRAAx] distanceBounded q (entry T j) A B) : Γ ⊢[PRAAx] hit q T A B := by
  refine .exI j ?_
  simpa [hit] using Prf.andI hj hd

theorem cover_transport (s : Side) (S T z A B : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length (original (other s) S T)))
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] rawCover s S T z A B) :
    Γ ⊢[PRAAx] cover (original s S T) (original (other s) S T) A B := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift (original s S T))) :: Γ.map Fm.shift
  have target : Δ ⊢[PRAAx] le one (length (original (other s) (Syn.shift S) (Syn.shift T))) := by
    simpa only [Δ,Fm.shift,subst_le,subst_length,subst_original,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hT.shift.wk
  have b : Δ ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Δ,Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hB.shift.wk
  have coverRaw : Δ ⊢[PRAAx] rawCover s (Syn.shift S) (Syn.shift T) (Syn.shift z) (Syn.shift A) (Syn.shift B) := by
    simpa only [Δ,Fm.shift,subst_rawCover,Syn.shift] using hc.shift.wk
  have range : Δ ⊢[PRAAx] lt (var 0) (length (original s (Syn.shift S) (Syn.shift T))) := by
    simpa only [Δ,Syn.shift,subst_original] using Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift)
      (φ := lt (var 0) (length (Syn.shift (original s S T))))
  have cert := selected_certificate s (Syn.shift S) (Syn.shift T) (Syn.shift z) (Syn.shift A) (Syn.shift B) (var 0) target b coverRaw range
  have result := hit_intro _ _ _ _ _ (Prf.andE₁ cert) (Prf.andE₂ cert)
  simpa only [Δ,hit,Syn.shift,subst_entry,subst_original,Syn.subst_var,Syn.shift_var,Fin.succ_zero_eq_one] using result

theorem close_transport (S T z A B : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] rawClose S T z A B) :
    Γ ⊢[PRAAx] close S T A B :=
  .andI (cover_transport .source S T z A B hT hB (Prf.andE₁ hc))
    (cover_transport .target S T z A B hS hB (Prf.andE₂ hc))

/-! Actual original-point output and the checker for the literal rational
cover, rather than a checker for the auxiliary integer lists. -/

def coverSyntax (S T A B : PTm n) : BFm n :=
  .all (length S) (.ex (length (Syn.shift T))
    (boundedSyntax (GaussianRationalMetric.qsub
      (entry (Syn.shift (Syn.shift S)) (var 1)) (entry (Syn.shift (Syn.shift T)) (var 0)))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B))))
def closeSyntax (S T A B : PTm n) : BFm n := .and (coverSyntax S T A B) (coverSyntax T S A B)

theorem cover_formula (S T A B : PTm n) : formula (coverSyntax S T A B) = cover S T A B := by
  simp only [coverSyntax,formula,GaussianRationalMetric.bounded_formula,cover,Syn.shift,subst_length,
    GaussianRationalMetric.distanceBounded]
theorem close_formula (S T A B : PTm n) : formula (closeSyntax S T A B) = close S T A B := by
  simp only [closeSyntax,formula,cover_formula,close]

def closeCheckF : PR 4 := bitF (closeSyntax (var 0) (var 1) (var 2) (var 3))
def check (S T A B : PTm n) : PTm n := PTm.app closeCheckF ![S,T,A,B]

theorem checker_program (S T A B : PTm n) : Γ ⊢[PRAAx] check S T A B ≐
    bit (closeSyntax (var 0) (var 1) (var 2) (var 3)) ![S,T,A,B] :=
  program_correct (closeSyntax (var 0) (var 1) (var 2) (var 3)) ![S,T,A,B]

theorem checker_reflection (S T A B : PTm n) : Γ ⊢[PRAAx]
    Fm.iff (check S T A B ≐ one) (close S T A B) := by
  have r := bounded_reflection (Γ := Γ) (closeSyntax (var 0) (var 1) (var 2) (var 3)) ![S,T,A,B]
  rw [close_formula] at r
  have h : Γ ⊢[PRAAx] Fm.iff
      (bit (closeSyntax (var 0) (var 1) (var 2) (var 3)) ![S,T,A,B] ≐ one) (close S T A B) := by
    simpa only [subst_close,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using r
  have p := checker_program (Γ := Γ) S T A B
  exact .iffI (.impI (h.wk.iffMp (p.wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI (p.wk.eqTrans (h.wk.iffMpr Prf.hyp0)))

theorem checker_boolean (S T A B : PTm n) : Γ ⊢[PRAAx] (check S T A B ≐ zero) ⋎ (check S T A B ≐ one) := by
  have p := checker_program (Γ := Γ) S T A B
  exact .orE (bit_cases (closeSyntax (var 0) (var 1) (var 2) (var 3)) ![S,T,A,B])
    (.orI₁ (p.wk.eqTrans Prf.hyp0)) (.orI₂ (p.wk.eqTrans Prf.hyp0))

theorem checker_accepts (S T z A B : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] rawClose S T z A B) :
    Γ ⊢[PRAAx] check S T A B ≐ one :=
  (checker_reflection S T A B).iffMpr (close_transport S T z A B hS hT hB hc)

def output (s : Side) (S T z i B : PTm n) : PTm n := pairT (selected s S T z i B)
  (entry (original (other s) S T) (selected s S T z i B))
def outputF (s : Side) : PR 5 := PTm.toPR (output s (var 0) (var 1) (var 2) (var 3) (var 4))
def run (s : Side) (S T z i B : PTm n) : PTm n := PTm.app (outputF s) ![S,T,z,i,B]

@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (s : Side) (S T z i B : PTm n) :
    Syn.subst σ (output s S T z i B) = output s (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ z) (Syn.subst σ i) (Syn.subst σ B) := by simp [output]
@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (s : Side) (S T z i B : PTm n) :
    Syn.subst σ (run s S T z i B) = run s (Syn.subst σ S) (Syn.subst σ T)
      (Syn.subst σ z) (Syn.subst σ i) (Syn.subst σ B) := by
  simp [run]
  funext j
  fin_cases j <;> rfl

theorem output_program_at (s : Side) (S T z i B : PTm n) : Γ ⊢[PRAAx]
    run s S T z i B ≐ output s S T z i B := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output s (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![S,T,z,i,B]

theorem output_index (s : Side) (S T z i B : PTm n) : Γ ⊢[PRAAx]
    fstT (run s S T z i B) ≐ selected s S T z i B :=
  (congrFst (output_program_at s S T z i B)).eqTrans (fst_pair _ _)
theorem output_point (s : Side) (S T z i B : PTm n) : Γ ⊢[PRAAx]
    sndT (run s S T z i B) ≐ entry (original (other s) S T) (selected s S T z i B) :=
  (congrSnd (output_program_at s S T z i B)).eqTrans (snd_pair _ _)
theorem output_point_index (s : Side) (S T z i B : PTm n) : Γ ⊢[PRAAx]
    sndT (run s S T z i B) ≐ entry (original (other s) S T) (fstT (run s S T z i B)) :=
  (output_point s S T z i B).eqTrans
    (Foundations.SequenceComposition.entry_congr (.eqRefl _) (output_index s S T z i B).eqSymm)

theorem distance_congr {q q' r r' A A' B B' : PTm n}
    (hq : Γ ⊢[PRAAx] q ≐ q') (hr : Γ ⊢[PRAAx] r ≐ r')
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B')
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx] distanceBounded q' r' A' B' := by
  have e := Prf.eqSubst (distanceBounded (var 0) (var 1) (var 2) (var 3) : Fm PTm 4)
    (σ := ![q,r,A,B]) (σ' := ![q',r',A',B']) (fun i => by fin_cases i <;> assumption)
    (by simpa using h)
  simpa using e

theorem output_certificate (s : Side) (S T z A B i : PTm n)
    (hT : Γ ⊢[PRAAx] le one (length (original (other s) S T)))
    (hB : Γ ⊢[PRAAx] le one B) (hc : Γ ⊢[PRAAx] rawCover s S T z A B)
    (hi : Γ ⊢[PRAAx] lt i (length (original s S T))) : Γ ⊢[PRAAx]
    lt (fstT (run s S T z i B)) (length (original (other s) S T)) ⋏
      (sndT (run s S T z i B) ≐ entry (original (other s) S T) (fstT (run s S T z i B)) ⋏
        distanceBounded (entry (original s S T) i) (sndT (run s S T z i B)) A B) := by
  have h := selected_certificate s S T z A B i hT hB hc hi
  exact .andI (lt_congr (output_index s S T z i B).eqSymm (.eqRefl _) (Prf.andE₁ h))
    (.andI (output_point_index s S T z i B)
      (distance_congr (.eqRefl _) (output_point s S T z i B).eqSymm (.eqRefl _) (.eqRefl _) (Prf.andE₂ h)))

theorem original_close_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (var 4) ⟶
      rawClose (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ close (var 0) (var 1) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (close_transport _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem original_checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 0)) ⟶ le one (length (var 1)) ⟶ le one (var 4) ⟶
      rawClose (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ (check (var 0) (var 1) (var 3) (var 4) ≐ one)) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (checker_accepts _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

theorem original_checker_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (check (var 0) (var 1) (var 2) (var 3) ≐ one) (close (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (checker_reflection _ _ _ _)

theorem original_output_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (length (var 1)) ⟶ le one (var 4) ⟶
      rawCover .source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ lt (var 5) (length (var 0)) ⟶
      (lt (fstT (run .source (var 0) (var 1) (var 2) (var 5) (var 4))) (length (var 1)) ⋏
        (sndT (run .source (var 0) (var 1) (var 2) (var 5) (var 4)) ≐
          entry (var 1) (fstT (run .source (var 0) (var 1) (var 2) (var 5) (var 4))) ⋏
          distanceBounded (entry (var 0) (var 5)) (sndT (run .source (var 0) (var 1) (var 2) (var 5) (var 4)))
            (var 3) (var 4)))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (output_certificate .source _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalCover
