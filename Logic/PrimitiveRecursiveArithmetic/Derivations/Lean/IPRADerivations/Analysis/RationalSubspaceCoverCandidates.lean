import IPRADerivations.Analysis.RationalFiniteSpanCover
import IPRADerivations.Foundations.SequenceEquality
import IPRADerivations.AnalyticNumberTheory.RSA

/-!
# Actual finite mask-tuple candidates for rational span covers

The original classifier masks are encoded at radix 2^t. The actual code is
below 2^(tM), and its numerical digits recover every original mask. The
candidate-family program reconstructs the same raw subtuple-span family
already produced from the original finite cover. This proves finite
certificate coverage, without proving that a quantitative cover exists.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSubspaceCoverCandidates

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open LeanProofs.IPRA.Foundations.MixedRadix (Cd Pl dP)
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def radix (T : PTm n) : PTm n := pw two (length T)
def bound (T M : PTm n) : PTm n := pw two (length T * M)
def digit (T w g : PTm n) : PTm n := rem (quo w (pw (radix T) g)) (radix T)
def codecData (H C : PTm n) : PTm n := pairT H C
def radixBody : PTm 2 := fstT (var 1)
def digitBody : PTm 2 := entry (sndT (var 1)) (var 0)
def encode (T D N : PTm n) : PTm n := Cd radixBody digitBody (length D)
  (codecData (radix T) (RationalFiniteSpanCover.masks D N T))
def candidateBody : PTm 2 := RationalSubtupleSpan.selected (fstT (var 1))
  (digit (fstT (var 1)) (sndT (var 1)) (var 0))
def candidate (T M w : PTm n) : PTm n := sequence candidateBody M (pairT T w)

@[simp] theorem subst_radix {q : ℕ} (σ : Fin n → PTm q) (T : PTm n) :
    Syn.subst σ (radix T) = radix (Syn.subst σ T) := by simp [radix]
@[simp] theorem subst_bound {q : ℕ} (σ : Fin n → PTm q) (T M : PTm n) :
    Syn.subst σ (bound T M) = bound (Syn.subst σ T) (Syn.subst σ M) := by simp [bound]
@[simp] theorem subst_digit {q : ℕ} (σ : Fin n → PTm q) (T w g : PTm n) :
    Syn.subst σ (digit T w g) = digit (Syn.subst σ T) (Syn.subst σ w) (Syn.subst σ g) := by simp [digit]
@[simp] theorem subst_codecData {q : ℕ} (σ : Fin n → PTm q) (H C : PTm n) :
    Syn.subst σ (codecData H C) = codecData (Syn.subst σ H) (Syn.subst σ C) := by simp [codecData]
@[simp] theorem subst_encode {q : ℕ} (σ : Fin n → PTm q) (T D N : PTm n) :
    Syn.subst σ (encode T D N) = encode (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ N) := by simp [encode]
@[simp] theorem subst_candidate {q : ℕ} (σ : Fin n → PTm q) (T M w : PTm n) :
    Syn.subst σ (candidate T M w) = candidate (Syn.subst σ T) (Syn.subst σ M) (Syn.subst σ w) := by simp [candidate]

theorem radix_body_at (H C i : PTm n) : Γ ⊢[PRAAx] inst2 radixBody i (codecData H C) ≐ H := by
  simpa [radixBody,codecData,inst2] using fst_pair (Γ := Γ) H C
theorem digit_body_at (H C i : PTm n) : Γ ⊢[PRAAx] inst2 digitBody i (codecData H C) ≐ entry C i := by
  simpa [digitBody,codecData,inst2] using entry_congr (Γ := Γ) (snd_pair H C) (.eqRefl i)
theorem places (H C k : PTm n) : Γ ⊢[PRAAx] Pl radixBody k (codecData H C) ≐ pw H k := by
  apply prod_const_of
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_codecData] using radix_body_at (Syn.shift H) (Syn.shift C) (var 0)
theorem radix_power (T M : PTm n) : Γ ⊢[PRAAx] pw (radix T) M ≐ bound T M :=
  AnalyticNumberTheory.RSA.pw_mul two (length T) M

theorem encode_bound (T D N : PTm n) : Γ ⊢[PRAAx] lt (encode T D N) (bound T (length D)) := by
  have digits : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (length D)) ⟶
      lt (inst2 digitBody (var 0) (Syn.shift (codecData (radix T) (RationalFiniteSpanCover.masks D N T))))
        (inst2 radixBody (var 0) (Syn.shift (codecData (radix T) (RationalFiniteSpanCover.masks D N T))))) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (length (Syn.shift D)) :: Γ.map Fm.shift
    have hr : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift D)) := Prf.hyp0
    simpa [Δ,Syn.shift,radix] using
      lt_congr (digit_body_at (radix (Syn.shift T)) (RationalFiniteSpanCover.masks (Syn.shift D) (Syn.shift N) (Syn.shift T)) (var 0)).eqSymm
        (radix_body_at (radix (Syn.shift T)) (RationalFiniteSpanCover.masks (Syn.shift D) (Syn.shift N) (Syn.shift T)) (var 0)).eqSymm (RationalFiniteSpanCover.masks_bound (Syn.shift D) (Syn.shift N) (Syn.shift T) (var 0) hr)
  exact lt_congr (.eqRefl _) ((places _ _ _).eqTrans (radix_power T (length D)))
    (Foundations.MixedRadix.code_lt _ _ _ _ digits)

theorem encode_digit (T D N g : PTm n) (hg : Γ ⊢[PRAAx] lt g (length D)) : Γ ⊢[PRAAx]
    digit T (encode T D N) g ≐ entry (RationalFiniteSpanCover.masks D N T) g := by
  let t := monus (length D) (succ g)
  let p := codecData (radix T) (RationalFiniteSpanCover.masks D N T)
  have span : Γ ⊢[PRAAx] succ g + t ≐ length D := (eq_add_of_le hg).eqSymm
  have ss : Γ.map Fm.shift ⊢[PRAAx] Syn.shift (succ g+t) ≐ length (Syn.shift D) := by simpa [Fm.shift,Syn.shift] using span.shift
  have digits : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ g+t)) ⟶
      lt (inst2 digitBody (var 0) (Syn.shift p)) (inst2 radixBody (var 0) (Syn.shift p))) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (succ g+t)) :: Γ.map Fm.shift
    have hr : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift D)) := lt_congr (.eqRefl _) ss.wk Prf.hyp0
    simpa [Δ,p,Syn.shift,radix] using
      lt_congr (digit_body_at (radix (Syn.shift T)) (RationalFiniteSpanCover.masks (Syn.shift D) (Syn.shift N) (Syn.shift T)) (var 0)).eqSymm
        (radix_body_at (radix (Syn.shift T)) (RationalFiniteSpanCover.masks (Syn.shift D) (Syn.shift N) (Syn.shift T)) (var 0)).eqSymm (RationalFiniteSpanCover.masks_bound (Syn.shift D) (Syn.shift N) (Syn.shift T) (var 0) hr)
  have codeEq : Γ ⊢[PRAAx] Cd radixBody digitBody (succ g+t) p ≐ encode T D N :=
    congrAp2 (sumF (dP radixBody digitBody)) span (.eqRefl _)
  exact (congrAp2 remF (congrAp2 quoF codeEq (places _ _ g)) (radix_body_at _ _ g)).eqSymm.eqTrans
    ((Foundations.MixedRadix.decode digits).eqTrans (digit_body_at _ _ g))

private theorem digit_congr {T S w v g h : PTm n} (hT : Γ ⊢[PRAAx] T ≐ S)
    (hw : Γ ⊢[PRAAx] w ≐ v) (hg : Γ ⊢[PRAAx] g ≐ h) : Γ ⊢[PRAAx] digit T w g ≐ digit S v h := by
  simpa only [subst_digit,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (digit (var 0) (var 1) (var 2) : PTm 3) (σ := ![T,w,g]) (σ' := ![S,v,h])
      (fun i => by fin_cases i; exact hT; exact hw; exact hg)
private theorem selected_congr {T S u v : PTm n} (hT : Γ ⊢[PRAAx] T ≐ S)
    (hu : Γ ⊢[PRAAx] u ≐ v) : Γ ⊢[PRAAx] RationalSubtupleSpan.selected T u ≐ RationalSubtupleSpan.selected S v := by
  simpa only [RationalSubtupleSpan.subst_selected,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (RationalSubtupleSpan.selected (var 0) (var 1) : PTm 2) (σ := ![T,u]) (σ' := ![S,v])
      (fun i => by fin_cases i; exact hT; exact hu)

theorem candidate_body_at (T w g : PTm n) : Γ ⊢[PRAAx] inst2 candidateBody g (pairT T w) ≐
    RationalSubtupleSpan.selected T (digit T w g) := by
  simp only [candidateBody,inst2,RationalSubtupleSpan.subst_selected,subst_digit,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact selected_congr (fst_pair _ _) (digit_congr (fst_pair _ _) (snd_pair _ _) (.eqRefl _))
theorem candidate_length (T M w : PTm n) : Γ ⊢[PRAAx] length (candidate T M w) ≐ M := sequence_length _ _ _
theorem candidate_lookup (T M w g : PTm n) (hg : Γ ⊢[PRAAx] lt g M) : Γ ⊢[PRAAx]
    entry (candidate T M w) g ≐ RationalSubtupleSpan.selected T (digit T w g) :=
  (sequence_decode candidateBody (x := pairT T w) hg).eqTrans (candidate_body_at _ _ _)

/-- Equality of the actual sequence constructors, never extensionality of arbitrary lists. -/
theorem reconstruction (T D N : PTm n) : Γ ⊢[PRAAx]
    candidate T (length D) (encode T D N) ≐ RationalFiniteSpanCover.normalized D N T := by
  apply Foundations.SequenceEquality.sequence_equal candidateBody RationalFiniteSpanCover.familyBody (length D)
    (pairT T (encode T D N)) (RationalFiniteSpanCover.data D N T)
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (length (Syn.shift D)) :: Γ.map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 0) (length (Syn.shift D)) := Prf.hyp0
  have maskEq := (encode_digit (Γ := Δ) (Syn.shift T) (Syn.shift D) (Syn.shift N) (var 0) hr).eqTrans
    (RationalFiniteSpanCover.masks_lookup _ _ _ _ hr)
  have low := (candidate_body_at (Γ := Δ) (Syn.shift T) (encode (Syn.shift T) (Syn.shift D) (Syn.shift N)) (var 0)).eqTrans
    (selected_congr (.eqRefl _) maskEq)
  have high := RationalFiniteSpanCover.family_body_at (Γ := Δ) (Syn.shift D) (Syn.shift N) (Syn.shift T) (var 0)
  simpa only [Δ,Syn.shift,subst_encode,subst_pairT,RationalFiniteSpanCover.subst_data,RationalFiniteSpanCover.subtuple,Foundations.SequenceComposition.subst_length] using low.eqTrans high.eqSymm

theorem reconstructed_certificate (T D N : PTm n) (hf : Γ ⊢[PRAAx] RationalFiniteSpanCover.family D N)
    (hc : Γ ⊢[PRAAx] RationalFiniteSpanCover.covered T D N) : Γ ⊢[PRAAx]
    RationalFiniteSpanCover.certificate T D N (candidate T (length D) (encode T D N)) := by
  let φ := RationalFiniteSpanCover.certificate (Syn.shift T) (Syn.shift D) (Syn.shift N) (var 0)
  have start : Γ ⊢[PRAAx] φ.subst (Syn.inst (RationalFiniteSpanCover.normalized D N T)) := by
    simpa only [φ,RationalFiniteSpanCover.subst_certificate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      RationalFiniteSpanCover.produced_certificate T D N hf hc
  simpa only [φ,RationalFiniteSpanCover.subst_certificate,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqSubst1 φ (reconstruction T D N).eqSymm start

def candidateF : PR 3 := PTm.toPR (candidate (var 0) (var 1) (var 2))
def encodeF : PR 3 := PTm.toPR (encode (var 0) (var 1) (var 2))
def output (T D N : PTm n) : PTm n := pairT (encode T D N)
  (pairT (candidate T (length D) (encode T D N)) (bound T (length D)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (T D N : PTm n) : PTm n := app outputF ![T,D,N]
@[simp] theorem subst_output {q : ℕ} (σ : Fin n → PTm q) (T D N : PTm n) :
    Syn.subst σ (output T D N) = output (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {q : ℕ} (σ : Fin n → PTm q) (T D N : PTm n) :
    Syn.subst σ (run T D N) = run (Syn.subst σ T) (Syn.subst σ D) (Syn.subst σ N) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem candidate_program_at (T M w : PTm n) : Γ ⊢[PRAAx] app candidateF ![T,M,w] ≐ candidate T M w := by
  simpa [candidateF] using toPR_eq (Γ := Γ) (candidate (var 0) (var 1) (var 2) : PTm 3) ![T,M,w]
theorem encode_program_at (T D N : PTm n) : Γ ⊢[PRAAx] app encodeF ![T,D,N] ≐ encode T D N := by
  simpa [encodeF] using toPR_eq (Γ := Γ) (encode (var 0) (var 1) (var 2) : PTm 3) ![T,D,N]
theorem program_at (T D N : PTm n) : Γ ⊢[PRAAx] run T D N ≐ output T D N := by
  simpa [run,outputF,output,Matrix.cons_val_succ',Matrix.cons_val_zero'] using
    toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![T,D,N]
theorem returned_code (T D N : PTm n) : Γ ⊢[PRAAx] fstT (run T D N) ≐ encode T D N :=
  (congrFst (program_at T D N)).eqTrans (fst_pair _ _)
theorem returned_family (T D N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run T D N)) ≐ candidate T (length D) (encode T D N) :=
  (congrFst ((congrSnd (program_at T D N)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_bound (T D N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run T D N)) ≐ bound T (length D) :=
  (congrSnd ((congrSnd (program_at T D N)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_code_bound (T D N : PTm n) : Γ ⊢[PRAAx] lt (fstT (run T D N)) (sndT (sndT (run T D N))) :=
  lt_congr (returned_code T D N).eqSymm (returned_bound T D N).eqSymm (encode_bound T D N)

theorem actual_candidate_length_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (candidate (var 0) (var 1) (var 2)) ≐ var 1) := closeUniv 3 (candidate_length _ _ _)
theorem actual_candidate_code_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (encode (var 0) (var 1) (var 2)) (pw two (length (var 0) * length (var 1)))) := closeUniv 3 (encode_bound _ _ _)
theorem actual_candidate_digit_decode_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (length (var 1)) ⟶ digit (var 0) (encode (var 0) (var 1) (var 2)) (var 3) ≐
      entry (RationalFiniteSpanCover.masks (var 1) (var 2) (var 0)) (var 3)) :=
  closeUniv 4 (.impI (encode_digit _ _ _ _ Prf.hyp0))
theorem actual_candidate_reconstruction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (candidate (var 0) (length (var 1)) (encode (var 0) (var 1) (var 2)) ≐
      RationalFiniteSpanCover.normalized (var 1) (var 2) (var 0)) := closeUniv 3 (reconstruction _ _ _)
theorem actual_finite_cover_candidate_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (RationalFiniteSpanCover.family (var 1) (var 2) ⟶ RationalFiniteSpanCover.covered (var 0) (var 1) (var 2) ⟶
      RationalFiniteSpanCover.certificate (var 0) (var 1) (var 2)
        (candidate (var 0) (length (var 1)) (encode (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (.impI (reconstructed_certificate _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_candidate_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (app candidateF ![var 0,var 1,var 2] ≐ candidate (var 0) (var 1) (var 2)) := closeUniv 3 (candidate_program_at _ _ _)
theorem actual_candidate_encoding_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_candidate_code_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (fstT (run (var 0) (var 1) (var 2))) (sndT (sndT (run (var 0) (var 1) (var 2))))) := closeUniv 3 (returned_code_bound _ _ _)

end LeanProofs.IPRA.Analysis.RationalSubspaceCoverCandidates
