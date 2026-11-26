import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalReducedSpanMembership
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalOriginalSpanRank
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalRowSpanForward

/-!
# Actual exact membership in the original Gaussian-rational row span

The original finite coefficient existential is equivalent to acceptance
of the computed reduced-span test. Forward coefficients prove
completeness and the actual rewind proves soundness. The returned
witness is the same already computed original-row coefficient vector,
not a selected witness from the existential hypothesis.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalOriginalSpanMembership

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalRowElimination (shape)
open GaussianRationalRowSpan (membership)
open GaussianSuperellipticSubspaceFromSpan (hasCoefficients)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def test (A R N v : PTm n) : PTm n := GaussianRationalReducedSpanMembership.test A R N v
def coefficients (A R N v : PTm n) : PTm n := GaussianRationalOriginalSpanRank.weights A R N v

@[simp] theorem subst_test {k : ℕ} (σ : Fin n → PTm k) (A R N v : PTm n) :
    Syn.subst σ (test A R N v) = test (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ v) := by simp [test]
@[simp] theorem subst_coefficients {k : ℕ} (σ : Fin n → PTm k) (A R N v : PTm n) :
    Syn.subst σ (coefficients A R N v) = coefficients (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ v) := by simp [coefficients]

theorem coefficients_length (A R N v : PTm n) : Γ ⊢[PRAAx] length (coefficients A R N v) ≐ R :=
  GaussianRationalOriginalSpanRank.weights_length A R N v

theorem test_sound (A R N v : PTm n) (h : Γ ⊢[PRAAx] test A R N v ≐ one) : Γ ⊢[PRAAx]
    membership A R N (coefficients A R N v) v := by
  simpa only [coefficients,GaussianRationalOriginalSpanRank.weights] using
    GaussianRationalRowSpanRewind.membership_original A R N N (GaussianRationalFullReducedSpan.weights A R N v) v
      (GaussianRationalReducedSpanMembership.test_sound A R N v h)

theorem accepted_hasCoefficients (A R N v : PTm n) (h : Γ ⊢[PRAAx] test A R N v ≐ one) : Γ ⊢[PRAAx]
    hasCoefficients A R N v := by
  refine .exI (coefficients A R N v) ?_
  simpa only [hasCoefficients,Fm.subst_and,Fm.subst_eq,subst_length,GaussianRationalRowSpan.subst_membership,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.andI (coefficients_length A R N v) (test_sound A R N v h)

theorem test_complete (A R N v : PTm n) (hA : Γ ⊢[PRAAx] shape A R N)
    (hm : Γ ⊢[PRAAx] hasCoefficients A R N v) : Γ ⊢[PRAAx] test A R N v ≐ one := by
  have As : Γ.map Fm.shift ⊢[PRAAx] shape (Syn.shift A) (Syn.shift R) (Syn.shift N) := by
    simpa only [Fm.shift,GaussianRationalRowElimination.subst_shape,Syn.shift] using hA.shift
  refine .exE hm ?_
  let Δ := ((length (var 0) ≐ Syn.shift R) ⋏ membership (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift v)) :: Γ.map Fm.shift
  have forwarded := GaussianRationalRowSpanForward.membership_forward (Γ := Δ) (Syn.shift A) (Syn.shift R)
    (Syn.shift N) (var 0) (Syn.shift v) (Syn.shift N) As.wk (le_refl _) (.andE₂ Prf.hyp0)
  have hit := GaussianRationalReducedSpanMembership.test_complete (Γ := Δ) (Syn.shift A) (Syn.shift R)
    (Syn.shift N) (GaussianRationalRowSpanForward.weights (Syn.shift A) (Syn.shift R) (Syn.shift N) (var 0) (Syn.shift N))
      (Syn.shift v) As.wk forwarded
  simpa only [Δ,Fm.shift,Fm.subst_eq,subst_test,test,GaussianRationalReducedSpanMembership.subst_test,
    Syn.shift,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using hit

theorem test_iff (A R N v : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx]
    Fm.iff (test A R N v ≐ one) (hasCoefficients A R N v) :=
  .andI (.impI (accepted_hasCoefficients A R N v Prf.hyp0)) (.impI (test_complete A R N v hA.wk Prf.hyp0))

theorem membership_decidable (A R N v : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx]
    (hasCoefficients A R N v) ⋎ neg (hasCoefficients A R N v) := by
  refine .orE (eq_or_ne (test A R N v) one) (.orI₁ (accepted_hasCoefficients A R N v Prf.hyp0)) ?_
  exact .orI₂ (.impI (.impE Prf.hyp1 (test_complete A R N v hA.wk.wk Prf.hyp0)))

theorem membership_coefficients_congr (A R N C D v : PTm n) (h : Γ ⊢[PRAAx] C ≐ D)
    (hm : Γ ⊢[PRAAx] membership A R N C v) : Γ ⊢[PRAAx] membership A R N D v := by
  have rule := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (membership (var 0) (var 1) (var 2) (var 3) (var 4) : Fm PTm 5)
    ![A,R,N,C,v] ![A,R,N,D,v] (fun j => by
      fin_cases j
      · exact .eqRefl _
      · exact .eqRefl _
      · exact .eqRefl _
      · exact h
      · exact .eqRefl _)
  have transport : (Γ ⊢[PRAAx] membership A R N C v) → (Γ ⊢[PRAAx] membership A R N D v) := by
    simpa only [GaussianRationalRowSpan.subst_membership,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using rule
  exact transport hm

def output (A R N v : PTm n) : PTm n := pairT (test A R N v) (coefficients A R N v)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (A R N v : PTm n) : PTm n := app outputF ![A,R,N,v]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (A R N v : PTm n) :
    Syn.subst σ (output A R N v) = output (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ v) := by simp [output]
@[simp] theorem subst_run {k : ℕ} (σ : Fin n → PTm k) (A R N v : PTm n) :
    Syn.subst σ (run A R N v) = run (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ v) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext j
  fin_cases j <;> rfl
theorem program_at (A R N v : PTm n) : Γ ⊢[PRAAx] run A R N v ≐ output A R N v := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,R,N,v]
theorem returned_test (A R N v : PTm n) : Γ ⊢[PRAAx] fstT (run A R N v) ≐ test A R N v :=
  (congrFst (program_at A R N v)).eqTrans (fst_pair _ _)
theorem returned_coefficients (A R N v : PTm n) : Γ ⊢[PRAAx] sndT (run A R N v) ≐ coefficients A R N v :=
  (congrSnd (program_at A R N v)).eqTrans (snd_pair _ _)
theorem returned_length (A R N v : PTm n) : Γ ⊢[PRAAx] length (sndT (run A R N v)) ≐ R :=
  (congrFst (returned_coefficients A R N v)).eqTrans (coefficients_length A R N v)
theorem returned_certificate (A R N v : PTm n) (h : Γ ⊢[PRAAx] fstT (run A R N v) ≐ one) : Γ ⊢[PRAAx]
    (length (sndT (run A R N v)) ≐ R) ⋏ membership A R N (sndT (run A R N v)) v :=
  .andI (returned_length A R N v) (membership_coefficients_congr A R N _ _ v
    (returned_coefficients A R N v).eqSymm (test_sound A R N v ((returned_test A R N v).eqSymm.eqTrans h)))
theorem returned_test_iff (A R N v : PTm n) (hA : Γ ⊢[PRAAx] shape A R N) : Γ ⊢[PRAAx]
    Fm.iff (fstT (run A R N v) ≐ one) (hasCoefficients A R N v) :=
  .andI (.impI (accepted_hasCoefficients A R N v ((returned_test A R N v).wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI ((returned_test A R N v).wk.eqTrans (test_complete A R N v hA.wk Prf.hyp0)))

theorem actual_original_membership_test_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (shape (var 0) (var 1) (var 2) ⟶
      Fm.iff (test (var 0) (var 1) (var 2) (var 3) ≐ one) (hasCoefficients (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (test_iff _ _ _ _ Prf.hyp0))
theorem actual_original_membership_decidable_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (shape (var 0) (var 1) (var 2) ⟶ (hasCoefficients (var 0) (var 1) (var 2) (var 3)) ⋎
      neg (hasCoefficients (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (membership_decidable _ _ _ _ Prf.hyp0))
theorem actual_original_membership_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((test (var 0) (var 1) (var 2) (var 3) ≐ one) ⟶
      membership (var 0) (var 1) (var 2) (coefficients (var 0) (var 1) (var 2) (var 3)) (var 3)) :=
  closeUniv 4 (.impI (test_sound _ _ _ _ Prf.hyp0))
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_membership_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ one) ⟶
      (length (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ var 1) ⋏
        membership (var 0) (var 1) (var 2) (sndT (run (var 0) (var 1) (var 2) (var 3))) (var 3)) :=
  closeUniv 4 (.impI (returned_certificate _ _ _ _ Prf.hyp0))
theorem actual_returned_membership_test_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (shape (var 0) (var 1) (var 2) ⟶
      Fm.iff (fstT (run (var 0) (var 1) (var 2) (var 3)) ≐ one) (hasCoefficients (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (returned_test_iff _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalOriginalSpanMembership
