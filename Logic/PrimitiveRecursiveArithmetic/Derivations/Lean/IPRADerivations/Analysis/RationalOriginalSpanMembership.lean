import IPRADerivations.Analysis.RationalRowSpanGaussianEmbedding
import IPRADerivations.Analysis.GaussianRationalOriginalSpanMembership

/-!
# Exact membership in an original rational row span

The bounded elimination test runs on the embedded numerical matrix. An
accepted test supplies real coefficients for the original rows, and every
original rational representation forces the same test to accept.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalOriginalSpanMembership

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalRowSpanGaussianEmbedding (matrix matrix_shape realVector membership hasCoefficients)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def test (A R N v : PTm n) : PTm n := GaussianRationalOriginalSpanMembership.test
  (matrix A R N) R N (RationalPolynomialGaussianEmbedding.coefficients v N)

def weights (A R N v : PTm n) : PTm n := realVector (GaussianRationalOriginalSpanMembership.coefficients
  (matrix A R N) R N (RationalPolynomialGaussianEmbedding.coefficients v N)) R

@[simp] theorem subst_test {q : ℕ} (σ : Fin n → PTm q) (A R N v : PTm n) :
    Syn.subst σ (test A R N v) = test (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ v) := by
  simp [test]

@[simp] theorem subst_weights {q : ℕ} (σ : Fin n → PTm q) (A R N v : PTm n) :
    Syn.subst σ (weights A R N v) = weights (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ v) := by
  simp [weights]

theorem weights_length (A R N v : PTm n) : Γ ⊢[PRAAx] length (weights A R N v) ≐ R :=
  RationalRowSpanGaussianEmbedding.real_vector_length _ _

theorem test_sound (A R N v : PTm n) (h : Γ ⊢[PRAAx] test A R N v ≐ one) :
    Γ ⊢[PRAAx] membership A R N (weights A R N v) v :=
  RationalRowSpanGaussianEmbedding.membership_real_part A R N _ v
    (GaussianRationalOriginalSpanMembership.test_sound _ _ _ _ h)

theorem test_complete (A R N v : PTm n) (h : Γ ⊢[PRAAx] hasCoefficients A R N v) :
    Γ ⊢[PRAAx] test A R N v ≐ one :=
  GaussianRationalOriginalSpanMembership.test_complete _ _ _ _ (matrix_shape A R N)
    (RationalRowSpanGaussianEmbedding.span_embedding A R N v h)

theorem test_iff (A R N v : PTm n) : Γ ⊢[PRAAx] Fm.iff (test A R N v ≐ one) (hasCoefficients A R N v) :=
  .andI (.impI (RationalRowSpanGaussianEmbedding.rational_span_intro A R N (weights A R N v) v
    (weights_length _ _ _ _) (test_sound _ _ _ _ Prf.hyp0))) (.impI (test_complete _ _ _ _ Prf.hyp0))

def output (A R N v : PTm n) : PTm n := pairT (test A R N v) (weights A R N v)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (A R N v : PTm n) : PTm n := app outputF ![A,R,N,v]

@[simp] theorem subst_output {q : ℕ} (σ : Fin n → PTm q) (A R N v : PTm n) :
    Syn.subst σ (output A R N v) = output (Syn.subst σ A) (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ v) := by
  simp [output]

theorem program_at (A R N v : PTm n) : Γ ⊢[PRAAx] run A R N v ≐ output A R N v := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![A,R,N,v]

theorem returned_test (A R N v : PTm n) : Γ ⊢[PRAAx] fstT (run A R N v) ≐ test A R N v :=
  (congrFst (program_at A R N v)).eqTrans (fst_pair _ _)

theorem returned_weights (A R N v : PTm n) : Γ ⊢[PRAAx] sndT (run A R N v) ≐ weights A R N v :=
  (congrSnd (program_at A R N v)).eqTrans (snd_pair _ _)

theorem actual_rational_original_span_membership_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Fm.iff (test (var 0) (var 1) (var 2) (var 3) ≐ one) (hasCoefficients (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (test_iff _ _ _ _)

theorem actual_rational_original_span_weights_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (test (var 0) (var 1) (var 2) (var 3) ≐ one ⟶ (length (weights (var 0) (var 1) (var 2) (var 3)) ≐ var 1) ⋏
      membership (var 0) (var 1) (var 2) (weights (var 0) (var 1) (var 2) (var 3)) (var 3)) :=
  closeUniv 4 (.impI (.andI (weights_length _ _ _ _) (test_sound _ _ _ _ Prf.hyp0)))

theorem actual_rational_span_membership_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalOriginalSpanMembership
