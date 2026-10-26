import IterationMathlib
import DiophantineConsistency.AnnotatedClosure

/-! Authored candidate; full pinned-project elaboration is still required. -/
namespace DiophantineConsistency.AnnotatedClosure
open SetTheory SetTheory.Form AnnotatedProofCode AnnotatedRename
open CheckerRefactor.MathlibAdapter

/-- The source syntax iterator agrees with the standard iterator. -/
theorem closeN_eq_iterate_candidate (n : Nat) (f : Form) :
    closeN n f = fAll^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => exact ih (fAll f)

/-- A coded closure theorem only needs correctness on genuine formula codes,
not equality of coded steps on arbitrary (possibly malformed) natural inputs. -/
theorem coded_closure_candidate (codedStep : Nat → Nat)
    (hstep : ∀ f : Form, codedStep (formCode f) = formCode (fAll f))
    (f : Form) (n : Nat) :
    n.rec (formCode f) (fun _ acc => codedStep acc) = formCode (closeN n f) := by
  rw [rec_eq_iterate, closeN_eq_iterate_candidate]
  have h : Function.Semiconj formCode fAll codedStep := fun a => (hstep a).symm
  exact (h.iterate_right n f).symm

-- Replacement of closeCode_formCode.
example (f : Form) (n : Nat) :
    closeCode (formCode f) n = formCode (closeN n f) :=
  coded_closure_candidate (unaryCode 6) (fun a => (code_all a).symm) f n

-- Replacement of closeQuadratic_formCode.
example (f : Form) (n : Nat) :
    closeQuadratic (formCode f) n = formCode (closeN n f) :=
  coded_closure_candidate (fun c => c * c + 39)
    (fun a => (code_all_quadratic a).symm) f n

end DiophantineConsistency.AnnotatedClosure
