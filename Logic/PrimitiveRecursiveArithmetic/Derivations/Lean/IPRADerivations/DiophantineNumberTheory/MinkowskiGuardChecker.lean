import IPRADerivations.DiophantineNumberTheory.MinkowskiWellFormed
import IPRADerivations.Foundations.BoundedSyntax
import IPRADerivations.Core.Header

/-!
# Boolean reflection of the canonical rational-vector guard

This compiles the actual code-reconstruction, signed-part, gcd, length and
bounded entry tests.  The resulting fixed PR2 symbol is proved equivalent
to the full canonical vector guard, uniformly in the runtime dimension.
In particular, the bounded quantifier in that guard is not treated as a
quantifier-free formula.  This is the well-formedness component of the
source's numerical certificate checker, not the entire `BoxOK` checker.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiGuardChecker

set_option maxRecDepth 8192

open_ipra
open LeanProofs.IPRA.Analysis.RationalSupMetric (numeratorOf denominatorOf rationalCode)
open LeanProofs.IPRA.Analysis.RationalNormalForm (wellFormed)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open LeanProofs.IPRA.Foundations.BoundedSyntax
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiCenterVectors
open LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiWellFormed

variable {n : ℕ} {Γ : List (Fm PTm n)}

def scalarSyntax (c : PTm n) : BFm n :=
  .and (.eq c (rationalCode (numeratorOf c) (denominatorOf c)))
    (.and (.or (.eq (numeratorOf c).pos zero) (.eq (numeratorOf c).neg zero))
      (.eq (gcd (zabs (numeratorOf c)) (denominatorOf c)) one))

def vectorSyntax (N C : PTm n) : BFm n :=
  .and (.eq (length C) N)
    (.and (.eq C (sequence entryBody N C))
      (.all N (scalarSyntax (entry (Syn.shift C) (var 0)))))

theorem scalar_formula (c : PTm n) : formula (scalarSyntax c) = wellFormed c := rfl
theorem vector_formula (N C : PTm n) : formula (vectorSyntax N C) = vectorGuard N C := rfl

def guardF : PR 2 := bitF (vectorSyntax (var 0) (var 1) : BFm 2)
def check (N C : PTm n) : PTm n := ap2 guardF N C

theorem checker_program (N C : PTm n) : Γ ⊢[PRAAx] check N C ≐
    bit (vectorSyntax (var 0) (var 1) : BFm 2) ![N,C] :=
  program_correct (vectorSyntax (var 0) (var 1) : BFm 2) ![N,C]

theorem check_reflection (N C : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (check N C ≐ one) (vectorGuard N C) := by
  have h : Γ ⊢[PRAAx] Fm.iff
      (bit (vectorSyntax (var 0) (var 1) : BFm 2) ![N,C] ≐ one) (vectorGuard N C) := by
    have r := bounded_reflection (Γ := Γ) (vectorSyntax (var 0) (var 1) : BFm 2) ![N,C]
    rw [vector_formula] at r
    simpa only [subst_vectorGuard,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using r
  have p := checker_program (Γ := Γ) N C
  exact .iffI (.impI (h.wk.iffMp (p.wk.eqSymm.eqTrans Prf.hyp0)))
    (.impI (p.wk.eqTrans (h.wk.iffMpr Prf.hyp0)))

theorem check_boolean (N C : PTm n) : Γ ⊢[PRAAx] (check N C ≐ zero) ⋎ (check N C ≐ one) := by
  have p := checker_program (Γ := Γ) N C
  exact .orE (bit_cases (vectorSyntax (var 0) (var 1) : BFm 2) ![N,C])
    (.orI₁ (p.wk.eqTrans Prf.hyp0)) (.orI₂ (p.wk.eqTrans Prf.hyp0))

theorem guard_checker_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Fm.iff (check (var 0) (var 1) ≐ one) (vectorGuard (var 0) (var 1))) :=
  closeUniv 2 (check_reflection _ _)

theorem guard_checker_boolean_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((check (var 0) (var 1) ≐ zero) ⋎ (check (var 0) (var 1) ≐ one)) :=
  closeUniv 2 (check_boolean _ _)

theorem generated_checks_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶
      ((check (var 0) (centerVector (var 0) (var 1) (var 2)) ≐ one) ⋏
        ((check (var 0) (oppositeVector (var 0) (var 2)) ≐ one) ⋏
          ((check (var 0) (midpointVector (var 0) (var 1) (var 2)) ≐ one) ⋏
            (check (var 0) (integerVector (var 0) (var 2)) ≐ one))))) :=
  closeUniv 3 (.impI (.andI
    ((check_reflection _ _).iffMpr (center_vector_guard _ _ _ Prf.hyp0))
    (.andI ((check_reflection _ _).iffMpr (opposite_vector_guard _ _))
      (.andI ((check_reflection _ _).iffMpr (midpoint_vector_guard _ _ _))
        ((check_reflection _ _).iffMpr (integer_vector_guard _ _))))))

end LeanProofs.IPRA.DiophantineNumberTheory.MinkowskiGuardChecker
