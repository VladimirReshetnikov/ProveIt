import IPRADerivations.Foundations.MasterCertificate
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CommonLemmas
import IPRADerivations.Core.Header
import IPRADerivations.Core.BoundedSums

/-!
# Literal equality of sequences constructed by the checked stack program

Two fixed primitive-recursive sequence bodies, possibly at different
persistent parameters, construct the same natural-number code when every
in-range body value agrees. A guarded QF induction proves equality of their
actual reverse stacks. The bounded pointwise contract stays in the fixed
context; no induction on a quantified formula is used.

This theorem concerns the actual `MasterCertificate.sequence` constructor.
It does not assert extensionality of arbitrary or malformed sequence codes.
-/

namespace LeanProofs.IPRA.Foundations.SequenceEquality

open_ipra exports
open LeanProofs.IPRA.Foundations.MasterCertificate
  (stack stack_zero stack_succ sequence)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private alias pair_congr := Common.congrPairT

def agree (A B : PTm 2) (N x y : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ (inst2 A (var 0) (Syn.shift x) ≐ inst2 B (var 0) (Syn.shift y)))

@[simp] theorem subst_agree {m : ℕ} (σ : Fin n → PTm m) (A B : PTm 2) (N x y : PTm n) :
    (agree A B N x y).subst σ = agree A B (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) := by
  simp only [agree,Fm.subst_all,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_inst2,
    Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

@[simp] theorem subst_stack {m : ℕ} (σ : Fin n → PTm m) (A : PTm 2) (N x : PTm n) :
    Syn.subst σ (stack A N x) = stack A (Syn.subst σ N) (Syn.subst σ x) := subst_ap2 _ _ _ _

theorem agree_at (A B : PTm 2) (N x y i : PTm n) (h : Γ ⊢[PRAAx] agree A B N x y)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] inst2 A i x ≐ inst2 B i y := by
  have rule : Γ ⊢[PRAAx] lt i N ⟶ (inst2 A i x ≐ inst2 B i y) := by
    simpa only [agree,Fm.subst_imp,Fm.subst_eq,subst_lt,subst_inst2,Syn.subst_var,
      Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE i h
  exact .impE rule hi

theorem stack_equal (A B : PTm 2) (N x y : PTm n) (h : Γ ⊢[PRAAx] agree A B N x y) :
    Γ ⊢[PRAAx] stack A N x ≐ stack B N y := by
  let P : Fm PTm (n + 1) := stack A (var 0) (Syn.shift x) ≐ stack B (var 0) (Syn.shift y)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N trivial ?_ ?_
    · simpa only [P,Fm.subst_eq,subst_stack,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
        using (stack_zero (Γ := Γ) A x).eqTrans (stack_zero B y).eqSymm
    · simp only [P,Fm.subst_eq,subst_stack,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let Δ := lt (var 0) (Syn.shift N) :: P :: Γ.map Fm.shift
      have contract : Γ.map Fm.shift ⊢[PRAAx] agree A B (Syn.shift N) (Syn.shift x) (Syn.shift y) := by
        simpa only [Fm.shift,subst_agree,Syn.shift] using h.shift
      have head := agree_at A B (Syn.shift N) (Syn.shift x) (Syn.shift y) (var 0)
        contract.wk.wk (Prf.hyp0 : Δ ⊢[PRAAx] _)
      exact (stack_succ A _ _).eqTrans ((pair_congr head Prf.hyp1).eqTrans (stack_succ B _ _).eqSymm)
  simpa only [P,Fm.subst_eq,subst_stack,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using atBound

theorem sequence_equal (A B : PTm 2) (N x y : PTm n) (h : Γ ⊢[PRAAx] agree A B N x y) :
    Γ ⊢[PRAAx] sequence A N x ≐ sequence B N y := pair_congr (.eqRefl _) (stack_equal A B N x y h)

theorem constructed_sequence_equality (A B : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (agree A B (var 0) (var 1) (var 2) ⟶
        (sequence A (var 0) (var 1) ≐ sequence B (var 0) (var 2))) :=
  closeUniv 3 (.impI (sequence_equal A B _ _ _ Prf.hyp0))

#print axioms agree_at
#print axioms stack_equal
#print axioms sequence_equal
#print axioms constructed_sequence_equality

end LeanProofs.IPRA.Foundations.SequenceEquality

export_ipra Foundations.SequenceEquality (sequence_equal)
