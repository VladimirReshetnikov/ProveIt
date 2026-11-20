import ConciseIPRA.PR

/-! Imported from the packet `foundations/ipra_continuous_mathematics_2026-11-20`, `lean/ObjectTransport.lean`: the namespace is placed under `LeanProofs.IPRA.Foundations` and the `#print axioms` lines are dropped (the library audits axioms in `Checks/Axioms.lean`). -/

/-! Transport a signed threshold sequent through any fixed finite play.
Selectors are actual object terms. Leaves are actual object derivations.
The checker never assumes a universal evaluator for programs. -/
namespace LeanProofs.IPRA.Foundations.QuantifierTransport
open LeanProofs.ConciseIPRA Syn
open scoped Fm
set_option autoImplicit false

variable {n : Nat} {Γ : List (Fm PTm n)}

private theorem openWith (P : Fm PTm (n+1)) (t : PTm (n+1)) :
    (P.subst (up (fun i : Fin n => (var i.succ : PTm (n+1))))).subst (inst t)
      = P.subst (repl t) := by
  rw [Fm.subst_subst]
  congr 1
  refine funext (Fin.cases ?_ fun j => ?_) <;> simp

/-- A response on the source side takes each target challenge to a source challenge. -/
theorem pullAll (P Q : Fm PTm (n+1)) (s : PTm (n+1))
    (localProof : Γ.map Fm.shift ⊢[PRAAx] P.subst (repl s) ⟶ Q) :
    Γ ⊢[PRAAx] Fm.all P ⟶ Fm.all Q := by
  apply Prf.impI
  apply Prf.allI
  have h := Prf.allE s (Prf.shift (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := Fm.all P)))
  change _ ⊢[PRAAx] (P.subst (up _)).subst (inst s) at h
  rw [openWith] at h
  exact Prf.impE localProof.wk h

/-- A response on the target side sends an exhibited source witness to a target witness. -/
theorem pushEx (P Q : Fm PTm (n+1)) (t : PTm (n+1))
    (localProof : Γ.map Fm.shift ⊢[PRAAx] P ⟶ Q.subst (repl t)) :
    Γ ⊢[PRAAx] Fm.ex P ⟶ Fm.ex Q := by
  apply Prf.impI
  apply Prf.exE Prf.hyp0
  change _ ⊢[PRAAx] Fm.ex (Q.subst (up (fun i : Fin n => (var i.succ : PTm (n+1)))))
  apply Prf.exI t
  rw [openWith]
  exact Prf.impE localProof.wk.wk Prf.hyp0

/-- Derivation recipes for strings of numerical quantifiers. Domain guards,
threshold slack and extensionality premises belong to the leaf sequents.
The source/target substitution at each constructor also acts under binders. -/
inductive Plan : {n : Nat} → List (Fm PTm n) → Fm PTm n → Fm PTm n → Type
  | leaf {n : Nat} {Γ : List (Fm PTm n)} {P Q : Fm PTm n}
      (h : Γ ⊢[PRAAx] P ⟶ Q) : Plan Γ P Q
  | allStep {n : Nat} {Γ : List (Fm PTm n)} {P Q : Fm PTm (n+1)}
      (s : PTm (n+1)) (subplan : Plan (Γ.map Fm.shift) (P.subst (repl s)) Q) :
      Plan Γ (.all P) (.all Q)
  | exStep {n : Nat} {Γ : List (Fm PTm n)} {P Q : Fm PTm (n+1)}
      (t : PTm (n+1)) (subplan : Plan (Γ.map Fm.shift) P (Q.subst (repl t))) :
      Plan Γ (.ex P) (.ex Q)

theorem Plan.derive {P Q : Fm PTm n} (plan : Plan Γ P Q) : Γ ⊢[PRAAx] P ⟶ Q := by
  induction plan with
  | leaf proof => exact proof
  | allStep s _ ih => exact pullAll _ _ s ih
  | exStep t _ ih => exact pushEx _ _ t ih

end LeanProofs.IPRA.Foundations.QuantifierTransport
