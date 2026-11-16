import ObjectKernel

/-!
# Substitution and cut for witness contracts

These theorems conclude `Prf PRAAx ...`: they manipulate genuine object-iPRA
derivations.  The input certificates are obligations, not unproved axioms.
Witnesses are terms; a fixed term compiles structurally to a fixed PR symbol.
-/

namespace LeanProofs.ConciseIPRA.Framework

open Syn
open scoped Fm

/-- Q has its result in variable 0 and the original parameters after it. -/
structure TermContract {n : Nat} (P : Fm PTm n) (Q : Fm PTm (n + 1)) where
  witness : PTm n
  certified : [P] ⊢[PRAAx] Q.subst (inst witness)

namespace TermContract

variable {n : Nat} {P : Fm PTm n} {Q : Fm PTm (n + 1)}

theorem existsOutput (c : TermContract P Q) : [P] ⊢[PRAAx] Fm.ex Q :=
  Prf.exI c.witness c.certified

theorem asImplication (c : TermContract P Q) :
    [] ⊢[PRAAx] P ⟶ Fm.ex Q := Prf.impI c.existsOutput

/-- Sequential composition retains the first witness as a term in the second
postcondition.  The result is still a first-order iPRA proof. -/
def compose {R : Fm PTm (n + 2)}
    (c : TermContract P Q) (d : TermContract Q R) :
    TermContract P (R.subst (up (inst c.witness))) where
  witness := Syn.subst (inst c.witness) d.witness
  certified := by
    have hd := d.certified.subst (inst c.witness)
    rw [Fm.subst_inst] at hd
    apply hd.trans
    intro ψ hψ
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hψ
    subst ψ
    exact c.certified

/-- Specialization of fixed free parameters commutes with the contract. -/
def specialize {m : Nat} (c : TermContract P Q) (σ : Fin n → PTm m) :
    TermContract (P.subst σ) (Q.subst (up σ)) where
  witness := Syn.subst σ c.witness
  certified := by
    have h := c.certified.subst σ
    simpa only [List.map_cons, List.map_nil, Fm.subst_inst] using h

end TermContract

/-- Exact quantifier-free induction interface for compiled finite invariants. -/
structure LoopCertificate {n : Nat} (Γ : List (Fm PTm n)) where
  invariant : Fm PTm (n + 1)
  qf : invariant.QF
  base : Γ ⊢[PRAAx] invariant.subst (inst PTm.zero)
  step : invariant :: Γ.map Fm.shift ⊢[PRAAx]
    invariant.subst (repl (PTm.succ (var 0)))

theorem LoopCertificate.conclude {n : Nat} {Γ : List (Fm PTm n)}
    (c : LoopCertificate Γ) : Γ ⊢[PRAAx] Fm.all c.invariant :=
  PRA.qfInd c.invariant c.qf c.base c.step

/-- Explicit fixed PR symbol: iteration of the identity on the accumulator. -/
def identityIteration : PR 2 :=
  .prec (.proj (0 : Fin 1)) (.proj (1 : Fin 3))

/-- The invariant has the iteration counter at 0 and the seed at 1. -/
def identityInvariant : Fm PTm 2 :=
  PTm.app identityIteration var ≐ var 1

theorem identityIteration_proved :
    ([] : List (Fm PTm 1)) ⊢[PRAAx] Fm.all identityInvariant := by
  apply PRA.qfInd identityInvariant (by trivial)
  · change ([] : List (Fm PTm 1)) ⊢[PRAAx]
      PTm.app identityIteration (Fin.cases PTm.zero var) ≐ var 0
    exact Prf.eqTrans (PRA.precZero _ _ _) (PRA.proj _ _)
  · change [identityInvariant] ⊢[PRAAx]
      PTm.app identityIteration (repl (PTm.succ (var 0))) ≐ var 1
    have h := PRA.precSucc (Γ := [identityInvariant]) (.proj (0 : Fin 1)) (.proj (1 : Fin 3))
      (var 0 : PTm 2) (fun _ => (var 1 : PTm 2))
    have hp := PRA.proj (Γ := [identityInvariant]) (1 : Fin 3)
      (Fin.cases (var 0 : PTm 2)
        (Fin.cases (PTm.app identityIteration (Fin.cases (var 0) (fun _ => var 1)))
          (fun _ => var 1)))
    have hi : [identityInvariant] ⊢[PRAAx] identityInvariant := Prf.hyp0
    have e0 : (Fin.cases (var 0 : PTm 2) (fun _ : Fin 1 => var 1)) = var := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      have hj : j = 0 := by omega
      subst j
      rfl
    have e1 : (Fin.cases (PTm.succ (var 0 : PTm 2)) (fun _ : Fin 1 => var 1)) =
        repl (PTm.succ (var 0)) := by
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      have hj : j = 0 := by omega
      subst j
      rfl
    rw [e1, e0] at h
    rw [e0] at hp
    exact Prf.eqTrans (Prf.eqTrans h hp) hi

end LeanProofs.ConciseIPRA.Framework

#print axioms LeanProofs.ConciseIPRA.Framework.TermContract.compose
#print axioms LeanProofs.ConciseIPRA.Framework.identityIteration_proved
