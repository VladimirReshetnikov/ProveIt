import ObjectBridge

/-!
# An actual object-iPRA induction and witness

These are `Prf PRAAx` derivations, not just equations about host natural
numbers.  Addition is represented by its explicit PR syntax.  The example
tests the scoping and induction boundary used by larger compiled contracts.
-/

namespace LeanProofs.ConciseIPRA.FrameworkExamples

open Syn
open scoped Fm

def addStep : PR 3 := PR.comp PR.succ (fun _ : Fin 1 => PR.proj (1 : Fin 3))

def addSymbol : PR 2 := PR.prec (PR.proj (0 : Fin 1)) addStep

def addTerm {n : Nat} (y x : PTm n) : PTm n :=
  PTm.app addSymbol (Fin.cases y (fun _ : Fin 1 => x))

@[simp] theorem subst_addTerm {n m : Nat} (σ : Fin n → PTm m) (y x : PTm n) :
    Syn.subst σ (addTerm y x) = addTerm (Syn.subst σ y) (Syn.subst σ x) := by
  simp only [addTerm, PTm.subst_app]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem add_zero {n : Nat} {Γ : List (Fm PTm n)} (x : PTm n) :
    Γ ⊢[PRAAx] addTerm PTm.zero x ≐ x := by
  have h₁ := PRA.precZero (Γ := Γ) (PR.proj (0 : Fin 1)) addStep
    (fun _ : Fin 1 => x)
  have h₂ := PRA.proj (Γ := Γ) (0 : Fin 1) (fun _ : Fin 1 => x)
  exact Prf.eqTrans h₁ h₂

theorem add_succ {n : Nat} {Γ : List (Fm PTm n)} (y x : PTm n) :
    Γ ⊢[PRAAx] addTerm (PTm.succ y) x ≐ PTm.succ (addTerm y x) := by
  let args : Fin 3 → PTm n :=
    Fin.cases y (Fin.cases (addTerm y x) (fun _ : Fin 1 => x))
  have h₁ := PRA.precSucc (Γ := Γ) (PR.proj (0 : Fin 1)) addStep y
    (fun _ : Fin 1 => x)
  have h₂ := PRA.comp (Γ := Γ) PR.succ
    (fun _ : Fin 1 => PR.proj (1 : Fin 3)) args
  have h₃ := Prf.eqCongr1 (PTm.succ (Syn.var 0))
    (PRA.proj (Γ := Γ) (1 : Fin 3) args)
  have h₃' : Γ ⊢[PRAAx]
      PTm.app PR.succ (fun _ : Fin 1 => PTm.app (PR.proj (1 : Fin 3)) args)
        ≐ PTm.succ (addTerm y x) := by
    simpa [PTm.succ, args] using h₃
  exact Prf.eqTrans h₁ (Prf.eqTrans h₂ h₃')

def zeroRight : Fm PTm 1 :=
  addTerm (Syn.var 0) PTm.zero ≐ Syn.var 0

/-- A non-definitional identity obtained by object quantifier-free induction. -/
theorem add_right_zero : ([] : List (Fm PTm 0)) ⊢[PRAAx] Fm.all zeroRight := by
  apply PRA.qfInd zeroRight
  · trivial
  · simpa [zeroRight] using
      (add_zero (Γ := ([] : List (Fm PTm 0))) (PTm.zero : PTm 0))
  · have ih : [zeroRight] ⊢[PRAAx]
        addTerm (Syn.var 0) PTm.zero ≐ (Syn.var 0 : PTm 1) := Prf.hyp0
    have hs := add_succ (Γ := [zeroRight]) (Syn.var 0 : PTm 1) PTm.zero
    have hc := Prf.eqCongr1 (PTm.succ (Syn.var 0)) ih
    have hc' : [zeroRight] ⊢[PRAAx]
        PTm.succ (addTerm (Syn.var 0) PTm.zero) ≐ PTm.succ (Syn.var 0 : PTm 1) := by
      simpa using hc
    simpa [zeroRight] using Prf.eqTrans hs hc'

/-- Output slot 0, input slot 1: `y = x`. -/
def identityContract : FiniteContracts.Contract 1 where
  pre := PTm.zero ≐ (PTm.zero : PTm 1)
  program := PR.proj 0
  post := Syn.var 0 ≐ (Syn.var 1 : PTm 2)
  certified := by
    simpa using (PRA.proj (Γ := [PTm.zero ≐ (PTm.zero : PTm 1)])
      (0 : Fin 1) (Syn.var : Fin 1 → PTm 1))

theorem identity_exists :
    [] ⊢[PRAAx] (identityContract.pre ⟶ Fm.ex identityContract.post) :=
  identityContract.asImplication

end LeanProofs.ConciseIPRA.FrameworkExamples
