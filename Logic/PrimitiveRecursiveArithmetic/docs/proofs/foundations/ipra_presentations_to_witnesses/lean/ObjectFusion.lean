import ObjectKernel

/-!
# Iteration fusion in the object theory iPRA

These theorems construct the actual judgment `Prf PRAAx`. A host equation is
never promoted to an arithmetic axiom. `fusion` consumes a proof of the local
commutation equation and produces a proof at every finite iteration count.
-/

namespace LeanProofs.ConciseIPRA.FiniteMethods

open Syn
open scoped Fm

def unary {n : Nat} (f : PR 1) (x : PTm n) : PTm n :=
  PTm.app f (fun _ => x)

def iterate (f : PR 1) : PR 2 :=
  .prec (.proj (0 : Fin 1)) (.comp f (fun _ => .proj (1 : Fin 3)))

def iterTerm {n : Nat} (f : PR 1) (k x : PTm n) : PTm n :=
  PTm.app (iterate f) (Fin.cases k (fun _ => x))

@[simp] theorem subst_unary {n m : Nat} (σ : Fin n → PTm m)
    (f : PR 1) (x : PTm n) :
    Syn.subst σ (unary f x) = unary f (Syn.subst σ x) := rfl

@[simp] theorem subst_iterTerm {n m : Nat} (σ : Fin n → PTm m)
    (f : PR 1) (k x : PTm n) :
    Syn.subst σ (iterTerm f k x) = iterTerm f (Syn.subst σ k) (Syn.subst σ x) := by
  unfold iterTerm
  simp only [PTm.subst_app]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem unary_congr {n : Nat} {Γ : List (Fm PTm n)}
    (f : PR 1) {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] unary f x ≐ unary f y := by
  simpa only [unary, PTm.subst_app, Syn.subst_var] using
    (Prf.eqCongr (PTm.app f var) (σ := fun _ => x) (σ' := fun _ => y) (fun _ => h))

theorem iter_zero {n : Nat} {Γ : List (Fm PTm n)} (f : PR 1) (x : PTm n) :
    Γ ⊢[PRAAx] iterTerm f PTm.zero x ≐ x :=
  Prf.eqTrans (PRA.precZero _ _ (fun _ => x)) (PRA.proj _ _)

theorem iter_succ {n : Nat} {Γ : List (Fm PTm n)} (f : PR 1) (k x : PTm n) :
    Γ ⊢[PRAAx] iterTerm f (PTm.succ k) x ≐ unary f (iterTerm f k x) := by
  have h₁ := PRA.precSucc (Γ := Γ) (.proj (0 : Fin 1))
    (.comp f (fun _ => .proj (1 : Fin 3))) k (fun _ => x)
  have h₂ := PRA.comp (Γ := Γ) f (fun _ => .proj (1 : Fin 3))
    (Fin.cases k (Fin.cases (iterTerm f k x) (fun _ => x)))
  have hp := PRA.proj (Γ := Γ) (1 : Fin 3)
    (Fin.cases k (Fin.cases (iterTerm f k x) (fun _ => x)))
  exact Prf.eqTrans (Prf.eqTrans h₁ h₂) (unary_congr f hp)

/-- The local equation in one free variable. -/
def commutes (f g h : PR 1) : Fm PTm 1 :=
  unary h (unary f (var 0)) ≐ unary g (unary h (var 0))

/-- The synthesized QF invariant: counter 0, initial state 1. -/
def fusionInvariant (f g h : PR 1) : Fm PTm 2 :=
  unary h (iterTerm f (var 0) (var 1)) ≐
    iterTerm g (var 0) (unary h (var 1))

/-- A real derivation builder, not a reflection principle. -/
theorem fusion (f g h : PR 1)
    (hlocal : ([] : List (Fm PTm 1)) ⊢[PRAAx] commutes f g h) :
    ([] : List (Fm PTm 1)) ⊢[PRAAx] Fm.all (fusionInvariant f g h) := by
  apply PRA.qfInd (fusionInvariant f g h) (by trivial)
  · simp only [fusionInvariant, Fm.subst_eq, subst_unary, subst_iterTerm,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one]
    exact Prf.eqTrans (unary_congr h (iter_zero f (var 0)))
      (Prf.eqSymm (iter_zero g (unary h (var 0))))
  · simp only [fusionInvariant, Fm.subst_eq, subst_unary, subst_iterTerm,
      Syn.subst_var, Syn.repl_zero, List.map_nil]
    have hi : [fusionInvariant f g h] ⊢[PRAAx]
        unary h (iterTerm f (var 0) (var 1)) ≐
          iterTerm g (var 0) (unary h (var 1)) := Prf.hyp0
    have hc : [fusionInvariant f g h] ⊢[PRAAx]
        unary h (unary f (iterTerm f (var 0) (var 1))) ≐
          unary g (unary h (iterTerm f (var 0) (var 1))) := by
      have hs := hlocal.subst (fun _ => iterTerm f (var 0 : PTm 2) (var 1))
      simpa [commutes] using hs.ofNil (Γ := [fusionInvariant f g h])
    exact Prf.eqTrans (unary_congr h (iter_succ f (var 0) (var 1)))
      (Prf.eqTrans hc (Prf.eqTrans (unary_congr g hi)
        (Prf.eqSymm (iter_succ g (var 0) (unary h (var 1))))))

end LeanProofs.ConciseIPRA.FiniteMethods

#print axioms LeanProofs.ConciseIPRA.FiniteMethods.iter_succ
#print axioms LeanProofs.ConciseIPRA.FiniteMethods.fusion
