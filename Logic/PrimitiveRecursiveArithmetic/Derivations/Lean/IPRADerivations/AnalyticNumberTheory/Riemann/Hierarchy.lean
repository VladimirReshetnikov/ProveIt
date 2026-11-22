import ConciseIPRA.PR

/-! Imported from the packet `analytic-number-theory/riemann_hypotheses_ipra_2026-11-20`,
`Hierarchy.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! The three closed sentences and their specialization inside iPRA.
    The function symbol's arguments are (degree parameter, H, u, v, cutoff). -/

namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RHHierarchy

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- An atomic equality of scoped iPRA terms. -/
def atom {n : Nat} (f : PR 5) (d H u v t : PTm n) : Fm PTm n :=
  Fm.eq (PTm.app f (Fin.cases d (Fin.cases H (Fin.cases u (Fin.cases v (fun _ => t)))))) PTm.zero

def ERHOf (f : PR 5) : Fm PTm 0 :=
  Fm.all (Fm.all (Fm.all (Fm.all (Fm.all
    (atom f (var 4) (var 3) (var 2) (var 1) (var 0))))))

def GRHOf (f : PR 5) : Fm PTm 0 :=
  Fm.all (Fm.all (atom f (var 1) PTm.zero PTm.zero (PTm.succ PTm.zero) (var 0)))

def RHOf (f : PR 5) : Fm PTm 0 :=
  Fm.all (atom f PTm.zero PTm.zero PTm.zero (PTm.succ PTm.zero) (var 0))

private theorem subst_atom {n m : Nat} (f : PR 5) (d H u v t : PTm n)
    (σ : Fin n → PTm m) :
    (atom f d H u v t).subst σ =
      atom f (subst σ d) (subst σ H) (subst σ u) (subst σ v) (subst σ t) := by
  simp only [atom, Fm.subst_eq, PTm.subst_app, PTm.subst_zero]
  congr 2
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun c =>
    Fin.cases ?_ (fun _ => rfl) c) b) a) i <;> rfl

@[simp] private theorem casesTwo {α : Sort _} {n : Nat} (a : α) (g : Fin (n+2) → α) :
    (Fin.cases a g : Fin (n+3) → α) 2 = g 1 := rfl

@[simp] private theorem casesThree {α : Sort _} {n : Nat} (a : α) (g : Fin (n+3) → α) :
    (Fin.cases a g : Fin (n+4) → α) 3 = g 2 := rfl

@[simp] private theorem casesFour {α : Sort _} {n : Nat} (a : α) (g : Fin (n+4) → α) :
    (Fin.cases a g : Fin (n+5) → α) 4 = g 3 := rfl

/-- Set H and u to zero and v to one, leaving d and the cutoff universal. -/
theorem erh_implies_grh (f : PR 5) :
    Prf PRAAx [] (Fm.imp (ERHOf f) (GRHOf f)) := by
  apply Prf.impI
  apply Prf.allI
  have h := Prf.allOpen (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := ERHOf f))
  have hH := Prf.allE PTm.zero h
  have hu := Prf.allE PTm.zero hH
  have hv := Prf.allE (PTm.succ PTm.zero) hu
  simpa [ERHOf, Fm.subst_all, subst_atom, Syn.up, Syn.inst] using hv

/-- Set d to zero while leaving the cutoff universal. -/
theorem grh_implies_rh (f : PR 5) :
    Prf PRAAx [] (Fm.imp (GRHOf f) (RHOf f)) := by
  apply Prf.impI
  have hd := Prf.allE PTm.zero (Prf.hyp0 (Ax := PRAAx) (Γ := []) (φ := GRHOf f))
  simpa [GRHOf, RHOf, Fm.subst_all, subst_atom, Syn.up, Syn.inst] using hd

theorem erh_implies_rh (f : PR 5) :
    Prf PRAAx [] (Fm.imp (ERHOf f) (RHOf f)) :=
  Prf.impTrans (erh_implies_grh f) (grh_implies_rh f)

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RHHierarchy
