import DemandCompiler

/-!
# Genuine object-iPRA equations for the demand compiler

The statements below conclude `Prf PRAAx`, rather than host semantic equality.
They handle the primitive-recursive backward pass for an ARBITRARY fixed
symbol `D`.  Completing the full two-pass recursion equation still requires
the arithmetic horizon/coherence lemmas to be lowered to the object theory;
the host proof in `BackwardDemand` is not used as an axiom here.
-/

namespace LeanProofs.ConciseIPRA.DemandCompiler

open Syn
open scoped Fm

theorem map_v2 {α β : Type} (f : α → β) (a b : α) :
    (fun i => f (v2 a b i)) = v2 (f a) (f b) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  have hj : j = 0 := by omega
  subst j
  rfl

def backwardTerm {n : Nat} (D : PR 2) (j N k : PTm n) : PTm n :=
  PTm.app (backwardSymbol D) (v3 j N k)

def subTerm {n : Nat} (a b : PTm n) : PTm n :=
  PTm.app monusRev (v2 b a)

def backStepTerm (D : PR 2) : PTm 4 :=
  PTm.app D (v2 (subTerm (var 2) (PTm.succ (var 0))) (var 1))

theorem backStep_compiled (D : PR 2) :
    TermCompiler.symbol (backStepTerm D) = backStep D := by
  unfold backStepTerm backStep
  change PR.comp D _ = PR.comp D _
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change PR.comp monusRev _ = PR.comp monusRev _
    congr 1
    funext j
    refine Fin.cases rfl (fun l => ?_) j
    have hl : l = 0 := by omega
    subst l
    rfl
  · have hj : j = 0 := by omega
    subst j
    rfl

theorem object_backward_zero {n : Nat} {Γ : List (Fm PTm n)}
    (D : PR 2) (N k : PTm n) :
    Γ ⊢[PRAAx] backwardTerm D PTm.zero N k ≐ k := by
  exact Prf.eqTrans (PRA.precZero (.proj 1) (backStep D) (v2 N k))
    (PRA.proj 1 (v2 N k))

theorem object_backward_succ {n : Nat} {Γ : List (Fm PTm n)}
    (D : PR 2) (j N k : PTm n) :
    Γ ⊢[PRAAx] backwardTerm D (PTm.succ j) N k ≐
      PTm.app D (v2 (subTerm N (PTm.succ j)) (backwardTerm D j N k)) := by
  have hr := PRA.precSucc (Γ := Γ) (.proj 1) (backStep D) j (v2 N k)
  let σ : Fin 4 → PTm n :=
    Fin.cases j (Fin.cases (backwardTerm D j N k) (v2 N k))
  have hs := TermCompiler.symbol_correct (Γ := Γ) (backStepTerm D) σ
  rw [backStep_compiled] at hs
  have hσ0 : σ 0 = j := rfl
  have hσ1 : σ 1 = backwardTerm D j N k := rfl
  have hσ2 : σ 2 = N := rfl
  simp only [backStepTerm, subTerm, PTm.subst_app, map_v2, PTm.subst_succ,
    Syn.subst_var, hσ0, hσ1, hσ2] at hs
  apply Prf.eqTrans hr
  dsimp [σ, backwardTerm, backwardSymbol, v3, v2, subTerm] at hs ⊢
  exact hs

end LeanProofs.ConciseIPRA.DemandCompiler

#print axioms LeanProofs.ConciseIPRA.DemandCompiler.object_backward_zero
#print axioms LeanProofs.ConciseIPRA.DemandCompiler.object_backward_succ
