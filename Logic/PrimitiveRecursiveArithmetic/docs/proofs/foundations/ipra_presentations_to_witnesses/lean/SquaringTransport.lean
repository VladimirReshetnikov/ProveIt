import ObjectSimulation

/-!
# Repeated squaring transported by a certified multiplicative map

The two multiplication codes need not be identical. The sole local algebraic
input is an actual object proof of multiplicativity. No host semiring instance
or evaluation theorem is silently reflected into iPRA.
-/

namespace LeanProofs.ConciseIPRA.FiniteMethods

open Syn
open scoped Fm

def binary {n : Nat} (m : PR 2) (x y : PTm n) : PTm n :=
  PTm.app m (tuple2 x y)

@[simp] theorem subst_binary {n k : Nat} (σ : Fin n → PTm k)
    (m : PR 2) (x y : PTm n) :
    Syn.subst σ (binary m x y) = binary m (Syn.subst σ x) (Syn.subst σ y) := by
  simp only [binary, PTm.subst_app, subst_tuple2]

def square (m : PR 2) : PR 1 := .comp m (fun _ => .proj (0 : Fin 1))

theorem square_eq {n : Nat} {Γ : List (Fm PTm n)} (m : PR 2) (x : PTm n) :
    Γ ⊢[PRAAx] unary (square m) x ≐ binary m x x := by
  have h₁ := PRA.comp (Γ := Γ) m (fun _ => .proj (0 : Fin 1)) (fun _ => x)
  have h₂ := Prf.eqCongr (Γ := Γ) (PTm.app m var)
    (σ := fun _ => PTm.app (.proj (0 : Fin 1)) (fun _ => x))
    (σ' := tuple2 x x) (fun i => Fin.cases (PRA.proj _ _) (fun _ => PRA.proj _ _) i)
  exact Prf.eqTrans h₁ h₂

def multiplicative (m m' : PR 2) (h : PR 1) : Fm PTm 2 :=
  unary h (binary m (var 0) (var 1)) ≐
    binary m' (unary h (var 0)) (unary h (var 1))

theorem squaring_commutes (m m' : PR 2) (h : PR 1)
    (hMul : ([] : List (Fm PTm 2)) ⊢[PRAAx] multiplicative m m' h) :
    ([] : List (Fm PTm 1)) ⊢[PRAAx] commutes (square m) (square m') h := by
  have hm : ([] : List (Fm PTm 1)) ⊢[PRAAx]
      unary h (binary m (var 0) (var 0)) ≐
        binary m' (unary h (var 0)) (unary h (var 0)) := by
    simpa [multiplicative] using hMul.subst (fun _ => (var 0 : PTm 1))
  exact Prf.eqTrans (unary_congr h (square_eq m (var 0)))
    (Prf.eqTrans hm (Prf.eqSymm (square_eq m' (unary h (var 0)))))

/-- Finite powers x^(2^n) commute with every certified multiplicative map. -/
theorem repeated_squaring_transport (m m' : PR 2) (h : PR 1)
    (hMul : ([] : List (Fm PTm 2)) ⊢[PRAAx] multiplicative m m' h) :
    ([] : List (Fm PTm 1)) ⊢[PRAAx]
      Fm.all (fusionInvariant (square m) (square m') h) :=
  fusion _ _ _ (squaring_commutes m m' h hMul)

/-- An unconditional arithmetic instance, requiring no local certificate. -/
theorem successor_transport :
    ([] : List (Fm PTm 1)) ⊢[PRAAx]
      Fm.all (fusionInvariant PR.succ PR.succ PR.succ) :=
  fusion _ _ _ (Prf.eqRefl _)

end LeanProofs.ConciseIPRA.FiniteMethods

#print axioms LeanProofs.ConciseIPRA.FiniteMethods.repeated_squaring_transport
#print axioms LeanProofs.ConciseIPRA.FiniteMethods.successor_transport
