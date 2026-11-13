import DiophantineConsistency.ModelJonesSyntax

/-! UNCOMPILED arity-generic input substitution, independent of any seed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign32GenericRemoveInput
variable {R : Type*} [CommRing R]

def removeInput {n : ℕ} (e : Expr (Fin (n + 1))) : Expr (Fin n) :=
  e.subst (Fin.cons (.constant 1) (fun i => .var i))

theorem eval_removeInput {n : ℕ} (e : Expr (Fin (n + 1))) (a : Fin n → R) :
    (removeInput e).evalRing a = e.evalRing (Fin.cons 1 a) := by
  rw [removeInput, ModelJonesSyntax.evalRing_subst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Expr.evalRing]
  · simp [Expr.evalRing]
end DiophantineConsistency.Sign32GenericRemoveInput
#print axioms DiophantineConsistency.Sign32GenericRemoveInput.eval_removeInput
