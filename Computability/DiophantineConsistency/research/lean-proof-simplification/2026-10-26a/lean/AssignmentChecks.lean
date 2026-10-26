import DiophantineConsistency.Representation

namespace DiophantineConsistency.ProofSimplification

theorem natAssignment_comp_map {σ σ' τ τ' : Type*}
    (v : σ' → Nat) (w : τ' → Nat) (f : σ → σ') (g : τ → τ') :
    natAssignment v w ∘ Sum.map f g = natAssignment (v ∘ f) (w ∘ g) := by
  funext i
  cases i <;> rfl

theorem eval_rename_natAssignment {σ σ' τ τ' : Type*}
    (e : Expr (σ ⊕ τ)) (v : σ' → Nat) (w : τ' → Nat)
    (f : σ → σ') (g : τ → τ') :
    (e.rename (Sum.map f g)).eval (natAssignment v w) =
      e.eval (natAssignment (v ∘ f) (w ∘ g)) := by
  rw [Expr.eval_rename, natAssignment_comp_map]

#print axioms natAssignment_comp_map
#print axioms eval_rename_natAssignment

end DiophantineConsistency.ProofSimplification
