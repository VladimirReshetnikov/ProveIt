import DiophantineConsistency.DirectComposition

open DiophantineConsistency

private def c : GraphRep (fun _ : Fin 0 → ℕ => 7) := GraphRep.constant 7
private def args : ∀ i : Fin 0, GraphRep (fun _ : Fin 1 → ℕ => i.val) := fun i => Fin.elim0 i

-- Even an empty argument block should not copy the exposed output coordinate.
example : (GraphRep.composeDirect c args).witnessCount = 0 := rfl
example : (GraphRep.compose c args).witnessCount = 1 := rfl

#print axioms GraphRep.composeDirect
#print axioms GraphRep.composeDirect_saves_one
