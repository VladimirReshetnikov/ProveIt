import DiophantineConsistency.SplitCircuitTranslation59
open DiophantineConsistency.SplitCircuitTranslation59
#print axioms positiveValue_eq_naturalValue

example {R : Type*} [CommRing R] (p : Fin 12 → R) (x : Fin 9 → R) :
    DiophantineConsistency.SplitCircuit59.positiveValue p (fun i => x i+1) =
      DiophantineConsistency.SplitCircuit59.naturalValue p x := by
  rw [positiveValue_eq_naturalValue]
  simp only [add_sub_cancel_right]
