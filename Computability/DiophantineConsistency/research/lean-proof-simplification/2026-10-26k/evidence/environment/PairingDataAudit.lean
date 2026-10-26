import DiophantineConsistency.PairingRepresentation

/-! Exact baseline graph data copied from repository commit
6175dff9a15491497c7a3c1bda4f6a62a6349c74, then compared by definitional equality.
This validates both witness count and expression, and proof irrelevance
accounts for the changed correctness certificate. -/
namespace DiophantineConsistency.GraphRep

/-- The first inverse-pairing coordinate graph uses the second as a witness. -/
def unpairLeftCoordinateBaseline : GraphRep (fun v : Fin 1 → ℕ => (Nat.unpair (v 0)).1) := by
  let index : Option (Fin 2) → Option (Fin 1) ⊕ Fin 1
    | none => .inl (some 0)
    | some i => if i = 0 then .inl none else .inr 0
  refine ((Rep.reindex pairCoordinates index).existsBlock).ofIff ?_
  intro v
  change (∃ w : Fin 1 → ℕ, v (some 0) = Nat.pair (v none) (w 0)) ↔
    v none = (Nat.unpair (v (some 0))).1
  constructor
  · rintro ⟨w, h⟩
    rw [h, Nat.unpair_pair]
  · intro h
    refine ⟨fun _ => (Nat.unpair (v (some 0))).2, ?_⟩
    rw [h, Nat.pair_unpair]

/-- The second inverse-pairing coordinate graph uses the first as a witness. -/
def unpairRightCoordinateBaseline : GraphRep (fun v : Fin 1 → ℕ => (Nat.unpair (v 0)).2) := by
  let index : Option (Fin 2) → Option (Fin 1) ⊕ Fin 1
    | none => .inl (some 0)
    | some i => if i = 0 then .inr 0 else .inl none
  refine ((Rep.reindex pairCoordinates index).existsBlock).ofIff ?_
  intro v
  change (∃ w : Fin 1 → ℕ, v (some 0) = Nat.pair (w 0) (v none)) ↔
    v none = (Nat.unpair (v (some 0))).2
  constructor
  · rintro ⟨w, h⟩
    rw [h, Nat.unpair_pair]
  · intro h
    refine ⟨fun _ => (Nat.unpair (v (some 0))).1, ?_⟩
    rw [h, Nat.pair_unpair]

example : unpairLeftCoordinate = unpairLeftCoordinateBaseline := rfl
example : unpairRightCoordinate = unpairRightCoordinateBaseline := rfl

#print axioms unpairLeftCoordinate
#print axioms unpairRightCoordinate
#eval unpairLeftCoordinate.witnessCount
#eval unpairRightCoordinate.witnessCount

end DiophantineConsistency.GraphRep
