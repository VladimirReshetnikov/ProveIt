import DiophantineConsistency.Sign14Positive74CircuitTransitionProbe
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74Circuit

theorem symState4 (p : Fin 4 → ℤ) : symState p 4 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p, Sign14Positive74.g02 p, Sign14Positive74.g03 p] := by
  rw [symState, symState3]
  rfl

theorem numState4 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 4 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v, (Sign14Positive74.g02 p).evalRing v, (Sign14Positive74.g03 p).evalRing v] := by
  rw [numState, numState3]
  rfl

theorem symState5 (p : Fin 4 → ℤ) : symState p 5 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p, Sign14Positive74.g02 p, Sign14Positive74.g03 p, Sign14Positive74.g04 p] := by
  rw [symState, symState4]
  rfl

theorem numState5 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 5 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v, (Sign14Positive74.g02 p).evalRing v, (Sign14Positive74.g03 p).evalRing v, (Sign14Positive74.g04 p).evalRing v] := by
  rw [numState, numState4]
  rfl

theorem symState6 (p : Fin 4 → ℤ) : symState p 6 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p, Sign14Positive74.g02 p, Sign14Positive74.g03 p, Sign14Positive74.g04 p, Sign14Positive74.g05 p] := by
  rw [symState, symState5]
  rfl

theorem numState6 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 6 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v, (Sign14Positive74.g02 p).evalRing v, (Sign14Positive74.g03 p).evalRing v, (Sign14Positive74.g04 p).evalRing v, (Sign14Positive74.g05 p).evalRing v] := by
  rw [numState, numState5]
  rfl

theorem symState7 (p : Fin 4 → ℤ) : symState p 7 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p, Sign14Positive74.g02 p, Sign14Positive74.g03 p, Sign14Positive74.g04 p, Sign14Positive74.g05 p, Sign14Positive74.g06 p] := by
  rw [symState, symState6]
  rfl

theorem numState7 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 7 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v, (Sign14Positive74.g02 p).evalRing v, (Sign14Positive74.g03 p).evalRing v, (Sign14Positive74.g04 p).evalRing v, (Sign14Positive74.g05 p).evalRing v, (Sign14Positive74.g06 p).evalRing v] := by
  rw [numState, numState6]
  rfl

theorem symState8 (p : Fin 4 → ℤ) : symState p 8 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p, Sign14Positive74.g02 p, Sign14Positive74.g03 p, Sign14Positive74.g04 p, Sign14Positive74.g05 p, Sign14Positive74.g06 p, Sign14Positive74.g07 p] := by
  rw [symState, symState7]
  rfl

theorem numState8 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 8 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v, (Sign14Positive74.g02 p).evalRing v, (Sign14Positive74.g03 p).evalRing v, (Sign14Positive74.g04 p).evalRing v, (Sign14Positive74.g05 p).evalRing v, (Sign14Positive74.g06 p).evalRing v, (Sign14Positive74.g07 p).evalRing v] := by
  rw [numState, numState7]
  rfl

theorem symState9 (p : Fin 4 → ℤ) : symState p 9 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p, Sign14Positive74.g02 p, Sign14Positive74.g03 p, Sign14Positive74.g04 p, Sign14Positive74.g05 p, Sign14Positive74.g06 p, Sign14Positive74.g07 p, Sign14Positive74.g08 p] := by
  rw [symState, symState8]
  rfl

theorem numState9 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 9 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v, (Sign14Positive74.g02 p).evalRing v, (Sign14Positive74.g03 p).evalRing v, (Sign14Positive74.g04 p).evalRing v, (Sign14Positive74.g05 p).evalRing v, (Sign14Positive74.g06 p).evalRing v, (Sign14Positive74.g07 p).evalRing v, (Sign14Positive74.g08 p).evalRing v] := by
  rw [numState, numState8]
  rfl

theorem symState10 (p : Fin 4 → ℤ) : symState p 10 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p, Sign14Positive74.g02 p, Sign14Positive74.g03 p, Sign14Positive74.g04 p, Sign14Positive74.g05 p, Sign14Positive74.g06 p, Sign14Positive74.g07 p, Sign14Positive74.g08 p, Sign14Positive74.g09 p] := by
  rw [symState, symState9]
  rfl

theorem numState10 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 10 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v, (Sign14Positive74.g02 p).evalRing v, (Sign14Positive74.g03 p).evalRing v, (Sign14Positive74.g04 p).evalRing v, (Sign14Positive74.g05 p).evalRing v, (Sign14Positive74.g06 p).evalRing v, (Sign14Positive74.g07 p).evalRing v, (Sign14Positive74.g08 p).evalRing v, (Sign14Positive74.g09 p).evalRing v] := by
  rw [numState, numState9]
  rfl

theorem symState11 (p : Fin 4 → ℤ) : symState p 11 = [Sign14Positive74.g00 p, Sign14Positive74.g01 p, Sign14Positive74.g02 p, Sign14Positive74.g03 p, Sign14Positive74.g04 p, Sign14Positive74.g05 p, Sign14Positive74.g06 p, Sign14Positive74.g07 p, Sign14Positive74.g08 p, Sign14Positive74.g09 p, Sign14Positive74.g10 p] := by
  rw [symState, symState10]
  rfl

theorem numState11 {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) : numState p v 11 = [(Sign14Positive74.g00 p).evalRing v, (Sign14Positive74.g01 p).evalRing v, (Sign14Positive74.g02 p).evalRing v, (Sign14Positive74.g03 p).evalRing v, (Sign14Positive74.g04 p).evalRing v, (Sign14Positive74.g05 p).evalRing v, (Sign14Positive74.g06 p).evalRing v, (Sign14Positive74.g07 p).evalRing v, (Sign14Positive74.g08 p).evalRing v, (Sign14Positive74.g09 p).evalRing v, (Sign14Positive74.g10 p).evalRing v] := by
  rw [numState, numState10]
  rfl

end DiophantineConsistency.Sign14Positive74Circuit
#print axioms DiophantineConsistency.Sign14Positive74Circuit.symState11
#print axioms DiophantineConsistency.Sign14Positive74Circuit.numState11
