import DiophantineConsistency.ForwardWitness38

/-! Candidate 33-witness constructor with five supplied natural representatives. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingForward33

/-- The positive cuts are reused from the 38-witness constructor; the five
signed cuts are supplied as model-natural representatives. -/
def witnessCoordinates {S : Type*} [CommSemiring S] (ports : Fin 4 → S)
    (u : Fin 14 → S) (gap tau inner value negative : S) : Fin 33 → S :=
  let w := SharingForward38.witnessCoordinates ports u
  ![u 0, u 1, u 2, u 3, u 4, u 5, u 6, u 7, u 8, u 9, u 10, u 11, u 12, u 13, w 14, w 15, w 16, w 17, w 18, w 19, w 20, w 21, w 22, w 23, w 24, gap, tau, w 29, inner, value, w 34, w 35, negative]

theorem witness_inputs {S : Type*} [CommSemiring S] (ports : Fin 4 → S)
    (u : Fin 14 → S) (gap tau inner value negative : S) (i : Fin 14) :
    witnessCoordinates ports u gap tau inner value negative
      (Fin.castLE (by decide : 14 ≤ 33) i) = u i := by
  fin_cases i <;> rfl

theorem witness_signed {S : Type*} [CommSemiring S] (ports : Fin 4 → S)
    (u : Fin 14 → S) (gap tau inner value negative : S) :
    witnessCoordinates ports u gap tau inner value negative 25 = gap ∧
    witnessCoordinates ports u gap tau inner value negative 26 = tau ∧
    witnessCoordinates ports u gap tau inner value negative 28 = inner ∧
    witnessCoordinates ports u gap tau inner value negative 29 = value ∧
    witnessCoordinates ports u gap tau inner value negative 32 = negative := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
end DiophantineConsistency.SharingForward33
#print axioms DiophantineConsistency.SharingForward33.witness_inputs
#print axioms DiophantineConsistency.SharingForward33.witness_signed
