import DiophantineConsistency.Carrier65

/-! Proposed algebraic ingredient toward the degree bound, not a degree theorem. -/
namespace DiophantineConsistency.Current14Carrier65QCancel

theorem generic {R : Type*} [CommRing R] (X a c H g : R) :
    (X + a * c + g * H) ^ 2 - (a ^ 2 + H) * c ^ 2 =
      (X + g * H) ^ 2 + 2 * a * c * (X + g * H) - H * c ^ 2 := by
  ring

theorem current_core {R : Type*} [CommRing R]
    (p : Fin 4 → R) (v : Fin 14 → R) :
    let d := Carrier65.core p v
    d.Q = (d.X + v 13 * d.H) ^ 2 +
      2 * d.a * d.c * (d.X + v 13 * d.H) - d.H * d.c ^ 2 := by
  let d := Carrier65.core p v
  change d.Q = (d.X + v 13 * d.H) ^ 2 +
      2 * d.a * d.c * (d.X + v 13 * d.H) - d.H * d.c ^ 2
  have hQ : d.Q = d.D ^ 2 - d.delta * d.c ^ 2 := by rfl
  have hD : d.D = d.X + d.a * d.c + v 13 * d.H := by rfl
  have hdelta : d.delta = d.a ^ 2 + d.H := by rfl
  rw [hQ, hD, hdelta]
  exact generic d.X d.a d.c d.H (v 13)

end DiophantineConsistency.Current14Carrier65QCancel

#print axioms DiophantineConsistency.Current14Carrier65QCancel.generic
#print axioms DiophantineConsistency.Current14Carrier65QCancel.current_core
