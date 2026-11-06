import DiophantineConsistency.SharingForward33
import DiophantineConsistency.Sign33ResidualAssembly

/-! First three positive cut equations for the candidate forward constructor. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardGroup00
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def condition (ports : Fin 4 → V) (v : Fin 34 → V) : Prop :=
  ι (v 15) = Sign33ResidualBatch00.q (ports 0) v*Sign33ResidualBatch00.q (ports 0) v ∧
  ι (v 16) = ι (v 15)*Sign33ResidualBatch00.q (ports 0) v ∧
  ι (v 17) = (ι (v 9)+1)*Sign33ResidualBatch00.q (ports 0) v

theorem constructor_cuts (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V) :
    condition ports (Fin.cons (1 : V)
      (SharingForward33.witnessCoordinates ports u gap tau inner value negative)) := by
  let w := SharingForward33.witnessCoordinates ports u gap tau inner value negative
  change condition ports (Fin.cons (1 : V) w)
  have h1 : (Fin.cons (1 : V) w : Fin 34 → V) 1 = w 0 := by
    have hindex : (0 : Fin 33).succ = (1 : Fin 34) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 34 => V) (1 : V) w (0 : Fin 33)
  have h9 : (Fin.cons (1 : V) w : Fin 34 → V) 9 = w 8 := by
    have hindex : (8 : Fin 33).succ = (9 : Fin 34) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 34 => V) (1 : V) w (8 : Fin 33)
  have h15 : (Fin.cons (1 : V) w : Fin 34 → V) 15 = w 14 := by
    have hindex : (14 : Fin 33).succ = (15 : Fin 34) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 34 => V) (1 : V) w (14 : Fin 33)
  have h16 : (Fin.cons (1 : V) w : Fin 34 → V) 16 = w 15 := by
    have hindex : (15 : Fin 33).succ = (16 : Fin 34) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 34 => V) (1 : V) w (15 : Fin 33)
  have h17 : (Fin.cons (1 : V) w : Fin 34 → V) 17 = w 16 := by
    have hindex : (16 : Fin 33).succ = (17 : Fin 34) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 34 => V) (1 : V) w (16 : Fin 33)
  simp [condition, Sign33ResidualBatch00.q, h1, h9, h15, h16, h17,
    w, SharingForward33.witnessCoordinates, SharingForward38.witnessCoordinates,
    map_add, map_mul]
end DiophantineConsistency.Sign33ForwardGroup00
#print axioms DiophantineConsistency.Sign33ForwardGroup00.constructor_cuts
