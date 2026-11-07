import DiophantineConsistency.Sign33ForwardNormStrong38
import DiophantineConsistency.SharingForward33

/-! Shared positive coordinates give the 33-constructor scaled strong field. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33ForwardNormStrong
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem norm_strong_of_core (ports : Fin 4 → V) (u : Fin 14 → V)
    (gap tau inner value negative : V)
    (hs : let d := Carrier65.core (fun j => ι (ports j)) (fun j => ι (u j+1))
      Carrier65.strong d = 1) :
    let v : Fin 34 → V := Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative)
    ι (v 22)*ι (v 28)-ι (v 32) = ι (v 22) := by
  have ht := Sign33ForwardNormStrong38.strong_terminal ports u hs
  simp [NormAssignment38.assignment, pairValue, pairCompute, map_add, map_mul] at ht
  have h22 : (Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative) : Fin 34 → V) 22 = SharingForward38.witnessCoordinates ports u 21 := by
    have hindex : (21 : Fin 33).succ = (22 : Fin 34) := by decide
    rw [←hindex, Fin.cons_succ]
    rfl
  have h28 : (Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative) : Fin 34 → V) 28 = SharingForward38.witnessCoordinates ports u 29 := by
    have hindex : (27 : Fin 33).succ = (28 : Fin 34) := by decide
    rw [←hindex, Fin.cons_succ]
    rfl
  have h32 : (Fin.cons (1 : V) (SharingForward33.witnessCoordinates ports u gap tau inner value negative) : Fin 34 → V) 32 = SharingForward38.witnessCoordinates ports u 35 := by
    have hindex : (31 : Fin 33).succ = (32 : Fin 34) := by decide
    rw [←hindex, Fin.cons_succ]
    rfl
  dsimp only
  rw [h22, h28, h32]
  exact ht
end DiophantineConsistency.Sign33ForwardNormStrong
#print axioms DiophantineConsistency.Sign33ForwardNormStrong.norm_strong_of_core
