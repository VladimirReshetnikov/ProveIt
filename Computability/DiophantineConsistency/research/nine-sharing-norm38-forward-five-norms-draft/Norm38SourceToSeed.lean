import DiophantineConsistency.Norm38ForwardFiveNorms
import DiophantineConsistency.Norm38StaticToSeed
import FreshCarrierSpheres
import FreshModel106

/-! UNCOMPILED draft: a source-zero to seed-zero implication, conditional
on model-natural representatives and first-port positivity. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SourceToSeed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem source_zero_implies_seed_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V)
    (u : Fin 14 → V) (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hb : (0 : DiffRing V) < ((p 0 : ℤ) : DiffRing V))
    (hs : InternalZero (ObjectCurrentEquation2011.expressionAt p) (fun j => u j+1)) :
    InternalZero (SharingSeed38.seed p)
      (Fin.cons (1 : V) (SharingForward38.witnessCoordinates ports u)) := by
  have hvalue : Carrier65.value (fun j => ι (ports j)) (fun j => ι (u j+1)) = 0 := by
    rw [internalZero_iff, FreshModel106.evalRing_expressionAt65] at hs
    simpa only [hp] using hs
  have hbeta : (0 : DiffRing V) < ι (ports 0) := by simpa only [hp] using hb
  have hpositive : ∀ j, (0 : DiffRing V) < ι (u j+1) := fun j =>
    ι_pos (lt_of_lt_of_le _root_.zero_lt_one le_add_self)
  have hnorm := (FreshCarrierSpheres.value65_zero_iff_norms FreshCarrierSpheres.modelFacts
    (fun j => ι (ports j)) (fun j => ι (u j+1)) hbeta hpositive).mp hvalue
  exact Norm38Forward.static_implies_seed_zero p ports _ hp
    (Norm38ForwardGates.forward_gatesHold ι ports u)
    (Norm38ForwardFiveNorms.forward_fiveNorms ports u hnorm)
end DiophantineConsistency.Norm38SourceToSeed
#print axioms DiophantineConsistency.Norm38SourceToSeed.source_zero_implies_seed_zero
