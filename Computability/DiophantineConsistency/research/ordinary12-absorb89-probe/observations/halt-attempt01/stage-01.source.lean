import Absorb89Equivalence
import DirectMainHalt

/-! Fixed-port all-model halt comparison for the absorbed graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Absorb89Halt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb89
open AdaptiveEquationSyntax2011 Ordinary12FreeJ
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactSymbolicModelIff CompactBytePortsModelIff FreeJQCube92Halt
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_model_iff :
    (∃ v : Fin 12 → V, (∀ j,0<v j) ∧ InternalZero (graph p).output v) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  have hbounds := CompactFixedBeta.bounds (1:V) (by simp)
  have hp := DirectPortBounds.bounds CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat
    hbounds.1 hbounds.2.1 hbounds.2.2.1
  have h := Absorb89Equivalence.positive_zero_iff naturalPorts hp.1 hp.2.1 hp.2.2
  change (∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (graph p).output v) ↔
    (∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (FreeJDirectMainGraph.graph p).output v) at h
  exact h.trans (DirectMainHalt.positive_model_iff (V:=V))

theorem shifted_model_iff :
    (∃ x : Fin 12 → V, InternalZero (positiveShift (graph p).output) x) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  constructor
  · rintro ⟨x,hx⟩
    apply (positive_model_iff (V:=V)).mp
    refine ⟨fun j => x j+1, ?_, ?_⟩
    · intro j; simp
    · exact (internalZero_positiveShift _ x).mp hx
  · intro hh
    obtain ⟨v,hpos,hzero⟩ := (positive_model_iff (V:=V)).mpr hh
    let x : Fin 12 → V := fun j => v j-1
    have hx : (fun j => x j+1)=v := by
      funext j
      exact tsub_add_cancel_of_le (pos_iff_one_le.mp (hpos j))
    refine ⟨x,?_⟩
    rw [internalZero_positiveShift, hx]
    exact hzero

theorem shifted_byte_model_iff :
    (∃ x : Fin 12 → V, InternalZero (positiveShift (graph byteP).output) x) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0) := by
  rw [byteP_eq]
  exact shifted_model_iff (V:=V)

#print axioms Absorb89Halt.positive_model_iff
#print axioms Absorb89Halt.shifted_model_iff
#print axioms Absorb89Halt.shifted_byte_model_iff
end Absorb89Halt
