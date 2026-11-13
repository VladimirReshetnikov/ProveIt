import DirectBFSHalt80Graph
import DirectBFS80ModelHalt
import CompactSymbolicBetaCast
import CompactSymbolicMaskData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFS80ForwardBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open CompactConstructedRank TenPositive80Graph DirectBFSFourFieldsPacking
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem forward (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) :
    (∃ v : Fin 10 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v) →
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) := by
  rintro ⟨v,hv,hz⟩
  exact DirectBFS80ModelHalt.graph_halts p v hp0 hp1 hp2 hp3 hv hz

#print axioms DirectBFS80ForwardBranch.forward
end DirectBFS80ForwardBranch
