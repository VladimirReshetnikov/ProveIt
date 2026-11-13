import DirectBFSHalt80Graph
import DirectBFS80ModelHalt
import CompactSymbolicBetaCast
import CompactSymbolicMaskData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace DirectBFS80ModelIffFullPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel
open CompactConstructedRank TenPositive80Graph DirectBFSFourFieldsPacking
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] DirectBFSFourFieldsPacking.kernel rho DirectBFSSymbolicKernel.paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_model_iff (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=DirectBFSSymbolicKernel.paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hp0m : (p 0:V)=Exp.exp (590069:V)-1) (hp1m : (p 1:V)=(kernel:V))
    (hp2m : (p 2:V)=low) (hp3m : (p 3:V)=high+(Exp.exp (590069:V)-1)) :
    (∃ v : Fin 10 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) := by
  constructor
  · rintro ⟨v,hv,hz⟩
    exact DirectBFS80ModelHalt.graph_halts p v hp0 hp1 hp2 hp3 hv hz
  · rintro ⟨T,hT⟩
    exact DirectBFSHalt80Graph.halt_zero_of_model_ports p T hT hp0m hp1m hp2m hp3m
#print axioms DirectBFS80ModelIffFullPorts.positive_model_iff
end DirectBFS80ModelIffFullPorts
