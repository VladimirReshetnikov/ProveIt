import HaltReverseGraph
import Direct80SymbolicHaltForward
import CompactSymbolicBetaCast
import CompactSymbolicMaskData

/-! Two-way model-level machine/80-graph bridge for the symbolic ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Direct80SymbolicModelIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactConstructedRank TenPositive80Graph TenPositive80Factors
open TenPositive80SymbolicHaltForward TenPositiveHaltReverseGraph
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem symbolic_positive_model_iff (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hports : integerPorts p=CompactSymbolicModelIff.p)
    (hp1m : (p 1:V)=paramKernel rho) :
    (∃ v : Fin 10 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) := by
  have hp0m : (p 0:V)=Exp.exp (590069:V)-1 := by
    rw [hp0]
    exact CompactSymbolicBetaCast.beta_model
  have hp2m : (p 2:V)=low := by
    rw [hp2]
    exact CompactSymbolicMaskData.low_eq
  have hp3m : (p 3:V)=high+(Exp.exp (590069:V)-1) := by
    rw [hp3,Nat.cast_add,CompactSymbolicBetaCast.beta_model]
    have hh : (highNat:V)=high := CompactSymbolicMaskData.high_eq
    rw [hh]
    rw [add_comm]
  constructor
  · exact positive_zero_implies_halt p hp0 hp2 hp3 hports
  · rintro ⟨T,hT⟩
    exact halt_zero_of_model_ports p T hT hp0m hp1m hp2m hp3m

#print axioms Direct80SymbolicModelIff.symbolic_positive_model_iff
end Direct80SymbolicModelIff
