import Direct80To90Output
import DirectMainHalt

/-! Symbolic-port positive 80 zero implies the internal machine halts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80SymbolicHaltForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactSymbolicModelIff
open TenPositive80Graph TenPositive80Factors TenPositive80To90Output
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_zero_implies_halt (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hports : integerPorts p=CompactSymbolicModelIff.p) :
    (∃ v : Fin 10 → V, (∀j,0<v j) ∧
      InternalZero (graph (integerPorts p)).output v) →
    (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) := by
  rintro ⟨v,hv,hz⟩
  obtain ⟨w,hw,hout⟩ := graph_exists_zero p v hp0 hp2 hp3 hv hz
  apply (DirectMainHalt.positive_model_iff (V:=V)).mp
  refine ⟨w,hw,?_⟩
  rw [hports] at hout
  exact hout

#print axioms TenPositive80SymbolicHaltForward.positive_zero_implies_halt
end TenPositive80SymbolicHaltForward
