import Direct80SymbolicModelIff

/-! Derive symbolic tuple assumptions through a generic four-port lemma. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Direct80SymbolicPortProjection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts CompactSymbolicKernel CompactSymbolicKernelOpaque
open TenPositive80Graph TenPositive80Factors
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem generic_ports (p : Fin 4 → ℕ) (beta kernel lo hi : ℕ)
    (h0 : p 0=beta) (h1 : p 1=kernel) (h2 : p 2=lo) (h3 : p 3=beta+hi) :
    p=ports beta kernel lo hi := by
  funext j
  fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem symbolic_iff_of_four_ports (p : Fin 4 → ℕ)
    (hp0 : p 0=betaNat) (hp1 : p 1=paramKernel rho)
    (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat) :
    (∃ v : Fin 10 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) := by
  have ht := generic_ports p betaNat (paramKernel rho) lowNat highNat hp0 hp1 hp2 hp3
  have hports : integerPorts p=CompactSymbolicModelIff.p := by
    change (fun j => ((p j:ℕ):ℤ)) =
      (fun j => ((ports betaNat (paramKernel rho) lowNat highNat j:ℕ):ℤ))
    exact congrArg (fun f : Fin 4 → ℕ => fun j => ((f j:ℕ):ℤ)) ht
  have h1 : (p 1:V)=paramKernel rho := congrArg (fun x : ℕ => (x:V)) hp1
  exact Direct80SymbolicModelIff.symbolic_positive_model_iff p hp0 hp2 hp3 hports h1

#print axioms Direct80SymbolicPortProjection.generic_ports
#print axioms Direct80SymbolicPortProjection.symbolic_iff_of_four_ports
end Direct80SymbolicPortProjection
