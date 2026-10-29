import DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePortValues2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem vector_second {A : Type*} (a b c d : A) :
    (![a,b,c,d] : Fin 4 → A) 1=b := by
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero]

theorem port1_nat : currentPorts 1=CurrentKernel2011.K := by
  simpa only [currentPorts] using
    vector_second CurrentMasks2011.beta CurrentKernel2011.K CurrentMasks2011.lowPort
      (CurrentMasks2011.highPort+CurrentMasks2011.beta)

theorem port1_cast : (currentPorts 1:V)=(CurrentKernel2011.K:V) :=
  congrArg (fun n : ℕ => (n:V)) port1_nat
end DiophantineConsistency.ArithmeticAdaptivePortValues2011
