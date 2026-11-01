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

private theorem vector_first {A : Type*} (a b c d : A) :
    (![a,b,c,d] : Fin 4 → A) 0=a := by
  simp only [Matrix.cons_val_zero]
private theorem vector_third {A : Type*} (a b c d : A) :
    (![a,b,c,d] : Fin 4 → A) 2=c := by rfl
private theorem vector_fourth {A : Type*} (a b c d : A) :
    (![a,b,c,d] : Fin 4 → A) 3=d := by rfl

theorem port0_nat : currentPorts 0=CurrentMasks2011.beta := by
  simpa only [currentPorts] using
    vector_first CurrentMasks2011.beta CurrentKernel2011.K CurrentMasks2011.lowPort
      (CurrentMasks2011.highPort+CurrentMasks2011.beta)
theorem port2_nat : currentPorts 2=CurrentMasks2011.lowPort := by
  simpa only [currentPorts] using
    vector_third CurrentMasks2011.beta CurrentKernel2011.K CurrentMasks2011.lowPort
      (CurrentMasks2011.highPort+CurrentMasks2011.beta)
theorem port3_nat : currentPorts 3=CurrentMasks2011.highPort+CurrentMasks2011.beta := by
  simpa only [currentPorts] using
    vector_fourth CurrentMasks2011.beta CurrentKernel2011.K CurrentMasks2011.lowPort
      (CurrentMasks2011.highPort+CurrentMasks2011.beta)

theorem port1_nat : currentPorts 1=CurrentKernel2011.K := by
  simpa only [currentPorts] using
    vector_second CurrentMasks2011.beta CurrentKernel2011.K CurrentMasks2011.lowPort
      (CurrentMasks2011.highPort+CurrentMasks2011.beta)

theorem port0_cast : (currentPorts 0:V)=(CurrentMasks2011.beta:V) :=
  congrArg (fun n : ℕ => (n:V)) port0_nat
theorem port2_cast : (currentPorts 2:V)=(CurrentMasks2011.lowPort:V) :=
  congrArg (fun n : ℕ => (n:V)) port2_nat
theorem port3_cast : (currentPorts 3:V)=((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) :=
  congrArg (fun n : ℕ => (n:V)) port3_nat
theorem port1_cast : (currentPorts 1:V)=(CurrentKernel2011.K:V) :=
  congrArg (fun n : ℕ => (n:V)) port1_nat
end DiophantineConsistency.ArithmeticAdaptivePortValues2011
