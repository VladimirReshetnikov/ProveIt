import DiophantineConsistency.ArithmeticCheckerMachine215

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCheckerMachine215Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticCheckerMachine215

example : checkerMachineSentence =
    ( “(∃ code, !ArithmeticHistory222.checkDef code 1) ↔
      !ArithmeticMachineRun215.haltingSentence” : ArithmeticSentence) := rfl

example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ArithmeticMachineRun215.haltingSentence.val.Evalb (M:=V) ![] ↔
      ∃ time : V, first (ArithmeticMachineRun215.run time)=0 := haltingSentence_iff

section TypeZero
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (proof : V) (h : ArithmeticHistory222.checkDef.val.Evalb ![proof,1]) :
    ∃ time : V, first (ArithmeticMachineRun215.run time)=0 :=
  refutation_iff_blank_halts.mp ⟨proof,h⟩
example (time : V) (h : first (ArithmeticMachineRun215.run time)=0) :
    ∃ proof : V, ArithmeticHistory222.checkDef.val.Evalb ![proof,1] :=
  refutation_iff_blank_halts.mpr ⟨time,h⟩
example : checkerMachineSentence.Evalb (M:=V) ![] := checkerMachineSentence_true
example : (¬∃ proof : V, ArithmeticHistory222.checkDef.val.Evalb ![proof,1]) ↔
    ¬ArithmeticMachineRun215.haltingSentence.val.Evalb (M:=V) ![] :=
  not_congr refutation_iff_haltingSentence
end TypeZero

example : 𝗜𝚺₁ ⊢ checkerMachineSentence := isigma1_proves_checker_machine
example : Peano ⊢ checkerMachineSentence := peano_proves_checker_machine

#print axioms haltingSentence_iff
#print axioms refutation_iff_blank_halts
#print axioms refutation_iff_haltingSentence
#print axioms checkerMachineSentence_true
#print axioms isigma1_proves_checker_machine
#print axioms peano_proves_checker_machine
end DiophantineConsistency.ArithmeticCheckerMachine215Checks
