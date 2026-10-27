import DiophantineConsistency.ArithmeticProofWordEnumPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticProofWordEnumPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCommandStepPerm222 ArithmeticCommandRunPerm222 ArithmeticProofWordEnumPerm222

-- The reset theorem includes false1 in the initial cache and an arbitrary counter.
example {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (rest t S d : V)
    (h : ∀ top stack, evalValue rest (stateValue top stack 0 0)=0) :
    evalValue (resetWord rest) (stateValue t S d 1)=0 := resetWord_halts rest h _

-- The public scheduler client supplies only actual refutation acceptance.
example {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (code initialWork : V)
    (h : ArithmeticHistory222.checkDef.val.Evalb ![code,1]) :
    ∃ time, ArithmeticEnumRunPerm222.run time
      (ArithmeticEnumStepPerm222.liveValue 0 4 initialWork)=0 :=
  enum_halts_of_refutation code initialWork h

example : 𝗜𝚺₁ ⊢ refutationHaltingSentence := isigma1_proves_refutation_halting
example : Peano ⊢ refutationHaltingSentence := peano_proves_refutation_halting

#print axioms state_decode
#print axioms resetWord_ne_zero
#print axioms resetWord_candidate
#print axioms resetWord_halts
#print axioms enum_halts_of_refutation
#print axioms refutationHaltingSentence_true
#print axioms isigma1_proves_refutation_halting
#print axioms peano_proves_refutation_halting
end DiophantineConsistency.ArithmeticProofWordEnumPerm222Checks
