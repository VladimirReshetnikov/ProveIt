import DiophantineConsistency.ArithmeticCommandReplacePerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandReplacePerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandReplacePerm222 ArithmeticCommandStepPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

example (rest w : V) : stepValue (replaceValue 0 rest) w=stepValue 0 w :=
  step_replace 0 rest w
example (c y x r rest : V) :
    first (second (replaceValue (cantor (c+3) (cantor y (cantor x r))) rest))=y ∧
    first (second (second (replaceValue (cantor (c+3) (cantor y (cantor x r))) rest)))=x := by
  simp only [replace_ax,second_cantor,first_cantor,and_self]
example (raw rest w : V) : stepValue (replaceValue raw rest) w=0 ↔ stepValue raw w=0 := by
  rw [step_replace]

#print axioms replace_defined
#print axioms replace_total
#print axioms replace_nip
#print axioms replace_drop
#print axioms replace_mp
#print axioms replace_ax
#print axioms first_replace
#print axioms tail_replace
#print axioms replace_twice
#print axioms replace_own_tail
#print axioms step_replace
#print axioms replace_pack_nat
#print axioms replace_nat
end DiophantineConsistency.ArithmeticCommandReplacePerm222Checks
