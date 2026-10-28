import DiophantineConsistency.ArithmeticMachineTape215

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticMachineTape215Checks
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticMachineTape215
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : sparseCode 0=1 ∧ sparseCode 84=24 ∧ sparseCode 230=0 :=
  ⟨sparseCode_initial,sparseCode_dispatch,sparseCode_terminal⟩

/-- An absent hole also has code0; it is not identified with physical halt. -/
example : sparseCode 79=0 ∧ (79:Nat)≠230 := by
  constructor
  · rw [sparseCode,decode_hole]; rfl
  · decide

example (left right : V) (hr : right%2=0) :
    ArithmeticMachineStep215.stepValue (frameSparse 0 left right)=
      frameSparse 94 (2*left+1) (right/2) := by
  have h : KTableCore.tm215 0 false=some (true,true,94) := by decide +kernel
  simpa only [Bool.toNat_false,Bool.toNat_true,Nat.cast_zero,Nat.cast_one,if_true]
    using sparse_step h left right hr

example {q : Nat} {bit write move : Bool}
    (h : KTableCore.tm215 q bit=some (write,move,230)) (l r : V)
    (hr : r%2=(bit.toNat:V)) :
    first (ArithmeticMachineStep215.stepValue (frameSparse q l r))=0 := by
  rw [sparse_step h l r hr]
  cases move <;> simp [frameSparse,sparseCode_terminal]

example (t initial : V) : ∃! out, runFromDef.val.Evalb ![out,t,initial] := runFrom_total t initial
example (t : V) : ArithmeticMachineRun215.run (95714+t)=runFrom t (bootCode:V) := continuation t
example : ArithmeticMachineRun215.run (95714:V)=(bootCode:V) := internal_boot
example : first (bootCode:V)=24 := bootCode_state
example : (∃ t : V, first (ArithmeticMachineRun215.run t)=0) ↔
    ∃ t : V, first (runFrom t (bootCode:V))=0 := blank_halts_iff_boot

#print axioms decode_expansion
#print axioms actual_row
#print axioms sparse_step
#print axioms runFrom_defined
#print axioms runFrom_defined_delta
#print axioms runFrom_add
#print axioms runFrom_halted
#print axioms runFrom_blank
#print axioms standard_boot
#print axioms internal_boot
#print axioms bootCode_state
#print axioms continuation
#print axioms blank_halts_iff_boot
end DiophantineConsistency.ArithmeticMachineTape215Checks
