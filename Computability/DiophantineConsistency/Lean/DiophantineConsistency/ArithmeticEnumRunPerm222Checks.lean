import DiophantineConsistency.ArithmeticEnumRunPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticEnumRunPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticEnumStepPerm222 ArithmeticEnumRunPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (time initial : V) : ∃! out, runDef.val.Evalb ![out,time,initial] :=
  run_total time initial
example (time : V) : run time 0 = 0 := run_halted time
example (time initial : V) : run (time+1) initial = run time (enumValue initial) :=
  run_succ_first time initial
example (time : ℕ) (s : EnumPerm.St) : run time (encodeState s)=0 ↔
    EnumPerm.run time s=none := run_zero_iff_native_none time s
example (s : EnumPerm.St) : run (0 : ℕ) (encodeState s)=encodeState s := run_zero _

#print axioms run_defined
#print axioms run_defined_delta
#print axioms run_zero
#print axioms run_succ
#print axioms run_halted
#print axioms run_add
#print axioms run_one
#print axioms run_total
#print axioms run_succ_first
#print axioms encodeStateResult_eq_zero
#print axioms run_encode_nat
#print axioms runDef_encode_nat
#print axioms run_zero_iff_native_none
end DiophantineConsistency.ArithmeticEnumRunPerm222Checks
