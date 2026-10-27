import DiophantineConsistency.ArithmeticEnumStepPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticEnumStepPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandFetchPerm222 ArithmeticCommandStepPerm222 ArithmeticEnumStepPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

example : enumValue (0 : V)=0 := enum_zero
example (s : V) : ∃! out, enumDef.val.Evalb ![out,s] := enum_total s

/-- Finished candidate: execute raw np and advance the candidate counter. -/
example (np w : V) : enumValue (liveValue 0 np w)=execValue np (np+1) w := by
  rw [enum_live, raw_new, next_new]

/-- Shifted raw zero: execute NIP without advancing the candidate counter. -/
example (np w : V) : enumValue (liveValue 1 np w)=execValue 0 np w := by
  have hf : first (fetchValue (1 : V) np)=0 := by
    simpa only [zero_add] using raw_continuation (0 : V) np
  have hn : second (fetchValue (1 : V) np)=np := by
    simpa only [zero_add] using next_continuation (0 : V) np
  rw [enum_live, hf, hn]

example (np t ws d : V) : enumValue (liveValue 1 np (stateValue t ws d 1))=0 := by
  have hz : first (0 : V)=0 := by
    have hc : cantor (0 : V) 0=0 := by simp [cantor, triangle]
    simpa only [hc] using first_cantor (0 : V) 0
  rw [enum_live_eq_zero_iff]
  simp [fetchValue, stateValue, hz]

example (s : EnumPerm.St) : enumValue (encodeState s)=
    encodeStateResult (EnumPerm.execAt (EnumPerm.fetch s).1 (EnumPerm.fetch s).2 s) :=
  enumValue_nat s

#print axioms live_defined
#print axioms exec_defined
#print axioms enum_defined
#print axioms enum_total
#print axioms enum_zero
#print axioms enum_live
#print axioms exec_eq_zero_iff
#print axioms enum_live_eq_zero_iff
#print axioms execValue_nat
#print axioms enumValue_nat
#print axioms enumValue_nat_eq_zero_iff
end DiophantineConsistency.ArithmeticEnumStepPerm222Checks
