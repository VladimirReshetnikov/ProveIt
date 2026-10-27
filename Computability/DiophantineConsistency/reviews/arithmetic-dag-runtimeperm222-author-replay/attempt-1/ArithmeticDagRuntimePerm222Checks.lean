import BusyBeaver.ZFC.ArithmeticDagRuntimePerm222

set_option autoImplicit false
set_option Elab.async false
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagRuntimePerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticDagRuntimePerm222 ArithmeticDagMacrosPerm222 ArithmeticDagRootPerm222
open DiophantineConsistency
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : 𝚺₁-Relation[V] Related via relatedDef := related_defined
example (pl np t S d h : V) :
    Related (ArithmeticEnumStepPerm222.liveValue pl np
      (ArithmeticCommandStepPerm222.stateValue t S d h)) (controlOf pl np t S d h) :=
  ⟨pl,np,t,S,d,h,rfl,rfl⟩
example (pl np t S d h : V) :
    ArithmeticControlFile.regValue (enc (boundary pl np t S d h)) 1 = pl := by
  simp only [enc_boundary, ArithmeticControlFile.reg_file]
example : ArithmeticControlFile.regValue (enc (boundary (0 : V) 4 0 0 0 0)) 6 = 4 := by
  simp only [enc_boundary, ArithmeticControlFile.reg_file]
example (l c : V) (hr : Related l c) (hn : ArithmeticEnumStepPerm222.enumValue l ≠ 0) :
    ∃ k, 0 < k ∧ Related (ArithmeticEnumStepPerm222.enumValue l)
      (ArithmeticDagControlPerm222.run k c) := related_step l c hr hn
example (l c : V) (hr : Related l c) (hz : ArithmeticEnumStepPerm222.enumValue l = 0) :
    ∃ k, 0 < k ∧ ArithmeticDagControlPerm222.run k c = 0 := related_halt_pos l c hr hz
example (k : V) : ArithmeticDagControlPerm222.run k 0 = 0 :=
  ArithmeticDagControlPerm222.run_halted k
example (q f : V) : ArithmeticControlFile.liveValue q f ≠ 0 :=
  ArithmeticControlFile.live_ne_zero q f
example :
    (∃ n : V, ArithmeticEnumRunPerm222.run n (ArithmeticEnumStepPerm222.liveValue 0 4 0) = 0) ↔
    (∃ k : V, ArithmeticDagControlPerm222.run k (ArithmeticControlFile.liveValue 1
      (ArithmeticControlFile.fileValue ![0,0,0,0,0,0,4,0,0])) = 0) := seed_halts_iff

#print axioms related_defined
#print axioms related_definable
#print axioms related_live
#print axioms related_active
#print axioms boundary_ne_of_progress
#print axioms related_step
#print axioms related_halt
#print axioms related_halt_pos
#print axioms halts_iff
#print axioms seed_record
#print axioms seed_halts_iff

end SetTheory.BusyBeaver.ZFC.ArithmeticDagRuntimePerm222Checks
