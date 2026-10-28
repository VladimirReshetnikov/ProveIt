import DiophantineConsistency.ArithmeticRuntime215

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticRuntime215Checks
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlFile ArithmeticControlTable ArithmeticControl215Table
open ArithmeticMachineTape215 ArithmeticControlFrame215 ArithmeticRuntime215

example : seedEntryValue (0:Nat)=bootCode := standard_seed_entry
example : KBoot215.bootVs=[0,0,0,0,0,0,4,0,0]++List.replicate 40 1 := rfl
example : KBoot215.bootRight=List.replicate 65 false++true::KRuntimeCore.sepsR KBoot215.bootVs := rfl

variable {V:Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example : 𝚺₁-Relation[V] Related via relatedDef := related_defined
example : 𝚺₁-Function₁[V] seedEntryValue via seedEntryDef := seedEntry_defined
example : regValue (seedFile:V) (6:Fin 9)=4 := by rw [seed_registers]; rfl
example (b:V) : ¬Related (liveValue (0:V) 0) b := by
  intro hr
  obtain ⟨i,hi⟩:=related_supported hr
  rw [control_live] at hi
  exact (ne_of_gt (show (0:V)<(number i:V) by simp [number])) hi.symm
example (i:Control) (f k:V) (hk:0<k) :
    (∃ n:V,run215 n (liveValue (number i:V) f)=0) ↔
      ∃ t:V,first (runFrom t (entryValue (number i:V) f k 0))=0 := canonical_halts_iff i f k 0 hk
example (b t:V) (h:first b=0) : runFrom t b=b := halt_absorbs b t h
example : Related (liveValue (1:V) seedFile) (bootCode:V) := seed_related
example : entryValue (1:V) seedFile 40 1=(bootCode:V) := seed_entry
example : ArithmeticMachineRun215.run (95714:V)=(bootCode:V) := internal_boot
example (t:V) : ArithmeticMachineRun215.run (95714+t)=runFrom t (bootCode:V) := continuation t
example (n:V) (h:ArithmeticEnumRunPerm222.run n (ArithmeticEnumStepPerm222.liveValue 0 4 0)=0) :
    ∃ t:V,first (ArithmeticMachineRun215.run t)=0 := enum_blank_halts_iff.mp ⟨n,h⟩
example (t:V) (h:first (ArithmeticMachineRun215.run t)=0) :
    ∃ n:V,ArithmeticEnumRunPerm222.run n (ArithmeticEnumStepPerm222.liveValue 0 4 0)=0 :=
  enum_blank_halts_iff.mpr ⟨t,h⟩

#print axioms related_defined
#print axioms related_live
#print axioms related_active
#print axioms related_supported
#print axioms related_step
#print axioms related_halt_pos
#print axioms halt_absorbs
#print axioms control_tape_halts_iff
#print axioms canonical_halts_iff
#print axioms seedEntry_defined
#print axioms standard_seed_entry
#print axioms seed_entry
#print axioms seed_related
#print axioms control_blank_halts_iff
#print axioms enum_blank_halts_iff
end DiophantineConsistency.ArithmeticRuntime215Checks
