import DiophantineConsistency.ArithmeticControlFrame215

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticControlFrame215Checks
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlFile ArithmeticControlTable ArithmeticControl215Table
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215 ArithmeticControlFrame215

example : entries.length=4751 := entries_length
example : rows215 0=none := by rfl
example : rows215 4752=none := by rfl
private theorem first_source : source (0:Control)=([false,false,false],.decnz 8) := by decide +kernel
example : physical (0:Control)=(1:Fin 9) := by
  apply Fin.ext
  simp only [physical,first_source,registerOf,Permutation252Frame.physOf]
example : padded [true,false,false] 4=padded [true] 4 := rfl
example : padded [] 4=padded [false,false,false] 4 := rfl
example : ∀ r:Fin 9,Permutation252Frame.physOf r.val=KSim.physOf r.val := physical_map

variable {V:Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example : 𝚺₁-Function₄[V] entryValue via entryDef := entry_defined
example : 𝚫₁-Function₄[V] entryValue := entry_delta
example : 𝚺₁-Function₂[V] (blocksValue (List.finRange 9)) via blocksDef (List.finRange 9) := blocks_defined _
example : spareValue (0:V)=0 := by rw [spareValue,repeat3_zero]
example (q f k gap:V) : first (entryValue q f k gap)=(24:V) := entry_active _ _ _ _
example (q:V) (h:∀ i:Control,q≠(number i:V)) : opcodeValue table215 q=0 := by
  by_contra hn
  obtain ⟨i,hi⟩:=opcode_supported q hn
  exact h i hi
example (f k gap:V) (hk:0<k) (hz:regValue f (physical (0:Control))=0) :
    ReachPos (entryValue (1:V) f k gap)
      (entryValue (nextControl (0:Control) false:V) f k
        (gap+digit (KSim.allOnes (RegisterPath.stripPath false 1 (source (0:Control)).1)))) :=
  entry_decnz_zero 0 8 (congrArg Prod.snd first_source) f k gap hk hz
example (f:V) (hz:regValue f (physical (0:Control))=0) :
    ReachPos (entryValue (1:V) f 1 0)
      (entryValue (nextControl (0:Control) false:V) f 1
        (digit (KSim.allOnes (RegisterPath.stripPath false 1 (source (0:Control)).1)))) := by
  simpa only [zero_add] using entry_decnz_zero 0 8 (congrArg Prod.snd first_source) f (1:V) 0 (by simp) hz
example (i:Control) (f k gap:V) (hk:0<k)
    (hz:stepValue table215 (liveValue (number i:V) f)=0) :
    ∃ t:V,0<t ∧ first (runFrom t (entryValue (number i:V) f k gap))=0 := entry_halt i f k gap hk hz

#print axioms entries_length
#print axioms rows_at
#print axioms resolve_source
#print axioms physical_map
#print axioms pc_defined
#print axioms blocks_defined
#print axioms spare_defined
#print axioms entry_defined
#print axioms opcode_supported
#print axioms resolved_padded
#print axioms target_entry
#print axioms step_at
#print axioms entry_inc
#print axioms entry_decnz_zero
#print axioms entry_decnz_positive
#print axioms entry_break
#print axioms entry_continue
#print axioms entry_source_halt
#print axioms entry_step
#print axioms entry_halt
end DiophantineConsistency.ArithmeticControlFrame215Checks
