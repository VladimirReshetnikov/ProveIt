import DiophantineConsistency.ArithmeticControlFrame215
import BusyBeaver.ZFC.ArithmeticControlBisimPerm215
import BusyBeaver.ZFC.ArithmeticDagRuntimePerm222

/-! Actual internal scheduler/decimal215 halting equivalence. The supported
canonical relation, positive site clocks, full halt absorption and exact boot
entry discharge every generic transport premise. No source consistency,
external Nat runtime equivalence or polynomial/HA endpoint is assumed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticRuntime215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlFile ArithmeticControlTable ArithmeticControl215Table
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215 ArithmeticSymbolicCore215
open ArithmeticControlFrame215
open ArithmeticMachinePerm252 (bitsCode)

/-- Fixed syntax retains actual control support, rather than scalar liveness alone. -/
def relatedDef : 𝚺₁.Semisentence 2 := .mkSigma
  “l b. ∃ q, ∃ f, ∃ k, ∃ gap, 0<k ∧
    (∃ op, !(opcodeDef table215) op q ∧ op≠0) ∧
    !liveDef l q f ∧ !entryDef b q f k gap”
/-- One ignored parameter permits the same fixed function graph in every model. -/
def seedEntryDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out ignored. ∃ f, !fileDef f 0 0 0 0 0 0 4 0 0 ∧ !entryDef out 1 f 40 1”

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Related (l b : V) : Prop := ∃ q f k gap : V,
  0<k ∧ opcodeValue table215 q≠0 ∧ l=liveValue q f ∧ b=entryValue q f k gap
instance related_defined : 𝚺₁-Relation[V] Related via relatedDef :=
  .mk fun e => by simp [relatedDef,Related,(opcode_defined table215).iff]
instance related_definable : 𝚺₁-Relation[V] Related := related_defined.to_definable

theorem related_live {l b : V} (hr : Related l b) : l≠0 := by
  obtain ⟨q,f,k,gap,_,_,rfl,_⟩:=hr
  exact live_ne_zero q f
theorem related_active {l b : V} (hr : Related l b) : first b≠0 := by
  obtain ⟨q,f,k,gap,_,_,_,rfl⟩:=hr
  rw [entry_active]
  simp
theorem related_supported {l b : V} (hr : Related l b) :
    ∃ i:Control,controlValue l=(number i:V) := by
  obtain ⟨q,f,k,gap,_,hq,rfl,_⟩:=hr
  simpa only [control_live] using opcode_supported q hq

/-- Canonical source execution derives both the valid successor and its positive clock. -/
theorem related_step (l b : V) (hr : Related l b) (hn : stepValue table215 l≠0) :
    ∃ t:V,0<t ∧ Related (stepValue table215 l) (runFrom t b) := by
  obtain ⟨q,f,k,gap,hk,hq,rfl,rfl⟩:=hr
  obtain ⟨i,rfl⟩:=opcode_supported q hq
  obtain ⟨j,f',k',gap',hk',hs,t,ht,hb⟩:=entry_step i f k gap hk hn
  exact ⟨t,ht,(number j:V),f',k',gap',hk',opcode_nonzero j,hs,hb⟩
theorem related_halt_pos (l b : V) (hr : Related l b) (hz : stepValue table215 l=0) :
    ∃ t:V,0<t ∧ first (runFrom t b)=0 := by
  obtain ⟨q,f,k,gap,hk,hq,rfl,rfl⟩:=hr
  obtain ⟨i,rfl⟩:=opcode_supported q hq
  exact entry_halt i f k gap hk hz
theorem related_halt (l b : V) (hr : Related l b) (hz : stepValue table215 l=0) :
    ∃ t:V,first (runFrom t b)=0 := by
  obtain ⟨t,_,ht⟩:=related_halt_pos l b hr hz
  exact ⟨t,ht⟩
/-- The complete terminal payload is fixed, not replaced by scalar configuration zero. -/
theorem halt_absorbs (b t : V) (hb : first b=0) : runFrom t b=b := runFrom_halted t b hb

/-- No upper clock bound: the generic transport uses its genuine Sigma1 clock invariant. -/
theorem control_tape_halts_iff (q f k gap : V) (hq : opcodeValue table215 q≠0) (hk : 0<k) :
    (∃ n:V,run215 n (liveValue q f)=0) ↔
      ∃ t:V,first (runFrom t (entryValue q f k gap))=0 := by
  haveI : 𝚺₁-Function₁[V] (fun n => run215 n (liveValue q f)) := by definability
  apply ArithmeticPositiveSimulation254.halts_iff
    (stepValue table215) (fun n => run215 n (liveValue q f)) runFrom Related (fun b => first b=0)
    (liveValue q f) (entryValue q f k gap)
  · exact run215_zero _
  · intro n; exact controlRun_succ table215 n _
  · exact runFrom_zero
  · exact runFrom_add
  · exact ⟨q,f,k,gap,hk,hq,rfl,rfl⟩
  · intro l b hr; exact related_live hr
  · intro l b hr; exact related_active hr
  · exact related_step
  · exact related_halt
  · intro b hb t
    rwa [halt_absorbs b t hb]

theorem canonical_halts_iff (i : Control) (f k gap : V) (hk : 0<k) :
    (∃ n:V,run215 n (liveValue (number i:V) f)=0) ↔
      ∃ t:V,first (runFrom t (entryValue (number i:V) f k gap))=0 :=
  control_tape_halts_iff _ f k gap (opcode_nonzero i) hk

/-- The scheduler's file is already in physical order, with candidate4 at index6. -/
noncomputable def seedFile : V := fileValue ![0,0,0,0,0,0,4,0,0]
noncomputable def seedEntryValue (_ : V) : V := entryValue 1 seedFile (ORingStructure.numeral 40) 1
instance seedEntry_defined : 𝚺₁-Function₁[V] seedEntryValue via seedEntryDef := .mk fun e => by
  simp [seedEntryDef,seedEntryValue,seedFile,file_defined.iff,
    Matrix.comp_vecCons',Matrix.empty_eq,Matrix.constant_eq_singleton,numeral_eq_natCast]

theorem seed_registers : regValue (seedFile:V)=![0,0,0,0,0,0,4,0,0] := by
  funext i
  exact reg_file _ i
end Model

private theorem first_source : source (0:Control)=([false,false,false],.decnz 8) := by decide +kernel
private theorem first_number : number (0:Control)=1 := rfl

/-- Finite encoding algebra only; the already checked boot run is not recomputed. -/
theorem standard_seed_entry : seedEntryValue (0:Nat)=bootCode := by
  have hframe := entry_format (V:=Nat) (0:Control) (seedFile (V:=Nat)) (40:Nat) (1:Nat)
  simp only [first_number,first_source,binaryValue,Bool.false_eq_true,if_false,
    mul_zero,add_zero,zero_add,natCast_nat] at hframe
  have hlist : List.ofFn (regValue (seedFile:Nat))=[0,0,0,0,0,0,4,0,0] := by
    rw [seed_registers]
    decide +kernel
  have hb : bootCode=frameSparse (V:=Nat) 84 1
      (bitPrefix false 65 (2*bitsCode (KRuntimeCore.sepsR KBoot215.bootVs)+1)) := by
    rw [bootCode_frame,KBoot215.bootRight,bitsCode_prefix]
    simp only [bitsCode,Bool.toNat_true,frameSparse,sparseCode_dispatch,natCast_nat,Nat.add_comm]
  rw [seedEntryValue,Nat.numeral_eq]
  rw [hframe,plain_nat,hlist,←bitPrefix_add]
  change frameSparse 84 1 (bitPrefix false 65 (2*bitsCode (KRuntimeCore.sepsR KBoot215.bootVs)+1))=bootCode
  exact hb.symm

section InternalBoot
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The very same fixed graph transfers this literal code equality to all models. -/
theorem seed_entry : entryValue (1:V) seedFile 40 1=(bootCode:V) := by
  have h:=DefinedFunction.shigmaOne_absolute_func V
    (seedEntry_defined (V:=Nat)) (seedEntry_defined (V:=V)) ![0]
  have he : seedEntryValue (0:V)=((seedEntryValue (0:Nat):Nat):V) := by
    simpa only [Function.comp_apply,Matrix.cons_val_zero,Nat.cast_zero] using h.symm
  rw [standard_seed_entry] at he
  simpa only [seedEntryValue,numeral_eq_natCast,Nat.cast_ofNat] using he
theorem seed_supported : opcodeValue table215 (1:V)≠0 := by
  simpa only [first_number,Nat.cast_one] using opcode_nonzero (V:=V) (0:Control)
theorem seed_related : Related (liveValue (1:V) seedFile) (bootCode:V) :=
  ⟨1,seedFile,40,1,by simp,seed_supported,rfl,seed_entry.symm⟩

/-- The accepted 95714-step prefix includes exclusion of an earlier halted state. -/
theorem control_blank_halts_iff :
    (∃ n:V,run215 n (liveValue 1 seedFile)=0) ↔
      ∃ t:V,first (ArithmeticMachineRun215.run t)=0 := by
  have h:=control_tape_halts_iff (1:V) seedFile 40 1 seed_supported (by simp)
  rw [seed_entry] at h
  exact h.trans blank_halts_iff_boot.symm

/-- Actual permuted scheduler and literal decimal215, with internal clocks on both sides. -/
theorem enum_blank_halts_iff :
    (∃ n:V,ArithmeticEnumRunPerm222.run n (ArithmeticEnumStepPerm222.liveValue 0 4 0)=0) ↔
      ∃ t:V,first (ArithmeticMachineRun215.run t)=0 :=
  ArithmeticDagRuntimePerm222.seed_halts_iff.trans
    ((ArithmeticControlBisimPerm215.halts_iff seedFile).trans control_blank_halts_iff)
end InternalBoot
end DiophantineConsistency.ArithmeticRuntime215
