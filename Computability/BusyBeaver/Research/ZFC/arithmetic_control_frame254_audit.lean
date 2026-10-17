import BusyBeaver.ZFC.ArithmeticControlFrame254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlFrame254 ArithmeticControlStep254 ArithmeticControlData254
open ArithmeticFiniteControl254 FiniteControlTable254
open ArithmeticRegisterFilePerm252 ArithmeticSymbolicBoxesPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open RegisterPath

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.blocks_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.blocks_list
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.blocks_full
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.constantBlocks_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.constantBlocks_list
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.spare_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.spare_actual
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.pc_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.entry_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.entry_frame
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.entry_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.entry_classifies
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.related_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.related_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.related_live
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.entry_active
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.related_active
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.physicalValues_getD
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.physicalValues_write
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.write_same
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.canonical_runtime
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.source_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.source_decnz_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.source_decnz_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.source_break
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.source_continue
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254.source_halt

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (indices : List (Fin 9)) (out file suffix : V) :
    (blocksDef indices).val.Evalb ![out,file,suffix] ↔ out=blocksValue indices file suffix := by simp
example (indices : List (Fin 9)) (file suffix : V) :
    blocksValue indices file suffix=fileCode (indices.map (regValue file)) suffix := blocks_list indices file suffix
example (file suffix : V) : blocksValue (List.finRange 9) file suffix=
    fileCode (physicalValues file) suffix := blocks_full file suffix
example (values : List Nat) (out suffix : V) :
    (constantBlocksDef values).val.Evalb ![out,suffix] ↔ out=constantBlocksValue values suffix := by simp
example (values : List Nat) (suffix : V) : constantBlocksValue values suffix=
    fileCode (values.map (fun n : Nat => (n : V))) suffix := constantBlocks_list values suffix
example (out count : V) : spareDef.val.Evalb ![out,count] ↔ out=spareValue count := by simp
example (count : V) : spareValue count=spareTail count 0 := spare_actual count
example (i : Control) : pcValue (V := V) (number i : V)=(sourcePC i : V) := pc_at i
example (out q file count gap : V) : entryDef.val.Evalb ![out,q,file,count,gap] ↔
    out=entryValue q file count gap := by simp
example (q file count gap : V) : entryValue q file count gap=
    frameValue (pcValue q) (physicalValues file) count gap := entry_frame q file count gap
example (i : Control) (file count gap : V) : entryValue (number i : V) file count gap=
    ArithmeticSitePerm252.startValue (physicalValues file) count gap (source i).1 := entry_at i file count gap
example (q file count gap : V) (h : opcodeValue q≠0) :
    ∃ i : Control, q=(number i : V) ∧ entryValue q file count gap=
      ArithmeticSitePerm252.startValue (physicalValues file) count gap (source i).1 := entry_classifies q file count gap h
example (logical binary : V) : relatedDef.val.Evalb ![logical,binary] ↔ Related logical binary :=
  related_iff logical binary
example : 𝚺₁-Relation[V] Related := inferInstance
example (logical binary : V) (h : Related logical binary) : logical≠0 := related_live logical binary h
example (q file count gap : V) : ArithmeticCantor.first (entryValue q file count gap)≠0 :=
  entry_active q file count gap
example (logical binary : V) (h : Related logical binary) : ArithmeticCantor.first binary≠0 :=
  related_active logical binary h
example (file : V) (r : Fin 9) : (physicalValues file).getD r.val 0=regValue file r :=
  physicalValues_getD file r
example (file value : V) (r : Fin 9) : physicalValues (writeValue (r.val : V) value file)=
    writeAt (physicalValues file) r.val value := physicalValues_write file value r
example (file : V) (r : Fin 9) : writeValue (r.val : V) (regValue file r) file=file := write_same file r
example (i : Control) (r : Nat) (he : (source i).2=.inc r) (file count gap : V) :
    ∃ time : V, 0<time ∧ runFrom time (entryValue (number i : V) file count gap)=
      entryValue (number (resolveControl (incPath (source i).1)) : V)
        (writeValue ((Permutation252Frame.physOf r : Nat) : V)
          ((physicalValues file).getD (Permutation252Frame.physOf r) 0+1) file)
        count (gap+digit (SitePerm252.allOnes (source i).1)) := source_inc i r he file count gap
example (i : Control) (r : Nat) (he : (source i).2=.decnz r) (file count gap : V)
    (h : (physicalValues file).getD (Permutation252Frame.physOf r) 0=0) :
    ∃ time : V, 0<time ∧ runFrom time (entryValue (number i : V) file count gap)=
      entryValue (number (resolveControl (breakPath 1 (source i).1)) : V) file count
        (gap+digit (SitePerm252.allOnes (stripPath false 1 (source i).1))) :=
  source_decnz_zero i r he file count gap h
example (i : Control) (r : Nat) (he : (source i).2=.decnz r) (file count gap : V)
    (h : (physicalValues file).getD (Permutation252Frame.physOf r) 0≠0) :
    ∃ time : V, 0<time ∧ runFrom time (entryValue (number i : V) file count gap)=
      entryValue (number (resolveControl (incPath (source i).1)) : V)
        (writeValue ((Permutation252Frame.physOf r : Nat) : V)
          ((physicalValues file).getD (Permutation252Frame.physOf r) 0-1) file)
        (count+1) (gap+digit (SitePerm252.allOnes (source i).1)) := source_decnz_positive i r he file count gap h
example (i : Control) (k : Nat) (he : (source i).2=.brk k) (file count gap : V) :
    ∃ time : V, 0<time ∧ runFrom time (entryValue (number i : V) file count gap)=
      entryValue (number (resolveControl (breakPath k (source i).1)) : V) file count
        (gap+digit (SitePerm252.allOnes (stripPath false k (source i).1))) := source_break i k he file count gap
example (i : Control) (k : Nat) (he : (source i).2=.cont k) (file count gap : V) :
    ∃ time : V, 0<time ∧ runFrom time (entryValue (number i : V) file count gap)=
      entryValue (number (resolveControl (continuePath k (source i).1)) : V) file count gap :=
  source_continue i k he file count gap
example (i : Control) (he : (source i).2=.halt) (file count gap : V) :
    ∃ time : V, 0<time ∧ ArithmeticCantor.first (runFrom time (entryValue (number i : V) file count gap))=0 :=
  source_halt i he file count gap
example (file : V) : (physicalValues file).length=9 := physicalValues_length file
example (i : Control) (file count gap : V) :
    Related (liveValue (number i : V) file) (entryValue (number i : V) file count gap) := by
  refine ⟨live_ne_zero _ _,?_,count,gap,?_⟩
  · rw [control_live]
    exact (opcodeValue_nonzero_iff _).mpr ⟨i,rfl⟩
  · simp only [control_live,fileCode_live]
example (binary : V) : ¬Related (0 : V) binary := fun h => h.1 rfl
example (file count gap : V) : entryValue (1 : V) file count gap=
    ArithmeticSitePerm252.startValue (physicalValues file) count gap [false,false,false] := by
  have h := entry_at (V := V) ⟨0,by decide⟩ file count gap
  rw [first_source] at h
  have hn : (number (⟨0,by decide⟩ : Control) : V)=1 := by
    change ((1 : Nat) : V)=1
    exact Nat.cast_one
  rw [hn] at h
  exact h
