import BusyBeaver.ZFC.ArithmeticControlStep254

set_option autoImplicit false

/-!
A fixed Sigma1 whole binary frame from the numbered control and coded physical
register file. Only valid source controls enter the represented relation.
The list of nine fields is external fixed syntax; all values/counts/gaps may be
internal. Local runtime composition is developed below, without a run or
internal L2/scheduler equivalence claim.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlData254 ArithmeticControlStep254
open ArithmeticFiniteControl254 FiniteControlTable254
open ArithmeticRegisterForwardPerm252 ArithmeticRegisterFilePerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticZeroRegisterBlocks254
open ArithmeticSymbolicBoxesPerm252
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A fixed external sequence of physical fields, never an internal list. -/
noncomputable def blocksValue : List (Fin 9) → V → V → V
  | [], _, suffix => suffix
  | i::indices, file, suffix => registerBlock (regValue file i) (blocksValue indices file suffix)

def blocksDef : List (Fin 9) → 𝚺₁.Semisentence 3
  | [] => .mkSigma “out file suffix. out=suffix”
  | i::indices => .mkSigma
      “out file suffix. ∃ tail, !(blocksDef indices) tail file suffix ∧
        ∃ value, !(projectionDef 8 i) value file ∧ !registerBlockDef out value tail”
instance blocks_defined (indices : List (Fin 9)) :
    𝚺₁-Function₂[V] (blocksValue indices) via blocksDef indices := by
  induction indices with
  | nil => exact .mk fun e => by simp [blocksDef,blocksValue]
  | cons i indices ih =>
      exact .mk fun e => by
        simp [blocksDef,blocksValue,regValue,(projection_defined 8 i).iff,ih.iff]

theorem blocks_list (indices : List (Fin 9)) (file suffix : V) :
    blocksValue indices file suffix = fileCode (indices.map (regValue file)) suffix := by
  induction indices with
  | nil => rfl
  | cons i indices ih => simp only [blocksValue,List.map_cons,fileCode,ih]

noncomputable def physicalValues (file : V) : List V := List.ofFn (regValue file)

theorem physicalValues_length (file : V) : (physicalValues file).length=9 := by
  simp only [physicalValues,List.length_ofFn]

theorem blocks_full (file suffix : V) :
    blocksValue (List.finRange 9) file suffix = fileCode (physicalValues file) suffix := by
  rw [blocks_list,physicalValues,List.ofFn_eq_map]

noncomputable def constantBlocksValue : List Nat → V → V
  | [], suffix => suffix
  | value::values, suffix => registerBlock (value : V) (constantBlocksValue values suffix)

def constantBlocksDef : List Nat → 𝚺₁.Semisentence 2
  | [] => .mkSigma “out suffix. out=suffix”
  | value::values => .mkSigma
      “out suffix. ∃ tail, !(constantBlocksDef values) tail suffix ∧
        !registerBlockDef out !!(Semiterm.Operator.numeral ℒₒᵣ value) tail”
instance constantBlocks_defined (values : List Nat) :
    𝚺₁-Function₁[V] (constantBlocksValue values) via constantBlocksDef values := by
  induction values with
  | nil => exact .mk fun e => by simp [constantBlocksDef,constantBlocksValue]
  | cons value values ih =>
      exact .mk fun e => by
        simp [constantBlocksDef,constantBlocksValue,numeral_eq_natCast,ih.iff]

theorem constantBlocks_list (values : List Nat) (suffix : V) :
    constantBlocksValue values suffix = fileCode (values.map (fun n : Nat => (n : V))) suffix := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [constantBlocksValue,List.map_cons,fileCode,ih]

def spareConstants : List Nat := List.replicate 8 0 ++ [1]
noncomputable def spareValue (count : V) : V :=
  constantBlocksValue spareConstants (zeroBlocks count 0)
def spareDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out count. ∃ tail, !zeroBlocksDef tail count 0 ∧
    !(constantBlocksDef spareConstants) out tail”
instance spare_defined : 𝚺₁-Function₁[V] spareValue via spareDef :=
  .mk fun e => by simp [spareDef,spareValue]

theorem spare_actual (count : V) : spareValue count = spareTail count 0 := by
  rw [spareValue,constantBlocks_list]
  simp [spareTail,spareConstants,fixedSpares]

noncomputable def pcValue (q : V) : V := fieldValue sourcePC sourcePC q 0
def pcDef : 𝚺₀.Semisentence 2 := .mkSigma
  “out q. !(fieldDef sourcePC sourcePC) out q 0”
instance pc_defined : 𝚺₀-Function₁[V] pcValue via pcDef :=
  .mk fun e => by simp [pcDef,pcValue]

@[simp] theorem pc_at (i : Control) : pcValue (V := V) (number i : V) = (sourcePC i : V) := by
  simp only [pcValue,fieldValue_at,ite_self]

/-- The same fixed forty-bit frame as the actual checked site contract. -/
noncomputable def entryValue (q file count gap : V) : V :=
  frame 95 1 (pcValue q + bitPrefix false (40 : V)
    (bitPrefix false gap (2*blocksValue (List.finRange 9) file (spareValue count)+1)))

def entryDef : 𝚺₁.Semisentence 5 := .mkSigma
  “out q file count gap. ∃ pc, !pcDef pc q ∧ ∃ spares, !spareDef spares count ∧
    ∃ blocks, !(blocksDef (List.finRange 9)) blocks file spares ∧
    ∃ gapBits, !(bitPrefixDef false) gapBits gap (2*blocks+1) ∧
    ∃ pcBits, !(bitPrefixDef false) pcBits 40 gapBits ∧
    ∃ tape, !ArithmeticCantor.pairDef tape 1 (pc+pcBits) ∧
    !ArithmeticCantor.pairDef out 95 tape”
instance entry_defined : 𝚺₁-Function₄[V] entryValue via entryDef :=
  .mk fun e => by simp [entryDef,entryValue,frame,numeral_eq_natCast,Nat.cast_ofNat]

theorem entry_frame (q file count gap : V) :
    entryValue q file count gap = frameValue (pcValue q) (physicalValues file) count gap := by
  rw [entryValue,blocks_full,spare_actual]
  rfl

theorem entry_at (i : Control) (file count gap : V) :
    entryValue (number i : V) file count gap =
      ArithmeticSitePerm252.startValue (physicalValues file) count gap (source i).1 := by
  rw [entry_frame,pc_at]
  have hp : (sourcePC i : V)=binaryValue (source i).1 :=
    (binaryValue_cast (source i).1).symm
  rw [hp]
  exact (start_fixed_frame (source i).1 (source_length i) (physicalValues file) count gap).symm

theorem entry_classifies (q file count gap : V) (hq : opcodeValue q≠0) :
    ∃ i : Control, q=(number i : V) ∧ entryValue q file count gap=
      ArithmeticSitePerm252.startValue (physicalValues file) count gap (source i).1 := by
  obtain ⟨i,rfl⟩ := (opcodeValue_nonzero_iff q).mp hq
  exact ⟨i,rfl,entry_at i file count gap⟩

/-- No invalid control or already halted logical state is related to a live
binary frame. All count/gap witnesses remain internal arithmetic values. -/
def Related (logical binary : V) : Prop :=
  logical≠0 ∧ opcodeValue (controlValue logical)≠0 ∧
    ∃ count gap : V, binary=entryValue (controlValue logical) (fileCodeValue logical) count gap

def relatedDef : 𝚺₁.Semisentence 2 := .mkSigma
  “logical binary. logical≠0 ∧
    ∃ control, !controlDef control logical ∧ ∃ file, !fileCodeDef file logical ∧
    ∃ opcode, !opcodeDef opcode control ∧ opcode≠0 ∧
    ∃ count, ∃ gap, !entryDef binary control file count gap”

theorem related_iff (logical binary : V) :
    relatedDef.val.Evalb ![logical,binary] ↔ Related logical binary := by
  simp [relatedDef,Related]

instance related_defined : 𝚺₁-Relation[V] Related via relatedDef :=
  .mk fun e => by simp [relatedDef,Related]
instance related_definable : 𝚺₁-Relation[V] Related :=
  HierarchySymbol.Defined.to_definable relatedDef related_defined

theorem related_live (logical binary : V) (h : Related logical binary) : logical≠0 := h.1

theorem entry_active (q file count gap : V) : first (entryValue q file count gap)≠0 := by
  simp [entryValue,frame]

theorem related_active (logical binary : V) (h : Related logical binary) : first binary≠0 := by
  obtain ⟨_,_,count,gap,rfl⟩ := h
  exact entry_active _ _ count gap


open RegisterPath RegisterPathClean
open ArithmeticMachineRunFromPerm252 ArithmeticDispatchRebasePerm252

/-- The external nine-field view agrees with the physical box selector. -/
theorem physicalValues_getD (file : V) (r : Fin 9) :
    (physicalValues file).getD r.val 0 = regValue file r := by
  have hr : r.val < (physicalValues file).length := by
    simpa only [physicalValues_length] using r.isLt
  rw [←List.getElem_eq_getD (h := hr) (0 : V)]
  simp only [physicalValues,List.getElem_ofFn]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
private theorem writeAt_set (values : List V) (r : Nat) (value : V) :
    writeAt values r value = values.set r value := by
  induction values generalizing r with
  | nil => rfl
  | cons first values ih => cases r <;> simp [writeAt,List.set,ih]

theorem physicalValues_write (file value : V) (r : Fin 9) :
    physicalValues (writeValue (r.val : V) value file) =
      writeAt (physicalValues file) r.val value := by
  rw [writeAt_set]
  apply List.ext_getElem (by simp [physicalValues_length])
  intro j hj hj'
  simp only [physicalValues,List.getElem_ofFn,reg_write,List.getElem_set,Nat.cast_inj]

theorem write_same (file : V) (r : Fin 9) :
    writeValue (r.val : V) (regValue file r) file = file := by
  calc
    _ = fileValue (regValue (writeValue (r.val : V) (regValue file r) file)) :=
      (file_reg _).symm
    _ = fileValue (regValue file) := by
      apply congrArg fileValue
      funext j
      by_cases h : r=j
      · subst j; exact write_at _ _ _
      · exact write_other _ _ _ _ h
    _ = file := file_reg file

/-- Retain the actual walk witness from next_checked, then resolve its exact
catalogue index. The runtime premise is discharged by each actual site below. -/
theorem canonical_runtime (Q P : List Bool) (overflow : Bool) (effect : SymbolicPerm252.Effect)
    (file nextFile count gap time : V)
    (hP : P.length≤40) (hc : Clean Prog254.program P)
    (hr : runFrom time (ArithmeticSitePerm252.startValue (physicalValues file) count gap Q) =
      ArithmeticSymbolicExecutionPerm252.value (physicalValues file) count gap
        (SitePerm252.target P overflow (.plain effect)))
    (hv : physicalValues nextFile=effectValues (physicalValues file) effect) :
    runFrom time (ArithmeticSitePerm252.startValue (physicalValues file) count gap Q) =
      entryValue (number (resolveControl P) : V) nextFile (effectCount count effect)
        (gap+digit overflow) := by
  obtain ⟨e,d,hw,_,_,hd,hpad⟩ := next_checked P overflow hP hc
  have hi := resolve_source P e d hw
  have hpath : (source (resolveControl P)).1=consume P d := congrArg (fun x : List Bool × Edge => x.1) hi
  have he := entry_at (resolveControl P) nextFile (effectCount count effect) (gap+digit overflow)
  rw [hpath,hv] at he
  exact (hr.trans (target_rebase (physicalValues file) count gap P (consume P d)
    overflow effect hd hpad)).trans he.symm

/-- Every accepted actual increment has a positive binary clock and the exact
resolved numbered successor. No new guard computation is performed. -/
theorem source_inc (i : Control) (r : Nat) (he : (source i).2=.inc r)
    (file count gap : V) :
    ∃ time : V, 0<time ∧ runFrom time (entryValue (number i : V) file count gap) =
      entryValue (number (resolveControl (incPath (source i).1)) : V)
        (writeValue ((Permutation252Frame.physOf r : Nat) : V)
          ((physicalValues file).getD (Permutation252Frame.physOf r) 0+1) file)
        count (gap+digit (SitePerm252.allOnes (source i).1)) := by
  have hs : SitePerm252.checkSite (source i).1 (.inc r)=true := by
    simpa only [he] using source_accepted i
  have hr := SitePerm252.check_inc_bound _ _ hs
  let p := SitePerm252.physical r hr
  obtain ⟨time,ht,hv⟩ := ArithmeticSitePerm252.check_inc _ r hr hs
    (physicalValues file) (physicalValues_length file) count gap
  refine ⟨time,ht,?_⟩
  rw [entry_at]
  apply canonical_runtime _ _ _ (.increment p) _ _ _ _ time
  · rw [InstructionPerm252.incPath_length]; exact source_length i
  · exact clean_inc _ r (by simpa only [he] using source_follow i)
  · exact hv
  · exact physicalValues_write file _ p

/-- The zero branch preserves the file and adds no zero spare. -/
theorem source_decnz_zero (i : Control) (r : Nat) (he : (source i).2=.decnz r)
    (file count gap : V)
    (hz : (physicalValues file).getD (Permutation252Frame.physOf r) 0=0) :
    ∃ time : V, 0<time ∧ runFrom time (entryValue (number i : V) file count gap) =
      entryValue (number (resolveControl (breakPath 1 (source i).1)) : V) file count
        (gap+digit (SitePerm252.allOnes (stripPath false 1 (source i).1))) := by
  have hs : SitePerm252.checkSite (source i).1 (.decnz r)=true := by
    simpa only [he] using source_accepted i
  have hr := SitePerm252.check_decnz_bound _ _ hs
  obtain ⟨time,ht,hv⟩ := ArithmeticSitePerm252.check_decnz_zero _ r hr hs
    (physicalValues file) (physicalValues_length file) hz count gap
  refine ⟨time,ht,?_⟩
  rw [entry_at]
  apply canonical_runtime _ _ _ .unchanged _ file _ _ time
  · exact le_trans (InstructionPerm252.breakPath_length 1 _) (source_length i)
  · exact clean_decnz_zero _ r (by simpa only [he] using source_follow i)
  · exact hv
  · rfl

/-- Positive decrement changes only its physical register and adds one zero
spare exactly once, including when the old value is one. -/
theorem source_decnz_positive (i : Control) (r : Nat) (he : (source i).2=.decnz r)
    (file count gap : V)
    (hn : (physicalValues file).getD (Permutation252Frame.physOf r) 0≠0) :
    ∃ time : V, 0<time ∧ runFrom time (entryValue (number i : V) file count gap) =
      entryValue (number (resolveControl (incPath (source i).1)) : V)
        (writeValue ((Permutation252Frame.physOf r : Nat) : V)
          ((physicalValues file).getD (Permutation252Frame.physOf r) 0-1) file)
        (count+1) (gap+digit (SitePerm252.allOnes (source i).1)) := by
  have hs : SitePerm252.checkSite (source i).1 (.decnz r)=true := by
    simpa only [he] using source_accepted i
  have hr := SitePerm252.check_decnz_bound _ _ hs
  let p := SitePerm252.physical r hr
  obtain ⟨time,ht,hv⟩ := ArithmeticSitePerm252.check_decnz_positive _ r hr hs
    (physicalValues file) (physicalValues_length file) hn count gap
  refine ⟨time,ht,?_⟩
  rw [entry_at]
  apply canonical_runtime _ _ _ (.decrement p) _ _ _ _ time
  · rw [InstructionPerm252.incPath_length]; exact source_length i
  · exact clean_decnz_positive _ r (by simpa only [he] using source_follow i)
  · exact hv
  · exact physicalValues_write file _ p

theorem source_break (i : Control) (k : Nat) (he : (source i).2=.brk k)
    (file count gap : V) :
    ∃ time : V, 0<time ∧ runFrom time (entryValue (number i : V) file count gap) =
      entryValue (number (resolveControl (breakPath k (source i).1)) : V) file count
        (gap+digit (SitePerm252.allOnes (stripPath false k (source i).1))) := by
  have hs : SitePerm252.checkSite (source i).1 (.brk k)=true := by
    simpa only [he] using source_accepted i
  obtain ⟨time,ht,hv⟩ := ArithmeticSitePerm252.check_break _ k hs
    (physicalValues file) (physicalValues_length file) count gap
  refine ⟨time,ht,?_⟩
  rw [entry_at]
  apply canonical_runtime _ _ _ .unchanged _ file _ _ time
  · exact le_trans (InstructionPerm252.breakPath_length k _) (source_length i)
  · exact clean_break _ k (by simpa only [he] using source_follow i)
  · exact hv
  · rfl

theorem source_continue (i : Control) (k : Nat) (he : (source i).2=.cont k)
    (file count gap : V) :
    ∃ time : V, 0<time ∧ runFrom time (entryValue (number i : V) file count gap) =
      entryValue (number (resolveControl (continuePath k (source i).1)) : V) file count gap := by
  have hs : SitePerm252.checkSite (source i).1 (.cont k)=true := by
    simpa only [he] using source_accepted i
  obtain ⟨time,ht,hv⟩ := ArithmeticSitePerm252.check_continue _ k hs
    (physicalValues file) (physicalValues_length file) count gap
  refine ⟨time,ht,?_⟩
  rw [entry_at]
  have hh := canonical_runtime _ _ false .unchanged file file count gap time
    (le_trans (InstructionPerm252.continuePath_length k _) (source_length i))
    (clean_continue _ k (by simpa only [he] using source_follow i)) hv rfl
  simpa only [effectCount,digit,Bool.false_eq_true,if_false,add_zero] using hh

theorem source_halt (i : Control) (he : (source i).2=.halt) (file count gap : V) :
    ∃ time : V, 0<time ∧ first (runFrom time (entryValue (number i : V) file count gap))=0 := by
  rw [entry_at]
  exact ArithmeticSitePerm252.check_halt _ (by simpa only [he] using source_accepted i)
    (physicalValues file) (physicalValues_length file) count gap

end SetTheory.BusyBeaver.ZFC.ArithmeticControlFrame254
