import BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240
import BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240
import BusyBeaver.ZFC.ArithmeticBootstrapRotation240
import BusyBeaver.ZFC.BootstrapFrameRotation240

set_option autoImplicit false

/-!
Identify the already checked 409691-step bootstrap code with the represented
Rotation240 dispatch frame. The physical file is [0,0,0,3,0,0,3,0,0], followed
by 167 value-one spares. Its 181 zero bits split into the fixed margin 64 and
gap 117. The full numeric tape is retained, including the zero exterior.

Only finite codec identities and the first decoder entry are proved here;
the bootstrap is imported, not replayed. This is an initial Related witness,
not the subsequent arbitrary-control simulation or a PA consistency endpoint.
The imported machine, source and calibration attribution of Mira-Cult,
Jeff Ketchersid, Andrew James Wade and ProveIt is retained.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlFile
open ArithmeticMachinePerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticMachineStepPerm252 (encodeConfig)
open ArithmeticCarryTraversalRotation240 ArithmeticOneRegisterBlocksRotation240
open ArithmeticFiniteTapeRotation240 ArithmeticControlFrameDataRotation240
open ControlCatalogueRotation240

/-- The two historical finite register codecs agree structurally. -/
theorem registerBits_eq (values : List Nat) :
    RegisterBoxes253.registerBits values = RegisterBoxesPerm252.registerBits values := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [RegisterBoxes253.registerBits, RegisterBoxesPerm252.registerBits, ih]

def firstControl : Control := ⟨0, by decide⟩

theorem first_number : number firstControl = 1 := rfl

private theorem crank_nil (t : ControlCatalogue.CTree) :
    ControlCatalogue.crank t [] = 0 := by
  induction t with
  | none => rfl
  | leaf _ => rfl
  | node _ _ _ ih _ => exact ih

private theorem resolve_empty : resolveControl [] = firstControl := by
  apply Fin.ext
  exact crank_nil CountedTreeRotation240.counted

/-- Only the three leftmost decoder decisions are reduced. -/
theorem first_source : source firstControl = ([false, false, false], .decnz 8) := by
  have hw : RegisterPath.walk SourceRotation240.program
      (SourceRotation240.program.nnodes + 1) SourceRotation240.program.root [] 0 =
      some (.decnz 8, 3) := by
    rw [TreeRotation240.walk_eq_tree]
    rfl
  have h := resolve_source [] (.decnz 8) 3 hw
  rw [resolve_empty] at h
  exact h

def seedPhysical : List Nat := [0, 0, 0, 3, 0, 0, 3, 0, 0]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def seedValues : Fin 9 → V := ![0, 0, 0, 3, 0, 0, 3, 0, 0]
noncomputable def seedFile : V := fileValue (seedValues (V := V))

/-- This is also the nested-pair physical seed used by the register endpoint. -/
theorem seedFile_pairs : seedFile (V := V) =
    cantor 0 (cantor 0 (cantor 0 (cantor 3 (cantor 0 (cantor 0 (cantor 3 (cantor 0 0))))))) :=
  rfl

theorem seed_registers (i : Fin 9) : regValue (seedFile (V := V)) i = seedValues i :=
  reg_file _ i

theorem physical_seed : physicalValues (seedFile (V := V)) =
    seedPhysical.map (fun n : Nat => (n : V)) := by
  have hf : regValue (seedFile (V := V)) = seedValues := funext seed_registers
  rw [physicalValues, hf]
  simp only [seedPhysical, List.map_cons, List.map_nil, Nat.cast_zero, Nat.cast_ofNat]
  rfl

private theorem fileTape_append (xs ys : List V) (suffix : V) :
    fileTape (xs ++ ys) suffix = fileTape xs (fileTape ys suffix) := by
  induction xs with
  | nil => rfl
  | cons value xs ih => simp only [List.cons_append, fileTape, ih]

/-- External finite register syntax, with an arbitrary internal untouched tail. -/
theorem registerBits_file (values : List Nat) (spares : Nat) (suffix : V) :
    bitsPrefix (RegisterBoxes253.registerBits (values ++ List.replicate spares 1)) suffix =
      fileTape (values.map (fun n : Nat => (n : V))) (oneBlocks (spares : V) suffix) := by
  rw [registerBits_eq, ←fileTape_nat, List.map_append, fileTape_append,
    List.map_replicate, Nat.cast_one, ←oneBlocks_nat]

theorem target_left : ((encodeZip BootstrapFrameRotation240.target).left : V) = 1 := by
  change (bitsCode (true :: List.replicate 9 false) : V) = 1
  rw [bitsCode_cast]
  change 2 * bitsPrefix (List.replicate 9 false) (0 : V) + 1 = 1
  rw [←bitPrefix_replicate]
  simp only [ArithmeticSymbolicTapePerm252.bitPrefix_false_zero, mul_zero, zero_add]

/-- Keep the long bit-list codec symbolic until after its algebra is proved. -/
private theorem registerRight_cast (gap spares : Nat) (values : List Nat) :
    (bitsCode (List.replicate gap false ++ [true] ++
      RegisterBoxes253.registerBits (values ++ List.replicate spares 1) ++
      List.replicate 0 false) : V) =
    bitPrefix false (gap : V)
      (2 * fileTape (values.map (fun n : Nat => (n : V)))
        (oneBlocks (spares : V) 0) + 1) := by
  rw [bitsCode_cast]
  simp only [List.replicate_zero, List.append_nil, bitsPrefix_append]
  rw [←bitPrefix_replicate]
  change bitPrefix false (gap : V)
    (2 * bitsPrefix (RegisterBoxes253.registerBits
      (values ++ List.replicate spares 1)) 0 + 1) = _
  rw [registerBits_file]

theorem target_right : ((encodeZip BootstrapFrameRotation240.target).right : V) =
    bitPrefix false 181
      (2 * fileTape (physicalValues (seedFile (V := V))) (oneBlocks 167 0) + 1) := by
  have hright (z : FiniteZipper.ZipConfig 240) :
      ((encodeZip z).right : V) = (bitsCode z.right : V) := rfl
  have hshape : BootstrapFrameRotation240.target.right =
      List.replicate 181 false ++ [true] ++
        RegisterBoxes253.registerBits (seedPhysical ++ List.replicate 167 1) ++
        List.replicate 0 false := rfl
  rw [hright, hshape, registerRight_cast, ←physical_seed]
  simp only [Nat.cast_ofNat]

/-- Transport the complete checked zipper without evaluating its large code. -/
theorem bootCode_frame : (ArithmeticBootstrapRotation240.bootCode : V) =
    frame 85 1 (bitPrefix false 181
      (2 * fileTape (physicalValues (seedFile (V := V))) (oneBlocks 167 0) + 1)) := by
  have hstate : ((encodeZip BootstrapFrameRotation240.target).state : V) = 85 :=
    congrArg (fun n : Nat => (n : V))
      (show (encodeZip BootstrapFrameRotation240.target).state = 85 from rfl)
  rw [ArithmeticBootstrapRotation240.bootCode, BootstrapFrameRotation240.target_checkpoint,
    encodeConfig_cast, target_left, target_right, hstate]

theorem entry_seed : entryValue 1 (seedFile (V := V)) 0 117 =
    frame 85 1 (bitPrefix false 181
      (2 * fileTape (physicalValues (seedFile (V := V))) (oneBlocks 167 0) + 1)) := by
  have h := entry_at firstControl (seedFile (V := V)) 0 117
  simp only [first_number, Nat.cast_one, first_source, ArithmeticControlTable.binaryValue,
    Bool.false_eq_true, if_false, mul_zero, add_zero, zero_add] at h
  have hcount : (64 : V) + 117 = 181 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      congrArg (fun n : Nat => (n : V)) (show (64 : Nat) + 117 = 181 from rfl)
  rw [←ArithmeticSymbolicTapePerm252.bitPrefix_add, hcount] at h
  exact h

theorem bootCode_entry : (ArithmeticBootstrapRotation240.bootCode : V) =
    entryValue 1 (seedFile (V := V)) 0 117 := bootCode_frame.trans entry_seed.symm

/-- Keep the lookup lemma generic before specializing the 6455-row table. -/
private theorem opcode_first (rl : List ArithmeticControlBisim.Row)
    (row : ArithmeticControlBisim.Row) (h : getElem? rl 0 = some row) :
    ArithmeticControlTable.opcodeValue (V := V) rl 1 = (row.op : V) := by
  cases rl with
  | nil => cases h
  | cons head tail =>
      have he : head = row := Option.some.inj h
      subst head
      simpa only [Nat.zero_add, Nat.cast_one, List.getElem_cons_zero] using
        (ArithmeticControlTable.opcodeValue_at (V := V) (rl := row :: tail)
          0 (Nat.zero_lt_succ _))

theorem first_opcode : ArithmeticControlTable.opcodeValue (V := V) table 1 = 2 := by
  have h := opcode_first (V := V) table
    (ArithmeticControlTable.rowOf TreeRotation240.tree (source firstControl))
    (table_row_at firstControl)
  simpa only [first_source, ArithmeticControlTable.rowOf,
    ArithmeticControlTable.edgeOpcode, Nat.cast_ofNat] using h

theorem initialRelated : Related (liveValue 1 (seedFile (V := V)))
    (ArithmeticBootstrapRotation240.bootCode : V) := by
  refine ⟨live_ne_zero _ _, ?_, 0, 117, ?_⟩
  · simpa only [control_live, first_opcode] using (by simp : (2 : V) ≠ 0)
  · simpa only [control_live, fileCode_live] using (bootCode_entry (V := V))

theorem run_entry : ArithmeticMachineRunRotation240.run (409691 : V) =
    entryValue 1 (seedFile (V := V)) 0 117 :=
  ArithmeticBootstrapRotation240.internal_boot.trans bootCode_entry

theorem run_related : Related (liveValue 1 (seedFile (V := V)))
    (ArithmeticMachineRunRotation240.run (409691 : V)) := by
  rw [ArithmeticBootstrapRotation240.internal_boot]
  exact initialRelated

end SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240
