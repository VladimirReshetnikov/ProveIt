import BusyBeaver.ZFC.ArithmeticStartupFrameRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlFile ArithmeticMachinePerm252
open ArithmeticMachineUniformScansPerm252 ArithmeticCarryTraversalRotation240
open ArithmeticOneRegisterBlocksRotation240 ArithmeticFiniteTapeRotation240
open ArithmeticControlFrameDataRotation240 ControlCatalogueRotation240
open ArithmeticStartupFrameRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.registerBits_eq
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.first_number
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.first_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.seedFile_pairs
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.seed_registers
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.physical_seed
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.registerBits_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.target_left
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.target_right
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.bootCode_frame
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.entry_seed
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.bootCode_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.first_opcode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.initialRelated
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.run_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStartupFrameRotation240.run_related

example (values : List Nat) :
    RegisterBoxes253.registerBits values = RegisterBoxesPerm252.registerBits values :=
  registerBits_eq values
example : number firstControl = 1 := first_number
example : source firstControl = ([false, false, false], .decnz 8) := first_source

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : seedFile (V := V) =
    cantor 0 (cantor 0 (cantor 0 (cantor 3 (cantor 0 (cantor 0 (cantor 3 (cantor 0 0))))))) :=
  seedFile_pairs
example (i : Fin 9) : regValue (seedFile (V := V)) i = seedValues i := seed_registers i
example : physicalValues (seedFile (V := V)) =
    seedPhysical.map (fun n : Nat => (n : V)) := physical_seed
example (values : List Nat) (spares : Nat) (suffix : V) :
    bitsPrefix (RegisterBoxes253.registerBits (values ++ List.replicate spares 1)) suffix =
      fileTape (values.map (fun n : Nat => (n : V))) (oneBlocks (spares : V) suffix) :=
  registerBits_file values spares suffix
example : ((encodeZip BootstrapFrameRotation240.target).left : V) = 1 := target_left
example : ((encodeZip BootstrapFrameRotation240.target).right : V) =
    bitPrefix false 181
      (2 * fileTape (physicalValues (seedFile (V := V))) (oneBlocks 167 0) + 1) := target_right
example : (ArithmeticBootstrapRotation240.bootCode : V) =
    frame 85 1 (bitPrefix false 181
      (2 * fileTape (physicalValues (seedFile (V := V))) (oneBlocks 167 0) + 1)) := bootCode_frame
example : entryValue 1 (seedFile (V := V)) 0 117 =
    frame 85 1 (bitPrefix false 181
      (2 * fileTape (physicalValues (seedFile (V := V))) (oneBlocks 167 0) + 1)) := entry_seed
example : (ArithmeticBootstrapRotation240.bootCode : V) =
    entryValue 1 (seedFile (V := V)) 0 117 := bootCode_entry
example : ArithmeticControlTable.opcodeValue (V := V) table 1 = 2 := first_opcode
example : Related (liveValue 1 (seedFile (V := V)))
    (ArithmeticBootstrapRotation240.bootCode : V) := initialRelated
example : ArithmeticMachineRunRotation240.run (409691 : V) =
    entryValue 1 (seedFile (V := V)) 0 117 := run_entry
example : Related (liveValue 1 (seedFile (V := V)))
    (ArithmeticMachineRunRotation240.run (409691 : V)) := run_related

-- The finite compatibility theorem retains an arbitrary internal suffix.
example (suffix : V) :
    bitsPrefix (RegisterBoxes253.registerBits (seedPhysical ++ List.replicate 167 1)) suffix =
      fileTape (physicalValues (seedFile (V := V))) (oneBlocks 167 suffix) := by
  simpa only [Nat.cast_ofNat, physical_seed] using registerBits_file seedPhysical 167 suffix
-- The nonempty logical seed and the active binary frame are both explicit.
example : liveValue 1 (seedFile (V := V)) ≠ 0 ∧
    first (ArithmeticBootstrapRotation240.bootCode : V) ≠ 0 :=
  ⟨related_live _ _ initialRelated, related_active _ _ initialRelated⟩
