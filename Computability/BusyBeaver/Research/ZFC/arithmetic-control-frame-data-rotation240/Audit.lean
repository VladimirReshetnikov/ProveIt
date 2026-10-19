import BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlFile
open ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 (registerBlock)
open ArithmeticOneRegisterBlocksRotation240 ArithmeticCarryTraversalRotation240
open ControlCatalogueRotation240 ArithmeticControlFrameDataRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.blocks_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.blocks_list
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.physicalValues_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.blocks_full
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.physicalValues_getD
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.spare_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.spare_nonempty
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.pc_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.pc_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.entry_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.entry_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.opcode_supported
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.related_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.related_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.related_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.related_live
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.entry_active
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240.related_active

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (indices : List (Fin 9)) :
    𝚺₁-Function₂[V] (blocksValue indices) via blocksDef indices := blocks_defined indices
example (indices : List (Fin 9)) (file suffix : V) :
    blocksValue indices file suffix = fileTape (indices.map (regValue file)) suffix :=
  blocks_list indices file suffix
example (file : V) : (physicalValues file).length = 9 := physicalValues_length file
example (file suffix : V) :
    blocksValue (List.finRange 9) file suffix = fileTape (physicalValues file) suffix :=
  blocks_full file suffix
example (file : V) (r : Fin 9) :
    (physicalValues file).getD r.val 0 = regValue file r := physicalValues_getD file r
example : 𝚺₁-Function₁[V] spareValue via spareDef := spare_defined
example (extra : V) : spareValue extra = registerBlock 1 (oneBlocks (166+extra) 0) :=
  spare_nonempty extra
example : 𝚺₀-Function₁[V] pcValue via pcDef := pc_defined
example (i : Control) : pcValue (V := V) (number i : V) = (sourcePC i : V) := pc_at i
example : 𝚺₁-Function₄[V] entryValue via entryDef := entry_defined
example (i : Control) (file extra gap : V) :
    entryValue (number i : V) file extra gap =
      frame 85 1 (ArithmeticControlTable.binaryValue (source i).1 +
        bitPrefix false (64 : V) (bitPrefix false gap
          (2*fileTape (physicalValues file) (oneBlocks (167+extra) 0)+1))) :=
  entry_at i file extra gap
example (q : V) (hq : ArithmeticControlTable.opcodeValue table q ≠ 0) :
    ∃ i : Control, q = (number i : V) := opcode_supported q hq
example (logical binary : V) :
    relatedDef.val.Evalb ![logical, binary] ↔ Related logical binary := related_iff logical binary
example : 𝚺₁-Relation[V] Related via relatedDef := related_defined
example : 𝚺₁-Relation[V] Related := related_definable
example (logical binary : V) (h : Related logical binary) : logical ≠ 0 :=
  related_live logical binary h
example (q file extra gap : V) : first (entryValue q file extra gap) ≠ 0 :=
  entry_active q file extra gap
example (logical binary : V) (h : Related logical binary) : first binary ≠ 0 :=
  related_active logical binary h
