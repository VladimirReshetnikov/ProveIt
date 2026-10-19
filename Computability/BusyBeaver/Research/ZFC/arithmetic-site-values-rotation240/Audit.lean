import BusyBeaver.ZFC.ArithmeticSiteValuesRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RegisterPathClean
open ArithmeticMachineUniformScansPerm252
open ArithmeticSymbolicTapeRotation240 ArithmeticSymbolicBoxesRotation240
open ArithmeticFiniteTapeRotation240 (bitsPrefix)
open ArithmeticCarryTraversalRotation240 (fileTape)
open ArithmeticOneRegisterBlocksRotation240 (oneBlocks)
open ArithmeticControlFile
open ArithmeticControlFrameDataRotation240 (physicalValues entryValue)
open ArithmeticDispatchRebaseRotation240 (startPathValue targetPathValue)
open ControlCatalogueRotation240
open SymbolicRotation240 (Effect Segment Box)
open ArithmeticSiteValuesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.effectValues_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.box_plain
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.map_bits_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.target_format
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.start_format
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.physicalValues_write
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.write_same
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.effect_increment
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.effect_decrement
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.start_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.target_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSiteValuesRotation240.target_next_entry

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (values : List V) (effect : Effect) :
    (effectValues values effect).length = values.length := effectValues_length values effect
example (values : List V) (extra suffix : V) (effect : Effect) :
    boxPrefix values extra (.plain effect) suffix =
      fileTape (effectValues values effect) (oneBlocks (167+effectExtra extra effect) suffix) :=
  box_plain values extra suffix effect
example (gap : V) (boxes : Box → V → V) (P : List Bool) (suffix : V) :
    tapePrefix gap boxes (P.map Segment.bit) suffix = bitsPrefix P suffix :=
  map_bits_prefix gap boxes P suffix
example (values : List V) (extra gap : V) (P : List Bool) (o : Bool)
    (pad : Nat) (effect : Effect) :
    targetValue values extra gap P o pad effect =
      targetPathValue P o pad gap (2*boxPrefix values extra (.plain effect) 0+1) :=
  target_format values extra gap P o pad effect
example (values : List V) (extra gap : V) (P : List Bool) :
    startValue values extra gap P = startPathValue P gap
      (2*fileTape values (oneBlocks (167+extra) 0)+1) := start_format values extra gap P
example (file value : V) (r : Fin 9) :
    physicalValues (writeValue (r.val : V) value file) =
      writeAt (physicalValues file) r.val value := physicalValues_write file value r
example (file : V) (r : Fin 9) :
    writeValue (r.val : V) (regValue file r) file = file := write_same file r
example (file : V) (r : Fin 9) :
    effectValues (physicalValues file) (.increment r) =
      physicalValues (writeValue (r.val : V) (regValue file r+1) file) := effect_increment file r
example (file : V) (r : Fin 9) :
    effectValues (physicalValues file) (.decrement r) =
      physicalValues (writeValue (r.val : V) (regValue file r-1) file) := effect_decrement file r
example (i : Control) (file extra gap : V) :
    startValue (physicalValues file) extra gap (source i).1 =
      entryValue (number i : V) file extra gap := start_source i file extra gap
example (values : List V) (extra gap : V) (P : List Bool) (o : Bool) (pad : Nat)
    (effect : Effect) (nextFile : V) (hv : effectValues values effect = physicalValues nextFile)
    (hp : P.length ≤ 64) (hc : Clean SourceRotation240.program P) :
    targetValue values extra gap P o pad effect =
      entryValue (number (resolveControl P) : V) nextFile (effectExtra extra effect)
        (gap+digit o+(pad : V)) := target_entry values extra gap P o pad effect nextFile hv hp hc
example (i : Control) (positive o : Bool) (pad : Nat) (file nextFile extra gap : V)
    (effect : Effect) (hv : effectValues (physicalValues file) effect = physicalValues nextFile)
    (hn : (source i).2 ≠ .halt)
    (hc : Clean SourceRotation240.program
      (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive)) :
    targetValue (physicalValues file) extra gap
        (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive) o pad effect =
      entryValue (nextControl i positive : V) nextFile (effectExtra extra effect)
        (gap+digit o+(pad : V)) :=
  target_next_entry i positive o pad file nextFile extra gap effect hv hn hc
-- Increment adds a value-one spare; this is separate from PC padding.
example (file extra gap : V) (P : List Bool) (o : Bool) (r : Fin 9)
    (hp : P.length ≤ 64) (hc : Clean SourceRotation240.program P) :
    targetValue (physicalValues file) extra gap P o 0 (.increment r) =
      entryValue (number (resolveControl P) : V)
        (writeValue (r.val : V) (regValue file r+1) file) (extra+1) (gap+digit o) := by
  simpa only [effectExtra,Nat.cast_zero,add_zero] using
    target_entry (physicalValues file) extra gap P o 0 (.increment r) _
      (effect_increment file r) hp hc
-- Positive decrement adds one padding cell and leaves the spare count alone.
example (file extra gap : V) (P : List Bool) (o : Bool) (r : Fin 9)
    (hp : P.length ≤ 64) (hc : Clean SourceRotation240.program P) :
    targetValue (physicalValues file) extra gap P o 1 (.decrement r) =
      entryValue (number (resolveControl P) : V)
        (writeValue (r.val : V) (regValue file r-1) file) extra (gap+digit o+1) := by
  simpa only [effectExtra,Nat.cast_one] using
    target_entry (physicalValues file) extra gap P o 1 (.decrement r) _
      (effect_decrement file r) hp hc
