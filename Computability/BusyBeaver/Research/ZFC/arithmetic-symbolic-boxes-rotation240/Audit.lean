import BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 (registerBlock)
open ArithmeticOneRegisterBlocksRotation240
open ArithmeticCarryTraversalRotation240
open ArithmeticSymbolicBoxesRotation240
open SymbolicRotation240 (Box Reg Branch)

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.fileTape_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.getD_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.writeAt_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.writeAt_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.markedPrefix_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.split_register
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.spareTail_first
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.spareTail_push
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.unchanged_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.marked_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.increment_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.decrement_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.decrement_positive_split
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.fileTape_even
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.markedPrefix_even
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240.boxPrefix_even

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (pre rest : List V) (suffix : V) :
    fileTape (pre++rest) suffix = fileTape pre (fileTape rest suffix) :=
  fileTape_append pre rest suffix
example (pre rest : List V) (value : V) :
    (pre++value::rest).getD pre.length 0 = value := getD_split pre value rest
example (pre rest : List V) (value newValue : V) :
    writeAt (pre++value::rest) pre.length newValue = pre++newValue::rest :=
  writeAt_split pre value rest newValue
example (values : List V) (r : Nat) (value : V) :
    (writeAt values r value).length = values.length := writeAt_length values r value
example (pre rest : List V) (value suffix : V) :
    markedPrefix pre.length (pre++value::rest) suffix =
      fileTape pre (4*bitPrefix true value (fileTape rest suffix)) :=
  markedPrefix_split pre value rest suffix
example (r : Nat) (values : List V) (hr : r < values.length) :
    ∃ pre value rest, values = pre++value::rest ∧ pre.length = r ∧
      values.getD r 0 = value := split_register r values hr
example (extra suffix : V) :
    spareTail extra suffix = registerBlock 1 (oneBlocks (166+extra) suffix) :=
  spareTail_first extra suffix
example (extra suffix : V) :
    spareTail extra (registerBlock 1 suffix) = spareTail (extra+1) suffix :=
  spareTail_push extra suffix
example (pre rest : List V) (value extra suffix : V) :
    boxPrefix (pre++value::rest) extra (.plain .unchanged) suffix =
      fileTape pre (registerBlock value (fileTape rest (spareTail extra suffix))) :=
  unchanged_split pre value rest extra suffix
example (pre rest : List V) (value extra suffix : V) (r : Reg) (hr : pre.length = r.val) :
    boxPrefix (pre++value::rest) extra (.marked r) suffix =
      fileTape pre (4*bitPrefix true value (fileTape rest (spareTail extra suffix))) :=
  marked_split pre value rest r hr extra suffix
example (pre rest : List V) (value extra suffix : V) (r : Reg) (hr : pre.length = r.val) :
    boxPrefix (pre++value::rest) extra (.plain (.increment r)) suffix =
      fileTape pre (registerBlock (value+1) (fileTape rest (spareTail (extra+1) suffix))) :=
  increment_split pre value rest r hr extra suffix
example (pre rest : List V) (value extra suffix : V) (r : Reg) (hr : pre.length = r.val) :
    boxPrefix (pre++value::rest) extra (.plain (.decrement r)) suffix =
      fileTape pre (registerBlock (value-1) (fileTape rest (spareTail extra suffix))) :=
  decrement_split pre value rest r hr extra suffix
example (pre rest : List V) (value extra suffix : V) (r : Reg) (hr : pre.length = r.val) :
    boxPrefix (pre++(value+1)::rest) extra (.plain (.decrement r)) suffix =
      fileTape pre (registerBlock value (fileTape rest (spareTail extra suffix))) :=
  decrement_positive_split pre value rest r hr extra suffix
example (values : List V) (hne : values ≠ []) (suffix : V) :
    ∃ half : V, fileTape values suffix = 2*half := fileTape_even values hne suffix
example (r : Nat) (values : List V) (hne : values ≠ []) (suffix : V) :
    ∃ half : V, markedPrefix r values suffix = 2*half := markedPrefix_even r values hne suffix
example (values : List V) (hlen : values.length = 9) (extra : V) (x : Box) (suffix : V) :
    ∃ half : V, boxPrefix values extra x suffix = 2*half :=
  boxPrefix_even values hlen extra x suffix

-- The last-register zero branch requires no additional spare-count premise.
example (values : List V) (r : Reg) (h : ValidValues (some (r,true)) values) :
    values.length = 9 ∧ values.getD r.val 0 = 0 := h
-- Zero extra spares still includes the permanent 167 blocks.
example (suffix : V) : spareTail (0 : V) suffix = oneBlocks 167 suffix := by
  simp only [spareTail,add_zero]
