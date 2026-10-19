import BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RegisterPathClean
open ArithmeticMachineUniformScansPerm252
open ArithmeticFiniteTapeRotation240 (bitsPrefix)
open ArithmeticCarryTraversalRotation240 (fileTape)
open ArithmeticOneRegisterBlocksRotation240 (oneBlocks)
open ArithmeticControlFrameDataRotation240 (physicalValues entryValue)
open ControlCatalogueRotation240 ArithmeticDispatchRebaseRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.budget_ge
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.padded_prefix
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.bitsPrefix_affine
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.start_format
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.target_rebase
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.next_checked
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.start_source
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.target_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.reenter
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.clean_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.clean_decnz_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.clean_decnz_positive
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.clean_break
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.clean_continue
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.outgoing_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240.target_next_entry

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (overflow : Bool) (padExtra : Nat) : 64 ≤ budget overflow padExtra :=
  budget_ge overflow padExtra
example (P : List Bool) (N : Nat) (gap header : V) :
    bitsPrefix P (bitPrefix false (gap+((N-P.length : Nat) : V)) header) =
      bitsPrefix (padded P N) (bitPrefix false gap header) := padded_prefix P N gap header
example (P : List Bool) (suffix : V) :
    bitsPrefix P suffix = ArithmeticControlTable.binaryValue P +
      bitPrefix false (P.length : V) suffix := bitsPrefix_affine P suffix
example (P : List Bool) (gap header : V) (hP : P.length ≤ 64) :
    startPathValue P gap header = frame 85 1 (ArithmeticControlTable.binaryValue P +
      bitPrefix false (64 : V) (bitPrefix false gap header)) := start_format P gap header hP
example (P Q : List Bool) (overflow : Bool) (padExtra : Nat) (gap header : V)
    (hQ : Q.length ≤ 64)
    (hp : padded P (budget overflow padExtra) = padded Q (budget overflow padExtra)) :
    targetPathValue P overflow padExtra gap header =
      startPathValue Q (gap+digit overflow+(padExtra : V)) header :=
  target_rebase P Q overflow padExtra gap header hQ hp
example (P : List Bool) (overflow : Bool) (padExtra : Nat) (hP : P.length ≤ 64)
    (hc : Clean SourceRotation240.program P) :
    ∃ e d, walk SourceRotation240.program (SourceRotation240.program.nnodes+1)
        SourceRotation240.program.root P 0 = some (e,d) ∧
      follow SourceRotation240.program (.node SourceRotation240.program.root) (consume P d) = some e ∧
      SiteRotation240.checkSite (consume P d) e = true ∧ (consume P d).length ≤ 64 ∧
      padded P (budget overflow padExtra) = padded (consume P d) (budget overflow padExtra) :=
  next_checked P overflow padExtra hP hc
example (i : Control) (file spareExtra gap : V) :
    startPathValue (source i).1 gap
        (2*fileTape (physicalValues file) (oneBlocks (167+spareExtra) 0)+1) =
      entryValue (number i : V) file spareExtra gap := start_source i file spareExtra gap
example (P : List Bool) (overflow : Bool) (padExtra : Nat) (file spareExtra gap : V)
    (hP : P.length ≤ 64) (hc : Clean SourceRotation240.program P) :
    targetPathValue P overflow padExtra gap
        (2*fileTape (physicalValues file) (oneBlocks (167+spareExtra) 0)+1) =
      entryValue (number (resolveControl P) : V) file spareExtra
        (gap+digit overflow+(padExtra : V)) := target_entry P overflow padExtra file spareExtra gap hP hc
example (P : List Bool) (overflow : Bool) (padExtra : Nat)
    (current time file spareExtra gap : V) (ht : 0 < time)
    (hr : ArithmeticMachineRunFromRotation240.runFrom time current =
      targetPathValue P overflow padExtra gap
        (2*fileTape (physicalValues file) (oneBlocks (167+spareExtra) 0)+1))
    (hP : P.length ≤ 64) (hc : Clean SourceRotation240.program P) :
    0 < time ∧ ArithmeticMachineRunFromRotation240.runFrom time current =
      entryValue (number (resolveControl P) : V) file spareExtra
        (gap+digit overflow+(padExtra : V)) :=
  reenter P overflow padExtra current time file spareExtra gap ht hr hP hc
example (Q : List Bool) (r : Nat)
    (hf : follow SourceRotation240.program (.node SourceRotation240.program.root) Q = some (.inc r)) :
    Clean SourceRotation240.program (incPath Q) := ArithmeticDispatchRebaseRotation240.clean_inc Q r hf
example (Q : List Bool) (r : Nat)
    (hf : follow SourceRotation240.program (.node SourceRotation240.program.root) Q = some (.decnz r)) :
    Clean SourceRotation240.program (breakPath 1 Q) := clean_decnz_zero Q r hf
example (Q : List Bool) (r : Nat)
    (hf : follow SourceRotation240.program (.node SourceRotation240.program.root) Q = some (.decnz r)) :
    Clean SourceRotation240.program (incPath Q) := clean_decnz_positive Q r hf
example (Q : List Bool) (k : Nat)
    (hf : follow SourceRotation240.program (.node SourceRotation240.program.root) Q = some (.brk k)) :
    Clean SourceRotation240.program (breakPath k Q) := clean_break Q k hf
example (Q : List Bool) (k : Nat)
    (hf : follow SourceRotation240.program (.node SourceRotation240.program.root) Q = some (.cont k)) :
    Clean SourceRotation240.program (continuePath k Q) := clean_continue Q k hf
example (Q : List Bool) (e : Edge) (positive : Bool) :
    (ArithmeticControlTable.outgoingPathOf Q e positive).length ≤ Q.length := outgoing_length Q e positive
example (i : Control) (positive overflow : Bool) (padExtra : Nat) (file spareExtra gap : V)
    (hn : (source i).2 ≠ .halt)
    (hc : Clean SourceRotation240.program
      (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive)) :
    targetPathValue (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive)
        overflow padExtra gap (2*fileTape (physicalValues file) (oneBlocks (167+spareExtra) 0)+1) =
      entryValue (nextControl i positive : V) file spareExtra (gap+digit overflow+(padExtra : V)) :=
  target_next_entry i positive overflow padExtra file spareExtra gap hn hc

-- The positive-decrement extra zero is independent of the spare count.
example (P : List Bool) (overflow : Bool) (file spareExtra gap : V)
    (hP : P.length ≤ 64) (hc : Clean SourceRotation240.program P) :
    targetPathValue P overflow 1 gap
        (2*fileTape (physicalValues file) (oneBlocks (167+spareExtra) 0)+1) =
      entryValue (number (resolveControl P) : V) file spareExtra (gap+digit overflow+1) := by
  simpa only [Nat.cast_one] using target_entry P overflow 1 file spareExtra gap hP hc
-- Increment's separate spare update may be supplied as an internal argument.
example (P : List Bool) (overflow : Bool) (file spareExtra gap : V)
    (hP : P.length ≤ 64) (hc : Clean SourceRotation240.program P) :
    targetPathValue P overflow 0 gap
        (2*fileTape (physicalValues file) (oneBlocks (167+(spareExtra+1)) 0)+1) =
      entryValue (number (resolveControl P) : V) file (spareExtra+1) (gap+digit overflow) := by
  simpa only [Nat.cast_zero,add_zero] using target_entry P overflow 0 file (spareExtra+1) gap hP hc
