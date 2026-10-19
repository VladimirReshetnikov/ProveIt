import BusyBeaver.ZFC.ArithmeticFiniteTapeRotation240
import BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252
import BusyBeaver.ZFC.ArithmeticControlFrameDataRotation240
import BusyBeaver.ZFC.RuntimeInstanceRotation240

set_option autoImplicit false

/-!
Exact consumed-path padding for Rotation240's canonical arithmetic frame.
The state is 85 and the fixed PC margin is 64. The additional finite zero
padding `padExtra` is distinct from the internal count `spareExtra` of extra
value-one register blocks. In particular positive decrement uses padExtra=1
without adding a spare, whereas increment's spare update belongs to the box
interpretation. Every numeric equality preserves the complete tape suffix.

Only finite paths are external; numeric files, spares, gaps and clocks range
over arbitrary IΣ1-model elements. The conditional reentry theorem assumes
the actual numeric runtime endpoint. It does not prove box execution, checker
soundness, a complete internal simulation, or a PA consistency endpoint.
The path proof follows ArithmeticDispatchRebasePerm252; only its pure checked
bitPrefix algebra is imported. Mira-Cult, Jeff Ketchersid, Andrew James Wade
and ProveIt retain their source/program/simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath RegisterPathClean
open ArithmeticMachineUniformScansPerm252
open ArithmeticFiniteTapeRotation240 (bitsPrefix bitsPrefix_append bitPrefix_replicate)
open ArithmeticSymbolicTapePerm252 (bitPrefix_add)
open ArithmeticCarryTraversalRotation240 (fileTape)
open ArithmeticOneRegisterBlocksRotation240 (oneBlocks)
open ControlCatalogueRotation240
open ArithmeticControlFrameDataRotation240 (physicalValues entryValue)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def padded (P : List Bool) (N : Nat) : List Bool :=
  P ++ List.replicate (N-P.length) false

def budget (overflow : Bool) (padExtra : Nat) : Nat :=
  64+overflow.toNat+padExtra

theorem budget_ge (overflow : Bool) (padExtra : Nat) : 64 ≤ budget overflow padExtra := by
  unfold budget
  omega

/-- The complete outgoing PC, gap, marker and arbitrary suffix. -/
noncomputable def targetPathValue (P : List Bool) (overflow : Bool)
    (padExtra : Nat) (gap header : V) : V :=
  frame 85 1 (bitsPrefix P
    (bitPrefix false (gap+((budget overflow padExtra-P.length : Nat) : V)) header))

noncomputable def startPathValue (P : List Bool) (gap header : V) : V :=
  frame 85 1 (bitsPrefix P
    (bitPrefix false (gap+((64-P.length : Nat) : V)) header))

theorem padded_prefix (P : List Bool) (N : Nat) (gap header : V) :
    bitsPrefix P (bitPrefix false (gap+((N-P.length : Nat) : V)) header) =
      bitsPrefix (padded P N) (bitPrefix false gap header) := by
  rw [padded,bitsPrefix_append,←bitPrefix_replicate,←bitPrefix_add]
  rw [add_comm gap]

/-- Numeric PC plus its exact finite-width suffix contribution. -/
theorem bitsPrefix_affine (P : List Bool) (suffix : V) :
    bitsPrefix P suffix = ArithmeticControlTable.binaryValue P +
      bitPrefix false (P.length : V) suffix := by
  induction P with
  | nil => simp [bitsPrefix,ArithmeticControlTable.binaryValue]
  | cons b P ih =>
    rw [bitsPrefix,ih,List.length_cons,Nat.cast_succ,bitPrefix_succ]
    cases b <;> simp only [ArithmeticControlTable.binaryValue,digit,
      Bool.false_eq_true,if_false,if_true] <;> ring

theorem start_format (P : List Bool) (gap header : V) (hP : P.length ≤ 64) :
    startPathValue P gap header =
      frame 85 1 (ArithmeticControlTable.binaryValue P +
        bitPrefix false (64 : V) (bitPrefix false gap header)) := by
  have hn : P.length+(64-P.length) = 64 := Nat.add_sub_of_le hP
  have hv : (P.length : V)+(gap+((64-P.length : Nat) : V)) = (64 : V)+gap := by
    calc
      _ = ((P.length+(64-P.length) : Nat) : V)+gap := by rw [Nat.cast_add]; ring
      _ = _ := by rw [hn]; rfl
  rw [startPathValue,bitsPrefix_affine,←bitPrefix_add,hv,bitPrefix_add]

/-- Finite padding equality rebases the entire numeric configuration. -/
theorem target_rebase (P Q : List Bool) (overflow : Bool) (padExtra : Nat)
    (gap header : V) (hQ : Q.length ≤ 64)
    (hp : padded P (budget overflow padExtra) = padded Q (budget overflow padExtra)) :
    targetPathValue P overflow padExtra gap header =
      startPathValue Q (gap+digit overflow+(padExtra : V)) header := by
  have hn : budget overflow padExtra-Q.length =
      overflow.toNat+padExtra+(64-Q.length) := by unfold budget; omega
  have hc : (overflow.toNat : V) = digit (V := V) overflow := by
    cases overflow <;> simp [digit]
  rw [targetPathValue,padded_prefix,hp,←padded_prefix,startPathValue,hn,
    Nat.cast_add,Nat.cast_add,hc]
  congr 3
  ring

/-- Closed coverage supplies the accepted consumed path, including zero
extension. Clean supplies precisely the zero suffix needed for whole-tape
padding equality; no assumption about intermediate binary controls is used. -/
theorem next_checked (P : List Bool) (overflow : Bool) (padExtra : Nat)
    (hP : P.length ≤ 64) (hc : Clean SourceRotation240.program P) :
    ∃ e d, walk SourceRotation240.program (SourceRotation240.program.nnodes+1)
        SourceRotation240.program.root P 0 = some (e,d) ∧
      follow SourceRotation240.program (.node SourceRotation240.program.root) (consume P d) = some e ∧
      SiteRotation240.checkSite (consume P d) e = true ∧
      (consume P d).length ≤ 64 ∧
      padded P (budget overflow padExtra) = padded (consume P d) (budget overflow padExtra) := by
  obtain ⟨e,d,hw⟩ := SitesRotation240.actual_walk_exists P
  have hs := SitesRotation240.actual_walk_checked P e d hw
  have hd : d ≤ 64 := by
    simpa only [consume_length,SiteRotation240.minDistance] using SiteRotation240.checkSite_length _ _ hs
  have hb := budget_ge overflow padExtra
  have hz := RuntimeInstanceRotation240.clean_suffix SourceRotation240.program P e d hc hw
  have hp := gap_consume P (budget overflow padExtra-P.length) d (by omega) hz
  have hh : P.length+(budget overflow padExtra-P.length) = budget overflow padExtra := by omega
  refine ⟨e,d,hw,walk_follow_consume SourceRotation240.program P e d hw,
    hs,by simpa only [consume_length] using hd,?_⟩
  simpa only [padded,consume_length,hh] using hp

theorem start_source (i : Control) (file spareExtra gap : V) :
    startPathValue (source i).1 gap
        (2*fileTape (physicalValues file) (oneBlocks (167+spareExtra) 0)+1) =
      entryValue (number i : V) file spareExtra gap := by
  rw [start_format _ _ _ (source_length i),ArithmeticControlFrameDataRotation240.entry_at]

/-- Exact accepted-control entry, with the whole updated register file and
spare tail supplied explicitly rather than inferred from the control rank. -/
theorem target_entry (P : List Bool) (overflow : Bool) (padExtra : Nat)
    (file spareExtra gap : V) (hP : P.length ≤ 64)
    (hc : Clean SourceRotation240.program P) :
    targetPathValue P overflow padExtra gap
        (2*fileTape (physicalValues file) (oneBlocks (167+spareExtra) 0)+1) =
      entryValue (number (resolveControl P) : V) file spareExtra
        (gap+digit overflow+(padExtra : V)) := by
  obtain ⟨e,d,hw,_,_,hd,hpad⟩ := next_checked P overflow padExtra hP hc
  have hp : (source (resolveControl P)).1 = consume P d :=
    congrArg Prod.fst (resolve_source P e d hw)
  have he := start_source (resolveControl P) file spareExtra
    (gap+digit overflow+(padExtra : V))
  rw [hp] at he
  exact (target_rebase P (consume P d) overflow padExtra gap _ hd hpad).trans he

/-- Conditional on the numeric instruction endpoint, the same positive
internal clock reaches the represented canonical frame. -/
theorem reenter (P : List Bool) (overflow : Bool) (padExtra : Nat)
    (current time file spareExtra gap : V) (ht : 0 < time)
    (hr : ArithmeticMachineRunFromRotation240.runFrom time current =
      targetPathValue P overflow padExtra gap
        (2*fileTape (physicalValues file) (oneBlocks (167+spareExtra) 0)+1))
    (hP : P.length ≤ 64) (hc : Clean SourceRotation240.program P) :
    0 < time ∧ ArithmeticMachineRunFromRotation240.runFrom time current =
      entryValue (number (resolveControl P) : V) file spareExtra
        (gap+digit overflow+(padExtra : V)) :=
  ⟨ht,hr.trans (target_entry P overflow padExtra file spareExtra gap hP hc)⟩

/-- Dummy external registers select the path branch only. Internal arithmetic
register values are neither converted to naturals nor constrained here. -/
theorem clean_inc (Q : List Bool) (r : Nat)
    (hf : follow SourceRotation240.program (.node SourceRotation240.program.root) Q = some (.inc r)) :
    Clean SourceRotation240.program (incPath Q) :=
  execute_clean SourceRotation240.program (.inc r) Q (fun _ => 0)
    ⟨incPath Q,update (fun _ => 0) r 1⟩ hf rfl

theorem clean_decnz_zero (Q : List Bool) (r : Nat)
    (hf : follow SourceRotation240.program (.node SourceRotation240.program.root) Q = some (.decnz r)) :
    Clean SourceRotation240.program (breakPath 1 Q) :=
  execute_clean SourceRotation240.program (.decnz r) Q (fun _ => 0)
    ⟨breakPath 1 Q,fun _ => 0⟩ hf rfl

theorem clean_decnz_positive (Q : List Bool) (r : Nat)
    (hf : follow SourceRotation240.program (.node SourceRotation240.program.root) Q = some (.decnz r)) :
    Clean SourceRotation240.program (incPath Q) :=
  execute_clean SourceRotation240.program (.decnz r) Q (fun _ => 1)
    ⟨incPath Q,update (fun _ => 1) r 0⟩ hf rfl

theorem clean_break (Q : List Bool) (k : Nat)
    (hf : follow SourceRotation240.program (.node SourceRotation240.program.root) Q = some (.brk k)) :
    Clean SourceRotation240.program (breakPath k Q) :=
  execute_clean SourceRotation240.program (.brk k) Q (fun _ => 0)
    ⟨breakPath k Q,fun _ => 0⟩ hf rfl

theorem clean_continue (Q : List Bool) (k : Nat)
    (hf : follow SourceRotation240.program (.node SourceRotation240.program.root) Q = some (.cont k)) :
    Clean SourceRotation240.program (continuePath k Q) :=
  execute_clean SourceRotation240.program (.cont k) Q (fun _ => 0)
    ⟨continuePath k Q,fun _ => 0⟩ hf rfl

theorem outgoing_length (Q : List Bool) (e : Edge) (positive : Bool) :
    (ArithmeticControlTable.outgoingPathOf Q e positive).length ≤ Q.length := by
  cases e with
  | node _ | halt => exact Nat.le_refl _
  | inc _ => exact le_of_eq (InstructionRotation240.incPath_length Q)
  | decnz _ =>
      cases positive
      · exact InstructionRotation240.breakPath_length 1 Q
      · exact le_of_eq (InstructionRotation240.incPath_length Q)
  | brk k => exact InstructionRotation240.breakPath_length k Q
  | cont k => exact InstructionRotation240.continuePath_length k Q

/-- The control number is the actual packed-table successor. The missing
instruction/box runtime obligation remains the explicit endpoint hypothesis
when this equality is used with `reenter`. -/
theorem target_next_entry (i : Control) (positive overflow : Bool) (padExtra : Nat)
    (file spareExtra gap : V) (hn : (source i).2 ≠ .halt)
    (hc : Clean SourceRotation240.program
      (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive)) :
    targetPathValue (ArithmeticControlTable.outgoingPathOf (source i).1 (source i).2 positive)
        overflow padExtra gap (2*fileTape (physicalValues file) (oneBlocks (167+spareExtra) 0)+1) =
      entryValue (nextControl i positive : V) file spareExtra
        (gap+digit overflow+(padExtra : V)) := by
  rw [nextControl_number i positive hn]
  exact target_entry _ overflow padExtra file spareExtra gap
    (le_trans (outgoing_length _ _ _) (source_length i)) hc

end SetTheory.BusyBeaver.ZFC.ArithmeticDispatchRebaseRotation240
