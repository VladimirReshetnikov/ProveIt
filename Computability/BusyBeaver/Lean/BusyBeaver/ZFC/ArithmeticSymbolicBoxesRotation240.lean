import BusyBeaver.ZFC.ArithmeticCarryTraversalRotation240
import BusyBeaver.ZFC.SymbolicRotation240

set_option autoImplicit false

/-!
Pure numeric prefixes for the actual Rotation240 symbolic boxes. There are
nine physical register values and an arbitrary internal extra-spare count;
the permanent 167 value-one blocks remain explicit in every interpretation.
Increment adds one value-one spare, whereas decrement preserves the count.
The positive-decrement boundary shift belongs to the symbolic left tape.

All prefix equalities allow an arbitrary numeric exterior. This algebra does
not assert a machine endpoint for a nonzero exterior, a first-exit property,
a complete simulation or an internal PA consistency result. The finite list
proofs follow ArithmeticSymbolicBoxesPerm252; no old machine or spare-file
semantics are used. Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt
retain attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 (registerBlock)
open ArithmeticOneRegisterBlocksRotation240
open ArithmeticCarryTraversalRotation240
open SymbolicRotation240 (Box Reg Branch)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Extra spares supplement the permanent 167 value-one blocks. -/
noncomputable def spareTail (extra suffix : V) : V := oneBlocks (167+extra) suffix

/-- Replacement at a finite physical selector, total on all lists. -/
def writeAt : List V → Nat → V → List V
  | [], _, _ => []
  | _ :: values, 0, value => value :: values
  | first :: values, r+1, value => first :: writeAt values r value

/-- The target header is 00, followed by its unchanged unary value. -/
noncomputable def markedPrefix : Nat → List V → V → V
  | _, [], suffix => suffix
  | 0, value :: rest, suffix => 4*bitPrefix true value (fileTape rest suffix)
  | r+1, value :: rest, suffix => registerBlock value (markedPrefix r rest suffix)

/-- Concrete interpretation of the existing Box datatype, without padding. -/
noncomputable def boxPrefix (values : List V) (extra : V) : Box → V → V
  | .plain .unchanged, suffix => fileTape values (spareTail extra suffix)
  | .plain (.increment r), suffix =>
      fileTape (writeAt values r.val (values.getD r.val 0+1)) (spareTail (extra+1) suffix)
  | .plain (.decrement r), suffix =>
      fileTape (writeAt values r.val (values.getD r.val 0-1)) (spareTail extra suffix)
  | .marked r, suffix => markedPrefix r.val values (spareTail extra suffix)

/-- Internal values at nine external physical positions; no spare premise. -/
def ValidValues (br : Branch) (values : List V) : Prop :=
  values.length = 9 ∧ match br with
  | none => True
  | some (r, zero) => if zero then values.getD r.val 0 = 0 else values.getD r.val 0 ≠ 0

lemma fileTape_append (pre rest : List V) (suffix : V) :
    fileTape (pre++rest) suffix = fileTape pre (fileTape rest suffix) := by
  induction pre with
  | nil => rfl
  | cons value pre ih => simp only [List.cons_append,fileTape,ih]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma getD_split (pre : List V) (value : V) (rest : List V) :
    (pre++value::rest).getD pre.length 0 = value := by
  induction pre with
  | nil => rfl
  | cons first pre ih => simpa only [List.cons_append,List.length_cons,List.getD_cons_succ] using ih

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma writeAt_split (pre : List V) (value : V) (rest : List V) (newValue : V) :
    writeAt (pre++value::rest) pre.length newValue = pre++newValue::rest := by
  induction pre with
  | nil => rfl
  | cons first pre ih => simpa only [List.cons_append,List.length_cons,writeAt] using congrArg (List.cons first) ih

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
lemma writeAt_length (values : List V) (r : Nat) (newValue : V) :
    (writeAt values r newValue).length = values.length := by
  induction values generalizing r with
  | nil => rfl
  | cons first values ih => cases r <;> simp [writeAt,ih]

lemma markedPrefix_split (pre : List V) (value : V) (rest : List V) (suffix : V) :
    markedPrefix pre.length (pre++value::rest) suffix =
      fileTape pre (4*bitPrefix true value (fileTape rest suffix)) := by
  induction pre with
  | nil => rfl
  | cons first pre ih => simp only [List.cons_append,List.length_cons,markedPrefix,fileTape,ih]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The list structure and selector are finite; the values are internal. -/
lemma split_register (r : Nat) (values : List V) (hr : r < values.length) :
    ∃ pre value rest, values = pre++value::rest ∧ pre.length = r ∧
      values.getD r 0 = value := by
  induction r generalizing values with
  | zero =>
    cases values with
    | nil => simp at hr
    | cons value rest => exact ⟨[],value,rest,rfl,rfl,rfl⟩
  | succ r ih =>
    cases values with
    | nil => simp at hr
    | cons first values =>
      obtain ⟨pre,value,rest,he,hl,hv⟩ := ih values (by simpa using hr)
      exact ⟨first::pre,value,rest,by simp [he],by simp [hl],hv⟩

/-- Even the last physical register has a following complete one block. -/
lemma spareTail_first (extra suffix : V) :
    spareTail extra suffix = registerBlock 1 (oneBlocks (166+extra) suffix) := by
  unfold spareTail
  rw [show (167+extra : V) = (166+extra)+1 by ring,
    oneBlocks_succ, registerBlock_one]

/-- Appending a one block at the far end increases only the extra count. -/
lemma spareTail_push (extra suffix : V) :
    spareTail extra (registerBlock 1 suffix) = spareTail (extra+1) suffix := by
  unfold spareTail
  rw [registerBlock_one, oneBlocks_push]
  exact congrArg (fun n : V => oneBlocks n suffix)
    (show (167+extra)+1 = 167+(extra+1) by ring)

lemma unchanged_split (pre : List V) (value : V) (rest : List V) (extra suffix : V) :
    boxPrefix (pre++value::rest) extra (.plain .unchanged) suffix =
      fileTape pre (registerBlock value (fileTape rest (spareTail extra suffix))) := by
  simp only [boxPrefix,fileTape_append,fileTape]

lemma marked_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (extra suffix : V) :
    boxPrefix (pre++value::rest) extra (.marked r) suffix =
      fileTape pre (4*bitPrefix true value (fileTape rest (spareTail extra suffix))) := by
  simp only [boxPrefix,←hr,markedPrefix_split]

lemma increment_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (extra suffix : V) :
    boxPrefix (pre++value::rest) extra (.plain (.increment r)) suffix =
      fileTape pre (registerBlock (value+1) (fileTape rest (spareTail (extra+1) suffix))) := by
  simp only [boxPrefix,←hr,getD_split,writeAt_split,fileTape_append,fileTape]

lemma decrement_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (extra suffix : V) :
    boxPrefix (pre++value::rest) extra (.plain (.decrement r)) suffix =
      fileTape pre (registerBlock (value-1) (fileTape rest (spareTail extra suffix))) := by
  simp only [boxPrefix,←hr,getD_split,writeAt_split,fileTape_append,fileTape]

lemma decrement_positive_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (extra suffix : V) :
    boxPrefix (pre++(value+1)::rest) extra (.plain (.decrement r)) suffix =
      fileTape pre (registerBlock value (fileTape rest (spareTail extra suffix))) := by
  simpa only [add_tsub_cancel_right] using
    decrement_split pre (value+1) rest r hr extra suffix

lemma fileTape_even (values : List V) (hne : values ≠ []) (suffix : V) :
    ∃ half : V, fileTape values suffix = 2*half := by
  cases values with
  | nil => exact False.elim (hne rfl)
  | cons value rest => exact ⟨bitPrefix true (value+1) (fileTape rest suffix),rfl⟩

lemma markedPrefix_even (r : Nat) (values : List V) (hne : values ≠ []) (suffix : V) :
    ∃ half : V, markedPrefix r values suffix = 2*half := by
  cases values with
  | nil => exact False.elim (hne rfl)
  | cons value rest =>
    cases r with
    | zero => exact ⟨2*bitPrefix true value (fileTape rest suffix),by simp only [markedPrefix]; ring⟩
    | succ r => exact ⟨bitPrefix true (value+1) (markedPrefix r rest suffix),rfl⟩

/-- Every concrete box retains its literal leading false cell. -/
lemma boxPrefix_even (values : List V) (hlen : values.length = 9)
    (extra : V) (x : Box) (suffix : V) :
    ∃ half : V, boxPrefix values extra x suffix = 2*half := by
  have hne : values ≠ [] := by intro he; simp [he] at hlen
  have hwrite (r : Nat) (value : V) : writeAt values r value ≠ [] := by
    intro he
    have hw := writeAt_length values r value
    rw [he] at hw
    simp only [List.length_nil] at hw
    omega
  cases x with
  | plain effect => cases effect with
    | unchanged => exact fileTape_even values hne _
    | increment r => exact fileTape_even _ (hwrite r.val _) _
    | decrement r => exact fileTape_even _ (hwrite r.val _) _
  | marked r => exact markedPrefix_even r.val values hne _

end SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesRotation240
