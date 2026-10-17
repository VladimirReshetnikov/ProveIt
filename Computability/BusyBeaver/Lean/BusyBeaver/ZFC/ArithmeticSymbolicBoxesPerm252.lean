import BusyBeaver.ZFC.ArithmeticRegisterMarkPerm252
import BusyBeaver.ZFC.ArithmeticWritingScansPerm252

/-!
Concrete numeric prefixes for the actual SymbolicPerm252 Box datatype.
The primary file is an externally fixed list of nine arbitrary internal values.
It is followed by the fixed eight-zero/one boot suffix, an arbitrary internal
number of zero spares, and the literal final false padding of boxBits.

The local box endpoints reuse the checked literal mark, increment, zero and
positive-decrement macros. Positive decrement alone appends one zero spare.
Execution contracts fix the terminal exterior to zero; prefix algebra itself
retains an arbitrary terminal suffix. No symbolic-step checker, first exit,
internal variable-length-list graph, dispatch refinement or PA endpoint is
asserted. Mira-Cult, Jeff and Wade retain their machine/framework attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineGraphPerm252 ArithmeticMachineStepPerm252
open ArithmeticMachineRunFromPerm252 ArithmeticMachineUniformScansPerm252
open ArithmeticRegisterForwardPerm252 ArithmeticRegisterReturnPerm252
open ArithmeticZeroRegisterBlocks254 ArithmeticRegisterFilePerm252
open SymbolicPerm252 (Box Effect Reg Branch)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The fixed boot spares before the variable zero suffix. -/
def fixedSpares : List V := List.replicate 8 0 ++ [1]

/-- The multiplication by two is the explicit final false cell of boxBits. -/
noncomputable def spareTail (count suffix : V) : V :=
  fileCode fixedSpares (zeroBlocks count (2*suffix))

/-- Replacement at an externally selected index; out-of-range lists are total. -/
def writeAt : List V → Nat → V → List V
  | [], _, _ => []
  | _ :: values, 0, value => value :: values
  | first :: values, r+1, value => first :: writeAt values r value

/-- The actual marked00 header, followed by the old target's value ones. -/
noncomputable def markedPrefix : Nat → List V → V → V
  | _, [], suffix => suffix
  | 0, value :: rest, suffix => 4*bitPrefix true value (fileCode rest suffix)
  | r+1, value :: rest, suffix => registerBlock value (markedPrefix r rest suffix)

/-- A concrete interpretation of actual finite Box syntax. Its register values
and zero-spare count are internal; no arbitrary box-prefix oracle is supplied. -/
noncomputable def boxPrefix (values : List V) (count : V) : Box → V → V
  | .plain .unchanged, suffix => fileCode values (spareTail count suffix)
  | .plain (.increment r), suffix =>
      fileCode (writeAt values r.val (values.getD r.val 0+1)) (spareTail count suffix)
  | .plain (.decrement r), suffix =>
      fileCode (writeAt values r.val (values.getD r.val 0-1)) (spareTail (count+1) suffix)
  | .marked r, suffix => markedPrefix r.val values (spareTail count suffix)

lemma fileCode_append (pre rest : List V) (suffix : V) :
    fileCode (pre++rest) suffix = fileCode pre (fileCode rest suffix) := by
  induction pre with
  | nil => rfl
  | cons value pre ih => simp only [List.cons_append,fileCode,ih]

lemma getD_split (pre : List V) (value : V) (rest : List V) :
    (pre++value::rest).getD pre.length 0 = value := by
  induction pre with
  | nil => rfl
  | cons first pre ih => simpa only [List.cons_append,List.length_cons,List.getD_cons_succ] using ih

lemma writeAt_split (pre : List V) (value : V) (rest : List V) (newValue : V) :
    writeAt (pre++value::rest) pre.length newValue = pre++newValue::rest := by
  induction pre with
  | nil => rfl
  | cons first pre ih => simpa only [List.cons_append,List.length_cons,writeAt] using congrArg (List.cons first) ih

lemma writeAt_length (values : List V) (r : Nat) (newValue : V) :
    (writeAt values r newValue).length = values.length := by
  induction values generalizing r with
  | nil => rfl
  | cons first values ih => cases r <;> simp [writeAt,ih]

lemma markedPrefix_split (pre : List V) (value : V) (rest : List V) (suffix : V) :
    markedPrefix pre.length (pre++value::rest) suffix =
      fileCode pre (4*bitPrefix true value (fileCode rest suffix)) := by
  induction pre with
  | nil => rfl
  | cons first pre ih => simp only [List.cons_append,List.length_cons,markedPrefix,fileCode,ih]

/-- Only the finite selector/list structure is split externally. -/
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

lemma unchanged_split (pre : List V) (value : V) (rest : List V) (count suffix : V) :
    boxPrefix (pre++value::rest) count (.plain .unchanged) suffix =
      fileCode pre (registerBlock value (fileCode (rest++fixedSpares) (zeroBlocks count (2*suffix)))) := by
  simp only [boxPrefix,spareTail,fileCode_append,fileCode]

lemma marked_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (count suffix : V) :
    boxPrefix (pre++value::rest) count (.marked r) suffix =
      fileCode pre (4*bitPrefix true value (fileCode (rest++fixedSpares) (zeroBlocks count (2*suffix)))) := by
  simp only [boxPrefix,←hr,markedPrefix_split,spareTail,fileCode_append]

lemma increment_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (count suffix : V) :
    boxPrefix (pre++value::rest) count (.plain (.increment r)) suffix =
      fileCode pre (registerBlock (value+1) (fileCode (rest++fixedSpares) (zeroBlocks count (2*suffix)))) := by
  simp only [boxPrefix,←hr,getD_split,writeAt_split,spareTail,fileCode_append,fileCode]

lemma decrement_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (count suffix : V) :
    boxPrefix (pre++value::rest) count (.plain (.decrement r)) suffix =
      fileCode pre (registerBlock (value-1) (fileCode (rest++fixedSpares) (zeroBlocks (count+1) (2*suffix)))) := by
  simp only [boxPrefix,←hr,getD_split,writeAt_split,spareTail,fileCode_append,fileCode]

lemma fileCode_even (values : List V) (hne : values ≠ []) (suffix : V) :
    ∃ half : V, fileCode values suffix = 2*half := by
  cases values with
  | nil => exact False.elim (hne rfl)
  | cons value rest => exact ⟨bitPrefix true (value+1) (fileCode rest suffix),rfl⟩

lemma markedPrefix_even (r : Nat) (values : List V) (hne : values ≠ []) (suffix : V) :
    ∃ half : V, markedPrefix r values suffix = 2*half := by
  cases values with
  | nil => exact False.elim (hne rfl)
  | cons value rest =>
    cases r with
    | zero => exact ⟨2*bitPrefix true value (fileCode rest suffix),by simp only [markedPrefix]; ring⟩
    | succ r => exact ⟨bitPrefix true (value+1) (markedPrefix r rest suffix),rfl⟩

/-- All concrete box interpretations keep the literal leading false cell. -/
lemma boxPrefix_even (values : List V) (hlen : values.length = 9)
    (count : V) (x : Box) (suffix : V) :
    ∃ half : V, boxPrefix values count x suffix = 2*half := by
  have hne : values ≠ [] := by intro he; simp [he] at hlen
  have hwrite (r : Nat) (value : V) : writeAt values r value ≠ [] := by
    intro he
    have hw := writeAt_length values r value
    rw [he] at hw
    simp only [List.length_nil] at hw
    omega
  cases x with
  | plain effect => cases effect with
    | unchanged => exact fileCode_even values hne _
    | increment r => exact fileCode_even _ (hwrite r.val _) _
    | decrement r => exact fileCode_even _ (hwrite r.val _) _
  | marked r => exact markedPrefix_even r.val values hne _

/-- A left-moving false-write action keeps its final write and move, including
when target is the arithmetic halt state0. -/
theorem box_back (values : List V) (hlen : values.length = 9)
    (count state target left : V) (x : Box)
    (hrow : actionLookup state (digit false) = 4*target+1+digit false) :
    runFrom 1 (frame state left (boxPrefix values count x 0)) =
      leftFrame target left (boxPrefix values count x 0) := by
  obtain ⟨half,hh⟩ := boxPrefix_even values hlen count x (0 : V)
  rw [runFrom_one,hh]
  simpa only [digit,Bool.false_eq_true,if_false,add_zero] using
    step_left_row false false state target hrow left half

/-- Exact numeric mark box. Only the selector index is externally finite. -/
theorem box_mark_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (count left : V) :
    runFrom (2*fileTime pre+3)
      (frame (ArithmeticRegisterMarkPerm252.skipCode r.val : V) left
        (boxPrefix (pre++value::rest) count (.plain .unchanged) 0)) =
      leftFrame (ArithmeticRegisterMarkPerm252.markExit pre) left
        (boxPrefix (pre++value::rest) count (.marked r) 0) := by
  simpa only [unchanged_split,marked_split pre value rest r hr,mul_zero,hr] using
    ArithmeticRegisterMarkPerm252.mark_file pre (by have := r.isLt; omega) value left
      (fileCode (rest++fixedSpares) (zeroBlocks count 0))

/-- Increment retains every spare and the explicit final padding. -/
theorem box_increment_split (pre : List V) (value : V) (rest : List V) (r : Reg)
    (hr : pre.length = r.val) (count left : V) :
    runFrom (2*fileTime pre+2*value+2*fileTime (rest++fixedSpares)+4*count+7)
      (frame 72 left (boxPrefix (pre++value::rest) count (.marked r) 0)) =
      leftFrame 48 left
        (boxPrefix (pre++value::rest) count (.plain (.increment r)) 0) := by
  simpa only [marked_split pre value rest r hr,increment_split pre value rest r hr,mul_zero] using
    increment_zip pre (rest++fixedSpares) value count left

/-- The original selected value is literally zero; the spare count is unchanged. -/
theorem box_zero_split (pre rest : List V) (r : Reg)
    (hr : pre.length = r.val) (count left : V) :
    runFrom (2*fileTime pre+5)
      (frame 43 left (boxPrefix (pre++(0 : V)::rest) count (.marked r) 0)) =
      leftFrame 5 left
        (boxPrefix (pre++(0 : V)::rest) count (.plain .unchanged) 0) := by
  simpa only [marked_split pre (0 : V) rest r hr,unchanged_split,mul_zero,bitPrefix_zero] using
    ArithmeticRegisterZeroPerm252.zero_decrement pre (rest++fixedSpares) count left

/-- A positive original value loses exactly one, while one zero spare is appended. -/
theorem box_positive_split (pre rest : List V) (value : V) (r : Reg)
    (hr : pre.length = r.val) (count left : V) :
    runFrom (2*fileTime pre+2*value+2*fileTime (rest++fixedSpares)+4*count+9)
      (frame 43 left (boxPrefix (pre++(value+1)::rest) count (.marked r) 0)) =
      leftFrame (ArithmeticRegisterDecrementPerm252.positiveExit pre) left
        (boxPrefix (pre++(value+1)::rest) count (.plain (.decrement r)) 0) := by
  simpa only [marked_split pre (value+1) rest r hr,
    decrement_split pre (value+1) rest r hr,mul_zero,add_tsub_cancel_right] using
    ArithmeticRegisterDecrementPerm252.positive_decrement pre (rest++fixedSpares) value count left

/-- Numeric codes of the actual native finite-state constructors. -/
noncomputable def stateValue (q : Option (Fin 252)) : V :=
  (ArithmeticMachinePerm252.stateCode q : Nat)

private theorem skip_state_facts : ∀ r : Reg,
    ArithmeticMachinePerm252.stateCode (some (RegisterMarkPerm252.skip r.val)) =
      ArithmeticRegisterMarkPerm252.skipCode r.val := by decide
private theorem mark_state_facts : ∀ r : Reg,
    ArithmeticMachinePerm252.stateCode (some (SymbolicPerm252.markExit r)) =
      if r.val = 0 then 4 else 7 := by decide
private theorem positive_state_facts : ∀ r : Reg,
    ArithmeticMachinePerm252.stateCode (some (SymbolicPerm252.positiveExit r)) =
      if r.val = 0 then 63 else 48 := by decide

lemma state_skip (r : Reg) :
    stateValue (V := V) (some (RegisterMarkPerm252.skip r.val)) =
      (ArithmeticRegisterMarkPerm252.skipCode r.val : V) := by
  simp only [stateValue,skip_state_facts]

lemma state_mark_exit (pre : List V) (r : Reg) (hr : pre.length = r.val) :
    stateValue (some (SymbolicPerm252.markExit r)) =
      ArithmeticRegisterMarkPerm252.markExit pre := by
  simp only [stateValue,mark_state_facts,←hr]
  cases pre <;> simp [ArithmeticRegisterMarkPerm252.markExit,Nat.cast_ofNat]

lemma state_positive_exit (pre : List V) (r : Reg) (hr : pre.length = r.val) :
    stateValue (some (SymbolicPerm252.positiveExit r)) =
      ArithmeticRegisterDecrementPerm252.positiveExit pre := by
  simp only [stateValue,positive_state_facts,←hr]
  cases pre <;> simp [ArithmeticRegisterDecrementPerm252.positiveExit,Nat.cast_ofNat]

@[simp] lemma state_seek_inc :
    stateValue (V := V) (some RegisterIncrementPerm252.seekInc) = 72 := by
  simp [stateValue,ArithmeticMachinePerm252.stateCode,RegisterIncrementPerm252.seekInc,Nat.cast_ofNat]
@[simp] lemma state_inc_return :
    stateValue (V := V) (some RegisterIncrementPerm252.incReturnZero) = 48 := by
  simp [stateValue,ArithmeticMachinePerm252.stateCode,RegisterIncrementPerm252.incReturnZero,Nat.cast_ofNat]
@[simp] lemma state_seek_dec :
    stateValue (V := V) (some RegisterBoxesPerm252.seekDec) = 43 := by
  simp [stateValue,ArithmeticMachinePerm252.stateCode,RegisterBoxesPerm252.seekDec,Nat.cast_ofNat]
@[simp] lemma state_zero_return :
    stateValue (V := V) (some RegisterBoxesPerm252.returnZero) = 5 := by
  simp [stateValue,ArithmeticMachinePerm252.stateCode,RegisterBoxesPerm252.returnZero,Nat.cast_ofNat]

/-- The actual Branch guard on the original nine physical primary values.
This restricts the native length-at-least-nine interface to the fixed nine-field
representation; appended spare values are not selectable registers. -/
def ValidValues (br : Branch) (values : List V) : Prop :=
  values.length = 9 ∧ match br with
    | none => True
    | some (r,zero) => if zero then values.getD r.val 0 = 0 else values.getD r.val 0 ≠ 0

/-- The exact native mark source/target constructors, with an internal clock. -/
theorem box_mark (br : Branch) (values : List V) (hv : ValidValues br values)
    (r : Reg) (count left : V) :
    ∃ time : V, runFrom time
      (frame (stateValue (some (RegisterMarkPerm252.skip r.val))) left
        (boxPrefix values count (.plain .unchanged) 0)) =
      leftFrame (stateValue (some (SymbolicPerm252.markExit r))) left
        (boxPrefix values count (.marked r) 0) := by
  obtain ⟨pre,value,rest,he,hl,_⟩ := split_register r.val values (by
    have := r.isLt; have := hv.1; omega)
  rw [he]
  refine ⟨2*fileTime pre+3,?_⟩
  rw [state_skip,state_mark_exit pre r hl]
  exact box_mark_split pre value rest r hl count left

/-- Native increment always returns to incReturnZero, including selector zero. -/
theorem box_increment (br : Branch) (values : List V) (hv : ValidValues br values)
    (r : Reg) (count left : V) :
    ∃ time : V, runFrom time
      (frame (stateValue (some RegisterIncrementPerm252.seekInc)) left
        (boxPrefix values count (.marked r) 0)) =
      leftFrame (stateValue (some RegisterIncrementPerm252.incReturnZero)) left
        (boxPrefix values count (.plain (.increment r)) 0) := by
  obtain ⟨pre,value,rest,he,hl,_⟩ := split_register r.val values (by
    have := r.isLt; have := hv.1; omega)
  rw [he]
  refine ⟨2*fileTime pre+2*value+2*fileTime (rest++fixedSpares)+4*count+7,?_⟩
  simpa only [state_seek_inc,state_inc_return] using
    box_increment_split pre value rest r hl count left

/-- The literal zero guard is checked on the original primary value. -/
theorem box_zero_decrement (values : List V) (r : Reg)
    (hv : ValidValues (some (r,true)) values) (count left : V) :
    ∃ time : V, runFrom time
      (frame (stateValue (some RegisterBoxesPerm252.seekDec)) left
        (boxPrefix values count (.marked r) 0)) =
      leftFrame (stateValue (some RegisterBoxesPerm252.returnZero)) left
        (boxPrefix values count (.plain .unchanged) 0) := by
  obtain ⟨pre,value,rest,he,hl,hvalue⟩ := split_register r.val values (by
    have := r.isLt; have := hv.1; omega)
  have hz : value = 0 := hvalue.symm.trans hv.2
  rw [hz] at he
  rw [he]
  refine ⟨2*fileTime pre+5,?_⟩
  simpa only [state_seek_dec,state_zero_return] using
    box_zero_split pre rest r hl count left

/-- The positive guard licenses the only box effect which appends a spare. -/
theorem box_positive_decrement (values : List V) (r : Reg)
    (hv : ValidValues (some (r,false)) values) (count left : V) :
    ∃ time : V, runFrom time
      (frame (stateValue (some RegisterBoxesPerm252.seekDec)) left
        (boxPrefix values count (.marked r) 0)) =
      leftFrame (stateValue (some (SymbolicPerm252.positiveExit r))) left
        (boxPrefix values count (.plain (.decrement r)) 0) := by
  obtain ⟨pre,value,rest,he,hl,hvalue⟩ := split_register r.val values (by
    have := r.isLt; have := hv.1; omega)
  have hn : value ≠ 0 := by intro hz; exact hv.2 (hvalue.trans hz)
  rcases zero_or_succ value with hz | ⟨value,rfl⟩
  · exact False.elim (hn hz)
  · rw [he]
    refine ⟨2*fileTime pre+2*value+2*fileTime (rest++fixedSpares)+4*count+9,?_⟩
    rw [state_seek_dec,state_positive_exit pre r hl]
    exact box_positive_split pre rest value r hl count left

end SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicBoxesPerm252
