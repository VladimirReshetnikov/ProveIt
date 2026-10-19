import BusyBeaver.ZFC.ControlCatalogueRotation240

set_option autoImplicit false

/-!
Exact represented step equations for the checked Rotation240 control table.
The catalogue has 6,455 external finite entries; file values are arbitrary
IΣ₁-model elements. These equations use the checked table identity and the
catalogue-generic step theorem, without reducing the large literal table.
They do not assert a binary simulation. Source/program/framework attribution
remains with Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath
open ArithmeticControlFile ArithmeticControlTable
open ControlCatalogueRotation240

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The physical selector of the actual source instruction. -/
def physical (i : Control) : Fin 9 := ⟨registerOf (source i).2,registerOf_lt _⟩

private theorem opcode_get (rl : List ArithmeticControlBisim.Row) (n : Nat)
    (row : ArithmeticControlBisim.Row) (h : rl[n]? = some row) :
    opcodeValue rl ((n+1 : Nat) : V) = (row.op : V) := by
  have hn : n < rl.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at h
    cases h
  rw [List.getElem?_eq_getElem hn,Option.some.injEq] at h
  rw [opcodeValue_at n hn,h]

theorem opcode_at (i : Control) :
    opcodeValue table (number i : V) = (edgeOpcode (source i).2 : V) :=
  opcode_get table i.val (rowOf TreeRotation240.tree (source i)) (table_row_at i)

theorem opcode_nonzero (i : Control) : opcodeValue table (number i : V) ≠ 0 := by
  rw [opcode_at]
  cases he : (source i).2 with
  | node n => exact False.elim (source_not_node i n he)
  | inc r => simp [edgeOpcode]
  | decnz r => simp [edgeOpcode]
  | brk k => simp [edgeOpcode]
  | cont k => simp [edgeOpcode]
  | halt => simp [edgeOpcode]

/-- The four fields of the actual packed row drive the represented step. -/
theorem step_at (i : Control) (file : V) :
    stepValue table (liveValue (number i : V) file) =
      ArithmeticControlBisim.sem regValue write liveValue
        ⟨edgeOpcode (source i).2,physical i,nextControl i false,nextControl i true⟩ file := by
  apply spec_get table (number i) (rowOf TreeRotation240.tree (source i)) file (by
    simp only [number]; omega)
  simpa only [number,Nat.add_sub_cancel] using table_row_at i

theorem step_inc (i : Control) (r : Nat) (he : (source i).2 = .inc r) (file : V) :
    stepValue table (liveValue (number i : V) file) =
      liveValue (nextControl i false : V)
        (write (physical i) (regValue file (physical i)+1) file) := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,if_true]

theorem step_decnz_zero (i : Control) (r : Nat) (he : (source i).2 = .decnz r)
    (file : V) (hz : regValue file (physical i) = 0) :
    stepValue table (liveValue (number i : V) file) =
      liveValue (nextControl i false : V) file := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,show (2 : Nat) ≠ 1 by decide,
    if_false,if_true,hz]

theorem step_decnz_positive (i : Control) (r : Nat) (he : (source i).2 = .decnz r)
    (file : V) (hn : regValue file (physical i) ≠ 0) :
    stepValue table (liveValue (number i : V) file) =
      liveValue (nextControl i true : V)
        (write (physical i) (regValue file (physical i)-1) file) := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,show (2 : Nat) ≠ 1 by decide,
    if_false,if_true,hn]

theorem step_break (i : Control) (k : Nat) (he : (source i).2 = .brk k) (file : V) :
    stepValue table (liveValue (number i : V) file) =
      liveValue (nextControl i false : V) file := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,show (3 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 2 by decide,if_false,if_true]

theorem step_continue (i : Control) (k : Nat) (he : (source i).2 = .cont k) (file : V) :
    stepValue table (liveValue (number i : V) file) =
      liveValue (nextControl i false : V) file := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,show (3 : Nat) ≠ 1 by decide,
    show (3 : Nat) ≠ 2 by decide,if_false,if_true]

theorem step_halt (i : Control) (he : (source i).2 = .halt) (file : V) :
    stepValue table (liveValue (number i : V) file) = 0 := by
  rw [step_at]
  simp only [ArithmeticControlBisim.sem,he,edgeOpcode,show (4 : Nat) ≠ 1 by decide,
    show (4 : Nat) ≠ 2 by decide,show (4 : Nat) ≠ 3 by decide,if_false]

/-- Every nonhalting source resolves to a live catalogue control. -/
theorem next_opcode_nonzero (i : Control) (positive : Bool) (hn : (source i).2 ≠ .halt) :
    opcodeValue table (nextControl i positive : V) ≠ 0 := by
  rw [nextControl_number i positive hn]
  exact opcode_nonzero _

end SetTheory.BusyBeaver.ZFC.ArithmeticControlStepRotation240
