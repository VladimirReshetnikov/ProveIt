import DiophantineConsistency.ArithmeticUnaryRecursion
import DiophantineConsistency.ArithmeticCommandReplacePerm222
import Foundation.FirstOrder.Arithmetic.HFS.PRF

/-!
Represented append for the shifted actual permuted C222 command-word codec.
The public graphs have order (out,left,right). A single right parameter is
retained throughout primitive recursion; history index0 stores that right
word, and raw index z appends the entry for shifted word z+1.

All internal statements assume IΣ1. All out-of-range history lookups retain default0.
The finite-list adapter uses actual EnumPerm.pack with the correct permutation. No compiler execution
contract or PA nonhalting/consistency equivalence is inferred here.
-/
namespace DiophantineConsistency.ArithmeticCommandAppendPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCommandWordPerm222 ArithmeticCommandReplacePerm222
set_option autoImplicit false
set_option Elab.async false

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The predecessor index is already a RAW command code: do not subtract again. -/
noncomputable def stepValue (previous raw : V) : V :=
  replaceValue raw (znth previous (tailValue raw)) + 1

def stepDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out previous raw. ∃ tail, !tailDef tail raw ∧
    ∃ child, !znthDef child previous tail ∧
    ∃ replaced, !replaceDef replaced raw child ∧ out = replaced + 1”

instance step_defined : 𝚺₁-Function₂[V] stepValue via stepDef :=
  .mk fun e => by simp [stepDef, stepValue]

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma
  “s right. !mkSeq₁Def s right”

/-- PR.Construction orders its successor graph as output/previous/index/params. -/
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “s previous index right. ∃ value, !stepDef value previous index ∧
    !seqConsDef s previous value”

def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef

noncomputable def construction : PR.Construction V blueprint where
  zero parameters := seqCons ∅ (parameters 0)
  succ _ index previous := seqCons previous (stepValue previous index)
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

/-- History entry i is append(i,right); entry0 is right itself. -/
noncomputable def history (left right : V) : V :=
  construction.result ![right] left

def historyDef : 𝚺₁.Semisentence 3 := blueprint.resultDef

def historyDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef

instance history_defined : 𝚺₁-Function₂[V] history via historyDef :=
  ArithmeticUnaryRecursion.result_defined blueprint construction

instance history_defined_delta : 𝚫₁-Function₂[V] history via historyDeltaDef :=
  history_defined.graph_delta

instance history_definable : 𝚺₁-Function₂[V] history := history_defined.to_definable

@[simp] theorem history_zero (right : V) :
    history 0 right = seqCons ∅ right := by simp [history, construction]

@[simp] theorem history_succ (left right : V) :
    history (left + 1) right =
      seqCons (history left right) (stepValue (history left right) left) := by
  simp [history, PR.Construction.result_succ, construction]

/-- Actual internal induction, including nonstandard indices. -/
theorem history_seq (left right : V) : Seq (history left right) := by
  induction left using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ left ih =>
    rw [history_succ]
    exact ih.seqCons _

theorem history_length (left right : V) : lh (history left right) = left + 1 := by
  induction left using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ left ih =>
    rw [history_succ, (history_seq left right).lh_seqCons, ih]

noncomputable def appendValue (left right : V) : V :=
  znth (history left right) left

def appendDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out left right. ∃ s, !historyDef s left right ∧ !znthDef out s left”

instance append_defined : 𝚺₁-Function₂[V] appendValue via appendDef :=
  .mk fun e => by simp [appendDef, appendValue]

def appendDeltaDef : 𝚫₁.Semisentence 3 := appendDef.graphDelta

instance append_defined_delta : 𝚫₁-Function₂[V] appendValue via appendDeltaDef :=
  append_defined.graph_delta

instance append_definable : 𝚺₁-Function₂[V] appendValue := append_defined.to_definable

/-- Right-append preserves every older entry of a valid internal sequence. -/
theorem znth_append_old {s : V} (hs : Seq s) (x i : V) (hi : i < lh s) :
    znth (seqCons s x) i = znth s i := by
  apply (hs.seqCons x).znth_eq_of_mem
  exact Seq.subset_seqCons s x (hs.znth hi)

theorem znth_append_last {s : V} (hs : Seq s) (x : V) :
    znth (seqCons s x) (lh s) = x :=
  (hs.seqCons x).znth_eq_of_mem (Seq.mem_seqCons s x)

@[simp] theorem appendValue_zero (right : V) : appendValue 0 right = right := by
  rw [appendValue, history_zero]
  simpa only [lh_empty] using znth_append_last (seq_empty (V := V)) right

/-- Every earlier history entry equals its own represented result. The
quantifier is bounded, so the induction predicate is still Sigma1. -/
theorem history_lookup_le (left right : V) :
    ∀ i ≤ left, znth (history left right) i = appendValue i right := by
  induction left using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro i hi
    have hi0 : i = 0 := le_antisymm hi (by simp)
    subst i
    rfl
  case succ left ih =>
    intro i hi
    by_cases he : i = left + 1
    · subst i
      rfl
    · have hilt : i < left + 1 := lt_of_le_of_ne hi he
      have hile : i ≤ left := lt_succ_iff_le.mp hilt
      rw [history_succ, znth_append_old (history_seq left right) _ i
        (by simpa only [history_length] using hilt)]
      exact ih i hile

/-- The exact word recurrence holds at all internal model inputs. -/
theorem appendValue_succ (raw right : V) :
    appendValue (raw + 1) right =
      replaceValue raw (appendValue (tailValue raw) right) + 1 := by
  calc
    appendValue (raw + 1) right = stepValue (history raw right) raw := by
      unfold appendValue
      rw [history_succ]
      simpa only [history_length] using
        znth_append_last (history_seq raw right) (stepValue (history raw right) raw)
    _ = _ := by
      unfold stepValue
      rw [history_lookup_le raw right _ (tail_le raw)]

/-- Empty append has exactly the two empty inputs, even internally. -/
theorem appendValue_eq_zero (left right : V) :
    appendValue left right = 0 ↔ left = 0 ∧ right = 0 := by
  rcases zero_or_succ left with (rfl | ⟨raw, rfl⟩)
  · simp
  · simp [appendValue_succ]

/-- Full internal history lookup, including the default0 exterior. -/
theorem history_lookup (left right i : V) :
    znth (history left right) i =
      if i ≤ left then appendValue i right else 0 := by
  classical
  by_cases hi : i ≤ left
  · simp only [hi, if_pos]
    exact history_lookup_le left right i hi
  · simp only [hi, if_false]
    apply znth_prop_not
    right
    rw [history_length]
    exact lt_iff_succ_le.mp (lt_of_not_ge hi)

@[simp] theorem append_right_zero (left : V) : appendValue left 0 = left := by
  induction left using ISigma1.sigma1_order_induction
  · definability
  case ind left ih =>
    rcases zero_or_succ left with (rfl | ⟨raw, rfl⟩)
    · simp
    · rw [appendValue_succ, ih (tailValue raw) (lt_succ_iff_le.mpr (tail_le raw)),
        replace_own_tail]

/-- Associativity uses Sigma1 induction with the other two inputs fixed.
It does not assume that an internal word is an external finite list. -/
theorem append_assoc (left middle right : V) :
    appendValue (appendValue left middle) right =
      appendValue left (appendValue middle right) := by
  induction left using ISigma1.sigma1_order_induction
  · definability
  case ind left ih =>
    rcases zero_or_succ left with (rfl | ⟨raw, rfl⟩)
    · simp
    · rw [appendValue_succ, appendValue_succ, tail_replace, replace_twice,
        appendValue_succ, ih (tailValue raw) (lt_succ_iff_le.mpr (tail_le raw))]

/-- Shifted encoding of actual command lists, using the literal pack layout. -/
def encodeList : List EnumPerm.Cmd → Nat
  | [] => 0
  | c::cs => EnumPerm.pack c (encodeList cs)+1

/-- Actual packed finite programs concatenate according to the represented
append graph. Internal append itself is defined for every model element. -/
theorem append_encodeList (p q : List EnumPerm.Cmd) :
    appendValue (encodeList p) (encodeList q)=encodeList (p++q) := by
  induction p with
  | nil => simp [encodeList]
  | cons c cs ih =>
    simp only [encodeList,List.cons_append,appendValue_succ,tail_pack_nat,
      ih,replace_pack_nat]

theorem history_total (left right : V) :
    ∃! s, historyDef.val.Evalb ![s,left,right] := by simp

theorem append_total (left right : V) :
    ∃! out, appendDef.val.Evalb ![out,left,right] := by simp

/-- A fixed closed assertion of unique append evaluation, separate from any
compiler or consistency transport. -/
def totalitySentence : ArithmeticSentence :=
  “∀ left, ∀ right, ∃ out, !appendDef out left right ∧
    ∀ other, !appendDef other left right → other = out”

theorem totalitySentence_true : totalitySentence.Evalb (M := V) ![] := by
  simp [totalitySentence]

theorem isigma1_proves_totality : 𝗜𝚺₁ ⊢ totalitySentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (totalitySentence_true (V := M))

theorem peano_proves_totality : Peano ⊢ totalitySentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_totality

end DiophantineConsistency.ArithmeticCommandAppendPerm222
