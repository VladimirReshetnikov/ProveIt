import BusyBeaver.ZFC.ArithmeticCommandAppend254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCommandWord254 ArithmeticCommandAppend254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.step_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.history_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.history_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.history_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.history_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.history_seq
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.history_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.append_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.append_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.znth_append_old
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.znth_append_last
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.appendValue_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.history_lookup_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.appendValue_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.appendValue_eq_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.history_lookup
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.appendValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.history_lookup_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.appendDef_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.history_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.append_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.totalitySentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.isigma1_proves_totality
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandAppend254.peano_proves_totality
section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (e : Fin 3 → V) : stepDef.val.Evalb e ↔
    e 0 = replaceValue (e 2) (znth (e 1) (tailValue (e 2))) + 1 := step_defined.df e
example (e : Fin 3 → V) : historyDef.val.Evalb e ↔
    e 0 = history (e 1) (e 2) := history_defined.df e
example (e : Fin 3 → V) : appendDef.val.Evalb e ↔
    e 0 = appendValue (e 1) (e 2) := append_defined.df e
example (e : Fin 3 → V) : historyDeltaDef.val.Evalb e ↔
    e 0 = history (e 1) (e 2) := history_defined_delta.df e
example (e : Fin 3 → V) : appendDeltaDef.val.Evalb e ↔
    e 0 = appendValue (e 1) (e 2) := append_defined_delta.df e
example (r : V) : history 0 r = seqCons ∅ r := history_zero r
example (l r : V) : Seq (history l r) := history_seq l r
example (l r : V) : lh (history l r) = l+1 := history_length l r
example (l r : V) : ∃! s, historyDef.val.Evalb ![s,l,r] := history_total l r
example (l r : V) : ∃! o, appendDef.val.Evalb ![o,l,r] := append_total l r
example (r : V) : appendValue 0 r = r := appendValue_zero r
example (z r : V) : appendValue (z+1) r =
    replaceValue z (appendValue (tailValue z) r)+1 := appendValue_succ z r
example (l r : V) : appendValue l r = 0 ↔ l = 0 ∧ r = 0 := appendValue_eq_zero l r
example (r : V) : appendValue 1 r ≠ 0 := by simp [appendValue_eq_zero]
example (l r i : V) (h : i ≤ l) : znth (history l r) i = appendValue i r := history_lookup_le l r i h
example (l r i : V) : znth (history l r) i = if i ≤ l then appendValue i r else 0 := history_lookup l r i
example (l r : V) : znth (history l r) (l+1) = 0 := by
  rw [history_lookup, if_neg (by simp)]
example : totalitySentence.Evalb (M := V) ![] := totalitySentence_true
end Generic
example (l r : Nat) : appendValue l r = CommandWord254.append l r := appendValue_nat l r
example (l r i : Nat) : znth (history l r) i =
    if i ≤ l then CommandWord254.append i r else 0 := history_lookup_nat l r i
example (o l r : Nat) : appendDef.val.Evalb ![o,l,r] ↔
    o = CommandWord254.append l r := appendDef_nat o l r
example (r : Nat) : appendValue 0 r = r := by rw [appendValue_zero]
example (l : Nat) : appendValue l 0 = l := by rw [appendValue_nat, CommandWord254.append_right_zero]
example (xs ys : List Enum254.Cmd) :
    appendValue (CommandWord254.encode xs) (CommandWord254.encode ys) =
      CommandWord254.encode (xs ++ ys) := by rw [appendValue_nat, CommandWord254.append_encode]
example : appendValue (1 : Nat) 0 = 1 := by rw [appendValue_nat, CommandWord254.append_right_zero]
example : appendValue (0 : Nat) 1 = 1 := appendValue_zero 1
example : appendValue (1 : Nat) 1 = 6 := by
  calc
    appendValue (1 : Nat) 1 = CommandWord254.encode [.mp 0, .mp 0] := by
      rw [appendValue_nat]
      simpa only [CommandWord254.raw_zero_is_nonempty, List.cons_append, List.nil_append] using
        CommandWord254.append_encode [.mp 0] [.mp 0]
    _ = 6 := by
      simp [CommandWord254.encode, Enum254.pack, Code254.P,
        SetTheory.Cantor.toNat, SetTheory.Cantor.tri]
example (l r : Nat) : znth (history l r) (l+1) = 0 := by
  rw [history_lookup_nat, if_neg (by omega)]
example : 𝗜𝚺₁ ⊢ totalitySentence := isigma1_proves_totality
example : Peano ⊢ totalitySentence := peano_proves_totality
