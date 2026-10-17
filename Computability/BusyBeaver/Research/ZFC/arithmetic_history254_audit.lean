import BusyBeaver.ZFC.ArithmeticHistory254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticHistory254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.positiveStep_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.step_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.stepValue_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.stepValue_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.history_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.history_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.history_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.history_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.history_seq
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.history_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.value_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.value_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.check_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.checkValue_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.checkValue_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.value_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.checkValue_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.checkValue_range
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.foundation_div_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.foundation_rem_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.numeral_twelve_eq_twelve
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.positiveStep_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.stepValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.znth_append_old
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.znth_append_last
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.znth_append
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.history_lookup_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.value_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.checkDef_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.c254_iff_represented
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.history_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.value_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.checkValue_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.checkValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.totalitySentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.isigma1_proves_totality
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticHistory254.peano_proves_totality
section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (e : Fin 3 → V) : positiveStepDef.val.Evalb e ↔ e 0 = positiveStep (e 1) (e 2) := positiveStep_defined.df e
example (e : Fin 3 → V) : stepDef.val.Evalb e ↔ e 0 = stepValue (e 1) (e 2) := step_defined.df e
example (e : Fin 2 → V) : historyDef.val.Evalb e ↔ e 0 = history (e 1) := by simp
example (e : Fin 2 → V) : historyDeltaDef.val.Evalb e ↔ e 0 = history (e 1) := by simp
example (e : Fin 2 → V) : valueDef.val.Evalb e ↔ e 0 = value (e 1) := by simp
example (e : Fin 2 → V) : valueDeltaDef.val.Evalb e ↔ e 0 = value (e 1) := by simp
example (e : Fin 2 → V) : checkDef.val.Evalb e ↔ value (e 0) = e 1 + 1 := check_defined.df e
example (e : Fin 3 → V) : checkValueDef.val.Evalb e ↔ e 0 = checkValue (e 1) (e 2) := checkValue_defined.df e
example (e : Fin 3 → V) : checkValueDeltaDef.val.Evalb e ↔ e 0 = checkValue (e 1) (e 2) := checkValue_defined_delta.df e
example : history (0 : V) = seqCons ∅ 0 := history_zero
example (code : V) : history (code + 1) = seqCons (history code) (stepValue (history code) (code + 1)) := history_succ code
example (code : V) : Seq (history code) := history_seq code
example (code : V) : lh (history code) = code + 1 := history_length code
example (code : V) : ∃! s, historyDef.val.Evalb ![s, code] := history_total code
example (code : V) : ∃! r, valueDef.val.Evalb ![r, code] := value_total code
example (code conclusion : V) : ∃! b, checkValueDef.val.Evalb ![b, code, conclusion] := checkValue_total code conclusion
example (code conclusion : V) : checkValue code conclusion = 0 ∨ checkValue code conclusion = 1 := checkValue_range code conclusion
example : value (0 : V) = 0 := value_zero
example (n : V) : checkValue 0 n = 0 := checkValue_zero n
example {s : V} (hs : Seq s) (x i : V) (hi : i < lh s) : znth (seqCons s x) i = znth s i := znth_append_old hs x i hi
example {s : V} (hs : Seq s) (x : V) : znth (seqCons s x) (lh s) = x := znth_append_last hs x
example {s : V} (hs : Seq s) (x i : V) : znth (seqCons s x) i = if i < lh s then znth s i else if i = lh s then x else 0 := znth_append hs x i
example : totalitySentence.Evalb (M := V) ![] := totalitySentence_true
end Generic
-- The native operators below are explicit, not inferred scoped instances.
example (a b : Nat) : @Div.div Nat Arithmetic.instDiv_foundation a b = Nat.div a b := foundation_div_nat a b
example (a b : Nat) : @Mod.mod Nat Arithmetic.instMod_foundation a b = Nat.mod a b := foundation_rem_nat a b
example (s z : Nat) : positiveStep s z = Code254History.row (znth s) (Nat.mod z 12) (Nat.div z 12) := positiveStep_nat s z
example (s code : Nat) : stepValue s code = Code254History.step (znth s) code := stepValue_nat s code
example (n i : Nat) : znth (history n) i = Code254History.lookup (Code254History.history n) i := history_lookup_nat n i
example (code : Nat) : value code = Code254History.value code := value_nat code
example (code n : Nat) : checkDef.val.Evalb ![code, n] ↔ Code254Proof.check code n = true := checkDef_nat code n
example (code n : Nat) : checkValue code n = if Code254Proof.check code n = true then 1 else 0 := checkValue_nat code n
example (n : Nat) : Code254.C254 n ↔ ∃ code, checkDef.val.Evalb ![code,n] := c254_iff_represented n
example (n i : Nat) (hi : n < i) : znth (history n) i = 0 := by
  apply znth_prop_not
  right
  rw [history_length, Arithmetic.le_def]
  omega
-- Small malformed-code controls exercise the same represented formula.
example : checkDef.val.Evalb ![1,0] := (checkDef_nat 1 0).mpr (by decide)
example : ¬ checkDef.val.Evalb ![1,1] := by rw [checkDef_nat]; decide
example (n : Nat) : ¬ checkDef.val.Evalb ![0,n] := by
  simp [checkDef]
example : ¬ checkDef.val.Evalb ![2,0] := by rw [checkDef_nat]; decide
example : ¬ checkDef.val.Evalb ![3,0] := by rw [checkDef_nat]; decide
example : ¬ checkDef.val.Evalb ![12,0] := by rw [checkDef_nat]; decide
example : ¬ checkDef.val.Evalb ![13,0] := by rw [checkDef_nat]; decide
example : checkValue (1 : Nat) 0 = 1 := by rw [checkValue_nat]; decide
example : checkValue (2 : Nat) 0 = 0 := by rw [checkValue_nat]; decide
example : 𝗜𝚺₁ ⊢ totalitySentence := isigma1_proves_totality
example : Peano ⊢ totalitySentence := peano_proves_totality
