import BusyBeaver.ZFC.ArithmeticProofWord254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordRow254.row_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordRow254.row_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordRow254.row_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.positiveStep_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.history_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.history_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.history_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.history_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.history_seq
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.history_length
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.rawWord_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.rawWord_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.rawWord_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.history_lookup_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.history_lookup
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.rawWord_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.compiledWord_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.compiledWord_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.compiledWord_invalid
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.compiledWord_valid
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.compiledWord_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.history_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.rawWord_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.compiledWord_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.compiledWord_nat_gate
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.totalitySentence_true
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.isigma1_proves_totality
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWord254.peano_proves_totality
section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (e : Fin 5 → V) : ArithmeticProofWordRow254.rowDef.val.Evalb e ↔
    e 0 = ArithmeticProofWordRow254.rowValue (e 1) (e 2) (e 3) (e 4) :=
  ArithmeticProofWordRow254.row_defined.df e
example (k p u v : V) : ∃! out, ArithmeticProofWordRow254.rowDef.val.Evalb ![out,k,p,u,v] :=
  ArithmeticProofWordRow254.row_total k p u v
-- The unconditional truth row deliberately does NOT check payload=0.
example (p u v : V) : ArithmeticProofWordRow254.rowValue 0 p u v =
    ArithmeticCommandBlocks254.Circuit.discard.eval 0 0 0 0 := by
  simp [ArithmeticProofWordRow254.rowValue]
example (e : Fin 3 → V) : ArithmeticProofWord254.positiveStepDef.val.Evalb e ↔
    e 0 = ArithmeticProofWord254.positiveStep (e 1) (e 2) :=
  ArithmeticProofWord254.positiveStep_defined.df e
example (e : Fin 2 → V) : ArithmeticProofWord254.historyDef.val.Evalb e ↔
    e 0 = ArithmeticProofWord254.history (e 1) := ArithmeticProofWord254.history_defined.df e
example (e : Fin 2 → V) : ArithmeticProofWord254.rawWordDef.val.Evalb e ↔
    e 0 = ArithmeticProofWord254.rawWord (e 1) := ArithmeticProofWord254.rawWord_defined.df e
example (e : Fin 2 → V) : ArithmeticProofWord254.compiledWordDef.val.Evalb e ↔
    e 0 = ArithmeticProofWord254.compiledWord (e 1) := ArithmeticProofWord254.compiledWord_defined.df e
example (code : V) : Seq (ArithmeticProofWord254.history code) := ArithmeticProofWord254.history_seq code
example (code : V) : lh (ArithmeticProofWord254.history code) = code+1 := ArithmeticProofWord254.history_length code
example (code i : V) (hi : i ≤ code) :
    znth (ArithmeticProofWord254.history code) i = ArithmeticProofWord254.rawWord i :=
  ArithmeticProofWord254.history_lookup_le code i hi
example (code i : V) : znth (ArithmeticProofWord254.history code) i =
    if i ≤ code then ArithmeticProofWord254.rawWord i else 0 := ArithmeticProofWord254.history_lookup code i
example (code : V) : znth (ArithmeticProofWord254.history code) (code+1) = 0 := by
  rw [ArithmeticProofWord254.history_lookup, if_neg (by simp)]
example (code : V) (h : ArithmeticHistory254.value code = 0) :
    ArithmeticProofWord254.compiledWord code = 0 := ArithmeticProofWord254.compiledWord_invalid code h
example (code : V) (h : ArithmeticHistory254.value code ≠ 0) :
    ArithmeticProofWord254.compiledWord code = ArithmeticProofWord254.rawWord code := ArithmeticProofWord254.compiledWord_valid code h
example : ArithmeticProofWord254.rawWord (0 : V) = 0 := ArithmeticProofWord254.rawWord_zero
example : ArithmeticProofWord254.compiledWord (0 : V) = 0 := ArithmeticProofWord254.compiledWord_zero
example (code : V) : ∃! out, ArithmeticProofWord254.compiledWordDef.val.Evalb ![out,code] :=
  ArithmeticProofWord254.compiledWord_total code
example : ArithmeticProofWord254.totalitySentence.Evalb (M := V) ![] := ArithmeticProofWord254.totalitySentence_true
end Generic
example (code : Nat) : ArithmeticProofWord254.compiledWord code =
    if Code254History.value code = 0 then 0 else ArithmeticProofWord254.rawWord code := ArithmeticProofWord254.compiledWord_nat_gate code
example : 𝗜𝚺₁ ⊢ ArithmeticProofWord254.totalitySentence := ArithmeticProofWord254.isigma1_proves_totality
example : Peano ⊢ ArithmeticProofWord254.totalitySentence := ArithmeticProofWord254.peano_proves_totality
