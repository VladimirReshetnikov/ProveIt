import BusyBeaver.ZFC.ArithmeticRow254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticRow254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.pred_add_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.pred_le
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.mpGate_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.mp_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.bounded_succ_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.predecessor_witness
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.gen_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.payload_fields
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.foundation_sub_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.mpGate_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.mpValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.genValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.pair_fields
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.payload_fields_flat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.row_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.rowKernel_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticRow254.rowGraph_nat
section Generic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (e : Fin 3 → V) : mpGateDef.val.Evalb e ↔ MPGate (e 0) (e 1) (e 2) := mpGate_defined.df e
example (e : Fin 4 → V) : mpDef.val.Evalb e ↔ e 0 = mpValue (e 1) (e 2) (e 3) := mp_defined.df e
example (e : Fin 3 → V) : genDef.val.Evalb e ↔ e 0 = genValue (e 1) (e 2) := gen_defined.df e
example (e : Fin 5 → V) : rowDef.val.Evalb e ↔ e 0 = rowKernel (e 1) (e 2) (e 3) (e 4) := row_defined.df e
example (u : V) : u - 1 ≤ u := pred_le u
example (u : V) (hu : u ≠ 0) : u - 1 + 1 = u := pred_add_one u hu
example (p : V) (Q : V → V → V → V → Prop) :
    (∃ a, a ≤ p ∧ ∃ t, t ≤ p ∧ p = cantor a t ∧ ∃ b, b ≤ p ∧ ∃ c, c ≤ p ∧ t = cantor b c ∧ Q a t b c) ↔
    Q (first p) (second p) (first (second p)) (second (second p)) := payload_fields p Q
example (p bound : V) (hp : p ≤ bound) (Q : V → V → Prop) :
    (∃ a, a ≤ bound ∧ ∃ b, b ≤ bound ∧ p = cantor a b ∧ Q a b) ↔ Q (first p) (second p) := pair_fields p bound hp Q
example (p u v : V) : rowKernel 12 p u v = 0 := by simp [rowKernel]
example (a v : V) : mpValue a 0 v = 0 := by simp [mpValue, MPGate]
end Generic
example (rec : Nat → Nat) (tag p : Nat) :
    rowKernel tag p (if tag = 2 then rec (SetTheory.Cantor.ofNat p).2 else rec (SetTheory.Cantor.ofNat (SetTheory.Cantor.ofNat p).2).1)
      (rec (SetTheory.Cantor.ofNat (SetTheory.Cantor.ofNat p).2).2) = Code254History.row rec tag p := rowKernel_nat rec tag p
example (rec : Nat → Nat) (tag p out : Nat) : rowDef.val.Evalb (rowEnv rec tag p out) ↔ out = Code254History.row rec tag p := rowGraph_nat rec tag p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 0 p out) ↔ out = Code254History.row rec 0 p := rowGraph_nat rec 0 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 1 p out) ↔ out = Code254History.row rec 1 p := rowGraph_nat rec 1 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 2 p out) ↔ out = Code254History.row rec 2 p := rowGraph_nat rec 2 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 3 p out) ↔ out = Code254History.row rec 3 p := rowGraph_nat rec 3 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 4 p out) ↔ out = Code254History.row rec 4 p := rowGraph_nat rec 4 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 5 p out) ↔ out = Code254History.row rec 5 p := rowGraph_nat rec 5 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 6 p out) ↔ out = Code254History.row rec 6 p := rowGraph_nat rec 6 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 7 p out) ↔ out = Code254History.row rec 7 p := rowGraph_nat rec 7 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 8 p out) ↔ out = Code254History.row rec 8 p := rowGraph_nat rec 8 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 9 p out) ↔ out = Code254History.row rec 9 p := rowGraph_nat rec 9 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 10 p out) ↔ out = Code254History.row rec 10 p := rowGraph_nat rec 10 p out
example (rec : Nat → Nat) (p out : Nat) : rowDef.val.Evalb (rowEnv rec 11 p out) ↔ out = Code254History.row rec 11 p := rowGraph_nat rec 11 p out
-- Successful code0 remains encoded as value1; invalid is value0.
example (u v : Nat) : rowKernel 0 0 u v = 1 := by simp [rowKernel]
example (p u v : Nat) (hp : p ≠ 0) : rowKernel 0 p u v = 0 := by simp [rowKernel, hp]
example (p u v : Nat) : rowKernel 12 p u v = 0 := by simp [rowKernel]
example (p u v : Nat) : rowKernel 12345 p u v = 0 := by simp [rowKernel]
example (a v : Nat) : mpValue a 0 v = 0 := by simp
example (a u : Nat) : mpValue a u 0 = 0 := by simp
example : mpValue (0 : Nat) 1 1 = 1 := by simp [Code254.wim, Code254.P, SetTheory.Cantor.toNat, SetTheory.Cantor.tri]
example : mpValue (1 : Nat) 1 1 = 0 := by simp [Code254.wim, Code254.P, SetTheory.Cantor.toNat, SetTheory.Cantor.tri]
example (a : Nat) : genValue a 0 = 0 := by simp
example (a : Nat) : genValue a 1 = Code254.wal a 0 + 1 := by simp
-- Each failed bundle gate has a valid output0 graph even at arbitrary payload size.
example (a b u v : Nat) : rowKernel 11 (cantor a (cantor b a)) u v = 0 := by
  simp only [rowKernel, first_cantor, second_cantor]
  simp
example (a b u v : Nat) : rowKernel 11 (cantor a (cantor b b)) u v = 0 := by
  simp only [rowKernel, first_cantor, second_cantor]
  simp
example (rec : Nat → Nat) (p : Nat) : rowDef.val.Evalb (rowEnv rec 12 p 0) :=
  (rowGraph_nat rec 12 p 0).mpr (by simp [Code254History.row])
