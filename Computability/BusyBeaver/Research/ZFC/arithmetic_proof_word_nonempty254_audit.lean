import BusyBeaver.ZFC.ArithmeticProofWordNonempty254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCommandAppend254 ArithmeticCommandBlocks254
open ArithmeticProofWordRow254 ArithmeticProofWord254 ArithmeticProofWordNonempty254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.consMp_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.consDrop_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.consAx_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.discard_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.leaf_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.bundle_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.gen_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.mp_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.rowValue_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.rawWord_succ_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.rawWord_eq_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.compiledWord_eq_zero
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (x rest : Circuit) (a b c u : V) : (Circuit.consMp x rest).eval a b c u ≠ 0 :=
  consMp_ne_zero x rest a b c u
example (x rest : Circuit) (a b c u : V) : (Circuit.consDrop x rest).eval a b c u ≠ 0 :=
  consDrop_ne_zero x rest a b c u
example (i x y z rest : Circuit) (a b c u : V) : (Circuit.consAx i x y z rest).eval a b c u ≠ 0 :=
  consAx_ne_zero i x y z rest a b c u
example (a b c u : V) : Circuit.discard.eval a b c u ≠ 0 := discard_ne_zero a b c u
example (j : Nat) (x y z w : Circuit) (a b c u : V) :
    (Circuit.leaf j x y z w).eval a b c u ≠ 0 := leaf_ne_zero j x y z w a b c u
example (x y z : Circuit) (a b c u : V) :
    (Circuit.bundleLeaf x y z).eval a b c u ≠ 0 := bundle_ne_zero x y z a b c u
example (i p : Circuit) (a b c u : V) :
    (Circuit.genBlock i p).eval a b c u ≠ 0 := gen_ne_zero i p a b c u
example (b p q : Circuit) (a d c u : V) :
    (Circuit.mpBlock b p q).eval a d c u ≠ 0 := mp_ne_zero b p q a d c u
example (tag payload u v : V) (h : tag < 12) : rowValue tag payload u v ≠ 0 :=
  rowValue_ne_zero tag payload u v h
example (raw : V) : rawWord (raw+1) ≠ 0 := rawWord_succ_ne_zero raw
example (code : V) : rawWord code = 0 ↔ code = 0 := rawWord_eq_zero code
example (code : V) : rawWord code ≠ 0 ↔ code ≠ 0 := not_congr (rawWord_eq_zero code)
example (code : V) : compiledWord code = 0 ↔ ArithmeticHistory254.value code = 0 :=
  compiledWord_eq_zero code
example (code : V) (h : ArithmeticHistory254.value code ≠ 0) : compiledWord code ≠ 0 := by
  intro hz
  exact h ((compiledWord_eq_zero code).mp hz)
example : rawWord (0 : V) = 0 := rawWord_zero
example : compiledWord (0 : V) = 0 := compiledWord_zero
example (code : V) (h : ArithmeticHistory254.value code = 0) : compiledWord code = 0 :=
  (compiledWord_eq_zero code).mpr h
example : rawWord (1 : V) ≠ 0 := by simpa using rawWord_succ_ne_zero (0 : V)
