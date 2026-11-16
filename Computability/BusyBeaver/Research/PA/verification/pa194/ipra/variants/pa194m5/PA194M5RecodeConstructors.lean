import PA194RadixRecodingRoundTrip
import PA194TargetGate
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194M5RecodeConstructors
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194RadixRecoding PA194RadixModel PA194TargetCantor PA194TargetLeaves PA194TargetGate
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem numeral_cast (n : Nat) : modelNumeral M n = (n : M) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [PA194FiniteControls.modelNumeralSucc, ih, Nat.cast_succ]
noncomputable def lift5 (x : M) : M := F (recode 3 4) ![x]
noncomputable def imp5 (a b : M) : M := (5:M)*cantor a b
noncomputable def mem5 (a b : M) : M := imp5 a b + 1
noncomputable def all5 (a b : M) : M := imp5 b a + 2
noncomputable def eq5 (a b : M) : M := imp5 a b + 3
noncomputable def neg5 (a : M) : M := imp5 a 1
noncomputable def ex5 (a b : M) : M := neg5 (all5 a (neg5 b))

private theorem source_ge_two : (2 : M) ≤ modelNumeral M (3+1) := by rw [numeral_cast]; norm_num
private theorem tag_lt_four (tag : M) (h : tag < (4 : M)) : tag < modelNumeral M (3+1) := by simpa [numeral_cast] using h
private theorem tag_lt_five (tag : M) (h : tag < (5 : M)) : tag < modelNumeral M (4+1) := by simpa [numeral_cast] using h

theorem lift_zero : lift5 (0:M) = 0 := recodeZero 3 4
theorem lift_one : lift5 (1:M) = 1 := by
  exact recodeDigit 3 4 1 source_ge_two (tag_lt_four 1 (by norm_num)) (tag_lt_five 1 (by norm_num))

theorem lift_imp (a b : M) : lift5 (impValue a b) = imp5 (lift5 a) (lift5 b) := by
  have h := recodeConstructor 3 4 a b (0:M) source_ge_two (tag_lt_four 0 (by norm_num)) (tag_lt_five 0 (by norm_num))
  simpa [lift5,impValue,imp5,encode,numeral_cast] using h

theorem lift_mem (a b : M) : lift5 (memValue a b) = mem5 (lift5 a) (lift5 b) := by
  have h := recodeConstructor 3 4 a b (1:M) source_ge_two (tag_lt_four 1 (by norm_num)) (tag_lt_five 1 (by norm_num))
  simpa [lift5,memValue,impValue,mem5,imp5,encode,numeral_cast] using h

theorem lift_all (a b : M) : lift5 (allValue a b) = all5 (lift5 a) (lift5 b) := by
  have h := recodeConstructor 3 4 b a (2:M) source_ge_two (tag_lt_four 2 (by norm_num)) (tag_lt_five 2 (by norm_num))
  simpa [lift5,allValue,impValue,all5,imp5,encode,numeral_cast] using h

theorem lift_eq (a b : M) : lift5 (eqValue a b) = eq5 (lift5 a) (lift5 b) := by
  have h := recodeConstructor 3 4 a b (3:M) source_ge_two (tag_lt_four 3 (by norm_num)) (tag_lt_five 3 (by norm_num))
  simpa [lift5,eqValue,impValue,eq5,imp5,encode,numeral_cast] using h

theorem lift_neg (a : M) : lift5 (negValue a) = neg5 (lift5 a) := by
  rw [negValue,lift_imp,lift_one,neg5]

theorem lift_ex (a b : M) : lift5 (exValue a b) = ex5 (lift5 a) (lift5 b) := by
  simp only [exValue,ex5,lift_neg,lift_all]

theorem lift_injective : Function.Injective (lift5 : M → M) := by
  apply injective 3 4 source_ge_two
  rw [numeral_cast,numeral_cast]
  norm_num

theorem lift_eq_iff (a b : M) : lift5 a = lift5 b ↔ a = b :=
  ⟨fun h => lift_injective h,congrArg lift5⟩

#print axioms lift_imp
#print axioms lift_mem
#print axioms lift_all
#print axioms lift_eq
#print axioms lift_neg
#print axioms lift_ex
#print axioms lift_eq_iff
end models
end PA194M5RecodeConstructors
