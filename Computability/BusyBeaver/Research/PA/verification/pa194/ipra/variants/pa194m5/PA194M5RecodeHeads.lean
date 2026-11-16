import PA194M5RecodeConstructors
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194M5RecodeHeads
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194RadixRecoding PA194RadixModel PA194TargetCantor PA194TargetLeaves PA194TargetGate
open PA194M5RecodeConstructors
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

noncomputable def head1Five (a b : M) := imp5 (ex5 a (all5 a b)) b
noncomputable def head2Five (d a h : M) := imp5 (all5 d (all5 a h)) (all5 a (all5 d h))
noncomputable def head3Five (d a h : M) := imp5 (mem5 h d) (imp5 (eq5 h a) (mem5 a d))
noncomputable def head4Five (d a h : M) := imp5 (eq5 h d) (imp5 (mem5 a h) (mem5 a d))
noncomputable def head5Five (d h : M) := ex5 d (eq5 h d)
noncomputable def head6Five (d a h : M) := imp5 (all5 d a) (imp5 (all5 d (imp5 a h)) (all5 d h))
noncomputable def rho8Five (a b c u : M) := imp5 (imp5 (imp5 c u) a) (imp5 (imp5 a c) (imp5 b c))
noncomputable def diagonalFive (c : M) := imp5 c (all5 c c)
noncomputable def conjFive (p q : M) := neg5 (imp5 p (neg5 q))
noncomputable def memVacFive (a b c : M) := imp5 (mem5 a b) (all5 c (mem5 a b))
noncomputable def pointFive (b c : M) := imp5 c (mem5 c b)
noncomputable def sepFive (a b c : M) :=
  all5 b (conjFive (imp5 (mem5 a b) (pointFive b c)) (imp5 (mem5 c b) c))
noncomputable def sepTailFive (a b c : M) := all5 c (imp5 (sepFive a b c) (neg5 (pointFive b c)))
noncomputable def gateFive (a b c : M) := neg5 (imp5 (memVacFive a b c) (sepTailFive a b c))

theorem lift_head1 (a b : M) : lift5 (head1Value a b) = head1Five (lift5 a) (lift5 b) := by
  simp only [head1Value,head1Five,lift_imp,lift_ex,lift_all]
theorem lift_head2 (d a h : M) : lift5 (head2Value d a h) = head2Five (lift5 d) (lift5 a) (lift5 h) := by
  simp only [head2Value,head2Five,lift_imp,lift_all]
theorem lift_head3 (d a h : M) : lift5 (head3Value d a h) = head3Five (lift5 d) (lift5 a) (lift5 h) := by
  simp only [head3Value,head3Five,lift_imp,lift_mem,lift_eq]
theorem lift_head4 (d a h : M) : lift5 (head4Value d a h) = head4Five (lift5 d) (lift5 a) (lift5 h) := by
  simp only [head4Value,head4Five,lift_imp,lift_mem,lift_eq]
theorem lift_head5 (d h : M) : lift5 (head5Value d h) = head5Five (lift5 d) (lift5 h) := by
  simp only [head5Value,head5Five,lift_ex,lift_eq]
theorem lift_head6 (d a h : M) : lift5 (head6Value d a h) = head6Five (lift5 d) (lift5 a) (lift5 h) := by
  simp only [head6Value,head6Five,lift_imp,lift_all]
theorem lift_rho8 (a b c u : M) : lift5 (rho8Value a b c u) = rho8Five (lift5 a) (lift5 b) (lift5 c) (lift5 u) := by
  simp only [rho8Value,rho8Five,lift_imp]
theorem lift_diagonal (c : M) : lift5 (diagonalValue c) = diagonalFive (lift5 c) := by
  simp only [diagonalValue,diagonalFive,lift_imp,lift_all]
theorem lift_gate (a b c : M) : lift5 (oldBundleValue a b c) = gateFive (lift5 a) (lift5 b) (lift5 c) := by
  simp only [oldBundleValue,memVacValue,separationTailValue,separationValue,pointValue,conjValue,
    gateFive,memVacFive,sepTailFive,sepFive,pointFive,conjFive,lift_neg,lift_imp,lift_all,lift_mem]
#print axioms lift_head1
#print axioms lift_head2
#print axioms lift_head3
#print axioms lift_head4
#print axioms lift_head5
#print axioms lift_head6
#print axioms lift_rho8
#print axioms lift_diagonal
#print axioms lift_gate
end models
end PA194M5RecodeHeads
