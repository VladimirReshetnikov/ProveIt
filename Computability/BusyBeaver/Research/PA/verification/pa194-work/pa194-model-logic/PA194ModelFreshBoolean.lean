import PA194ModelFreshAtom
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance freshBooleanZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freshBooleanOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freshBooleanAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freshBooleanMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freshBooleanLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance freshBooleanIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Vacuity of a numerical negation implies vacuity of the original formula. -/
theorem negationVacuity_reverse (x a : M)
    (h : TargetProvable (impValue (negValue a) (allValue x (negValue a)))) :
    TargetProvable (impValue a (allValue x a)) :=
  imp_trans (doubleNegationIntroduction a)
    (imp_trans (negationVacuity x (negValue a) h) (liftImp x (doubleNegationElimination a)))

noncomputable def FreshBridge (e p : M) : Prop :=
  TargetProvable (impValue (negatedTranslation e p) (allValue (simBase e) (negatedTranslation e p)))

theorem freshBridge_and (e p q : M)
    (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q)
    (ihp : FreshBridge e p) (ihq : FreshBridge e q) : FreshBridge e (p ^⋏ q) := by
  unfold FreshBridge at ihp ihq ⊢
  rw [negatedTranslation_any] at ihp ihq
  rw [negatedTranslation_any,fixedFormulaTranslation_and p q _ _ _ _ hp hq]
  apply negationVacuity
  exact conjunctionVacuity (simBase e) _ _
    (negationVacuity_reverse _ _ ihp) (negationVacuity_reverse _ _ ihq)

theorem freshBridge_or (e p q : M)
    (hp : IsUFormula SourceL p) (hq : IsUFormula SourceL q)
    (ihp : FreshBridge e p) (ihq : FreshBridge e q) : FreshBridge e (p ^⋎ q) := by
  unfold FreshBridge at ihp ihq ⊢
  rw [negatedTranslation_any] at ihp ihq
  rw [negatedTranslation_any,fixedFormulaTranslation_or p q _ _ _ _ hp hq]
  apply negationVacuity
  exact implicationVacuity (simBase e) _ _ ihp (negationVacuity_reverse _ _ ihq)

theorem freshBridge_verum (e : M) : FreshBridge e (^⊤ : M) := by
  unfold FreshBridge
  rw [negatedTranslation_any,fixedFormulaTranslation_verum]
  apply negationVacuity
  exact tp_mp (tp_gen (simBase e) sequentTruth_zero) (imp_k _ 0)

theorem freshBridge_falsum (e : M) : FreshBridge e (^⊥ : M) := by
  unfold FreshBridge
  rw [negatedTranslation_any,fixedFormulaTranslation_falsum]
  apply negationVacuity
  exact explosion _

#print axioms negationVacuity_reverse
#print axioms freshBridge_and
#print axioms freshBridge_or
#print axioms freshBridge_verum
#print axioms freshBridge_falsum
end models
end PA194ModelLogic
