import PA194ModelSimAxiomRules
import PA194ModelBudgetShift
import PA194ModelFormulaTranslation
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.HierarchySymbol.Semiformula
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
local instance simPropositionalZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance simPropositionalOne : One M := ⟨F oneCode Fin.elim0⟩
local instance simPropositionalAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance simPropositionalMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance simPropositionalLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance simPropositionalIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem simAndBody (a b : M) :
    TargetProvable (impValue (impValue (negValue a) 1)
      (impValue (impValue (negValue b) 1) (impValue (negValue (conjValue a b)) 1))) := by
  let A := negValue (negValue a)
  let B := negValue (negValue b)
  let C := negValue (conjValue a b)
  let ha : Ctx [C,B,A] A := .assumption (by simp)
  let hb : Ctx [C,B,A] B := .assumption (by simp)
  let hc : Ctx [C,B,A] C := .assumption (by simp)
  let hab : Ctx [C,B,A] (conjValue a b) := Ctx.andIntro ha.dne hb.dne
  exact (Ctx.mp hab hc).deduction.deduction.deduction.empty

theorem simOrBody (a b : M) :
    TargetProvable (impValue (impValue (negValue b) (impValue (negValue a) 1))
      (impValue (negValue (impValue (negValue a) b)) 1)) := by
  let H := impValue (negValue b) (impValue (negValue a) 1)
  let J := negValue (impValue (negValue a) b)
  let hh : Ctx [J,H] H := .assumption (by simp)
  let hj : Ctx [J,H] J := .assumption (by simp)
  exact (Ctx.mp hj.negImpLeft (Ctx.mp hj.negImpRight hh)).deduction.deduction.empty

theorem simRuleAnd (e s p q : M)
    (hs : IsFormulaSet M6.PA.RelationalSource.language s) (hm : p ^⋏ q ∈ s) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e p) 1)
      (numericalQuant.imp (numericalQuant.imp (numericalTranslation.tr e q) 1)
        (numericalQuant.imp (numericalTranslation.tr e (p ^⋏ q)) 1))) := by
  have huv : IsUFormula M6.PA.RelationalSource.language (p ^⋏ q) := (hs _ hm).isUFormula
  obtain ⟨hp,hq⟩ := IsUFormula.and.mp huv
  change TargetProvable (impValue (impValue (negatedTranslation e p) 1)
    (impValue (impValue (negatedTranslation e q) 1) (impValue (negatedTranslation e (p ^⋏ q)) 1)))
  rw [negatedTranslation_any e p,negatedTranslation_any e q,negatedTranslation_any e (p ^⋏ q),
      fixedFormulaTranslation_and p q _ _ _ _ hp hq]
  exact simAndBody _ _

theorem simRuleOr (e s p q : M)
    (hs : IsFormulaSet M6.PA.RelationalSource.language s) (hm : p ^⋎ q ∈ s) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e q) (numericalQuant.imp (numericalTranslation.tr e p) 1))
      (numericalQuant.imp (numericalTranslation.tr e (p ^⋎ q)) 1)) := by
  have huv : IsUFormula M6.PA.RelationalSource.language (p ^⋎ q) := (hs _ hm).isUFormula
  obtain ⟨hp,hq⟩ := IsUFormula.or.mp huv
  change TargetProvable (impValue (impValue (negatedTranslation e q) (impValue (negatedTranslation e p) 1))
    (impValue (negatedTranslation e (p ^⋎ q)) 1))
  rw [negatedTranslation_any e p,negatedTranslation_any e q,negatedTranslation_any e (p ^⋎ q),
      fixedFormulaTranslation_or p q _ _ _ _ hp hq]
  exact simOrBody _ _

#print axioms simAndBody
#print axioms simOrBody
#print axioms simRuleAnd
#print axioms simRuleOr
end models
end PA194ModelLogic
