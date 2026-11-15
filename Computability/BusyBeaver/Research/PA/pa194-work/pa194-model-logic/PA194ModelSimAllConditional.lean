import PA194ModelSimNegation
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
local instance simAllConditionalZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance simAllConditionalOne : One M := ⟨F oneCode Fin.elim0⟩
local instance simAllConditionalAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance simAllConditionalMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance simAllConditionalLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance simAllConditionalIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Entering a source eigenvariable shifts the free stack and reserves the
current base label; bound stack remains as the outer formula environment. -/
noncomputable def simPushFree (e : M) : M :=
  pair (simBound e) (pair (pair (simBase e) (simFree e)+1)
    (pair (simBase e+1) (simReserve e)))

theorem simPushFree_fields (e : M) :
    simBound (simPushFree e) = simBound e ∧
    simFree (simPushFree e) = pair (simBase e) (simFree e)+1 ∧
    simBase (simPushFree e) = simBase e+1 ∧
    simReserve (simPushFree e) = simReserve e := by
  simp [simPushFree,simBound,simFree,simBase,simReserve]

theorem target_all_doubleNeg (d a : M) :
    TargetProvable (impValue (allValue d (negValue (negValue a)))
      (negValue (negValue (allValue d a)))) :=
  imp_trans (liftImp d (doubleNegationElimination a)) (doubleNegationIntroduction (allValue d a))

/-- The exact universal-rule target implication, conditional only on the
source free-variable transformation having the displayed translation. -/
theorem simRuleAll_of_freeBridge (e s p : M)
    (hs : IsFormulaSet M6.PA.RelationalSource.language s) (hm : (^∀ p) ∈ s)
    (hbridge : F fixedFormulaTranslation ![free M6.PA.RelationalSource.language p,
      simBound (simPushFree e),simFree (simPushFree e),simBase (simPushFree e),simReserve (simPushFree e)] =
      F fixedFormulaTranslation ![p,pair (simBase e) (simBound e)+1,simFree e,simBase e+1,simReserve e]) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.all (simBase e) (numericalQuant.imp
        (numericalTranslation.tr (simPushFree e) (free M6.PA.RelationalSource.language p)) 1))
      (numericalQuant.imp (numericalTranslation.tr e (^∀ p)) 1)) := by
  have huv : IsUFormula M6.PA.RelationalSource.language (^∀ p) := (hs _ hm).isUFormula
  have hp : IsUFormula M6.PA.RelationalSource.language p := IsUFormula.all.mp huv
  change TargetProvable (impValue
    (allValue (simBase e) (impValue (negatedTranslation (simPushFree e) (free M6.PA.RelationalSource.language p)) 1))
    (impValue (negatedTranslation e (^∀ p)) 1))
  rw [negatedTranslation_any,negatedTranslation_any,
    fixedFormulaTranslation_all p (simBound e) (simFree e) (simBase e) (simReserve e) hp,hbridge]
  exact target_all_doubleNeg _ _

#print axioms simPushFree_fields
#print axioms target_all_doubleNeg
#print axioms simRuleAll_of_freeBridge
end models
end PA194ModelLogic
