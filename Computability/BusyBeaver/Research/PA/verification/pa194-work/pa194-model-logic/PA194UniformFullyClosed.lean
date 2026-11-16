import PA194UniformFreeBoundModel
import PA194FullyClosedSeparation
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def pureFullyClosedSeparation (p : V) : V :=
  let root := sepRootPure p
  pureModelClose (pureFormulaFreeBound root) root
noncomputable def pureFullyClosedSepGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “q p. ∃ r, !sepRootGraph r p ∧ ∃ b, !pureFormulaFreeBoundGraph b r ∧
    !closeIterBlueprint.resultDef q b r”
theorem pureFullyClosedSepGraph_defined :
    𝚺₁-Function₁ (pureFullyClosedSeparation : V → V) via pureFullyClosedSepGraph := by
  haveI : 𝚺₁-Function₁ (sepRootPure : V → V) via sepRootGraph := sepRootGraph_defined
  haveI : 𝚺₁-Function₁ (pureFormulaFreeBound : V → V) via pureFormulaFreeBoundGraph := pureFormulaFreeBound_defined
  haveI : 𝚺₁-Function₂ (pureModelClose : V → V → V) via closeIterBlueprint.resultDef := pureModelClose_defined
  refine .mk fun v => ?_
  simp [pureFullyClosedSepGraph,pureFullyClosedSeparation]
#print axioms pureFullyClosedSepGraph_defined
end generic
end PA194BindSource
