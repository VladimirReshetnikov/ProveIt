import PA194UniformEnvelopeModel
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
noncomputable def fullSepPure (q : V) : Prop :=
  shift SourceL q = q ∧ ∃ p < pureWitnessEnvelope q, IsSemiformula SourceL 1 p ∧ pureFullyClosedSeparation p = q
noncomputable def fullSepUniform : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “q. !(shiftGraph SourceL) q q ∧ ∃ b, !pureWitnessEnvelopeGraph b q ∧
    ∃ p < b, !(isSemiformula SourceL).sigma 1 p ∧ !pureFullyClosedSepGraph q p”)
  (.mkPi “q. !((shiftGraph SourceL).graphDelta.pi) q q ∧ ∀ b, !pureWitnessEnvelopeGraph b q →
    ∃ p < b, !(isSemiformula SourceL).pi 1 p ∧ !(pureFullyClosedSepGraph.graphDelta.pi) q p”)

theorem fullSepUniform_defined : 𝚫₁-Predicate (fullSepPure : V → Prop) via fullSepUniform := by
  haveI : 𝚫₁-Function₁ (shift SourceL : V → V) via (shiftGraph SourceL).graphDelta :=
    HierarchySymbol.DefinedFunction.graph_delta (shift.defined (L := SourceL))
  haveI : 𝚺₁-Function₁ (pureWitnessEnvelope : V → V) via pureWitnessEnvelopeGraph := pureWitnessEnvelope_defined
  haveI : 𝚺₁-Function₁ (pureFullyClosedSeparation : V → V) via pureFullyClosedSepGraph := pureFullyClosedSepGraph_defined
  haveI : 𝚫₁-Function₁ (pureFullyClosedSeparation : V → V) via pureFullyClosedSepGraph.graphDelta :=
    HierarchySymbol.DefinedFunction.graph_delta pureFullyClosedSepGraph_defined
  refine ⟨?_⟩
  constructor
  · intro v
    simp [fullSepUniform, HierarchySymbol.Semiformula.val_sigma,
      HierarchySymbol.Defined.iff_delta_pi, HierarchySymbol.Defined.iff_delta_sigma]
  · intro v
    simp [fullSepUniform,fullSepPure, HierarchySymbol.Semiformula.val_sigma,
      HierarchySymbol.Defined.iff_delta_sigma, eq_comm]

theorem fullSepUniform_provablyProper : fullSepUniform.ProvablyProperOn 𝗜𝚺₁ := by
  apply HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0}
  intro W _ _
  letI : 𝚫₁-Predicate (fullSepPure : W → Prop) via fullSepUniform := fullSepUniform_defined
  exact HierarchySymbol.Defined.proper
#print axioms fullSepUniform_defined
#print axioms fullSepUniform_provablyProper
end generic
end PA194BindSource
