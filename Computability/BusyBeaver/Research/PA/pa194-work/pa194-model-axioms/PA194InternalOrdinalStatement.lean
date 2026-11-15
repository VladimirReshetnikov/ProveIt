import PA194InternalOrdinalStep
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalOrdinalStatement
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194BindSource
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance ordinalStatementZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalStatementOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalStatementAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalStatementMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalStatementLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalStatementIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Ordinal-induction implication assembled from base, step and conclusion codes. -/
noncomputable def inductionStatementCode (base step conclusion : M) : M :=
  neg SourceL base ^⋎ (neg SourceL step ^⋎ conclusion)

noncomputable def inductionStatementGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out base step conclusion. ∃ a, !(negGraph SourceL) a base ∧ ∃ b, !(negGraph SourceL) b step ∧
    ∃ c, !qqOrDef c b conclusion ∧ !qqOrDef out a c”

theorem inductionStatementGraph_defined :
    𝚺₁-Function₃ (inductionStatementCode : M → M → M → M) via inductionStatementGraph := .mk fun v => by
  simp [inductionStatementGraph,inductionStatementCode]

theorem inductionStatementCode_scoped (base step conclusion : M)
    (hb : IsSemiformula SourceL 0 base) (hs : IsSemiformula SourceL 0 step)
    (hc : IsSemiformula SourceL 0 conclusion) : IsSemiformula SourceL 0 (inductionStatementCode base step conclusion) := by
  simp [inductionStatementCode,IsSemiformula.or,hb,hs,hc]

#print axioms inductionStatementGraph_defined
#print axioms inductionStatementCode_scoped
end models
end PA194InternalOrdinalStatement
