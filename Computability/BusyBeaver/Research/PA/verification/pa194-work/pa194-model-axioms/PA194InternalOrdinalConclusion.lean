import PA194FullyClosedSeparation
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalOrdinalConclusion
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
local instance ordinalIntZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalIntOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalIntAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalIntMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalIntLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalIntIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Numeric ordinal-induction conclusion `∀x, domain(x) → p(x)`. -/
noncomputable def inductionConclusionCode (d p : M) : M :=
  ^∀ (neg SourceL d ^⋎ p)

noncomputable def inductionConclusionGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out d p. ∃ n, !(negGraph SourceL) n d ∧
    ∃ b, !qqOrDef b n p ∧ !qqAllDef out b”

theorem inductionConclusionGraph_defined :
    𝚺₁-Function₂ (inductionConclusionCode : M → M → M) via inductionConclusionGraph := .mk fun v => by
  simp [inductionConclusionGraph,inductionConclusionCode]

theorem inductionConclusionCode_scoped (d p : M) (hd : IsSemiformula SourceL 1 d) (hp : IsSemiformula SourceL 1 p) :
    IsSemiformula SourceL 0 (inductionConclusionCode d p) := by
  simp [inductionConclusionCode,IsSemiformula.all,IsSemiformula.or,hd,hp]

#print axioms inductionConclusionGraph_defined
#print axioms inductionConclusionCode_scoped
end models
end PA194InternalOrdinalConclusion
