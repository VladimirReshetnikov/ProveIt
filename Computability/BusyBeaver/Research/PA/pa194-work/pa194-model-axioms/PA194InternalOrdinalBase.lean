import PA194InternalOrdinalConclusion
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalOrdinalBase
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
local instance ordinalBaseZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalBaseOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalBaseAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalBaseMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalBaseLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalBaseIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Outer ordinal-induction base constructor, parameterized by both fixed templates. -/
noncomputable def inductionBaseCode (d z p : M) : M := ^∀ (neg SourceL (d ^⋏ z) ^⋎ p)

noncomputable def inductionBaseGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out d z p. ∃ a, !qqAndDef a d z ∧ ∃ n, !(negGraph SourceL) n a ∧
    ∃ b, !qqOrDef b n p ∧ !qqAllDef out b”

theorem inductionBaseGraph_defined :
    𝚺₁-Function₃ (inductionBaseCode : M → M → M → M) via inductionBaseGraph := .mk fun v => by
  simp [inductionBaseGraph,inductionBaseCode]

theorem inductionBaseCode_scoped (d z p : M)
    (hd : IsSemiformula SourceL 1 d) (hz : IsSemiformula SourceL 1 z)
    (hp : IsSemiformula SourceL 1 p) : IsSemiformula SourceL 0 (inductionBaseCode d z p) := by
  simp [inductionBaseCode,IsSemiformula.all,IsSemiformula.or,IsSemiformula.and,hd,hz,hp]

#print axioms inductionBaseGraph_defined
#print axioms inductionBaseCode_scoped
end models
end PA194InternalOrdinalBase
