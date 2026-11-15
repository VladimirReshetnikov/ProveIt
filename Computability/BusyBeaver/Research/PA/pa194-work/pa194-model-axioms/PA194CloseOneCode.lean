import PA194ContextAllCode
import PA194CloseProof
import PA194SeparationShiftCode
import PA194FullSepOpen
import PA194ReopenIterCode
import PA194UniformFullyClosedModel
import PA194ReopenOneCode
import PA194ContextSpecializeCode
import PA194ContextShiftCode
import PA194OrdinalClosed
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
import PA194OrdinalStatementFromProperty
import PA194OrdinalBaseQuote
import PA194OrdinalConclusionQuote
import PA194OrdinalStatementQuote
import PA194FoundationOrdinalInductionSchema
import PA194TypedSepQuote
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194CloseOneCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194OrdinalStatementFromProperty PA194OrdinalStepFromProperty PA194OrdinalBaseQuote PA194OrdinalConclusionQuote
  PA194InternalOrdinalBase PA194InternalOrdinalConclusion PA194InternalOrdinalStatement PA194OrdinalStatementQuote
open PA194OrdinalPropertyPlacement PA194OrdinalStepQuote PA194TypedSeparation PA194InternalOrdinalStep M6.PA.RelationalSource.Ordinal
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
local instance ordinalFixedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalFixedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalFixedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalFixedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalFixedLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalFixedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194ContextAllCode PA194CloseProof
open PA194SeparationShiftCode PA194ReopenIterCode PA194FullSepOpen PA194ReopenOneCode PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


noncomputable def closeOneCode (p d : M) : M := contextAllCode (bindFormula 0 p) (∅ : M) d

noncomputable def closeOneGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out p d. ∃ b, !sourceBindGraph b 0 p ∧ !contextAllGraph out b 0 d”

theorem closeOneGraph_defined : 𝚺₁-Function₂ (closeOneCode : M → M → M) via closeOneGraph := by
  haveI := sourceBindGraph_defined (M := M)
  haveI := contextAllGraph_defined (M := M)
  exact .mk fun v => by simp [closeOneGraph,closeOneCode,EmptyCollection.emptyCollection]

noncomputable def closeOneCodeProof (T : InternalTheory M SourceL) (p : M) (hp : IsSemiformula SourceL 0 p)
    (d : T ⊢! (⟨p,hp⟩ : Formula M SourceL)) :
    T ⊢! (⟨closeOne p, closeOne_scoped p hp⟩ : Formula M SourceL) := by
  have hb := bindFormula_scope_open p hp
  let body : Semiformula M SourceL 1 := ⟨bindFormula 0 p, by simpa using hb.1⟩
  have hopen : body.free = (⟨p,hp⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    simpa [body] using hb.2
  let din := TDerivation.cast (congrArg (fun f => insert f ∅) hopen.symm) d
  have hseq : insert body.free (∅ : Sequent M SourceL) = insert body.free (∅ : Sequent M SourceL).shift := by
    apply Sequent.ext
    intro x
    simp [Sequent.shift,Sequent.mem_iff]
  let din' := TDerivation.cast hseq din
  let out := contextAllProof T ∅ body din'
  have he : (∀⁰ body) = (⟨closeOne p,closeOne_scoped p hp⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    rfl
  exact TDerivation.toTProof (TDerivation.cast (congrArg (fun f => insert f ∅) he) out)

@[simp] theorem closeOneCodeProof_val (T : InternalTheory M SourceL) (p : M) (hp : IsSemiformula SourceL 0 p)
    (d : T ⊢! (⟨p,hp⟩ : Formula M SourceL)) :
    (closeOneCodeProof T p hp d).val = closeOneCode p d.val := by
  simp [closeOneCodeProof,closeOneCode,Sequent.shift,TDerivation.toTProof]

#print axioms closeOneGraph_defined
#print axioms closeOneCodeProof
#print axioms closeOneCodeProof_val
end models
end PA194CloseOneCode
