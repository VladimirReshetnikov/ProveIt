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
namespace PA194ReopenOneCode
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

open PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


/-- The source binder's fixed arithmetic graph. -/
noncomputable def sourceBindGraph : 𝚺₁.Semisentence 3 := FormulaClose.blueprint.result SourceL

theorem sourceBindGraph_defined : 𝚺₁-Function₂ (bindFormula : M → M → M) via sourceBindGraph := .mk fun v => by
  change sourceBindGraph.val.Evalb v ↔ v 0 = bindFormula (v 1) (v 2)
  simpa [sourceBindGraph,bindFormula] using FormulaClose.construction.result_defined.defined v

noncomputable def reopenOneCode (p d : M) : M :=
  let b := bindFormula 0 p
  let sh := contextShiftCode (^∀ b) (∅ : M) d
  contextSpecializeCode (shift SourceL b) (^&(0 : M)) (∅ : M) sh

noncomputable def reopenOneGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out p d. ∃ b, !sourceBindGraph b 0 p ∧ ∃ all, !qqAllDef all b ∧
    ∃ sh, !contextShiftGraph sh all 0 d ∧ ∃ sb, !(shiftGraph SourceL) sb b ∧
    ∃ t, !qqFvarDef t 0 ∧ !contextSpecializeGraph out sb t 0 sh”

theorem reopenOneGraph_defined : 𝚺₁-Function₂ (reopenOneCode : M → M → M) via reopenOneGraph := by
  haveI := sourceBindGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  haveI := contextSpecializeGraph_defined (M := M)
  exact .mk fun v => by simp [reopenOneGraph,reopenOneCode,EmptyCollection.emptyCollection]

noncomputable def reopenOneProof (T : InternalTheory M SourceL) (p : M) (hp : IsSemiformula SourceL 0 p)
    (d : T ⊢! (⟨closeOne p, closeOne_scoped p hp⟩ : Formula M SourceL)) :
    T ⊢! (⟨p,hp⟩ : Formula M SourceL) := by
  have hb := bindFormula_scope_open p hp
  let body : Semiformula M SourceL 1 := ⟨bindFormula 0 p, by simpa using hb.1⟩
  let closed : Formula M SourceL := ∀⁰ body
  have he : closed = (⟨closeOne p,closeOne_scoped p hp⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    rfl
  let din := TDerivation.cast (congrArg (fun f => insert f ∅) he.symm) d
  let sh := contextShiftProof T ∅ closed din
  have hseq : insert closed.shift (∅ : Sequent M SourceL).shift = insert (∀⁰ body.shift) ∅ := by
    apply Sequent.ext
    intro x
    simp [closed,Sequent.shift,Sequent.mem_iff]
  let sh' := TDerivation.cast hseq sh
  let out := contextSpecializeProof T ∅ body.shift (Semiterm.fvar 0) sh'
  have hopen : body.free = (⟨p,hp⟩ : Formula M SourceL) := by
    apply Semiformula.ext
    simpa [body] using hb.2
  exact TDerivation.toTProof (TDerivation.cast (congrArg (fun f => insert f ∅) hopen) out)

@[simp] theorem reopenOneProof_val (T : InternalTheory M SourceL) (p : M) (hp : IsSemiformula SourceL 0 p)
    (d : T ⊢! (⟨closeOne p, closeOne_scoped p hp⟩ : Formula M SourceL)) :
    (reopenOneProof T p hp d).val = reopenOneCode p d.val := by
  simp [reopenOneProof,reopenOneCode,closeOne,Sequent.shift,TDerivation.toTProof]

#print axioms sourceBindGraph_defined
#print axioms reopenOneGraph_defined
#print axioms reopenOneProof
#print axioms reopenOneProof_val
end models
end PA194ReopenOneCode
