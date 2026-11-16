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
namespace PA194SeparationRootCode
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

open PA194SeparationShiftCode PA194ReopenIterCode PA194FullSepOpen PA194ReopenOneCode PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


/-- Reopen the actual full-source separation axiom with a fixed proof-code function. -/
noncomputable def separationRootCode (p : M) : M :=
  let root := sepRoot p
  let n := formulaFreeBound root
  let closed := fullyClosedSeparation p
  let seed := axm ({closed} : M) closed
  reopenIterCode root n seed n

noncomputable def separationRootGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out p. ∃ root, !sepRootGraph root p ∧ ∃ n, !pureFormulaFreeBoundGraph n root ∧
    ∃ closed, !closeIterBlueprint.resultDef closed n root ∧ ∃ singleton, !expDef singleton closed ∧
    ∃ seed, !axmGraph seed singleton closed ∧ !reopenIterGraph out root n seed n”

theorem separationRootGraph_defined : 𝚺₁-Function₁ (separationRootCode : M → M) via separationRootGraph := by
  haveI := sepRootGraph_defined (V := M)
  haveI := pureFormulaFreeBound_defined (V := M)
  haveI := reopenIterGraph_defined (M := M)
  haveI := pureModelClose_defined (V := M)
  exact .mk fun v => by simp [separationRootGraph,separationRootCode,fullyClosedSeparation,
    pureFormulaFreeBound_model,sepRootPure_model_local,pureModelClose_model,singleton_def]

noncomputable def separationRootProof (p : M) (hp : IsSemiformula SourceL 1 p) :
    (⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩ : InternalTheory M SourceL) ⊢!
      (⟨sepRoot p,sepRoot_scoped p hp⟩ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  have ha : fullyClosedSeparation p ∈ T.theory.Δ₁Class (V := M) :=
    (adjunctiveFullSepTheory_class _).2 (Or.inr ⟨p,hp,rfl⟩)
  let d : T ⊢! (⟨fullyClosedSeparation p, (fullyClosedSeparation_sentence p hp).1⟩ : Formula M SourceL) := TProof.byAxm ha
  exact reopenIterProof T (sepRoot p) (formulaFreeBound (sepRoot p)) (sepRoot_scoped p hp) d

@[simp] theorem separationRootProof_val (p : M) (hp : IsSemiformula SourceL 1 p) :
    (separationRootProof p hp).val = separationRootCode p := by
  simp only [separationRootProof,separationRootCode,reopenIterProof_val,
    TProof.byAxm,TDerivation.byAxm_val,fullyClosedSeparation,
    Sequent.val_insert,Sequent.val_empty,singleton_def,insert_empty_eq]

#print axioms separationRootGraph_defined
#print axioms separationRootProof
#print axioms separationRootProof_val
end models
end PA194SeparationRootCode
