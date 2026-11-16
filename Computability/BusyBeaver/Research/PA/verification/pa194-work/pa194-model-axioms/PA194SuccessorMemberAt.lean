import PA194SuccessorMemberClosedModel
import PA194GreatestSuccessorClosedModel
import PA194FullSepWitnessBranch
import PA194DomainInstances
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194SuccessorMemberAt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SuccessorMemberClosedTemplate PA194SuccessorMemberClosedModel PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def successorPred2 : Semiproposition M6.PA.RelationalSource.language 2 := successor (.bvar 1) (.bvar 0)
def successorMem2 : Semiproposition M6.PA.RelationalSource.language 2 := mem (.bvar 0) (.bvar 1)

section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open M6.PA.RelationalSource

open M6.PA.RelationalSource

theorem successorPred2_eq : successorPred2 = successorTemplate := by rfl

theorem successorMem_at (a b : M) :
    ((⌜successorMem2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar a,Semiterm.fvar b] := by
  apply Semiformula.ext
  simp [successorMem2,mem,Semiformula.quote_def,SemitermVec.val_succ,Matrix.vecHead,Matrix.vecTail]

noncomputable def successorMemberAtCode (a b g du hs : M) : M :=
  let vec := (?[ ^&b, ^&a] : M)
  let body := (⌜successorMemberBound⌝ : M)
  let succ := subst SourceL vec (⌜successorPred2⌝ : M)
  let mem := subst SourceL vec (⌜successorMem2⌝ : M)
  let sp := contextDoubleCode body (^&b) (^&a) g du
  contextMPCode succ mem g sp hs

noncomputable def successorMemberAtGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out a b g du hs. ∃ tb, !qqFvarDef tb b ∧ ∃ ta, !qqFvarDef ta a ∧ ∃ tail, !adjoinDef tail ta 0 ∧ ∃ vec, !adjoinDef vec tb tail ∧
    ∃ body, !(fixedFormulaQuoteGraph successorMemberBound) body ∧ ∃ st, !(fixedFormulaQuoteGraph successorPred2) st ∧
    ∃ mt, !(fixedFormulaQuoteGraph successorMem2) mt ∧ ∃ succ, !(substsGraph SourceL) succ vec st ∧
    ∃ mem, !(substsGraph SourceL) mem vec mt ∧ ∃ sp, !contextDoubleGraph sp body tb ta g du ∧
    !contextMPGraph out succ mem g sp hs”

theorem successorMemberAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => successorMemberAtCode (v 0) (v 1) (v 2) (v 3) (v 4)) successorMemberAtGraph := by
  haveI := contextDoubleGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [successorMemberAtGraph,successorMemberAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def successorMemberAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hs : T ⊢!ᵈᵉʳ insert ((⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) :
    T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar a,Semiterm.fvar b]) : Formula M SourceL) Γ := by
  let body : Semiformula M SourceL 2 := ⌜successorMemberBound⌝
  let succ : Semiformula M SourceL 2 := ⌜successorPred2⌝
  let mem : Semiformula M SourceL 2 := ⌜successorMem2⌝
  have heb : body = succ 🡒 mem := by
    simp [body,succ,mem,successorMemberBound,successorPred2,successorMem2,sourceImply, ←Semiformula.neg_eq, Bootstrapping.Semiformula.imp_def]
    change Semiformula.typedQuote M _ = _
    simp only [Semiformula.typedQuote, Semiformula.typedQuote_neg]
    rfl
  have heu : (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ ∀⁰ body := by simp [body]
  let du' := TDerivation.cast (congrArg (fun q => insert q Γ) heu) du
  let sp := contextDoubleProof T Γ body (Semiterm.fvar b) (Semiterm.fvar a) du'
  have hei : (body.subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      ((succ.subst ![Semiterm.fvar b,Semiterm.fvar a]) 🡒 (mem.subst ![Semiterm.fvar b,Semiterm.fvar a])) := by
    rw [heb]; simp
  let sp' := TDerivation.cast (congrArg (fun q => insert q Γ) hei) sp
  have es : succ = (⌜successorTemplate⌝ : Semiformula M SourceL 2) := by simp [succ,successorPred2_eq]
  let hs' := TDerivation.cast (congrArg (fun f : Semiformula M SourceL 2 => insert (f.subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) es.symm) hs
  let out := contextMPProof T Γ _ _ sp' hs'
  exact TDerivation.cast (congrArg (fun q => insert q Γ) (successorMem_at a b)) out

@[simp] theorem successorMemberAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ successorMemberBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hs : T ⊢!ᵈᵉʳ insert ((⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a]) Γ) :
    (successorMemberAtProof T Γ a b du hs).val = successorMemberAtCode a b Γ.val du.val hs.val := by
  simp [successorMemberAtProof,successorMemberAtCode,Semiformula.imp_def,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms successorPred2_eq
#print axioms successorMem_at
#print axioms successorMemberAtGraph_defined
#print axioms successorMemberAtProof
#print axioms successorMemberAtProof_val
end models
end PA194SuccessorMemberAt
