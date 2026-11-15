import PA194LeastExcludesAtCode
import PA194GreatestSuccessorAtCode
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
namespace PA194LeastMemberProjection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194LeastExcludesAtCode PA194GreatestSuccessorAtCode PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def leastTailCB3 : Semiproposition M6.PA.RelationalSource.language 3 :=
  ∀⁰ (mem (.bvar 3) (.bvar 0) 🡒 (eq (.bvar 2) (.bvar 0) ⋎ mem (.bvar 0) (.bvar 2)))

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

theorem leastAt_decompose (a b c : M) :
    ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar c] : Formula M SourceL) =
      (Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar c] ⋏
       ((⌜leastTailCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar c])) := by
  have he : (⌜leastCB3⌝ : Semiformula M SourceL 3) =
      (⌜(mem (.bvar 2) (.bvar 1) : Semiproposition M6.PA.RelationalSource.language 3)⌝ : Semiformula M SourceL 3) ⋏ ⌜leastTailCB3⌝ := by
    simp [leastCB3,least,leastTailCB3,mem,eq,sourceImply]
  rw [he]
  simp only [Semiformula.substs_and]
  congr 1
  apply Semiformula.ext
  simp [Semiformula.typedQuote,Semiformula.quote_def,mem,SemitermVec.val_succ,substs1,Matrix.vecHead,Matrix.vecTail]

noncomputable def leastMemberCode (a b c g d : M) : M :=
  let mem := memberFvarCode b c
  let rest := subst SourceL (?[ ^&a, ^&b, ^&c] : M) (⌜leastTailCB3⌝ : M)
  contextAndLeftCode mem rest g d

noncomputable def leastMemberGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out a b c g d. ∃ mem, !memberFvarGraph mem b c ∧ ∃ tail, !(fixedFormulaQuoteGraph leastTailCB3) tail ∧
    ∃ ta, !qqFvarDef ta a ∧ ∃ tb, !qqFvarDef tb b ∧ ∃ tc, !qqFvarDef tc c ∧
    ∃ v1, !adjoinDef v1 tc 0 ∧ ∃ v2, !adjoinDef v2 tb v1 ∧ ∃ vec, !adjoinDef vec ta v2 ∧
    ∃ rest, !(substsGraph SourceL) rest vec tail ∧ !contextAndLeftGraph out mem rest g d”

theorem leastMemberGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => leastMemberCode (v 0) (v 1) (v 2) (v 3) (v 4)) leastMemberGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := contextAndLeftGraph_defined (M := M)
  exact .mk fun v => by simp [leastMemberGraph,leastMemberCode,fixedFormulaQuoteGraph_correct]

noncomputable def leastMemberProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b c : M)
    (d : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar c]) Γ) :
    T ⊢!ᵈᵉʳ insert ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar c]) : Formula M SourceL) Γ := by
  let mc : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar c]
  let rest : Formula M SourceL := (⌜leastTailCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar c]
  let d' := TDerivation.cast (congrArg (fun q => insert q Γ) (leastAt_decompose a b c)) d
  exact contextAndLeftProof T Γ mc rest d'

@[simp] theorem leastMemberProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b c : M)
    (d : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar c]) Γ) :
    (leastMemberProof T Γ a b c d).val = leastMemberCode a b c Γ.val d.val := by
  have hm : ((Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar c]) : Formula M SourceL).val = memberFvarCode b c := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [leastMemberProof,leastMemberCode,contextAndLeftProof_val,TDerivation.cast_val,
    Bootstrapping.Semiformula.val_substs,SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hm,Semiformula.quote_def]
  simp [Matrix.vecHead,Matrix.vecTail]

#print axioms leastAt_decompose
#print axioms leastMemberGraph_defined
#print axioms leastMemberProof
#print axioms leastMemberProof_val
end models
end PA194LeastMemberProjection
