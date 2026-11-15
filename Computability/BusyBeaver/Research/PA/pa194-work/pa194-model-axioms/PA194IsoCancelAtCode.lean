import PA194LeastExcludesClosedModel
import PA194FullSepWitnessBranch
import PA194ContextFourSpecializeCode
import PA194IsoCancelUniversal
import PA194ContextFiveSpecializeCode
import PA194OrderIsoGreatestUniversal
import PA194ContextTripleSpecializeCode
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194IsoCancelAtCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194FullSepWitnessBranch PA194LeastExcludesClosedModel PA194LeastExcludesClosedTemplate PA194ContextTripleSpecializeCode PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def domainB3 : Semiproposition M6.PA.RelationalSource.language 3 := domain (.bvar 1)
def leastCB3 : Semiproposition M6.PA.RelationalSource.language 3 := least (.bvar 2) (.bvar 1)
def memberBM3 : Semiproposition M6.PA.RelationalSource.language 3 := mem (.bvar 1) (.bvar 0)
def memberCM3 : Semiproposition M6.PA.RelationalSource.language 3 := mem (.bvar 2) (.bvar 0)

open PA194ContextFourSpecializeCode PA194IsoCancelUniversal PA194IsoCancelTemplate M6.PA.RelationalSource.PairGraph PA194ContextFiveSpecializeCode PA194OrderIsoGreatestUniversal PA194OrderIsoGreatestTemplate
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

def cancelDomainBound4 : Semiproposition M6.PA.RelationalSource.language 4 := Ordinal.domain (.bvar 1)
def cancelLeftSuccessorBound4 : Semiproposition M6.PA.RelationalSource.language 4 := Ordinal.successor (.bvar 2) (.bvar 0)
def cancelRightSuccessorBound4 : Semiproposition M6.PA.RelationalSource.language 4 := Ordinal.successor (.bvar 3) (.bvar 1)
def cancelSuccessorIsoBound4 : Semiproposition M6.PA.RelationalSource.language 4 := orderIso (.bvar 0) (.bvar 1)
def cancelPredecessorIsoBound4 : Semiproposition M6.PA.RelationalSource.language 4 := orderIso (.bvar 2) (.bvar 3)

noncomputable def isoCancelAtCode (a b p q ctx du hd hp hq hi : M) : M :=
  let vec := (?[ ^&a, ^&b, ^&p, ^&q] : M)
  let dom := subst SourceL vec (⌜cancelDomainBound4⌝ : M)
  let left := subst SourceL vec (⌜cancelLeftSuccessorBound4⌝ : M)
  let right := subst SourceL vec (⌜cancelRightSuccessorBound4⌝ : M)
  let iso := subst SourceL vec (⌜cancelSuccessorIsoBound4⌝ : M)
  let goal := subst SourceL vec (⌜cancelPredecessorIsoBound4⌝ : M)
  let imp4 := neg SourceL iso ^⋎ goal
  let imp3 := neg SourceL right ^⋎ imp4
  let imp2 := neg SourceL left ^⋎ imp3
  let sp := contextFourCode (⌜isoCancelBound⌝ : M) (^&a) (^&b) (^&p) (^&q) ctx du
  let r1 := contextMPCode dom imp2 ctx sp hd
  let r2 := contextMPCode left imp3 ctx r1 hp
  let r3 := contextMPCode right imp4 ctx r2 hq
  contextMPCode iso goal ctx r3 hi

noncomputable def isoCancelAtGraph : 𝚺₁.Semisentence 11 := .mkSigma
  “out a b p q ctx du hd hp hq hi.
    ∃ body, !(fixedFormulaQuoteGraph isoCancelBound) body ∧
    ∃ d0, !(fixedFormulaQuoteGraph cancelDomainBound4) d0 ∧ ∃ l0, !(fixedFormulaQuoteGraph cancelLeftSuccessorBound4) l0 ∧
    ∃ r0, !(fixedFormulaQuoteGraph cancelRightSuccessorBound4) r0 ∧ ∃ i0, !(fixedFormulaQuoteGraph cancelSuccessorIsoBound4) i0 ∧
    ∃ c0, !(fixedFormulaQuoteGraph cancelPredecessorIsoBound4) c0 ∧
    ∃ va, !qqFvarDef va a ∧ ∃ vb, !qqFvarDef vb b ∧ ∃ vp, !qqFvarDef vp p ∧ ∃ vq, !qqFvarDef vq q ∧
    ∃ v1, !adjoinDef v1 vq 0 ∧ ∃ v2, !adjoinDef v2 vp v1 ∧ ∃ v3, !adjoinDef v3 vb v2 ∧ ∃ vec, !adjoinDef vec va v3 ∧
    ∃ dom, !(substsGraph SourceL) dom vec d0 ∧ ∃ left, !(substsGraph SourceL) left vec l0 ∧
    ∃ right, !(substsGraph SourceL) right vec r0 ∧ ∃ iso, !(substsGraph SourceL) iso vec i0 ∧ ∃ goal, !(substsGraph SourceL) goal vec c0 ∧
    ∃ ni, !(negGraph SourceL) ni iso ∧ ∃ imp4, !qqOrDef imp4 ni goal ∧
    ∃ nr, !(negGraph SourceL) nr right ∧ ∃ imp3, !qqOrDef imp3 nr imp4 ∧
    ∃ nl, !(negGraph SourceL) nl left ∧ ∃ imp2, !qqOrDef imp2 nl imp3 ∧
    ∃ sp, !contextFourGraph sp body va vb vp vq ctx du ∧ ∃ r1, !contextMPGraph r1 dom imp2 ctx sp hd ∧
    ∃ r2, !contextMPGraph r2 left imp3 ctx r1 hp ∧ ∃ r3, !contextMPGraph r3 right imp4 ctx r2 hq ∧
    !contextMPGraph out iso goal ctx r3 hi”

theorem isoCancelAtGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 10 → M => isoCancelAtCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) (w 8) (w 9)) isoCancelAtGraph := by
  haveI := contextFourGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun w => by simp [isoCancelAtGraph,isoCancelAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def isoCancelAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b p q : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ isoCancelBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜cancelDomainBound4⌝ : Semiformula M SourceL 4).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) Γ)
    (hp : T ⊢!ᵈᵉʳ insert ((⌜cancelLeftSuccessorBound4⌝ : Semiformula M SourceL 4).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) Γ)
    (hq : T ⊢!ᵈᵉʳ insert ((⌜cancelRightSuccessorBound4⌝ : Semiformula M SourceL 4).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) Γ)
    (hi : T ⊢!ᵈᵉʳ insert ((⌜cancelSuccessorIsoBound4⌝ : Semiformula M SourceL 4).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) Γ)
    : T ⊢!ᵈᵉʳ insert ((⌜cancelPredecessorIsoBound4⌝ : Semiformula M SourceL 4).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) Γ := by
  let body : Semiformula M SourceL 4 := ⌜isoCancelBound⌝
  let dom : Semiformula M SourceL 4 := ⌜cancelDomainBound4⌝
  let left : Semiformula M SourceL 4 := ⌜cancelLeftSuccessorBound4⌝
  let right : Semiformula M SourceL 4 := ⌜cancelRightSuccessorBound4⌝
  let iso : Semiformula M SourceL 4 := ⌜cancelSuccessorIsoBound4⌝
  let goal : Semiformula M SourceL 4 := ⌜cancelPredecessorIsoBound4⌝
  have heb : body = dom 🡒 (left 🡒 (right 🡒 (iso 🡒 goal))) := by
    simp [body,dom,left,right,iso,goal,isoCancelBound,cancelDomainBound4,cancelLeftSuccessorBound4,
      cancelRightSuccessorBound4,cancelSuccessorIsoBound4,cancelPredecessorIsoBound4, Bootstrapping.Semiformula.imp_def]
  have heu : (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ isoCancelBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ ∀⁰ ∀⁰ ∀⁰ body := by simp [body]
  let du' := TDerivation.cast (congrArg (fun z => insert z Γ) heu) du
  let sp := contextFourProof T Γ body (Semiterm.fvar a) (Semiterm.fvar b) (Semiterm.fvar p) (Semiterm.fvar q) du'
  have hei : (body.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q] : Formula M SourceL) =
      ((dom.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) 🡒 ((left.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) 🡒
       ((right.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) 🡒 ((iso.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) 🡒 (goal.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]))))) := by
    rw [heb]; simp
  let sp' := TDerivation.cast (congrArg (fun z => insert z Γ) hei) sp
  let r1 := contextMPProof T Γ _ _ sp' hd
  let r2 := contextMPProof T Γ _ _ r1 hp
  let r3 := contextMPProof T Γ _ _ r2 hq
  exact contextMPProof T Γ _ _ r3 hi

@[simp] theorem isoCancelAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b p q : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ ∀⁰ isoCancelBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜cancelDomainBound4⌝ : Semiformula M SourceL 4).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) Γ)
    (hp : T ⊢!ᵈᵉʳ insert ((⌜cancelLeftSuccessorBound4⌝ : Semiformula M SourceL 4).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) Γ)
    (hq : T ⊢!ᵈᵉʳ insert ((⌜cancelRightSuccessorBound4⌝ : Semiformula M SourceL 4).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) Γ)
    (hi : T ⊢!ᵈᵉʳ insert ((⌜cancelSuccessorIsoBound4⌝ : Semiformula M SourceL 4).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p,Semiterm.fvar q]) Γ)
    : (isoCancelAtProof T Γ a b p q du hd hp hq hi).val = isoCancelAtCode a b p q Γ.val du.val hd.val hp.val hq.val hi.val := by
  simp [isoCancelAtProof,isoCancelAtCode,Semiformula.imp_def,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms isoCancelAtGraph_defined
#print axioms isoCancelAtProof
#print axioms isoCancelAtProof_val
end models
end PA194IsoCancelAtCode
