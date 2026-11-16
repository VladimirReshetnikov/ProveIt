import PA194LeastExcludesClosedModel
import PA194FullSepWitnessBranch
import PA194IsoMatchUniversal
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
namespace PA194IsoMatchAtCode
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

open PA194IsoMatchUniversal PA194IsoMatchTemplate M6.PA.RelationalSource.PairGraph
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

def matchDomainBound3 : Semiproposition M6.PA.RelationalSource.language 3 := Ordinal.domain (.bvar 1)
def matchSuccessorBound3 : Semiproposition M6.PA.RelationalSource.language 3 := Ordinal.successor (.bvar 2) (.bvar 0)
def matchIsoBound3 : Semiproposition M6.PA.RelationalSource.language 3 := orderIso (.bvar 0) (.bvar 1)
def matchGoalBound3 : Semiproposition M6.PA.RelationalSource.language 3 := isoPredecessorMatch (.bvar 2) (.bvar 1)

noncomputable def isoMatchAtCode (a b p ctx du hd hs hi : M) : M :=
  let vec := (?[ ^&a, ^&b, ^&p] : M)
  let dom := subst SourceL vec (⌜matchDomainBound3⌝ : M)
  let succ := subst SourceL vec (⌜matchSuccessorBound3⌝ : M)
  let iso := subst SourceL vec (⌜matchIsoBound3⌝ : M)
  let goal := subst SourceL vec (⌜matchGoalBound3⌝ : M)
  let imp3 := neg SourceL iso ^⋎ goal
  let imp2 := neg SourceL succ ^⋎ imp3
  let sp := contextTripleCode (⌜isoMatchBound⌝ : M) (^&a) (^&b) (^&p) ctx du
  let r1 := contextMPCode dom imp2 ctx sp hd
  let r2 := contextMPCode succ imp3 ctx r1 hs
  contextMPCode iso goal ctx r2 hi

noncomputable def isoMatchAtGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “out a b p ctx du hd hs hi.
    ∃ body, !(fixedFormulaQuoteGraph isoMatchBound) body ∧
    ∃ d0, !(fixedFormulaQuoteGraph matchDomainBound3) d0 ∧ ∃ s0, !(fixedFormulaQuoteGraph matchSuccessorBound3) s0 ∧
    ∃ i0, !(fixedFormulaQuoteGraph matchIsoBound3) i0 ∧ ∃ c0, !(fixedFormulaQuoteGraph matchGoalBound3) c0 ∧
    ∃ va, !qqFvarDef va a ∧ ∃ vb, !qqFvarDef vb b ∧ ∃ vp, !qqFvarDef vp p ∧
    ∃ v1, !adjoinDef v1 vp 0 ∧ ∃ v2, !adjoinDef v2 vb v1 ∧ ∃ vec, !adjoinDef vec va v2 ∧
    ∃ dom, !(substsGraph SourceL) dom vec d0 ∧ ∃ succ, !(substsGraph SourceL) succ vec s0 ∧
    ∃ iso, !(substsGraph SourceL) iso vec i0 ∧ ∃ goal, !(substsGraph SourceL) goal vec c0 ∧
    ∃ ni, !(negGraph SourceL) ni iso ∧ ∃ imp3, !qqOrDef imp3 ni goal ∧
    ∃ ns, !(negGraph SourceL) ns succ ∧ ∃ imp2, !qqOrDef imp2 ns imp3 ∧
    ∃ sp, !contextTripleGraph sp body va vb vp ctx du ∧ ∃ r1, !contextMPGraph r1 dom imp2 ctx sp hd ∧
    ∃ r2, !contextMPGraph r2 succ imp3 ctx r1 hs ∧ !contextMPGraph out iso goal ctx r2 hi”

theorem isoMatchAtGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 8 → M => isoMatchAtCode (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7)) isoMatchAtGraph := by
  haveI := contextTripleGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun w => by simp [isoMatchAtGraph,isoMatchAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def isoMatchAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b p : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜matchDomainBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (hs : T ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (hi : T ⊢!ᵈᵉʳ insert ((⌜matchIsoBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    : T ⊢!ᵈᵉʳ insert ((⌜matchGoalBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ := by
  let body : Semiformula M SourceL 3 := ⌜isoMatchBound⌝
  let dom : Semiformula M SourceL 3 := ⌜matchDomainBound3⌝
  let succ : Semiformula M SourceL 3 := ⌜matchSuccessorBound3⌝
  let iso : Semiformula M SourceL 3 := ⌜matchIsoBound3⌝
  let goal : Semiformula M SourceL 3 := ⌜matchGoalBound3⌝
  have heb : body = dom 🡒 (succ 🡒 (iso 🡒 goal)) := by
    simp [body,dom,succ,iso,goal,isoMatchBound,matchDomainBound3,matchSuccessorBound3,
      matchIsoBound3,matchGoalBound3,Bootstrapping.Semiformula.imp_def]
  have heu : (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ ∀⁰ ∀⁰ body := by simp [body]
  let du' := TDerivation.cast (congrArg (fun z => insert z Γ) heu) du
  let sp := contextTripleProof T Γ body (Semiterm.fvar a) (Semiterm.fvar b) (Semiterm.fvar p) du'
  have hei : (body.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p] : Formula M SourceL) =
      ((dom.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) 🡒 ((succ.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) 🡒
       ((iso.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) 🡒 (goal.subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p])))) := by
    rw [heb]; simp
  let sp' := TDerivation.cast (congrArg (fun z => insert z Γ) hei) sp
  let r1 := contextMPProof T Γ _ _ sp' hd
  let r2 := contextMPProof T Γ _ _ r1 hs
  exact contextMPProof T Γ _ _ r2 hi

@[simp] theorem isoMatchAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b p : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ isoMatchBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜matchDomainBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (hs : T ⊢!ᵈᵉʳ insert ((⌜matchSuccessorBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    (hi : T ⊢!ᵈᵉʳ insert ((⌜matchIsoBound3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar a,Semiterm.fvar b,Semiterm.fvar p]) Γ)
    : (isoMatchAtProof T Γ a b p du hd hs hi).val = isoMatchAtCode a b p Γ.val du.val hd.val hs.val hi.val := by
  simp [isoMatchAtProof,isoMatchAtCode,Semiformula.imp_def,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms isoMatchAtGraph_defined
#print axioms isoMatchAtProof
#print axioms isoMatchAtProof_val
end models
end PA194IsoMatchAtCode
