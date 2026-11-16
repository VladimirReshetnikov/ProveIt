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
namespace PA194GreatestSuccessorAtCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def greatestBM2 : Semiproposition M6.PA.RelationalSource.language 2 := greatest (.bvar 1) (.bvar 0)
def successorMB2 : Semiproposition M6.PA.RelationalSource.language 2 := successor (.bvar 0) (.bvar 1)

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

noncomputable def greatestSuccessorAtCode (b m g du hd hg : M) : M :=
  let body := (⌜greatestSuccessorBound⌝ : M)
  let vec := (?[ ^&m, ^&b] : M)
  let dom := subst SourceL vec (⌜domainOne⌝ : M)
  let greatest := subst SourceL vec (⌜greatestBM2⌝ : M)
  let succ := subst SourceL vec (⌜successorMB2⌝ : M)
  let imp := neg SourceL greatest ^⋎ succ
  let sp := contextDoubleCode body (^&m) (^&b) g du
  let mid := contextMPCode dom imp g sp hd
  contextMPCode greatest succ g mid hg

noncomputable def greatestSuccessorAtGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out b m g du hd hg. ∃ body, !(fixedFormulaQuoteGraph greatestSuccessorBound) body ∧
    ∃ dt, !(fixedFormulaQuoteGraph domainOne) dt ∧ ∃ gt, !(fixedFormulaQuoteGraph greatestBM2) gt ∧
    ∃ st, !(fixedFormulaQuoteGraph successorMB2) st ∧ ∃ tm, !qqFvarDef tm m ∧ ∃ tb, !qqFvarDef tb b ∧
    ∃ tail, !adjoinDef tail tb 0 ∧ ∃ vec, !adjoinDef vec tm tail ∧
    ∃ dom, !(substsGraph SourceL) dom vec dt ∧ ∃ greatest, !(substsGraph SourceL) greatest vec gt ∧
    ∃ succ, !(substsGraph SourceL) succ vec st ∧ ∃ ng, !(negGraph SourceL) ng greatest ∧ ∃ imp, !qqOrDef imp ng succ ∧
    ∃ sp, !contextDoubleGraph sp body tm tb g du ∧ ∃ mid, !contextMPGraph mid dom imp g sp hd ∧
    !contextMPGraph out greatest succ g mid hg”

theorem greatestSuccessorAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 6 → M => greatestSuccessorAtCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) greatestSuccessorAtGraph := by
  haveI := contextDoubleGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [greatestSuccessorAtGraph,greatestSuccessorAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def greatestSuccessorAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (b m : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜domainOne⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ)
    (hg : T ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜successorMB2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ := by
  let body : Semiformula M SourceL 2 := ⌜greatestSuccessorBound⌝
  let dom : Semiformula M SourceL 2 := ⌜domainOne⌝
  let greatest : Semiformula M SourceL 2 := ⌜greatestBM2⌝
  let succ : Semiformula M SourceL 2 := ⌜successorMB2⌝
  have heb : body = dom 🡒 (greatest 🡒 succ) := by
    simp [body,dom,greatest,succ,greatestSuccessorBound,domainOne,greatestBM2,successorMB2,sourceImply, ←Semiformula.neg_eq, Bootstrapping.Semiformula.imp_def]
    change Semiformula.typedQuote M _ = _
    simp only [Semiformula.typedQuote, Semiformula.typedQuote_neg]
    rfl
  have heu : (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ ∀⁰ body := by simp [body]
  let du' := TDerivation.cast (congrArg (fun q => insert q Γ) heu) du
  let sp := contextDoubleProof T Γ body (Semiterm.fvar m) (Semiterm.fvar b) du'
  have hei : (body.subst ![Semiterm.fvar m,Semiterm.fvar b] : Formula M SourceL) =
      ((dom.subst ![Semiterm.fvar m,Semiterm.fvar b]) 🡒
       ((greatest.subst ![Semiterm.fvar m,Semiterm.fvar b]) 🡒 (succ.subst ![Semiterm.fvar m,Semiterm.fvar b]))) := by
    rw [heb]; simp
  let sp' := TDerivation.cast (congrArg (fun q => insert q Γ) hei) sp
  let mid := contextMPProof T Γ _ _ sp' hd
  exact contextMPProof T Γ _ _ mid hg

@[simp] theorem greatestSuccessorAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (b m : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜domainOne⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ)
    (hg : T ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ) :
    (greatestSuccessorAtProof T Γ b m du hd hg).val = greatestSuccessorAtCode b m Γ.val du.val hd.val hg.val := by
  simp [greatestSuccessorAtProof,greatestSuccessorAtCode,Semiformula.imp_def,Semiformula.quote_def,SemitermVec.val_succ]

/-- The predecessor-successor templates use opposite binder order. -/
theorem successorMB2At (b m : M) :
    ((⌜successorMB2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b] : Formula M SourceL) =
      (⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar m] := by
  have hs : successorMB2 = successorTemplate ⇜ ![#1,#0] := by
    simp [successorMB2,successorTemplate]
    successorSyntax
  have ht : (⌜successorMB2⌝ : Semiformula M SourceL 2) =
      (⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 1,Semiterm.bvar 0] := by
    rw [hs, Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht]
  simp [Semiformula.substs_substs]

noncomputable def greatestSuccessorAlignedProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (b m : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hg : T ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar m]) Γ := by
  let hd' := TDerivation.cast (congrArg (fun q => insert q Γ) (domainOneAt b m).symm) hd
  let out := greatestSuccessorAtProof T Γ b m du hd' hg
  exact TDerivation.cast (congrArg (fun q => insert q Γ) (successorMB2At b m)) out

@[simp] theorem greatestSuccessorAlignedProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (b m : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hg : T ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ) :
    (greatestSuccessorAlignedProof T Γ b m du hd hg).val = greatestSuccessorAtCode b m Γ.val du.val hd.val hg.val := by
  simp [greatestSuccessorAlignedProof]

noncomputable def greatestSuccessorAlignedFromTheory (Γ : Sequent M SourceL) (b m : M)
    (hd : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hg : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜greatestBM2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar m,Semiterm.fvar b]) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜successorTemplate⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar m]) Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let uq : Formula M SourceL := ⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝
  let du : T ⊢!ᵈᵉʳ insert uq Γ := TDerivation.wk (greatestSuccessorUniversalProof (M := M)) (by intro x hx; simp at hx ⊢; tauto)
  exact greatestSuccessorAlignedProof T Γ b m du hd hg

#print axioms greatestSuccessorAlignedFromTheory
#print axioms successorMB2At
#print axioms greatestSuccessorAlignedProof
#print axioms greatestSuccessorAlignedProof_val
#print axioms greatestSuccessorAtGraph_defined
#print axioms greatestSuccessorAtProof
#print axioms greatestSuccessorAtProof_val
end models
end PA194GreatestSuccessorAtCode
