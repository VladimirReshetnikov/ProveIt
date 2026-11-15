import PA194DomainLeastClosedModel
import PA194TraceSubset
import PA194MemberNonempty
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
namespace PA194DomainLeastAt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainLeastClosedModel PA194DomainLeastClosedTemplate PA194TraceSubset PA194MemberNonempty PA194FullSepWitnessBranch PA194DomainInstances PA194GreatestSuccessorClosedModel PA194GreatestSuccessorClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def leastDom2 : Semiproposition M6.PA.RelationalSource.language 2 := domain (.bvar 1)
def leastSubset2 : Semiproposition M6.PA.RelationalSource.language 2 := subset (.bvar 0) (.bvar 1)
def leastNonempty2 : Semiproposition M6.PA.RelationalSource.language 2 := nonempty (.bvar 0)
def leastExists2 : Semiproposition M6.PA.RelationalSource.language 2 := leastExists (.bvar 0)
def leastExistsTemplate : Semiproposition M6.PA.RelationalSource.language 1 := leastExists (.bvar 0)

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

theorem leastDom_at (s c : M) :
    ((⌜leastDom2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s] : Formula M SourceL) =
      (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s] := by
  have hs : leastDom2 = PA194OrdinalBaseQuote.domainTemplate ⇜ ![#1] := by
    simp [leastDom2,PA194OrdinalBaseQuote.domainTemplate]
    ordinalSyntax
  have ht : (⌜leastDom2⌝ : Semiformula M SourceL 2) =
      (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 1] := by
    rw [hs, Semiformula.typed_quote_substs]; congr 1; funext i; fin_cases i <;> simp
  rw [ht]; simp [Semiformula.substs_substs]

theorem leastSubset_at (s c : M) :
    ((⌜leastSubset2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s] : Formula M SourceL) =
      (⌜subsetCS2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar s,Semiterm.fvar c] := by
  have hs : leastSubset2 = subsetCS2 ⇜ ![#1,#0] := by
    simp [leastSubset2,subsetCS2]
    ordinalSyntax
  have ht : (⌜leastSubset2⌝ : Semiformula M SourceL 2) =
      (⌜subsetCS2⌝ : Semiformula M SourceL 2).subst ![Semiterm.bvar 1,Semiterm.bvar 0] := by
    rw [hs, Semiformula.typed_quote_substs]; congr 1; funext i; fin_cases i <;> simp
  rw [ht]; simp [Semiformula.substs_substs]

theorem leastNonempty_at (s c : M) :
    ((⌜leastNonempty2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s] : Formula M SourceL) =
      (⌜nonemptyTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar c] := by
  have hs : leastNonempty2 = nonemptyTemplate ⇜ ![#0] := by
    simp [leastNonempty2,nonemptyTemplate]
    ordinalSyntax
  have ht : (⌜leastNonempty2⌝ : Semiformula M SourceL 2) =
      (⌜nonemptyTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 0] := by
    rw [hs, Semiformula.typed_quote_substs]; congr 1; funext i; fin_cases i <;> simp
  rw [ht]; simp [Semiformula.substs_substs]

theorem leastExists_at (s c : M) :
    ((⌜leastExists2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s] : Formula M SourceL) =
      (⌜leastExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar c] := by
  have hs : leastExists2 = leastExistsTemplate ⇜ ![#0] := by
    simp only [leastExists2,leastExistsTemplate,leastExists]
    ordinalSyntax
  have ht : (⌜leastExists2⌝ : Semiformula M SourceL 2) =
      (⌜leastExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 0] := by
    rw [hs, Semiformula.typed_quote_substs]; congr 1; funext i; fin_cases i <;> simp
  rw [ht]; simp [Semiformula.substs_substs]

noncomputable def domainLeastAtCode (s c g du hd hs hn : M) : M :=
  let v := (?[ ^&c, ^&s] : M)
  let body := (⌜domainLeastBound⌝ : M)
  let dom := subst SourceL v (⌜leastDom2⌝ : M)
  let sub := subst SourceL v (⌜leastSubset2⌝ : M)
  let nonempty := subst SourceL v (⌜leastNonempty2⌝ : M)
  let ex := subst SourceL v (⌜leastExists2⌝ : M)
  let imp3 := neg SourceL nonempty ^⋎ ex
  let imp2 := neg SourceL sub ^⋎ imp3
  let sp := contextDoubleCode body (^&c) (^&s) g du
  let mid1 := contextMPCode dom imp2 g sp hd
  let mid2 := contextMPCode sub imp3 g mid1 hs
  contextMPCode nonempty ex g mid2 hn

noncomputable def domainLeastAtGraph : 𝚺₁.Semisentence 8 := .mkSigma
  “out s c g du hd hs hn. ∃ tc, !qqFvarDef tc c ∧ ∃ ts, !qqFvarDef ts s ∧ ∃ tail, !adjoinDef tail ts 0 ∧ ∃ v, !adjoinDef v tc tail ∧
    ∃ body, !(fixedFormulaQuoteGraph domainLeastBound) body ∧ ∃ dt, !(fixedFormulaQuoteGraph leastDom2) dt ∧
    ∃ st, !(fixedFormulaQuoteGraph leastSubset2) st ∧ ∃ nt, !(fixedFormulaQuoteGraph leastNonempty2) nt ∧
    ∃ et, !(fixedFormulaQuoteGraph leastExists2) et ∧ ∃ dom, !(substsGraph SourceL) dom v dt ∧
    ∃ sub, !(substsGraph SourceL) sub v st ∧ ∃ nonempty, !(substsGraph SourceL) nonempty v nt ∧
    ∃ ex, !(substsGraph SourceL) ex v et ∧ ∃ nn, !(negGraph SourceL) nn nonempty ∧ ∃ imp3, !qqOrDef imp3 nn ex ∧
    ∃ ns, !(negGraph SourceL) ns sub ∧ ∃ imp2, !qqOrDef imp2 ns imp3 ∧
    ∃ sp, !contextDoubleGraph sp body tc ts g du ∧ ∃ mid1, !contextMPGraph mid1 dom imp2 g sp hd ∧
    ∃ mid2, !contextMPGraph mid2 sub imp3 g mid1 hs ∧ !contextMPGraph out nonempty ex g mid2 hn”

theorem domainLeastAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 7 → M => domainLeastAtCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6)) domainLeastAtGraph := by
  haveI := contextDoubleGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [domainLeastAtGraph,domainLeastAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def domainLeastAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (s c : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜leastDom2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s]) Γ)
    (hs : T ⊢!ᵈᵉʳ insert ((⌜leastSubset2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert ((⌜leastNonempty2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜leastExists2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s]) Γ := by
  let body : Semiformula M SourceL 2 := ⌜domainLeastBound⌝
  let dom : Semiformula M SourceL 2 := ⌜leastDom2⌝
  let sub : Semiformula M SourceL 2 := ⌜leastSubset2⌝
  let ne : Semiformula M SourceL 2 := ⌜leastNonempty2⌝
  let ex : Semiformula M SourceL 2 := ⌜leastExists2⌝
  have heb : body = dom 🡒 (sub 🡒 (ne 🡒 ex)) := by
    simp [body,dom,sub,ne,ex,domainLeastBound,leastDom2,leastSubset2,leastNonempty2,leastExists2,sourceImply, ←Semiformula.neg_eq, Bootstrapping.Semiformula.imp_def]
    change Semiformula.typedQuote M _ = _
    simp only [Semiformula.typedQuote, Semiformula.typedQuote_neg]
    rfl
  have heu : (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ ∀⁰ body := by simp [body]
  let du' := TDerivation.cast (congrArg (fun q => insert q Γ) heu) du
  let sp := contextDoubleProof T Γ body (Semiterm.fvar c) (Semiterm.fvar s) du'
  have hei : (body.subst ![Semiterm.fvar c,Semiterm.fvar s] : Formula M SourceL) =
      ((dom.subst ![Semiterm.fvar c,Semiterm.fvar s]) 🡒
       ((sub.subst ![Semiterm.fvar c,Semiterm.fvar s]) 🡒
        ((ne.subst ![Semiterm.fvar c,Semiterm.fvar s]) 🡒 (ex.subst ![Semiterm.fvar c,Semiterm.fvar s])))) := by
    rw [heb]; simp
  let sp' := TDerivation.cast (congrArg (fun q => insert q Γ) hei) sp
  let mid1 := contextMPProof T Γ _ _ sp' hd
  let mid2 := contextMPProof T Γ _ _ mid1 hs
  exact contextMPProof T Γ _ _ mid2 hn

@[simp] theorem domainLeastAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (s c : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜leastDom2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s]) Γ)
    (hs : T ⊢!ᵈᵉʳ insert ((⌜leastSubset2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert ((⌜leastNonempty2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar c,Semiterm.fvar s]) Γ) :
    (domainLeastAtProof T Γ s c du hd hs hn).val = domainLeastAtCode s c Γ.val du.val hd.val hs.val hn.val := by
  simp [domainLeastAtProof,domainLeastAtCode,Semiformula.imp_def,Semiformula.quote_def,SemitermVec.val_succ]

noncomputable def domainLeastAlignedProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (s c : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hs : T ⊢!ᵈᵉʳ insert ((⌜subsetCS2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar s,Semiterm.fvar c]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert ((⌜nonemptyTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar c]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜leastExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar c]) Γ := by
  let hd' := TDerivation.cast (congrArg (fun q => insert q Γ) (leastDom_at s c).symm) hd
  let hs' := TDerivation.cast (congrArg (fun q => insert q Γ) (leastSubset_at s c).symm) hs
  let hn' := TDerivation.cast (congrArg (fun q => insert q Γ) (leastNonempty_at s c).symm) hn
  let out := domainLeastAtProof T Γ s c du hd' hs' hn'
  exact TDerivation.cast (congrArg (fun q => insert q Γ) (leastExists_at s c)) out

@[simp] theorem domainLeastAlignedProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (s c : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hs : T ⊢!ᵈᵉʳ insert ((⌜subsetCS2⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar s,Semiterm.fvar c]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert ((⌜nonemptyTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar c]) Γ) :
    (domainLeastAlignedProof T Γ s c du hd hs hn).val = domainLeastAtCode s c Γ.val du.val hd.val hs.val hn.val := by
  simp [domainLeastAlignedProof]

#print axioms domainLeastAtGraph_defined
#print axioms domainLeastAtProof
#print axioms domainLeastAtProof_val
#print axioms domainLeastAlignedProof
#print axioms domainLeastAlignedProof_val
#print axioms leastDom_at
#print axioms leastSubset_at
#print axioms leastNonempty_at
#print axioms leastExists_at
end models
end PA194DomainLeastAt
