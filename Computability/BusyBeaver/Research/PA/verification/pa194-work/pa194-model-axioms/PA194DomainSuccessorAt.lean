import PA194DomainSuccessorClosedModel
import PA194DomainGreatestClosedModel
import PA194ContextSpecializeCode
import PA194InternalBaseAtContext
import PA194FixedSyntaxQuote
import PA194OrdinalFixed
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194DomainSuccessorAt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainSuccessorClosedTemplate PA194DomainSuccessorClosedModel PA194DomainGreatestClosedModel PA194DomainGreatestClosedTemplate PA194ContextSpecializeCode PA194ContextModusPonensCode PA194BindSource PA194FixedSyntaxQuote PA194InternalInductionBaseAt PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
  PA194TypedSeparation
open M6.PA.RelationalSource
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal
def domainSuccessorExistsTemplate : Semiproposition M6.PA.RelationalSource.language 1 := domainSuccessorExists (.bvar 0)

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

noncomputable def domainSuccessorAtCode (a g du hd : M) : M :=
  let t := ^&a
  let body := (⌜domainSuccessorBound⌝ : M)
  let dom := substs1 SourceL t (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
  let ex := substs1 SourceL t (⌜domainSuccessorExistsTemplate⌝ : M)
  let sp := contextSpecializeCode body t g du
  contextMPCode dom ex g sp hd

noncomputable def domainSuccessorAtGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out a g du hd. ∃ t, !qqFvarDef t a ∧ ∃ body, !(fixedFormulaQuoteGraph domainSuccessorBound) body ∧
    ∃ dt, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dt ∧ ∃ et, !(fixedFormulaQuoteGraph domainSuccessorExistsTemplate) et ∧
    ∃ dom, !(substs1Graph SourceL) dom t dt ∧ ∃ ex, !(substs1Graph SourceL) ex t et ∧
    ∃ sp, !contextSpecializeGraph sp body t g du ∧ !contextMPGraph out dom ex g sp hd”

theorem domainSuccessorAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => domainSuccessorAtCode (v 0) (v 1) (v 2) (v 3)) domainSuccessorAtGraph := by
  haveI := contextSpecializeGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [domainSuccessorAtGraph,domainSuccessorAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def domainSuccessorAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜domainSuccessorExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ := by
  let body : Semiformula M SourceL 1 := ⌜domainSuccessorBound⌝
  let dom : Semiformula M SourceL 1 := ⌜PA194OrdinalBaseQuote.domainTemplate⌝
  let ex : Semiformula M SourceL 1 := ⌜domainSuccessorExistsTemplate⌝
  have heb : body = dom 🡒 ex := by
    simp [body,dom,ex,domainSuccessorBound,domainSuccessorStatement,domainSuccessorExistsTemplate,PA194OrdinalBaseQuote.domainTemplate, ←Semiformula.neg_eq, Bootstrapping.Semiformula.imp_def]
  have heu : (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ body := by simp [body]
  let du' := TDerivation.cast (congrArg (fun q => insert q Γ) heu) du
  let sp := contextSpecializeProof T Γ body (Semiterm.fvar a) du'
  have hei : (body.subst ![Semiterm.fvar a] : Formula M SourceL) =
      ((dom.subst ![Semiterm.fvar a]) 🡒 (ex.subst ![Semiterm.fvar a])) := by
    rw [heb]; simp
  let sp' := TDerivation.cast (congrArg (fun q => insert q Γ) hei) sp
  exact contextMPProof T Γ _ _ sp' hd

@[simp] theorem domainSuccessorAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ) :
    (domainSuccessorAtProof T Γ a du hd).val = domainSuccessorAtCode a Γ.val du.val hd.val := by
  simp [domainSuccessorAtProof,domainSuccessorAtCode,Semiformula.imp_def,Semiformula.quote_def,SemitermVec.val_succ,substs1]

#print axioms domainSuccessorAtGraph_defined
#print axioms domainSuccessorAtProof
#print axioms domainSuccessorAtProof_val
end models
end PA194DomainSuccessorAt
