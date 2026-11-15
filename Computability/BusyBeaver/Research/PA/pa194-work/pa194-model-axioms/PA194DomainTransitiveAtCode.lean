import PA194DomainTransitiveClosedModel
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
namespace PA194DomainTransitiveAtCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194ContextTripleSpecializeCode PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

def domainS3 : Semiproposition M6.PA.RelationalSource.language 3 := domain (.bvar 2)
def memberBS3 : Semiproposition M6.PA.RelationalSource.language 3 := mem (.bvar 2) (.bvar 1)
def memberMB3 : Semiproposition M6.PA.RelationalSource.language 3 := mem (.bvar 1) (.bvar 0)
def memberMS3 : Semiproposition M6.PA.RelationalSource.language 3 := mem (.bvar 2) (.bvar 0)

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

noncomputable def domainTransAtCode (c b m g du hd hl hm : M) : M :=
  let body := (⌜domainTransBound⌝ : M)
  let vec := (?[ ^&m, ^&b, ^&c] : M)
  let dom := subst SourceL vec (⌜domainS3⌝ : M)
  let least := subst SourceL vec (⌜memberBS3⌝ : M)
  let mem := subst SourceL vec (⌜memberMB3⌝ : M)
  let notmem := subst SourceL vec (⌜memberMS3⌝ : M)
  let imp3 := neg SourceL mem ^⋎ notmem
  let imp2 := neg SourceL least ^⋎ imp3
  let sp := contextTripleCode body (^&m) (^&b) (^&c) g du
  let r1 := contextMPCode dom imp2 g sp hd
  let r2 := contextMPCode least imp3 g r1 hl
  contextMPCode mem notmem g r2 hm

noncomputable def domainTransAtGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “out c b m g du hd hl hm. ∃ body, !(fixedFormulaQuoteGraph domainTransBound) body ∧
    ∃ d, !(fixedFormulaQuoteGraph domainS3) d ∧ ∃ l, !(fixedFormulaQuoteGraph memberBS3) l ∧
    ∃ mb, !(fixedFormulaQuoteGraph memberMB3) mb ∧ ∃ mc, !(fixedFormulaQuoteGraph memberMS3) mc ∧
    ∃ tm, !qqFvarDef tm m ∧ ∃ tb, !qqFvarDef tb b ∧ ∃ tc, !qqFvarDef tc c ∧
    ∃ v1, !adjoinDef v1 tc 0 ∧ ∃ v2, !adjoinDef v2 tb v1 ∧ ∃ vec, !adjoinDef vec tm v2 ∧
    ∃ dom, !(substsGraph SourceL) dom vec d ∧ ∃ least, !(substsGraph SourceL) least vec l ∧
    ∃ mem, !(substsGraph SourceL) mem vec mb ∧ ∃ ncm, !(substsGraph SourceL) ncm vec mc ∧
    ∃ nm, !(negGraph SourceL) nm mem ∧ ∃ imp3, !qqOrDef imp3 nm ncm ∧
    ∃ nl, !(negGraph SourceL) nl least ∧ ∃ imp2, !qqOrDef imp2 nl imp3 ∧
    ∃ sp, !contextTripleGraph sp body tm tb tc g du ∧ ∃ r1, !contextMPGraph r1 dom imp2 g sp hd ∧
    ∃ r2, !contextMPGraph r2 least imp3 g r1 hl ∧ !contextMPGraph out mem ncm g r2 hm”

theorem domainTransAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → M => domainTransAtCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) domainTransAtGraph := by
  haveI := contextTripleGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [domainTransAtGraph,domainTransAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def domainTransAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c b m : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜domainS3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜memberBS3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((⌜memberMB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜memberMS3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ := by
  let body : Semiformula M SourceL 3 := ⌜domainTransBound⌝
  let dom : Semiformula M SourceL 3 := ⌜domainS3⌝
  let least : Semiformula M SourceL 3 := ⌜memberBS3⌝
  let mem : Semiformula M SourceL 3 := ⌜memberMB3⌝
  let cm : Semiformula M SourceL 3 := ⌜memberMS3⌝
  have heb : body = dom 🡒 (least 🡒 (mem 🡒 cm)) := by
    simp [body,dom,least,mem,cm,domainTransBound,domainS3,memberBS3,memberMB3,memberMS3,sourceImply, ←Semiformula.neg_eq, Bootstrapping.Semiformula.imp_def]
    change Semiformula.typedQuote M _ = _
    simp only [Semiformula.typedQuote, Semiformula.typedQuote_neg]
    rfl
  have heu : (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ ∀⁰ ∀⁰ body := by
    simp [body]
  let du' := TDerivation.cast (congrArg (fun q => insert q Γ) heu) du
  let sp := contextTripleProof T Γ body (Semiterm.fvar m) (Semiterm.fvar b) (Semiterm.fvar c) du'
  have hei : (body.subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c] : Formula M SourceL) =
      ((dom.subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) 🡒
        ((least.subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) 🡒
          ((mem.subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) 🡒
            (cm.subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c])))) := by
    rw [heb]; simp
  let sp' := TDerivation.cast (congrArg (fun q => insert q Γ) hei) sp
  let r1 := contextMPProof T Γ _ _ sp' hd
  let r2 := contextMPProof T Γ _ _ r1 hl
  exact contextMPProof T Γ _ _ r2 hm

@[simp] theorem domainTransAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c b m : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜domainS3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜memberBS3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((⌜memberMB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ) :
    (domainTransAtProof T Γ c b m du hd hl hm).val = domainTransAtCode c b m Γ.val du.val hd.val hl.val hm.val := by
  simp [domainTransAtProof,domainTransAtCode,Semiformula.imp_def,Semiformula.quote_def,SemitermVec.val_succ]

#print axioms domainTransAtGraph_defined
#print axioms domainTransAtProof
#print axioms domainTransAtProof_val
end models
end PA194DomainTransitiveAtCode
