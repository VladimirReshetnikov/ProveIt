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
namespace PA194DomainGreatestAtCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainGreatestClosedModel PA194DomainGreatestClosedTemplate PA194ContextSpecializeCode PA194ContextModusPonensCode PA194BindSource PA194FixedSyntaxQuote PA194InternalInductionBaseAt PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
  PA194TypedSeparation
open M6.PA.RelationalSource
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
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

noncomputable def domainGreatestAtCode (a g du hd hn : M) : M :=
  let t := ^&a
  let body := (⌜domainGreatestBound⌝ : M)
  let dom := substs1 SourceL t (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
  let zero := substs1 SourceL t (⌜zeroTemplate⌝ : M)
  let nz := neg SourceL zero
  let ex := substs1 SourceL t (⌜greatestExistsTemplate⌝ : M)
  let imp := neg SourceL nz ^⋎ ex
  let sp := contextSpecializeCode body t g du
  let mid := contextMPCode dom imp g sp hd
  contextMPCode nz ex g mid hn

noncomputable def domainGreatestAtGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out a g du hd hn. ∃ t, !qqFvarDef t a ∧ ∃ body, !(fixedFormulaQuoteGraph domainGreatestBound) body ∧
    ∃ dt, !(fixedFormulaQuoteGraph PA194OrdinalBaseQuote.domainTemplate) dt ∧ ∃ zt, !(fixedFormulaQuoteGraph zeroTemplate) zt ∧
    ∃ et, !(fixedFormulaQuoteGraph greatestExistsTemplate) et ∧
    ∃ dom, !(substs1Graph SourceL) dom t dt ∧ ∃ zero, !(substs1Graph SourceL) zero t zt ∧
    ∃ nz, !(negGraph SourceL) nz zero ∧ ∃ ex, !(substs1Graph SourceL) ex t et ∧
    ∃ nnz, !(negGraph SourceL) nnz nz ∧ ∃ imp, !qqOrDef imp nnz ex ∧
    ∃ sp, !contextSpecializeGraph sp body t g du ∧ ∃ mid, !contextMPGraph mid dom imp g sp hd ∧
    !contextMPGraph out nz ex g mid hn”

theorem domainGreatestAtGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 5 → M => domainGreatestAtCode (v 0) (v 1) (v 2) (v 3) (v 4)) domainGreatestAtGraph := by
  haveI := contextSpecializeGraph_defined (M := M)
  haveI := contextMPGraph_defined (M := M)
  exact .mk fun v => by simp [domainGreatestAtGraph,domainGreatestAtCode,fixedFormulaQuoteGraph_correct]

noncomputable def domainGreatestAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert (∼((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a])) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ := by
  let body : Semiformula M SourceL 1 := ⌜domainGreatestBound⌝
  let dom : Semiformula M SourceL 1 := ⌜PA194OrdinalBaseQuote.domainTemplate⌝
  let zero : Semiformula M SourceL 1 := ⌜zeroTemplate⌝
  let ex : Semiformula M SourceL 1 := ⌜greatestExistsTemplate⌝
  have heb : body = dom 🡒 (∼zero 🡒 ex) := by
    simp [body,dom,zero,ex,domainGreatestBound,PA194OrdinalBaseQuote.domainTemplate,zeroTemplate,greatestExistsTemplate,sourceImply, ←Semiformula.neg_eq, Bootstrapping.Semiformula.imp_def]
    change Semiformula.typedQuote M _ = _
    simp only [Semiformula.typedQuote, Semiformula.typedQuote_neg]
    rfl
  have heu : (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) = ∀⁰ body := by simp [body]
  let du' := TDerivation.cast (congrArg (fun q => insert q Γ) heu) du
  let sp := contextSpecializeProof T Γ body (Semiterm.fvar a) du'
  have hei : (body.subst ![Semiterm.fvar a] : Formula M SourceL) =
      ((dom.subst ![Semiterm.fvar a]) 🡒 (∼(zero.subst ![Semiterm.fvar a]) 🡒 (ex.subst ![Semiterm.fvar a]))) := by
    rw [heb]; simp
  let sp' := TDerivation.cast (congrArg (fun q => insert q Γ) hei) sp
  let mid := contextMPProof T Γ _ _ sp' hd
  exact contextMPProof T Γ _ _ mid hn

@[simp] theorem domainGreatestAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert (∼((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a])) Γ) :
    (domainGreatestAtProof T Γ a du hd hn).val = domainGreatestAtCode a Γ.val du.val hd.val hn.val := by
  have hz : IsUFormula SourceL (substs1 SourceL (^&a) (⌜zeroTemplate⌝ : M)) := by
    have h := ((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![(Semiterm.fvar a : Term M SourceL)]).isUFormula
    simpa [substs1,SemitermVec.val_succ,Semiformula.quote_def] using h
  have hnn := hz.neg_neg
  simp [domainGreatestAtProof,domainGreatestAtCode,Semiformula.imp_def,Semiformula.quote_def,SemitermVec.val_succ,substs1] at hnn ⊢
  rw [hnn]

noncomputable def domainGreatestAtFromLogic (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a : M)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hn : T ⊢!ᵈᵉʳ insert (∼((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a])) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜greatestExistsTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ := by
  let uq : Formula M SourceL := ⌜(∀⁰ domainGreatestBound : Proposition M6.PA.RelationalSource.language)⌝
  let du : T ⊢!ᵈᵉʳ insert uq Γ := TDerivation.wk (domainGreatestUniversalProof T) (by intro x hx; simp at hx ⊢; tauto)
  exact domainGreatestAtProof T Γ a du hd hn

#print axioms domainGreatestAtGraph_defined
#print axioms domainGreatestAtProof
#print axioms domainGreatestAtProof_val
#print axioms domainGreatestAtFromLogic
end models
end PA194DomainGreatestAtCode
