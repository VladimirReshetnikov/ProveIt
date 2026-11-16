import PA194MemberDomainAtCode
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194DomainInstances
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194MemberDomainAtCode PA194MemberDomainClosedModel PA194MemberDomainClosedTemplate PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

open M6.PA.RelationalSource

open M6.PA.RelationalSource

open M6.PA.RelationalSource

/-- Domain-one and domain-zero agree with the one-variable domain template. -/
theorem domainOneAt (a b : M) :
    ((⌜domainOne⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a] := by
  have hs : domainOne = PA194OrdinalBaseQuote.domainTemplate ⇜ ![#1] := by
    simp [domainOne,PA194OrdinalBaseQuote.domainTemplate]
    ordinalSyntax
  have ht : (⌜domainOne⌝ : Semiformula M SourceL 2) =
      (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 1] := by
    rw [hs, Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht]
  simp [Semiformula.substs_substs]

theorem domainZeroAt (a b : M) :
    ((⌜domainZero⌝ : Semiformula M SourceL 2).subst ![Semiterm.fvar b,Semiterm.fvar a] : Formula M SourceL) =
      (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b] := by
  have hs : domainZero = PA194OrdinalBaseQuote.domainTemplate ⇜ ![#0] := by
    simp [domainZero,PA194OrdinalBaseQuote.domainTemplate]
    ordinalSyntax
  have ht : (⌜domainZero⌝ : Semiformula M SourceL 2) =
      (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 0] := by
    rw [hs, Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht]
  simp [Semiformula.substs_substs]

/-- Member-domain application in the one-variable domain syntax used by induction. -/
noncomputable def memberDomainOneVarProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar a]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ := by
  let hd' := TDerivation.cast (congrArg (fun q => insert q Γ) (domainOneAt a b).symm) hd
  let out := memberDomainAtProof T Γ a b du hd' hm
  exact TDerivation.cast (congrArg (fun q => insert q Γ) (domainZeroAt a b)) out

@[simp] theorem memberDomainOneVarProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar a]) : Formula M SourceL) Γ) :
    (memberDomainOneVarProof T Γ a b du hd hm).val = memberDomainAtCode a b Γ.val du.val hd.val hm.val := by
  simp [memberDomainOneVarProof]

noncomputable def memberDomainOneVarFromLogic (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (a b : M)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar a]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ := by
  let uq : Formula M SourceL := ⌜(∀⁰ ∀⁰ memberDomainBound : Proposition M6.PA.RelationalSource.language)⌝
  let du : T ⊢!ᵈᵉʳ insert uq Γ := TDerivation.wk (memberDomainUniversalProof T) (by intro x hx; simp at hx ⊢; tauto)
  exact memberDomainOneVarProof T Γ a b du hd hm

#print axioms memberDomainOneVarProof
#print axioms memberDomainOneVarProof_val
#print axioms memberDomainOneVarFromLogic
#print axioms domainOneAt
#print axioms domainZeroAt
end models
end PA194DomainInstances
