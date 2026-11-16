import PA194DomainLeastClosedTemplate
import PA194QuotedInduction
import PA194TypedClosure
import PA194CloseProof
import PA194InternalBaseAtContext
import PA194FixedSyntaxQuote
import PA194OrdinalFixed
import PA194InternalOrdinalBase
import PA194BoundSeparation
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 30000
namespace PA194DomainLeastClosedModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainLeastClosedTemplate PA194QuotedInduction PA194TypedClosure PA194CloseProof PA194BindSource PA194FixedSyntaxQuote PA194InternalInductionBaseAt PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
  PA194TypedSeparation
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

noncomputable def openProof (T : InternalTheory M SourceL) : T ⊢! (⌜domainLeastOpen⌝ : Formula M SourceL) :=
  dischargeQuotedDerivation T [] domainLeastOpen domainLeastOpenDerivation (by intro p hp; exact False.elim (by simpa using hp))

theorem openProvable (T : InternalTheory M SourceL) : Provable T.theory (⌜domainLeastOpen⌝ : M) :=
  TProvable.iff_provable.mp ⟨openProof T⟩

theorem closedProvable (T : InternalTheory M SourceL) :
    Provable T.theory (modelClose ((2 : Nat) : M) (⌜domainLeastOpen⌝ : M)) := by
  exact close_iterated_provable T ((2 : Nat) : M) (⌜domainLeastOpen⌝ : M)
    (Semiformula.quote_isSemiformula₀ domainLeastOpen) (openProvable T)

theorem closureCodeEq : modelClose ((2 : Nat) : M) (⌜domainLeastOpen⌝ : M) =
    (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : M) := by
  have hclose : modelClose ((2 : Nat) : M) (⌜domainLeastOpen⌝ : M) = (⌜domainLeastOpen.univCl⌝ : M) := by
    simpa [domainLeastOpen_fvSup] using modelClose_quote_univCl (M := M) domainLeastOpen
  rw [hclose]
  have h := congrArg (fun q : Proposition M6.PA.RelationalSource.language => (⌜q⌝ : M)) domainLeast_closure
  exact h

noncomputable def domainLeastUniversalProof (T : InternalTheory M SourceL) :
    T ⊢! (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := by
  have hc := closedProvable T
  rw [closureCodeEq] at hc
  have ht : T ⊢ (⌜(∀⁰ ∀⁰ domainLeastBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) :=
    (TProvable.iff_provable).2 hc
  exact ht.get

#print axioms domainLeastUniversalProof
#print axioms closureCodeEq
#print axioms openProof
#print axioms openProvable
#print axioms closedProvable
end models
end PA194DomainLeastClosedModel
