import PA194DomainTransitiveClosedTemplate
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
namespace PA194DomainTransitiveClosedModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainTransitiveClosedTemplate PA194QuotedInduction PA194TypedClosure PA194CloseProof PA194BindSource PA194FixedSyntaxQuote PA194InternalInductionBaseAt PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
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

noncomputable def openProof (T : InternalTheory M SourceL) : T ⊢! (⌜domainTransOpen⌝ : Formula M SourceL) :=
  dischargeQuotedDerivation T [] domainTransOpen domainTransOpenDerivation (by intro p hp; exact False.elim (by simpa using hp))

theorem openProvable (T : InternalTheory M SourceL) : Provable T.theory (⌜domainTransOpen⌝ : M) :=
  TProvable.iff_provable.mp ⟨openProof T⟩

theorem closedProvable (T : InternalTheory M SourceL) :
    Provable T.theory (modelClose ((3 : Nat) : M) (⌜domainTransOpen⌝ : M)) := by
  exact close_iterated_provable T ((3 : Nat) : M) (⌜domainTransOpen⌝ : M)
    (Semiformula.quote_isSemiformula₀ domainTransOpen) (openProvable T)

theorem closureCodeEq : modelClose ((3 : Nat) : M) (⌜domainTransOpen⌝ : M) =
    (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : M) := by
  have hclose : modelClose ((3 : Nat) : M) (⌜domainTransOpen⌝ : M) = (⌜domainTransOpen.univCl⌝ : M) := by
    simpa [domainTransOpen_fvSup] using modelClose_quote_univCl (M := M) domainTransOpen
  rw [hclose]
  have h := congrArg (fun q : Proposition M6.PA.RelationalSource.language => (⌜q⌝ : M)) domainTrans_closure
  exact h

noncomputable def domainTransUniversalProof (T : InternalTheory M SourceL) :
    T ⊢! (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := by
  have hc := closedProvable T
  rw [closureCodeEq] at hc
  have ht : T ⊢ (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) :=
    (TProvable.iff_provable).2 hc
  exact ht.get

#print axioms domainTransUniversalProof
#print axioms closureCodeEq
#print axioms openProof
#print axioms openProvable
#print axioms closedProvable
end models
end PA194DomainTransitiveClosedModel
