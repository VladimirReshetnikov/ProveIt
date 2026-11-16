import PA194GreatestSuccessorClosedTemplate
import PA194LeastExcludesClosedModel
import PA194StandardEqualitySuppliers
import PA194CongruenceSourceProof
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
set_option maxHeartbeats 250000
namespace PA194GreatestSuccessorClosedModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194LeastExcludesClosedModel PA194LeastExcludesClosedTemplate PA194GreatestSuccessorClosedTemplate PA194StandardEqualitySuppliers PA194CongruenceSourceProof PA194QuotedInduction PA194TypedClosure PA194CloseProof PA194BindSource PA194FixedSyntaxQuote PA194InternalInductionBaseAt PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
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

noncomputable def greatestSuccessorOpenModelProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜greatestSuccessorOpen⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  exact dischargeQuotedDerivation T equalityContext greatestSuccessorOpen greatestSuccessorOpenDerivation
    (fun q hq => equalityContextProof (M := M) q hq)

theorem greatestSuccessorOpenProvable :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    letI := T.Δ₁
    Provable T.theory (⌜greatestSuccessorOpen⌝ : M) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  letI := T.Δ₁
  have ht : T ⊢ (⌜greatestSuccessorOpen⌝ : Formula M SourceL) := ⟨greatestSuccessorOpenModelProof (M := M)⟩
  exact TProvable.iff_provable.mp ht

theorem greatestSuccessorClosureCodeEq : modelClose ((2 : Nat) : M) (⌜greatestSuccessorOpen⌝ : M) =
    (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : M) := by
  have hc : modelClose ((2 : Nat) : M) (⌜greatestSuccessorOpen⌝ : M) = (⌜greatestSuccessorOpen.univCl⌝ : M) := by
    simpa [greatestSuccessorOpen_fvSup] using modelClose_quote_univCl (M := M) greatestSuccessorOpen
  rw [hc]
  exact congrArg (fun q : Proposition M6.PA.RelationalSource.language => (⌜q⌝ : M)) greatestSuccessor_closure

noncomputable def greatestSuccessorUniversalProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  have ho : Provable T.theory (⌜greatestSuccessorOpen⌝ : M) := greatestSuccessorOpenProvable (M := M)
  have hc := close_iterated_provable T ((2 : Nat) : M) (⌜greatestSuccessorOpen⌝ : M)
    (Semiformula.quote_isSemiformula₀ greatestSuccessorOpen) ho
  rw [greatestSuccessorClosureCodeEq] at hc
  have ht : T ⊢ (⌜(∀⁰ ∀⁰ greatestSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) :=
    (TProvable.iff_provable).2 hc
  exact ht.get

#print axioms greatestSuccessorOpenModelProof
#print axioms greatestSuccessorOpenProvable
#print axioms greatestSuccessorClosureCodeEq
#print axioms greatestSuccessorUniversalProof
end models
end PA194GreatestSuccessorClosedModel
