import PA194DomainSuccessorClosedTemplate
import PA194StandardOrdinalProof
import PA194IntersectionMember
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
namespace PA194DomainSuccessorClosedModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainSuccessorClosedTemplate PA194StandardOrdinalProof PA194StandardOrdinalReduction PA194IntersectionMember PA194FullSepOpen PA194LeastExcludesClosedModel PA194LeastExcludesClosedTemplate PA194StandardEqualitySuppliers PA194CongruenceSourceProof PA194QuotedInduction PA194TypedClosure PA194CloseProof PA194BindSource PA194FixedSyntaxQuote PA194InternalInductionBaseAt PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalFixed PA194OrdinalBaseQuote
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

open M6.PA.RelationalSource M6.PA.RelationalSource.Ordinal

noncomputable def successorContextProof (q : Proposition M6.PA.RelationalSource.language) (hq : q ∈ successorAxioms) :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜q⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  by_cases h0 : q = reflexivityFormula
  · subst q; exact reflexivityProof
  by_cases h1 : q = symmetryFormula
  · subst q; exact symmetryProof
  by_cases h2 : q = transitivityFormula
  · subst q; exact transitivityProof
  by_cases h3 : q = congruenceFormula
  · subst q; exact congruenceProof
  by_cases h4 : q = adjunctionFormula
  · subst q; exact adjunctionProof
  have h5 : q = intersectionFormula := by simpa [successorAxioms,h0,h1,h2,h3,h4] using hq
  subst q
  exact proofOfInternalProvable T (⌜intersectionFormula⌝ : Formula M SourceL) (intersection_provable (M := M))

noncomputable def domainSuccessorOpenModelProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜domainSuccessorOpen⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  exact dischargeQuotedDerivation T successorAxioms domainSuccessorOpen domainSuccessorOpenDerivation
    (fun q hq => successorContextProof (M := M) q hq)

theorem domainSuccessorClosureCodeEq : modelClose ((1 : Nat) : M) (⌜domainSuccessorOpen⌝ : M) =
    (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : M) := by
  have hc : modelClose ((1 : Nat) : M) (⌜domainSuccessorOpen⌝ : M) = (⌜domainSuccessorOpen.univCl⌝ : M) := by
    simpa [domainSuccessorOpen_fvSup] using modelClose_quote_univCl (M := M) domainSuccessorOpen
  rw [hc]
  exact congrArg (fun q : Proposition M6.PA.RelationalSource.language => (⌜q⌝ : M)) domainSuccessor_closure

noncomputable def domainSuccessorUniversalProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  have ho : Provable T.theory (⌜domainSuccessorOpen⌝ : M) := TProvable.iff_provable.mp ⟨domainSuccessorOpenModelProof (M := M)⟩
  have hc := close_iterated_provable T ((1 : Nat) : M) (⌜domainSuccessorOpen⌝ : M)
    (Semiformula.quote_isSemiformula₀ domainSuccessorOpen) ho
  rw [domainSuccessorClosureCodeEq] at hc
  exact ((TProvable.iff_provable).2 hc).get

#print axioms successorContextProof
#print axioms domainSuccessorOpenModelProof
#print axioms domainSuccessorClosureCodeEq
#print axioms domainSuccessorUniversalProof
end models
end PA194DomainSuccessorClosedModel
