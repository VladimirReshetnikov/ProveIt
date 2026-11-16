import PA194SourceFixedQuotes
import PA194DomainSuccessorClosedModel
import PA194StandardEqualitySuppliers
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194SourceFixedFacts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194PAeqOrdinalValues
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance sourceFixedFactsZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceFixedFactsOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceFixedFactsAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceFixedFactsMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceFixedFactsLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceFixedFactsIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


open PA194GuardedCompiler PA194SourceFixedQuotes PA194SuccValueSchema PA194DomainSuccessorClosedTemplate PA194DomainSuccessorClosedModel
attribute [local instance] adjunctiveFullSepTheoryDelta

theorem s1 : (adjunctiveFullSepTheory.internalize M) ⊢ (tHyp sS1) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply (TProvable.iff_provable (T := T) (σ := tHyp sS1)).mpr
  rw [s1_code, ←succTotalCode_quote]
  exact (TProvable.iff_provable (T := T)
    (σ := (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : Bootstrapping.Formula M SourceL))).mp
      ⟨domainSuccessorUniversalProof (M := M)⟩

theorem e1 : (adjunctiveFullSepTheory.internalize M) ⊢ (tHyp sE1) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply (TProvable.iff_provable (T := T) (σ := tHyp sE1)).mpr
  rw [e1_code]
  exact (TProvable.iff_provable (T := T)
    (σ := (⌜reflexivityFormula⌝ : Bootstrapping.Formula M SourceL))).mp
      ⟨reflexivityProof (M := M)⟩
#print axioms s1
#print axioms e1
end models
end PA194SourceFixedFacts
