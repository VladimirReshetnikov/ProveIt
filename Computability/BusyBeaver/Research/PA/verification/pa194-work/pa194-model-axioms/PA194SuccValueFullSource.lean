import PA194SuccValueGuarded
import PA194DomainSuccessorClosedModel
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194SuccValueFullSource
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
local instance succValueFullSourceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance succValueFullSourceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance succValueFullSourceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance succValueFullSourceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance succValueFullSourceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance succValueFullSourceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


open PA194GuardedCompiler PA194SuccValueSchema PA194DomainSuccessorClosedTemplate PA194DomainSuccessorClosedModel
attribute [local instance] adjunctiveFullSepTheoryDelta

theorem succTotal_provable : Provable adjunctiveFullSepTheory (succTotalCode : M) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  have h : Provable T.theory (⌜(∀⁰ domainSuccessorBound : Proposition M6.PA.RelationalSource.language)⌝ : M) :=
    TProvable.iff_provable.mp ⟨domainSuccessorUniversalProof (M := M)⟩
  rw [succTotalCode_quote] at h
  exact h

theorem fullSource_succValue (s : M) (hs : IsSemiterm PA194PAeq.language 0 s) :
    GDerivable adjunctiveFullSepTheory (insert (neg SourceL (^∃ (valBody s)))
      (insert (^∃ (valBody (succT s))) (∅ : M))) :=
  succValueGuarded adjunctiveFullSepTheory (succTotal_provable (M := M)) s hs
#print axioms succTotal_provable
#print axioms fullSource_succValue
end models
end PA194SuccValueFullSource
