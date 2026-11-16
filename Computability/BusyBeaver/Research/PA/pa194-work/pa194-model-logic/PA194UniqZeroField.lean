import PA194UniqZeroProvable
import PA194UniqZeroTranslate
import PA194TermNames
import PA194Leibniz
import PA194SourceInhabited
import PA194GuardedCalculus
import PA194OrdinaryAxiomPacketBridge
import PA194ForwardSuccInjectiveRoot
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194UniqZeroField
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance uniqZeroFieldZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance uniqZeroFieldOne : One M := ⟨F oneCode Fin.elim0⟩
local instance uniqZeroFieldAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance uniqZeroFieldMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance uniqZeroFieldLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance uniqZeroFieldIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194FormulaDispatcher PA194ForwardTyped PA194GuardedCompiler PA194UniqZeroQuote
attribute [local instance] adjunctiveFullSepTheoryDelta

theorem uZero : GDerivable (V := M) adjunctiveFullSepTheory
    (insert (tr (uniq (zeroT : M))) (∅ : M)) := by
  have hp : Provable adjunctiveFullSepTheory (tr (uniq (zeroT : M))) := by
    rw [tr_uniqZero_quote]
    simpa only [PA194UniqZeroProof.target] using
      (PA194UniqZeroProof.source_provable (M := M))
  refine ⟨0, ?_⟩
  simpa [guards_zero] using hp.toDerivable
#print axioms uZero
end models
end PA194UniqZeroField
