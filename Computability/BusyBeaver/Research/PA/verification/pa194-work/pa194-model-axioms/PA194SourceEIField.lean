import PA194SourceEIQuote
import PA194SourceEqualityIsoFull
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194SourceEIField
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance eiSourceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eiSourceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eiSourceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eiSourceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eiSourceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance eiSourceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194GuardedCompiler PA194Schematic

theorem source_ei :
    letI := adjunctiveFullSepTheoryDelta
    (adjunctiveFullSepTheory.internalize M) ⊢ (tHyp sEI : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  rw [tHyp_eq_quote, PA194SourceEIQuote.source_quote_identity]
  change (adjunctiveFullSepTheory.internalize M) ⊢
    (⌜PA194SourceEqualityIso.eqIsoClosed⌝ : Formula M SourceL)
  exact ⟨PA194SourceEqualityIsoFull.sourceProof (M := M)⟩

#print axioms source_ei
end models
end PA194SourceEIField
