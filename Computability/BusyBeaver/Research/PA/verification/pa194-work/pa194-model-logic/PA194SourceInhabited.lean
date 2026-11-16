import PA194ForwardReflSuppliers
import PA194PAeqOrdinalValues
import PA194FoundationOrdinalInhabited
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194SourceInhabited
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
local instance sourceInhabited2Zero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sourceInhabited2One : One M := ⟨F oneCode Fin.elim0⟩
local instance sourceInhabited2Add : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sourceInhabited2Mul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sourceInhabited2LT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance sourceInhabited2IOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


noncomputable def inhabitedProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜Ordinal.inhabited⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T [emptyFormula] Ordinal.inhabited
    PA194Logic.Relational.Source.Ordinal.emptyFoundationDerivation
  intro q hq
  have hq' : q = emptyFormula := by simpa using hq
  subst q
  exact emptyProof

theorem inhabited_code : (⌜Ordinal.inhabited⌝ : M) = ^∃ (domainCode (^#(0 : M))) := by
  change (⌜∃⁰ Ordinal.domain (.bvar 0)⌝ : M) = _
  rw [Semiformula.quote_ex, ←domainCode_quote (.bvar (0 : Fin 1))]
  simp [Semiterm.quote_def]

theorem inhabited_provable :
    letI := adjunctiveFullSepTheoryDelta
    Provable adjunctiveFullSepTheory (^∃ (domainCode (^#(0 : M)))) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  have h : Provable T.theory (⌜Ordinal.inhabited⌝ : M) :=
    (TProvable.iff_provable (T := T) (σ := (⌜Ordinal.inhabited⌝ : Formula M SourceL))).mp ⟨inhabitedProof (M := M)⟩
  simpa only [inhabited_code] using h
#print axioms inhabitedProof
#print axioms inhabited_code
#print axioms inhabited_provable
end models
end PA194SourceInhabited
