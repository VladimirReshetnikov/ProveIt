import PA194ForwardReflSuppliers
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194OrderIsoReflClosed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance isoReflClosedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance isoReflClosedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance isoReflClosedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance isoReflClosedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance isoReflClosedLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance isoReflClosedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194ForwardReflProof
attribute [local irreducible] identityAxioms

def reflContextDerivation : LO.FirstOrder.Derivation
    (identityAxioms.map Semiformula.neg ++ [orderIsoReflexivityStatement]) :=
  orderIsoReflexivityDerivation.contra (by simp [ND.Proof])

noncomputable def sourceProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜orderIsoReflexivityStatement⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  change T ⊢! (⌜orderIsoReflexivityStatement⌝ : Formula M SourceL)
  exact dischargeQuotedDerivation T identityAxioms orderIsoReflexivityStatement reflContextDerivation contextSuppliers

#print axioms reflContextDerivation
#print axioms sourceProof
end models
end PA194OrderIsoReflClosed
