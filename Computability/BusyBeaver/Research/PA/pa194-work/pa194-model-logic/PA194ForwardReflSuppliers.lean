import PA194ForwardReflContext
import PA194StandardOrdinalProof
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194ForwardReflProof
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance reflSourceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance reflSourceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance reflSourceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance reflSourceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance reflSourceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance reflSourceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def contextSuppliers :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    ∀ q ∈ identityAxioms, T ⊢! (⌜q⌝ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  change ∀ q ∈ identityAxioms, T ⊢! (⌜q⌝ : Formula M SourceL)
  intro q hq
  by_cases h0 : q = reflexivityFormula
  · subst q; exact reflexivityProof
  by_cases h1 : q = symmetryFormula
  · subst q; exact symmetryProof
  by_cases h2 : q = transitivityFormula
  · subst q; exact transitivityProof
  by_cases h3 : q = congruenceFormula
  · subst q; exact congruenceProof
  by_cases h4 : q = emptyFormula
  · subst q; exact emptyProof
  by_cases h5 : q = adjunctionFormula
  · subst q; exact adjunctionProof
  by_cases h6 : q = Ordinal.intersectionFormula
  · subst q
    apply proofOfInternalProvable T (⌜Ordinal.intersectionFormula⌝ : Formula M SourceL)
    exact PA194IntersectionMember.intersection_provable
  have hs : q = separationFormula (∼identityProperty) := by
    simpa [identityAxioms,h0,h1,h2,h3,h4,h5,h6] using hq
  subst q
  apply proofOfInternalProvable T (⌜separationFormula (∼identityProperty)⌝ : Formula M SourceL)
  exact typed_negated_property_separation_provable identityProperty

#print axioms contextSuppliers
end models
end PA194ForwardReflProof
