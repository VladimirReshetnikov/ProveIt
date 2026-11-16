import PA194MulCoherenceSource
import PA194IsoCancelSource
import PA194InclusiveSeparationSource
import PA194IntersectionMember
import PA194ForwardReflSuppliers
import PA194TypedSepMember
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194MulCoherence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
open PA194TypedSchema PA194TypedSeparation
open PA194BindSource PA194QuotedInduction PA194StandardOrdinalReduction PA194OrdinalSuppliers
open PA194StandardEqualitySuppliers PA194EmptySourceProof PA194CongruenceSourceProof PA194StandardOrdinalProof
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph M6.PA.RelationalSource.Ordinal
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance mulCoherenceSourceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance mulCoherenceSourceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance mulCoherenceSourceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance mulCoherenceSourceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance mulCoherenceSourceLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance mulCoherenceSourceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] statement identityAxioms axioms negatedSeparation

noncomputable def negatedSeparationProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜negatedSeparation⌝ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  have h := PA194IntersectionProof.typed_separation_axiom_member (M := M) (∼property)
  have hcode : (⌜(separationFormula (∼property)).univCl⌝ : M) = (⌜negatedSeparation⌝ : M) := by
    simpa only [negatedSeparation] using (PA194IntersectionMember.quote_univCl_eq_self (M := M) negatedSeparation negatedSeparation_noFree)
  rw [hcode] at h
  apply TProof.byAxm
  exact h

noncomputable def sourceProof
    (haddition : let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
      T ⊢! (⌜addCoherenceStatement⌝ : Formula M SourceL)) :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜statement⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory,adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T axioms statement contextDerivation
  intro q hq
  by_cases h0 : q = negatedSeparation
  · subst q; exact negatedSeparationProof
  by_cases h1 : q = addCoherenceStatement
  · subst q; exact haddition
  by_cases h2 : q = closedStrictSeparation
  · subst q; exact PA194IsoCancelSource.closedStrictSeparationProof
  by_cases h3 : q = closedInclusiveSeparation
  · subst q; exact PA194InclusiveSeparationSource.closedSepProof
  have hq' : q ∈ identityAxioms := by simpa [axioms,h0,h1,h2,h3] using hq
  exact PA194ForwardReflProof.contextSuppliers q hq'

#print axioms negatedSeparationProof
#print axioms sourceProof
end models
end PA194MulCoherence
