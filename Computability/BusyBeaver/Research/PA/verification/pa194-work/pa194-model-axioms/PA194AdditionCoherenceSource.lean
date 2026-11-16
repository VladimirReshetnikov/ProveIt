import PA194AdditionCoherenceInduction
import PA194AdditionCoherenceApply
import PA194InclusiveSeparationSource
import PA194IsoCancelSource
import PA194ForwardReflSuppliers
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194AdditionCoherenceSource
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

open PA194ForwardReflProof
open PA194OrdinalSuppliers
attribute [local irreducible] identityAxioms

def axioms : List Form :=
  closedStrictSeparation :: closedInclusiveSeparation ::
    separationFormula (∼addCoherenceProperty) :: identityAxioms

def contextProof : ND.Proof axioms addCoherenceStatement := by
  apply additionCoherenceConclusion
    ⟨⟨ND.assumption (by simp [axioms, identityAxioms]),
       ND.assumption (by simp [axioms, identityAxioms]),
       ND.assumption (by simp [axioms, identityAxioms])⟩,
       ND.assumption (by simp [axioms, identityAxioms])⟩
  all_goals first | exact ND.assumption (by simp [axioms, identityAxioms])

def contextDerivation : LO.FirstOrder.Derivation (axioms.map Semiformula.neg ++ [addCoherenceStatement]) :=
  contextProof.contra (by simp [ND.Proof])

noncomputable def sourceProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜addCoherenceStatement⌝ : Formula M SourceL) := by
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  apply dischargeQuotedDerivation T axioms addCoherenceStatement contextDerivation
  intro q hq
  by_cases hs : q = closedStrictSeparation
  · subst q; exact PA194IsoCancelSource.closedStrictSeparationProof
  by_cases hi : q = closedInclusiveSeparation
  · subst q; exact PA194InclusiveSeparationSource.closedSepProof
  by_cases hp : q = separationFormula (∼addCoherenceProperty)
  · subst q
    apply proofOfInternalProvable T (⌜separationFormula (∼addCoherenceProperty)⌝ : Formula M SourceL)
    exact typed_negated_property_separation_provable addCoherenceProperty
  have hq' : q ∈ identityAxioms := by simpa [axioms, hs, hi, hp] using hq
  exact contextSuppliers q hq'

#print axioms contextProof
#print axioms contextDerivation
#print axioms sourceProof
end models
end PA194AdditionCoherenceSource
