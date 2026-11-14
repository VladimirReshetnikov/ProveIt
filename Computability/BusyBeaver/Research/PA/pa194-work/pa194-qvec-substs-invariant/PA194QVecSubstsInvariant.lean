import PA194SubstsOutputCeiling
import PA196PASubstitutionUniformGrowth
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
namespace PA194QVecSubstsInvariant
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PA194SubstsCeiling
open PA196PAQVecTowerAlgebra PA196PASubstitutionUniformGrowth
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


/-- The same witness bound covers all substitutions along one coded qVec
history, including every nonstandard internal index up to the limit. -/
theorem qVec_substitutions_bounded (seed limit : M) :
    ∃ qs bound : M,
      (PA196PAQVecSeqTrace.construction (V := M)).CSeq ![seed] qs ∧
      limit + 1 = lh qs ∧
      (∀ i ≤ limit, znth qs i ≤ iter limit seed) ∧
      (∀ i ≤ limit, ∀ p : M, IsUFormula ℒₒᵣ p → p ≤ iter limit seed →
        (bnd (substsGraph ℒₒᵣ).val).Eval
          (Fin.snoc ![subst ℒₒᵣ (znth qs i) p,znth qs i,p] bound) Empty.elim) := by
  obtain ⟨qs,hq,hl,htrace⟩ := PA194QVecCeiling.bounded_trace seed limit
  obtain ⟨bound,hbound⟩ := PA194SubstsOutputCeiling.common_substitution_witness_ceiling (iter limit seed)
  refine ⟨qs,bound,hq,hl,htrace,?_⟩
  intro i hi p hp hpc
  exact hbound p (znth qs i) hp hpc (htrace i hi)

#print axioms qVec_substitutions_bounded
end PA194QVecSubstsInvariant
