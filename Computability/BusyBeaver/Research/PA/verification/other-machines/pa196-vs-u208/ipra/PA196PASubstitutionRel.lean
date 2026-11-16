import PA196PASubstitutionClauses
import PA196PATermSubstVecGrowth
import DiophantineConsistency.PRAWitnessTermRec

/-! The negative relation clauses of arithmetic formula substitution have
bounded witnesses in every candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PASubstitutionRel
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
open PRAWitnessTermRec

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_rel : WB M (∼(Substs.blueprint ℒₒᵣ).rel.graphDelta.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨hrel, _⟩ := PA196PASubstitutionClauses.positive_clauses (M := M)
  refine wb_neg_graphDelta_pi_exp _ hrel ‘#0 + #3 + #1 + #2 + 8 + 4’ ‘20 * #3 + 2 * #1 + 26’ ?_
  intro V _ _ e y h
  simp [Substs.blueprint] at h
  rw [h]
  simpa [qqRel, PRAWitnessCodeGrowth.tau, numeral_eq_natCast] using
    PA196PATermSubstVecGrowth.relation_le (0 : V) (e 1) (e 2) (e 0) (e 3) (by norm_num)

theorem wb_nrel : WB M (∼(Substs.blueprint ℒₒᵣ).nrel.graphDelta.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨_, hnrel, _⟩ := PA196PASubstitutionClauses.positive_clauses (M := M)
  refine wb_neg_graphDelta_pi_exp _ hnrel ‘#0 + #3 + #1 + #2 + 8 + 4’ ‘20 * #3 + 2 * #1 + 26’ ?_
  intro V _ _ e y h
  simp [Substs.blueprint] at h
  rw [h]
  simpa [qqNRel, PRAWitnessCodeGrowth.tau, numeral_eq_natCast] using
    PA196PATermSubstVecGrowth.relation_le (1 : V) (e 1) (e 2) (e 0) (e 3) le_rfl

#print axioms wb_rel
#print axioms wb_nrel
end PA196PASubstitutionRel
