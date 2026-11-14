import PA194PAeqSubstClauses
import DiophantineConsistency.PRAWitnessTermRec
import DiophantineConsistency.PRAWitnessFormulaFunctions

/-! Six negative graph clauses for PAeq formula substitution. The
relation-symbol clauses and quantifier-vector growth remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194PAeqSubstNegative
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
open PRAWitnessTermRec PRAWitnessFormulaFunctions

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem negative_constructor_clauses :
    WB M (∼(Substs.blueprint PA194PAeq.language).verum.graphDelta.pi.val) ∧
    WB M (∼(Substs.blueprint PA194PAeq.language).falsum.graphDelta.pi.val) ∧
    WB M (∼(Substs.blueprint PA194PAeq.language).and.graphDelta.pi.val) ∧
    WB M (∼(Substs.blueprint PA194PAeq.language).or.graphDelta.pi.val) ∧
    WB M (∼(Substs.blueprint PA194PAeq.language).all.graphDelta.pi.val) ∧
    WB M (∼(Substs.blueprint PA194PAeq.language).exs.graphDelta.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  obtain ⟨_, _, hv, hf, ha, ho, hall, hex, _, _⟩ := PA194PAeqSubstClauses.positive_clauses (M := M)
  refine ⟨wb_neg_graphDelta_pi _ hv ‘(2 + 0 + 1) * (2 + 0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ hf ‘(3 + 0 + 1) * (3 + 0 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ ha ‘(4 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) * (4 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ ho ‘(5 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) * (5 + (#3 + #4 + 1) * (#3 + #4 + 1) + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ hall ‘(6 + #2 + 1) * (6 + #2 + 1) + 1’ ?_,
    wb_neg_graphDelta_pi _ hex ‘(7 + #2 + 1) * (7 + #2 + 1) + 1’ ?_⟩
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqVerum, numeral_eq_natCast] using code2_le (2 : V) 0
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqFalsum, numeral_eq_natCast] using code2_le (3 : V) 0
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqAnd, numeral_eq_natCast] using code3_le 4 (e 3) (e 4)
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqOr, numeral_eq_natCast] using code3_le 5 (e 3) (e 4)
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 2)
  · intro V _ _ e y h; simp [Substs.blueprint] at h; rw [h]; simpa [qqExs, numeral_eq_natCast] using code2_le 7 (e 2)

#print axioms negative_constructor_clauses
end PA194PAeqSubstNegative
