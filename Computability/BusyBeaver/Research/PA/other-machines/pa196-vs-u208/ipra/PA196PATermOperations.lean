import PA196PATermRecBound
import PA196PATermRankGeneral
import DiophantineConsistency.PRAWitnessTermFunctions

/-! Unconditional arithmetic-language graph bounds for term substitution,
free-variable shift, and bound-variable shift, including vectors. -/
set_option autoImplicit false
namespace PA196PATermOperations
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus

section rank
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem shift_rank : PRAFixpointRank.RankFinite
    ((TermShift.construction (V := V)).construction ℒₒᵣ) (fun x => x) := by
  apply PA196PATermRankGeneral.rankFinite
  intro param k f v w
  exact le_trans (PRAWitnessTermFunctions.listMax_le_self w) (terms_lt_qqFunc k f w).le

theorem bShift_rank : PRAFixpointRank.RankFinite
    ((TermBShift.construction (V := V)).construction ℒₒᵣ) (fun x => x) := by
  apply PA196PATermRankGeneral.rankFinite
  intro param k f v w
  exact le_trans (PRAWitnessTermFunctions.listMax_le_self w) (terms_lt_qqFunc k f w).le

theorem subst_rank : PRAFixpointRank.RankFinite
    ((TermSubst.construction (V := V)).construction ℒₒᵣ) (fun x => x) := by
  apply PA196PATermRankGeneral.rankFinite
  intro param k f v w
  exact le_trans (PRAWitnessTermFunctions.listMax_le_self w) (terms_lt_qqFunc k f w).le
end rank

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem shift_clauses : PA196PATermRecBound.ClauseBounds TermShift.blueprint M := by
  obtain ⟨a,b,c,d,e,f⟩ := PRAWitnessTermFunctions.shift_clauses (M := M)
  exact ⟨a,b,c,d,e,f⟩
theorem bShift_clauses : PA196PATermRecBound.ClauseBounds TermBShift.blueprint M := by
  obtain ⟨a,b,c,d,e,f⟩ := PRAWitnessTermFunctions.bShift_clauses (M := M)
  exact ⟨a,b,c,d,e,f⟩
theorem subst_clauses : PA196PATermRecBound.ClauseBounds TermSubst.blueprint M := by
  obtain ⟨a,b,c,d,e,f⟩ := PRAWitnessTermFunctions.subst_clauses (M := M)
  exact ⟨a,b,c,d,e,f⟩

theorem wb_termShiftGraph : WB M (termShiftGraph ℒₒᵣ).val :=
  PA196PATermRecBound.wb_result PRAWitnessTermFunctions.shiftConstructions shift_clauses
    (fun _ _ _ => shift_rank)
theorem wb_termShiftVecGraph : WB M (termShiftVecGraph ℒₒᵣ).val :=
  PA196PATermRecBound.wb_resultVec PRAWitnessTermFunctions.shiftConstructions shift_clauses
    (fun _ _ _ => shift_rank)
theorem wb_termBShiftGraph : WB M (termBShiftGraph ℒₒᵣ).val :=
  PA196PATermRecBound.wb_result PRAWitnessTermFunctions.bShiftConstructions bShift_clauses
    (fun _ _ _ => bShift_rank)
theorem wb_termBShiftVecGraph : WB M (termBShiftVecGraph ℒₒᵣ).val :=
  PA196PATermRecBound.wb_resultVec PRAWitnessTermFunctions.bShiftConstructions bShift_clauses
    (fun _ _ _ => bShift_rank)
theorem wb_termSubstGraph : WB M (termSubstGraph ℒₒᵣ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  simp only [termSubstGraph, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ (PA196PATermRecBound.wb_result PRAWitnessTermFunctions.substConstructions subst_clauses
    (fun _ _ _ => subst_rank))
theorem wb_termSubstVecGraph : WB M (termSubstVecGraph ℒₒᵣ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  simp only [termSubstVecGraph, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ (PA196PATermRecBound.wb_resultVec PRAWitnessTermFunctions.substConstructions subst_clauses
    (fun _ _ _ => subst_rank))

#print axioms wb_termShiftGraph
#print axioms wb_termShiftVecGraph
#print axioms wb_termBShiftGraph
#print axioms wb_termBShiftVecGraph
#print axioms wb_termSubstGraph
#print axioms wb_termSubstVecGraph
end PA196PATermOperations
