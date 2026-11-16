import PA196PATermRecBound
import DiophantineConsistency.PRAWitnessTermFunctions

/-! Unconditional all-model witness bounds for Foundation's actual
arithmetic-language bound-variable term and term-vector graphs. -/
set_option autoImplicit false
namespace PA196PATermBVGraph
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem bv_clauses : PA196PATermRecBound.ClauseBounds IsUTerm.BV.blueprint M := by
  obtain ⟨hb, hf, hfn, hbn, hfnv, hfnn⟩ := PRAWitnessTermFunctions.bv_clauses (M := M)
  exact ⟨hb, hf, hfn, hbn, hfnv, hfnn⟩

theorem wb_termBVGraph : WB M (termBVGraph ℒₒᵣ).val :=
  PA196PATermRecBound.wb_result PRAWitnessTermFunctions.bvConstructions bv_clauses
    (fun _ _ _ => PA196PATermBVRank.rankFinite)

theorem wb_termBVVecGraph : WB M (termBVVecGraph ℒₒᵣ).val :=
  PA196PATermRecBound.wb_resultVec PRAWitnessTermFunctions.bvConstructions bv_clauses
    (fun _ _ _ => PA196PATermBVRank.rankFinite)

#print axioms wb_termBVGraph
#print axioms wb_termBVVecGraph
end PA196PATermBVGraph
