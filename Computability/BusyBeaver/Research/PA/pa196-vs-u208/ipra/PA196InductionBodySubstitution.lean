import PA196InductionBodyOuter
import PA196PASubstitutionWitnessComplete

/-! Discharge the induction-body substitution graph witness-bound premise.
The fixed-substitution numeric growth hypothesis remains explicit. -/
set_option autoImplicit false
namespace PA196InductionBodySubstitution
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.PRAAddOne
open DiophantineConsistency.PRAWitnessCalculus

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_bodyGraph_of_growth (hgrowth : PA196InductionBodyOuter.FixedSubstitutionGrowth) :
    WB M indBodyValGraph.val :=
  PA196InductionBodyOuter.wb_bodyGraph_of_substitution
    PA196PASubstitutionWitnessComplete.wb_substsGraph hgrowth

#print axioms wb_bodyGraph_of_growth
end PA196InductionBodySubstitution
