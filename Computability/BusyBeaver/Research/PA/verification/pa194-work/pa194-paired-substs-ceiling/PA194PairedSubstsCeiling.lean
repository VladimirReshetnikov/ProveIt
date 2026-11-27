import PA194SubstsOutputCeiling
import PA194PAeqSubstUniformGrowth
import PA196PASubstitutionUniformGrowth
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
namespace PA194PairedSubstsCeiling
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


/-- A single explicit tower value bounds both substitution outputs. -/
theorem paired_output_le (c p w q v : M)
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula PA194PAeq.language q)
    (hpc : p ≤ c) (hwc : w ≤ c) (hqc : q ≤ c) (hvc : v ≤ c) :
    subst ℒₒᵣ w p ≤ PA194SubstsOutputCeiling.outputCeiling c ∧
      subst PA194PAeq.language v q ≤ PA194SubstsOutputCeiling.outputCeiling c := by
  refine ⟨PA194SubstsOutputCeiling.substitution_output_le c p w hp hpc hwc,?_⟩
  have hs : PA194PAeqSubstUniformGrowth.seed v q ≤ c+3*c+1 := by
    unfold PA194PAeqSubstUniformGrowth.seed
    exact add_le_add (add_le_add hvc (mul_le_mul' le_rfl hqc)) le_rfl
  have hn : q+1 ≤ c+1 := add_le_add hqc le_rfl
  exact le_trans (PA194PAeqSubstUniformGrowth.subst_le_uniform q hq v)
    (le_trans (iter_seed_mono _ _ _ hs) (iter_index_mono _ _ _ hn))

#print axioms paired_output_le
end PA194PairedSubstsCeiling
