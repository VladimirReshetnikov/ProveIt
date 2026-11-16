import PA196PASubstitutionCore
import PA196PASubstitutionRel

/-! Both core polarities for the exact arithmetic formula-substitution
recursion have bounded witnesses. This does not bound the recursion stage. -/
set_option autoImplicit false
namespace PA196PASubstitutionCoreComplete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.PRAWitnessCalculus

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_core_sigma : WB M ((Substs.blueprint ℒₒᵣ).blueprint ℒₒᵣ).core.sigma.val :=
  PA196PASubstitutionCore.wb_core_sigma

theorem wb_core_neg_pi : WB M (∼((Substs.blueprint ℒₒᵣ).blueprint ℒₒᵣ).core.pi.val) :=
  PA196PASubstitutionCore.wb_core_neg_pi PA196PASubstitutionRel.wb_rel PA196PASubstitutionRel.wb_nrel

#print axioms wb_core_sigma
#print axioms wb_core_neg_pi
end PA196PASubstitutionCoreComplete
