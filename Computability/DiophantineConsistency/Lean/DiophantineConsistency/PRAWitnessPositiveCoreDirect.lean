import DiophantineConsistency.PRAWitnessDerivationCoreLeft
import DiophantineConsistency.PRAWitnessPositiveSimpleRules
import DiophantineConsistency.PRAWitnessPositiveAndRule
import DiophantineConsistency.PRAWitnessPositiveOrRule
import DiophantineConsistency.PRAWitnessPositiveAllRule
import DiophantineConsistency.PRAWitnessPositiveExsRule
import DiophantineConsistency.PRAWitnessPositiveCutRule
import DiophantineConsistency.PRAWitnessPositiveAxiomRule
/-! All positive sigma-core leaves, conditional only on the theory recognizer. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessPositiveCoreDirect
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

theorem wb_coreSigma (T : SetTheory) [T.Δ₁] (hT : WB M (T.Δ₁ch).sigma.val) :
    WB M (Derivation.blueprint T).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  apply PRAWitnessDerivationCoreLeft.wb_coreSigma_of_tail T
  change WB M (PRAWitnessPositiveSimpleRules.identityBranch ⋎
    PRAWitnessPositiveSimpleRules.verumBranch ⋎ PRAWitnessPositiveAndRule.branch ⋎
    PRAWitnessPositiveOrRule.branch ⋎ PRAWitnessPositiveAllRule.branch ⋎
    PRAWitnessPositiveExsRule.branch ⋎ PRAWitnessPositiveSimpleRules.weakeningBranch ⋎
    PRAWitnessPositiveSimpleRules.shiftBranch ⋎ PRAWitnessPositiveCutRule.branch ⋎
    PRAWitnessPositiveAxiomRule.branch T)
  exact wb_or PRAWitnessPositiveSimpleRules.wb_identity
    (wb_or PRAWitnessPositiveSimpleRules.wb_verum
    (wb_or PRAWitnessPositiveAndRule.wb_branch
    (wb_or PRAWitnessPositiveOrRule.wb_branch
    (wb_or PRAWitnessPositiveAllRule.wb_branch
    (wb_or PRAWitnessPositiveExsRule.wb_branch
    (wb_or PRAWitnessPositiveSimpleRules.wb_weakening
    (wb_or PRAWitnessPositiveSimpleRules.wb_shift
    (wb_or PRAWitnessPositiveCutRule.wb_branch
      (PRAWitnessPositiveAxiomRule.wb_branch T hT)))))))))
end DiophantineConsistency.PRAWitnessPositiveCoreDirect
