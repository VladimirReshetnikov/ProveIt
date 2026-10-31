import DiophantineConsistency.PRAWitnessNegativeRuleAssembly
import DiophantineConsistency.PRAWitnessPositiveSimpleRules
import DiophantineConsistency.PRAWitnessPositiveAndRule

/-! Assemble the sigma-core rule leaves, discharging five checked branches. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessPositiveRuleAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
  PRAWitnessDerivationCoreLeft PRAWitnessCoreRules PRAWitnessNegativeRuleAssembly

noncomputable def sigmaRule (T : SetTheory) [T.Δ₁] (i : ℕ) : ArithmeticSemisentence 2 :=
  disjunctAt i (sigmaTail T)

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem positiveLeaves_of_remaining (T : SetTheory) [T.Δ₁]
    (h3 : WB M (sigmaRule T 3)) (h4 : WB M (sigmaRule T 4))
    (h5 : WB M (sigmaRule T 5)) (h8 : WB M (sigmaRule T 8))
    (h9 : WB M (sigmaRule T 9)) : PositiveLeaves (M := M) (sigmaTail T) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have h0 : WB M (sigmaRule T 0) := PRAWitnessPositiveSimpleRules.wb_actualIdentity T
  have h1 : WB M (sigmaRule T 1) := PRAWitnessPositiveSimpleRules.wb_actualVerum T
  have h2 : WB M (sigmaRule T 2) := PRAWitnessPositiveAndRule.wb_actual T
  have h6 : WB M (sigmaRule T 6) := PRAWitnessPositiveSimpleRules.wb_actualWeakening T
  have h7 : WB M (sigmaRule T 7) := PRAWitnessPositiveSimpleRules.wb_actualShift T
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

theorem wb_coreSigma_of_remaining (T : SetTheory) [T.Δ₁]
    (h3 : WB M (sigmaRule T 3)) (h4 : WB M (sigmaRule T 4))
    (h5 : WB M (sigmaRule T 5)) (h8 : WB M (sigmaRule T 8))
    (h9 : WB M (sigmaRule T 9)) : WB M (Derivation.blueprint T).core.sigma.val :=
  wb_coreSigma_of_leaves T (positiveLeaves_of_remaining T h3 h4 h5 h8 h9)
end DiophantineConsistency.PRAWitnessPositiveRuleAssembly
