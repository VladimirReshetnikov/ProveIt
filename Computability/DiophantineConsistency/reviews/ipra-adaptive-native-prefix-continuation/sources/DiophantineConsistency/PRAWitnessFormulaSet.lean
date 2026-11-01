import DiophantineConsistency.PRAWitnessArithmetic
import ZFCinPA.Instances
/-! Witness bounds for Foundation's actual set-language formula-set predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessFormulaSet
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]

theorem wb_isFormulaSet_sigma (hsemi : WB M (isSemiformula ℒₛₑₜ).sigma.val) : WB M (isFormulaSet ℒₛₑₜ).sigma.val := by
  have := hsemi
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [isFormulaSet, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_isFormulaSet_neg_pi (hsemi : WB M (∼(isSemiformula ℒₛₑₜ).pi.val)) : WB M (∼(isFormulaSet ℒₛₑₜ).pi.val) := by
  have := hsemi
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [isFormulaSet, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
end DiophantineConsistency.PRAWitnessFormulaSet
