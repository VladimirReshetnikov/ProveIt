import PA196InductionFvarTailComplete
import DiophantineConsistency.PRAWitnessPR

/-! The positive induction recognizer bound conditional on the arithmetic
formula-shift graph witness bound. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace PA196InductionPositiveConditional
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus PRAWitnessPR
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_positive (hshift : WB M (shiftGraph ℒₒᵣ).val) : WB M chUniv.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_qqAllsDef (M := M)
  have := PA196PAFormulaComplete.wb_isUFormula_sigma (M := M)
  have := PA196PAFormulaSetComplete.wb_bvGraph (M := M)
  have hf := PA196InductionFvarTailComplete.wb_actualFvarExists (M := M)
  simp only [PA196InductionFvarWitness.actualFvarExists, chUniv,
    HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma,
    Semiformula.bexsLT, FirstOrder.bexs] at hf
  simp only [chUniv, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  simpa [Semiformula.bexsLT, FirstOrder.bexs] using hf

#print axioms wb_positive
end PA196InductionPositiveConditional
