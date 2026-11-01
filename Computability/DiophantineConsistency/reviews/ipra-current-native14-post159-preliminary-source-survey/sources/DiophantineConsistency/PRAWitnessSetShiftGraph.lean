import DiophantineConsistency.PRAWitnessTransfer
import ZFCinPA.Instances
import DiophantineConsistency.PRAWitnessArithmetic
/-! Witness bounds for the actual set-shift graph. The graph contains one
unbounded image witness, which belongs to its output set and is therefore
bounded by that set. The bound for the shift graph is an explicit hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessSetShiftGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessTransfer
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_setShiftGraph (hshift : WB M (shiftGraph ℒₛₑₜ).val) : WB M (setShiftGraph ℒₛₑₜ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := hshift
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [setShiftGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e u h => ⟨u, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  exact le_of_lt (lt_of_mem h'.2)
end DiophantineConsistency.PRAWitnessSetShiftGraph
