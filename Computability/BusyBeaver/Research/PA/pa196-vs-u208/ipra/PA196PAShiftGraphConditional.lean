import PA196PATermOperations
import PA196PAFormulaRecBound
import DiophantineConsistency.PRAWitnessFormulaFunctions

/-! Arithmetic formula shift witness bound conditional on its two negative
relation clauses. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PAShiftGraphConditional
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PRAWitnessFormulaFunctions PRAWitnessFormulaRec PRAWitnessTransfer
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem positive_rel : WB M (Shift.blueprint ℒₒᵣ).rel.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196PATermOperations.wb_termShiftVecGraph (M := M)
  have := PRAWitnessArithmetic.wb_qqRelDef (M := M)
  simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
  exact wb_exs_poly _ (by simp) ‘#0’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      simpa [h'.2] using le_of_lt (v_lt_rel (e 2) (e 3) u), h⟩) (by wb_auto)

theorem positive_nrel : WB M (Shift.blueprint ℒₒᵣ).nrel.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := PA196PATermOperations.wb_termShiftVecGraph (M := M)
  have := PRAWitnessArithmetic.wb_qqNRelDef (M := M)
  simp only [Shift.blueprint, HierarchySymbol.Semiformula.val_mkSigma]
  exact wb_exs_poly _ (by simp) ‘#0’
    (fun V _ _ e u h => ⟨u, by
      have h' := h; simp at h'
      simpa [h'.2] using le_of_lt (v_lt_nrel (e 2) (e 3) u), h⟩) (by wb_auto)

theorem shift_clauses
    (hrel : WB M (∼(Shift.blueprint ℒₒᵣ).rel.graphDelta.pi.val))
    (hnrel : WB M (∼(Shift.blueprint ℒₒᵣ).nrel.graphDelta.pi.val)) :
    ClauseBounds (Shift.blueprint ℒₒᵣ) M := by
  have hc := PRAWitnessFormulaFunctions.shift_clauses (M := M)
  exact ⟨positive_rel,positive_nrel,hc.verum,hc.falsum,hc.and,hc.or,hc.all,hc.exs,
    hc.allChanges,hc.exsChanges,hrel,hnrel,hc.verum_pi,hc.falsum_pi,hc.and_pi,hc.or_pi,
    hc.all_pi,hc.exs_pi,hc.allChanges_le,hc.exsChanges_le⟩

noncomputable abbrev arithmeticShiftConstructions : Constructions (Shift.blueprint ℒₒᵣ) :=
  fun _ _ _ => Shift.construction ℒₒᵣ

theorem arithmeticShift_shape (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    RecShape (arithmeticShiftConstructions V) where
  all_le _ := by simp [Shift.construction]
  exs_le _ := by simp [Shift.construction]
  and_le _ _ _ y₁ y₂ := ⟨le_succ_of_lt (lt_K!_left y₁ y₂), le_succ_of_lt (lt_K!_right y₁ y₂)⟩
  or_le _ _ _ y₁ y₂ := ⟨le_succ_of_lt (lt_or_left y₁ y₂), le_succ_of_lt (lt_or_right y₁ y₂)⟩
  all_y _ _ y₁ := le_succ_of_lt (lt_forall y₁)
  exs_y _ _ y₁ := le_succ_of_lt (lt_exists y₁)

theorem wb_shiftGraph
    (hrel : WB M (∼(Shift.blueprint ℒₒᵣ).rel.graphDelta.pi.val))
    (hnrel : WB M (∼(Shift.blueprint ℒₒᵣ).nrel.graphDelta.pi.val)) :
    WB M (shiftGraph ℒₒᵣ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  simp only [shiftGraph, HierarchySymbol.Semiformula.val_rew]
  exact wb_rew _ (PA196PAFormulaRecBound.wb_result arithmeticShiftConstructions
    arithmeticShift_shape (shift_clauses hrel hnrel))

#print axioms wb_shiftGraph
end PA196PAShiftGraphConditional
