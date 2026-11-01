import DiophantineConsistency.PRAWitnessBoundTerms
import DiophantineConsistency.PRAWitnessSetShiftCandidate
/-! The actual set-shift output has an explicitly represented double-exponential
majorant in IΣ₁ models. Witness transfer uses this to bound the negative pi
functional graph in arbitrary candidate-PRA models. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessSetShiftOutput
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCodeGrowth PRAWitnessBoundTerms PRAWitnessBoundTerms.BoundTerm

/-- Majorant of the value of `setShift` in the second input position. -/
noncomputable def setShiftBound : BoundTerm 2 :=
  exp2 (poly ‘1’) (poly ‘((#1+2)*(#1+2)+1+8+4)*(#1*#1*64)+1’)

theorem setShiftBound_spec {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (e : Fin 2 → V) : setShift ℒₛₑₜ (e 1) ≤ setShiftBound.vval e := by
  simpa [setShiftBound, BoundTerm.vval, numeral_eq_natCast] using setShift_le (e 1)
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessArithmetic
  PRAWitnessBoundTerms
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_neg_setShiftGraphDelta_pi : WB M (∼(setShiftGraph ℒₛₑₜ).graphDelta.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := PRAWitnessSetShiftCandidate.wb_setShiftGraph (M := M)
  simp only [HierarchySymbol.Semiformula.graphDelta, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  refine wb_exs_bt _ (by simp) setShiftBound ?_ (by wb_auto)
  intro V _ _ e y h
  have h' := h
  simp [Matrix.comp_vecCons'', PRAHistoryTruncation.val_comp_bvar] at h'
  rw [h'.1]
  exact setShiftBound_spec e
end DiophantineConsistency.PRAWitnessSetShiftOutput
