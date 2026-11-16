import PA194ORModelFinal
import ConPAMachineEndpoint
import ConPAISigma1Relative
import PA194NativeControllerCorrectness

/-! The model-level OR comparison gives an iPRA nonhalting equivalence
with the primary PA194 table. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PA194ORNonhalt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open IPRAStandardTheory
open ConPA.Machine ConPA.MachineEndpoint ConPA.ISigma1Models ConPA.ISigma1Transfer
open StrictSigmaOneInduction

noncomputable def haltSentence := machineHaltSentence PA194ORData.table 194

theorem nonhalt_iff :
    standardTheory ⊢ ∼PA194ExplicitEndpoint.haltSentence 🡘 ∼haltSentence := by
  let H := (haltDef PA194ORData.table 194).val
  have hH : Hierarchy 𝚺 1 H := haltDef_sigma_one _ _
  apply ConPA.Relative.nonhalt_iff PA194ExplicitEndpoint.haltMatrix
    (by simp [PA194ExplicitEndpoint.haltMatrix, Semiformula.Open])
    PA194ExplicitEndpoint.haltMatrix_bounded (bnd H)
    (hierarchy_bnd hH (by decide) (by intro _; rfl))
  intro M _ _ _ _ hr
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  have hvariant : (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ bnd H)) ↔
      ∃ t : M, π₁ (run PA194ORData.table t) = (194 : M) :=
    models_iff.trans ((PRAWitnessTransfer.eval_lMap_std (∃⁰ bnd H) ![]).trans
      ((evalb_ex (bnd H)).trans ((StrictPiTwoBridge.eval_bnd_iff (M := M) hH).symm.trans
        (haltDef_iff (V := M) PA194ORData.table 194))))
  exact (PA194NativeControllerCorrectness.endpoint (M := M)).trans
    ((PA194ORModelFinal.halt_iff_controller (M := M)).symm.trans hvariant.symm)

#print axioms nonhalt_iff
end PA194ORNonhalt
