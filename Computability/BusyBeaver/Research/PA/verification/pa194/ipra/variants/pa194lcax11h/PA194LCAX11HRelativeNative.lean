import PA194LCAX11HController
import PA194AX11HPhysicalFinal
import PA194AX11HDirectNative
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace PA194LCAX11HRelativeNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open IPRAStandardTheory IPRAPA196Consistency
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch StrictSigmaOneInduction
open ConPA.Machine ConPA.MachineEndpoint ConPA.ISigma1Models ConPA.ISigma1Transfer

theorem relative_nonhalt (coverage : PA194LCAX11HChecks.AllContracts) :
    standardTheory ⊢ ∼machineHaltSentence PA194AX11HData.table 194 🡘
      ∼machineHaltSentence PA194LCAX11HData.table 194 := by
  apply ConPA.Relative.bounded_nonhalt_iff (bnd (haltDef PA194AX11HData.table 194).val)
    (bnd (haltDef PA194LCAX11HData.table 194).val)
    (hierarchy_bnd (haltDef_sigma_one _ _) (by decide) (by intro _; rfl))
    (hierarchy_bnd (haltDef_sigma_one _ _) (by decide) (by intro _; rfl))
  intro M _ _ _ _ reduct
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 reduct
  have modelsHalt (table : Table) (halt : Nat) :
      (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ bnd (haltDef table halt).val)) ↔
        ∃ t : M, π₁ (run table t) = (halt : M) := by
    let H := (haltDef table halt).val
    have hH : Hierarchy 𝚺 1 H := haltDef_sigma_one table halt
    exact models_iff.trans ((PRAWitnessTransfer.eval_lMap_std (∃⁰ bnd H) ![]).trans
      ((evalb_ex (bnd H)).trans ((StrictPiTwoBridge.eval_bnd_iff (M := M) hH).symm.trans
        (haltDef_iff (V := M) table halt))))
  have ax := PA194AX11HPhysicalFinal.halt_iff_site10 (M := M)
  have lc := PA194LCAX11HController.halt_iff_site10 (M := M) coverage
  exact (modelsHalt _ _).trans (ax.trans (lc.symm.trans (modelsHalt _ _).symm))

theorem consistency_iff (coverage : PA194LCAX11HChecks.AllContracts)
    (contracts : PA194AX11HDirectNative.CommandContracts) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194LCAX11HData.table 194 := by
  have a := Classical.choice (PA194AX11HDirectNative.consistency_iff_literal_nonhalt contracts)
  have b := Classical.choice (relative_nonhalt coverage)
  exact ⟨K_intro (C_trans (K_left a) (K_left b)) (C_trans (K_right b) (K_right a))⟩
#print axioms relative_nonhalt
#print axioms consistency_iff
end PA194LCAX11HRelativeNative
