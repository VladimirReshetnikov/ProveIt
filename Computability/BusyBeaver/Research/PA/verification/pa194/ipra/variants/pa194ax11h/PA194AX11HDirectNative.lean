import ConPAISigma1Relative
import ConPAMachineEndpoint
import PA194AX11HPhysicalFinal
import PA194AX11HConcreteScheduler
import PA194ControllerSchedulerPA

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace PA194AX11HDirectNative
open LO LO.Entailment LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open IPRAStandardTheory IPRAPA196Consistency
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch StrictSigmaOneInduction
open ConPA.Machine ConPA.MachineEndpoint ConPA.ISigma1Models ConPA.ISigma1Transfer
open PA194ControllerScheduler PA194ControllerSchedulerPA
open PA194AX11HSourceOrbit (sourceRun)
open PA194SourceControllerCode (pc)

/-- Source execution of returning and halting commands at model-valued
    clocks, for the top-updating MP, cache-only halt and eleven-entry AX
    scheduler of the revised table. -/
def CommandContracts : Prop :=
  ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA],
    let F := Structure.func (L := language) (M := M)
    letI : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
    letI : One M := ⟨F oneCode Fin.elim0⟩
    letI : Add M := ⟨fun x y => F addCode ![x,y]⟩
    letI : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
    letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
    ∀ [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
      (∀ s : M, F (haltAtK true) ![s] ≠ 1 →
        ∃ c : M, 0 < c ∧ F sourceRun ![c,F PA194SchedulerSourceFrame.frame ![s]] =
          F PA194SchedulerSourceFrame.frame ![F (stepK .top true) ![s]]) ∧
      (∀ s : M, F (haltAtK true) ![s] = 1 →
        ∃ c : M, F pc ![F sourceRun ![c,F PA194SchedulerSourceFrame.frame ![s]]] = modelNumeral M 10)

theorem scheduler_nonhalt_iff_literal (contracts : CommandContracts) :
    standardTheory ⊢ ∼haltSentenceK .top true true 🡘 ∼machineHaltSentence PA194AX11HData.table 194 := by
  let H := (haltDef PA194AX11HData.table 194).val
  have hH : Hierarchy 𝚺 1 H := haltDef_sigma_one _ _
  apply ConPA.Relative.nonhalt_iff (haltMatrixK .top true true)
    (by simp [haltMatrixK, Semiformula.Open])
    (Hierarchy.rel _ _ _ _) (bnd H)
    (hierarchy_bnd hH (by decide) (by intro _; rfl))
  intro M _ _ _ _ hr
  let F := Structure.func (L := language) (M := M)
  letI : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨F oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => F addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  have hs : (M↓[language] ⊧ ∃⁰ haltMatrixK .top true true) ↔
      ∃ n : M, F (haltAfterK .top true true) ![n] = 1 := by
    rw [models_iff, Semiformula.eval_ex]
    exact exists_congr fun n => by
      change (haltMatrixK .top true true).Eval ![n] Empty.elim ↔
        Structure.func (L := language) (M := M) (haltAfterK .top true true) ![n] =
          Structure.func (L := language) (M := M) oneCode Fin.elim0
      simpa only [← const_vec n] using (haltMatrixK_eval .top true true n)
  have ht : (M↓[language] ⊧ Semiformula.lMap embedding (∃⁰ bnd H)) ↔
      ∃ t : M, π₁ (ConPA.Machine.run PA194AX11HData.table t) = (194 : M) :=
    models_iff.trans ((PRAWitnessTransfer.eval_lMap_std (∃⁰ bnd H) ![]).trans
      ((evalb_ex (bnd H)).trans ((StrictPiTwoBridge.eval_bnd_iff (M := M) hH).symm.trans
        (haltDef_iff (V := M) PA194AX11HData.table 194))))
  obtain ⟨returning, halting⟩ := contracts M
  have hafter : (∃ n : M, F (haltAfterK .top true true) ![n] = 1) ↔
      ∃ n : M, F (haltAtK true) ![F (runK .top true) ![n,F PA194SchedulerIteration.initial Fin.elim0]] = 1 := by
    exact exists_congr fun n => by
      change Structure.func (L := language) (M := M) (haltAfterK .top true true) ![n] = 1 ↔
        Structure.func (L := language) (M := M) (haltAtK true)
          ![Structure.func (L := language) (M := M) (runK .top true)
            ![n,Structure.func (L := language) (M := M) PA194SchedulerIteration.initial Fin.elim0]] = 1
      rw [haltAfterK_model]
  have hsite := PA194AX11HConcreteScheduler.site10_iff_runK returning halting
  exact hs.trans (hafter.trans (hsite.symm.trans
    ((PA194AX11HPhysicalFinal.halt_iff_site10 (M := M)).symm.trans ht.symm)))

theorem consistency_iff_literal_nonhalt (contracts : CommandContracts) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194AX11HData.table 194 := by
  have scheduler := Classical.choice (consistency_iff_scheduler_nonhalt .top true true)
  have literal := Classical.choice (scheduler_nonhalt_iff_literal contracts)
  exact ⟨K_intro (C_trans (K_left scheduler) (K_left literal))
    (C_trans (K_right literal) (K_right scheduler))⟩

#print axioms scheduler_nonhalt_iff_literal
#print axioms consistency_iff_literal_nonhalt
end PA194AX11HDirectNative
