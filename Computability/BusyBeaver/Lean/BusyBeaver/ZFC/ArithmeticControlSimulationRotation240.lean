import BusyBeaver.ZFC.ArithmeticSiteRotation240
import BusyBeaver.ZFC.ArithmeticControlStepRotation240
import BusyBeaver.ZFC.ArithmeticPositiveSimulation254

set_option autoImplicit false

/-!
Positive-clock transport for the exact Rotation240 packed control table.
The six site endpoints preserve the entire represented tape and reenter the
actual consumed-path control, with arbitrary internal file values, spare
counts and gaps. The fixed finite control catalogue is external; both the
logical iterator and binary clocks range over the IΣ₁ model.

The generic Sigma1 cofinal-clock theorem supplies both halting directions.
This module does not identify the initial bootstrap or state a consistency
sentence; those combine separately with this arbitrary-entry equivalence.
The imported machine/source/calibration attribution of Mira-Cult,
Jeff Ketchersid, Andrew James Wade and ProveIt is retained.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulationRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlFile
open ArithmeticControlTable (stepValue controlRun controlRun_zero controlRun_succ)
open ArithmeticControlFrameDataRotation240
open ControlCatalogueRotation240
open ArithmeticControlStepRotation240
open ArithmeticMachineRunFromRotation240 (runFrom runFrom_zero runFrom_add runFrom_halt_state)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every actual catalogue slot, including its halt instruction, is live here. -/
theorem related_entry (i : Control) (file extra gap : V) :
    Related (liveValue (number i : V) file) (entryValue (number i : V) file extra gap) := by
  refine ⟨live_ne_zero _ _, ?_, extra, gap, ?_⟩
  · simpa only [control_live] using (opcode_nonzero (V := V) i)
  · simp only [control_live, fileCode_live]

private theorem related_next_entry (i : Control) (positive : Bool)
    (hn : (source i).2 ≠ .halt) (file extra gap : V) :
    Related (liveValue (nextControl i positive : V) file)
      (entryValue (nextControl i positive : V) file extra gap) := by
  rw [nextControl_number i positive hn]
  exact related_entry _ file extra gap

theorem step_nonzero (i : Control) (file : V) (hh : (source i).2 ≠ .halt) :
    stepValue table (liveValue (number i : V) file) ≠ 0 := by
  cases he : (source i).2 with
  | node n => exact False.elim (source_not_node i n he)
  | inc r => rw [step_inc i r he]; exact live_ne_zero _ _
  | decnz r =>
      by_cases hz : regValue file (physical i) = 0
      · rw [step_decnz_zero i r he file hz]; exact live_ne_zero _ _
      · rw [step_decnz_positive i r he file hz]; exact live_ne_zero _ _
  | brk k => rw [step_break i k he]; exact live_ne_zero _ _
  | cont k => rw [step_continue i k he]; exact live_ne_zero _ _
  | halt => exact False.elim (hh he)

/-- A positive internal binary clock for each nonhalting represented step. -/
theorem related_step (logical binary : V) (h : Related logical binary)
    (hn : stepValue table logical ≠ 0) :
    ∃ time : V, 0 < time ∧ Related (stepValue table logical) (runFrom time binary) := by
  obtain ⟨hl, hop, extra, gap, hb⟩ := h
  obtain ⟨i, hq⟩ := opcode_supported (controlValue logical) hop
  let file := fileCodeValue logical
  have heql : logical = liveValue (number i : V) file := by
    simpa only [hq] using (live_decode logical hl).symm
  have hb' : binary = entryValue (number i : V) file extra gap := by
    simpa only [hq] using hb
  cases he : (source i).2 with
  | node n => exact False.elim (source_not_node i n he)
  | inc r =>
      obtain ⟨time, ht, hr⟩ := ArithmeticSiteRotation240.source_inc i r he file extra gap
      refine ⟨time, ht, ?_⟩
      rw [heql, step_inc i r he, hb', hr]
      exact related_next_entry i false (by rw [he]; intro hh; cases hh) _ _ _
  | decnz r =>
      by_cases hz : regValue file (physical i) = 0
      · obtain ⟨time, ht, hr⟩ :=
          ArithmeticSiteRotation240.source_decnz_zero i r he file extra gap hz
        refine ⟨time, ht, ?_⟩
        rw [heql, step_decnz_zero i r he file hz, hb', hr]
        exact related_next_entry i false (by rw [he]; intro hh; cases hh) _ _ _
      · obtain ⟨time, ht, hr⟩ :=
          ArithmeticSiteRotation240.source_decnz_positive i r he file extra gap hz
        refine ⟨time, ht, ?_⟩
        rw [heql, step_decnz_positive i r he file hz, hb', hr]
        exact related_next_entry i true (by rw [he]; intro hh; cases hh) _ _ _
  | brk k =>
      obtain ⟨time, ht, hr⟩ := ArithmeticSiteRotation240.source_break i k he file extra gap
      refine ⟨time, ht, ?_⟩
      rw [heql, step_break i k he, hb', hr]
      exact related_next_entry i false (by rw [he]; intro hh; cases hh) _ _ _
  | cont k =>
      obtain ⟨time, ht, hr⟩ := ArithmeticSiteRotation240.source_continue i k he file extra gap
      refine ⟨time, ht, ?_⟩
      rw [heql, step_continue i k he, hb', hr]
      exact related_next_entry i false (by rw [he]; intro hh; cases hh) _ _ _
  | halt => exact False.elim (hn (by rw [heql, step_halt i he]))

/-- Invalid controls are excluded by Related before identifying the halt case. -/
theorem related_halt (logical binary : V) (h : Related logical binary)
    (hz : stepValue table logical = 0) :
    ∃ time : V, 0 < time ∧ first (runFrom time binary) = 0 := by
  obtain ⟨hl, hop, extra, gap, hb⟩ := h
  obtain ⟨i, hq⟩ := opcode_supported (controlValue logical) hop
  let file := fileCodeValue logical
  have heql : logical = liveValue (number i : V) file := by
    simpa only [hq] using (live_decode logical hl).symm
  have hb' : binary = entryValue (number i : V) file extra gap := by
    simpa only [hq] using hb
  have hh : (source i).2 = .halt := by
    by_contra hnot
    apply step_nonzero i file hnot
    rw [←heql]
    exact hz
  obtain ⟨time, ht, hr⟩ := ArithmeticSiteRotation240.source_halt i hh file extra gap
  exact ⟨time, ht, by simpa only [hb'] using hr⟩

/-- The two halting directions hold for every Related pair, at internal times. -/
theorem halts_iff_related (logical binary : V) (h : Related logical binary) :
    (∃ time : V, controlRun table time logical = 0) ↔
      (∃ time : V, first (runFrom time binary) = 0) := by
  haveI : 𝚺₁-Function₁[V] (fun time => controlRun table time logical) := by
    definability
  apply ArithmeticPositiveSimulation254.halts_iff
    (stepValue table) (fun time => controlRun table time logical)
    runFrom Related (fun config => first config = 0) logical binary
  · exact controlRun_zero table logical
  · intro time; exact controlRun_succ table time logical
  · exact runFrom_zero
  · exact runFrom_add
  · exact h
  · exact related_live
  · intro l b hr hh; exact related_active l b hr hh
  · exact related_step
  · intro l b hr hh
    obtain ⟨time, _, ht⟩ := related_halt l b hr hh
    exact ⟨time, ht⟩
  · intro config hh time
    exact runFrom_halt_state time config hh

theorem halts_iff_entry (i : Control) (file extra gap : V) :
    (∃ time : V, controlRun table time (liveValue (number i : V) file) = 0) ↔
      (∃ time : V,
        first (runFrom time (entryValue (number i : V) file extra gap)) = 0) :=
  halts_iff_related _ _ (related_entry i file extra gap)

end SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulationRotation240
