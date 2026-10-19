import BusyBeaver.ZFC.ArithmeticControlSimulationRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlFile
open ArithmeticControlTable (stepValue controlRun)
open ArithmeticControlFrameDataRotation240 ControlCatalogueRotation240
open ArithmeticMachineRunFromRotation240 (runFrom)
open ArithmeticControlSimulationRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulationRotation240.related_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulationRotation240.step_nonzero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulationRotation240.related_step
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulationRotation240.related_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulationRotation240.halts_iff_related
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlSimulationRotation240.halts_iff_entry

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (i : Control) (file extra gap : V) :
    Related (liveValue (number i : V) file) (entryValue (number i : V) file extra gap) :=
  related_entry i file extra gap
example (i : Control) (file : V) (hn : (source i).2 ≠ .halt) :
    stepValue table (liveValue (number i : V) file) ≠ 0 := step_nonzero i file hn
example (logical binary : V) (h : Related logical binary) (hn : stepValue table logical ≠ 0) :
    ∃ time : V, 0 < time ∧ Related (stepValue table logical) (runFrom time binary) :=
  related_step logical binary h hn
example (logical binary : V) (h : Related logical binary) (hz : stepValue table logical = 0) :
    ∃ time : V, 0 < time ∧ first (runFrom time binary) = 0 :=
  related_halt logical binary h hz
example (logical binary : V) (h : Related logical binary) :
    (∃ time : V, controlRun table time logical = 0) ↔
      (∃ time : V, first (runFrom time binary) = 0) := halts_iff_related logical binary h
example (i : Control) (file extra gap : V) :
    (∃ time : V, controlRun table time (liveValue (number i : V) file) = 0) ↔
      (∃ time : V, first (runFrom time (entryValue (number i : V) file extra gap)) = 0) :=
  halts_iff_entry i file extra gap

-- Logical-to-binary halting retains arbitrary internal extra spares and gap.
example (i : Control) (file extra gap : V)
    (h : ∃ time : V, controlRun table time (liveValue (number i : V) file) = 0) :
    ∃ time : V, first (runFrom time (entryValue (number i : V) file extra gap)) = 0 :=
  (halts_iff_entry i file extra gap).mp h
-- Binary-to-logical halting uses positivity and absorption, not a clock upper bound.
example (i : Control) (file extra gap : V)
    (h : ∃ time : V, first (runFrom time (entryValue (number i : V) file extra gap)) = 0) :
    ∃ time : V, controlRun table time (liveValue (number i : V) file) = 0 :=
  (halts_iff_entry i file extra gap).mpr h
