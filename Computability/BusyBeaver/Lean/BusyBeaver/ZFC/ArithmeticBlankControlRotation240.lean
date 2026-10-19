import BusyBeaver.ZFC.ArithmeticStartupFrameRotation240
import BusyBeaver.ZFC.ArithmeticControlSimulationRotation240
import BusyBeaver.ZFC.ArithmeticStartupRotation240

set_option autoImplicit false

/-!
The all-internal blank/seed specialization of the Rotation240 control-to-binary
simulation. The initial control is one; the complete physical file is
[0,0,0,3,0,0,3,0,0], followed by 167 value-one spares, margin 64 and gap 117.
The checked finite bootstrap and whole-configuration halt absorption remove
the 409691-step prefix even if a proposed halt occurs before its end.

Both time witnesses range over an arbitrary IΣ₁ model. The exact packed
catalogue and the explicit physical seed code are used directly; this module
does not import the L2 scheduler or a consistency sentence. Their named
interface is supplied by a separate definitional adapter.
Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt retain the source,
machine, calibration and framework attribution of the imported units.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticBlankControlRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticControlFile
open ArithmeticControlTable (controlRun)
open ControlCatalogueRotation240 (table)
open ArithmeticMachineRunFromRotation240 (runFrom)
open ArithmeticMachineRunRotation240 (run)
open ArithmeticBootstrapRotation240 (bootCode)
open ArithmeticStartupFrameRotation240 (seedFile)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Nine physical fields use eight nested pairs; the final zero is the tail. -/
theorem physical_seed_code : seedFile (V := V) =
    cantor 0 (cantor 0 (cantor 0 (cantor 3 (cantor 0 (cantor 0 (cantor 3 (cantor 0 0))))))) :=
  ArithmeticStartupFrameRotation240.seedFile_pairs

theorem control_iff_seed_halts :
    (∃ time : V, controlRun table time (liveValue 1 (seedFile (V := V))) = 0) ↔
      (∃ time : V, first (runFrom time (bootCode : V)) = 0) :=
  ArithmeticControlSimulationRotation240.halts_iff_related
    (liveValue 1 (seedFile (V := V))) (bootCode : V)
    ArithmeticStartupFrameRotation240.initialRelated

/-- The concrete control interpreter halts exactly when the binary blank run does. -/
theorem control_iff_blank_halts :
    (∃ time : V, controlRun table time (liveValue 1 (seedFile (V := V))) = 0) ↔
      (∃ time : V, first (run time) = 0) :=
  control_iff_seed_halts.trans ArithmeticStartupRotation240.blank_iff_seed_halts.symm

theorem blank_iff_control_halts :
    (∃ time : V, first (run time) = 0) ↔
      (∃ time : V, controlRun table time (liveValue 1 (seedFile (V := V))) = 0) :=
  control_iff_blank_halts.symm

/-- The same statement with the physical seed written out, without an L2 import. -/
theorem pairs_iff_blank_halts :
    (∃ time : V, controlRun table time
      (liveValue 1
        (cantor 0 (cantor 0 (cantor 0 (cantor 3
          (cantor 0 (cantor 0 (cantor 3 (cantor 0 0))))))))) = 0) ↔
      (∃ time : V, first (run time) = 0) := by
  simpa only [physical_seed_code] using (control_iff_blank_halts (V := V))

/-- Evaluation of the existing fixed blank sentence, at the exact control seed. -/
theorem blankSentence_iff_control_halts :
    ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![] ↔
      ∃ time : V, controlRun table time (liveValue 1 (seedFile (V := V))) = 0 :=
  ArithmeticStartupRotation240.blankHaltingSentence_eval.trans blank_iff_control_halts

end SetTheory.BusyBeaver.ZFC.ArithmeticBlankControlRotation240
