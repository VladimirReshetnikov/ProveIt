import BusyBeaver.ZFC.ArithmeticBlankControlRotation240

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticControlFile
open ArithmeticControlTable (controlRun)
open ControlCatalogueRotation240 (table)
open ArithmeticMachineRunFromRotation240 (runFrom)
open ArithmeticMachineRunRotation240 (run)
open ArithmeticBootstrapRotation240 (bootCode)
open ArithmeticStartupFrameRotation240 (seedFile)
open ArithmeticBlankControlRotation240

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBlankControlRotation240.physical_seed_code
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBlankControlRotation240.control_iff_seed_halts
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBlankControlRotation240.control_iff_blank_halts
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBlankControlRotation240.blank_iff_control_halts
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBlankControlRotation240.pairs_iff_blank_halts
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticBlankControlRotation240.blankSentence_iff_control_halts

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : seedFile (V := V) =
    cantor 0 (cantor 0 (cantor 0 (cantor 3 (cantor 0 (cantor 0 (cantor 3 (cantor 0 0))))))) :=
  physical_seed_code
example :
    (∃ time : V, controlRun table time (liveValue 1 (seedFile (V := V))) = 0) ↔
      (∃ time : V, first (runFrom time (bootCode : V)) = 0) := control_iff_seed_halts
example :
    (∃ time : V, controlRun table time (liveValue 1 (seedFile (V := V))) = 0) ↔
      (∃ time : V, first (run time) = 0) := control_iff_blank_halts
example :
    (∃ time : V, first (run time) = 0) ↔
      (∃ time : V, controlRun table time (liveValue 1 (seedFile (V := V))) = 0) :=
  blank_iff_control_halts
example :
    (∃ time : V, controlRun table time
      (liveValue 1
        (cantor 0 (cantor 0 (cantor 0 (cantor 3
          (cantor 0 (cantor 0 (cantor 3 (cantor 0 0))))))))) = 0) ↔
      (∃ time : V, first (run time) = 0) := pairs_iff_blank_halts
example : ArithmeticMachineRunRotation240.haltingSentence.val.Evalb (M := V) ![] ↔
    ∃ time : V, controlRun table time (liveValue 1 (seedFile (V := V))) = 0 :=
  blankSentence_iff_control_halts

-- The two directions keep the clocks internal and do not impose time bounds.
example (h : ∃ time : V, controlRun table time (liveValue 1 (seedFile (V := V))) = 0) :
    ∃ time : V, first (run time) = 0 := control_iff_blank_halts.mp h
example (h : ∃ time : V, first (run time) = 0) :
    ∃ time : V, controlRun table time (liveValue 1 (seedFile (V := V))) = 0 :=
  blank_iff_control_halts.mp h
