import BusyBeaver.ZFC.Rotation240KernelRows
import BusyBeaver.ZFC.ZipperRuns

/-!
Fresh exact240 port of Rotation244Pulse.
The checked predecessor proof bodies are retained under machine/state/module
changes and the exact nine selector literals. Arbitrary registers, complete
tapes and positive clocks remain explicit. Original Mira-Cult, Jeff Ketchersid,
Andrew James Wade and ProveIt attribution is retained.
This generated source is uncompiled; concrete decoder coverage, blank startup
and the final external consistency endpoint require separate actual proofs.
-/
namespace SetTheory.BusyBeaver.ZFC.Rotation240Pulse

open FiniteZipper ZipperRuns

private abbrev test := oldStateRotation240 75
private abbrev rollback := oldStateRotation240 112
private abbrev reverseCarry := oldStateRotation240 131

/-- The self-returning pulse reads the one written two transitions earlier. -/
theorem pulse_zero_zero (h : Int) (l r : List Bool) :
    zipRun machineRotation240 (zAt test h l (false :: false :: r)) 3 =
      leftAt reverseCarry h l (true :: true :: r) := by
  rw [zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowRotation240_old75_false,
    zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation240_old255_false,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation240_old255_true]
  simp only [zipRun]
  congr 1
  omega

/-- The neighboring-one branch restores its initial zero before rollback. -/
theorem pulse_zero_one (h : Int) (l r : List Bool) :
    zipRun machineRotation240 (zAt test h l (false :: true :: r)) 3 =
      leftAt rollback h l (false :: true :: r) := by
  rw [zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowRotation240_old75_false,
    zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation240_old255_true,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation240_old131_true]
  simp only [zipRun]
  congr 1
  omega

/-- Whole-tape Core transport for both local cases and arbitrary contexts. -/
theorem pulse_core {c : Config 240} (b : Bool) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt test h l (false :: b :: r))) :
    ZipRep (machineRotation240.runFrom c 3)
      (leftAt (if b then rollback else reverseCarry) h l ((!b) :: true :: r)) := by
  have hs := zipRun_sound machineRotation240 3 hc
  cases b with
  | false => rw [pulse_zero_zero] at hs; exact hs
  | true => rw [pulse_zero_one] at hs; exact hs

end SetTheory.BusyBeaver.ZFC.Rotation240Pulse
