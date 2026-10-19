import BusyBeaver.ZFC.Rotation244KernelRows
import BusyBeaver.ZFC.ZipperRuns

/-!
Fresh Rotation244 port of Routing245Pulse.
Only machine/state/module identities and the explicit selector literals change.
All-register, complete-tape and positive-clock hypotheses are retained.
The original Mira-Cult/Jeff Ketchersid/Andrew James Wade and ProveIt lineage
remains attributed. This source is uncompiled at emission; coverage, exact
blank initialization and the final Combined243 calibration remain separate.
-/
namespace SetTheory.BusyBeaver.ZFC.Rotation244Pulse

open FiniteZipper ZipperRuns

private abbrev test := oldStateRotation244 75
private abbrev rollback := oldStateRotation244 112
private abbrev reverseCarry := oldStateRotation244 131

/-- The self-returning pulse reads the one written two transitions earlier. -/
theorem pulse_zero_zero (h : Int) (l r : List Bool) :
    zipRun machineRotation244 (zAt test h l (false :: false :: r)) 3 =
      leftAt reverseCarry h l (true :: true :: r) := by
  rw [zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowRotation244_old75_false,
    zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation244_old255_false,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation244_old255_true]
  simp only [zipRun]
  congr 1
  omega

/-- The neighboring-one branch restores its initial zero before rollback. -/
theorem pulse_zero_one (h : Int) (l r : List Bool) :
    zipRun machineRotation244 (zAt test h l (false :: true :: r)) 3 =
      leftAt rollback h l (false :: true :: r) := by
  rw [zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowRotation244_old75_false,
    zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation244_old255_true,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRotation244_old131_true]
  simp only [zipRun]
  congr 1
  omega

/-- Whole-tape Core transport for both local cases and arbitrary contexts. -/
theorem pulse_core {c : Config 244} (b : Bool) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt test h l (false :: b :: r))) :
    ZipRep (machineRotation244.runFrom c 3)
      (leftAt (if b then rollback else reverseCarry) h l ((!b) :: true :: r)) := by
  have hs := zipRun_sound machineRotation244 3 hc
  cases b with
  | false => rw [pulse_zero_zero] at hs; exact hs
  | true => rw [pulse_zero_one] at hs; exact hs

end SetTheory.BusyBeaver.ZFC.Rotation244Pulse
