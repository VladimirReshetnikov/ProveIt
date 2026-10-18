import BusyBeaver.ZFC.TablePrefix246
import BusyBeaver.ZFC.ZipperRuns

/-!
The two contextual pulse identities for the exact246 table.

Adapted from the checked Prefix250Pulse local identities and source63's
contextual fold97→255. In the zero/zero case the pulse returns to state255
and reads the one deposited by its first transition. The three literal
steps retain their exact duration and every cell of the tape.
No global left-neighbor invariant is asserted for the folded state255.
The original machine and framework retain Mira-Cult, Jeff and Wade's
attribution; the contextual fold is the ProveIt source63 contribution.
-/
namespace SetTheory.BusyBeaver.ZFC.Prefix246Pulse

open FiniteZipper ZipperRuns

private abbrev test := oldStatePrefix246 75
private abbrev rollback := oldStatePrefix246 112
private abbrev reverseCarry := oldStatePrefix246 131

/-- The self-returning pulse reads the one written two transitions earlier. -/
theorem pulse_zero_zero (h : Int) (l r : List Bool) :
    zipRun machinePrefix246 (zAt test h l (false :: false :: r)) 3 =
      leftAt reverseCarry h l (true :: true :: r) := by
  rw [zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowPrefix246_old75_false,
    zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowPrefix246_old255_false,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowPrefix246_old255_true]
  simp only [zipRun]
  congr 1
  omega

/-- The neighboring-one branch restores its initial zero before rollback. -/
theorem pulse_zero_one (h : Int) (l r : List Bool) :
    zipRun machinePrefix246 (zAt test h l (false :: true :: r)) 3 =
      leftAt rollback h l (false :: true :: r) := by
  rw [zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowPrefix246_old75_false,
    zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowPrefix246_old255_true,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowPrefix246_old131_true]
  simp only [zipRun]
  congr 1
  omega

/-- Whole-tape Core transport for both local cases and arbitrary contexts. -/
theorem pulse_core {c : Config 246} (b : Bool) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt test h l (false :: b :: r))) :
    ZipRep (machinePrefix246.runFrom c 3)
      (leftAt (if b then rollback else reverseCarry) h l ((!b) :: true :: r)) := by
  have hs := zipRun_sound machinePrefix246 3 hc
  cases b with
  | false => rw [pulse_zero_zero] at hs; exact hs
  | true => rw [pulse_zero_one] at hs; exact hs

end SetTheory.BusyBeaver.ZFC.Prefix246Pulse
