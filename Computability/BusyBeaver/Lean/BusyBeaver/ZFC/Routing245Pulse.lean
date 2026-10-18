import BusyBeaver.ZFC.TableRouting245
import BusyBeaver.ZFC.ZipperRuns

/-!
The two contextual pulse identities for the exact routing245 table.

Direct port of the checked Prefix246Pulse local identities. The four used
old-label actions are unchanged in the routing245 candidate (source68,
arrival 8286787dd0468d848db345debe304b002d7064a4). Only their compact labels
and the binary state type are interpreted through the new literal table.
The zero/zero pulse returns to old255 and reads its deposited one. Both
three-step equations retain arbitrary contexts and every tape cell.

No global invariant, whole-table renaming or startup transport is asserted.
Mira-Cult, Jeff Ketchersid and Wade's original machine/framework attribution
and source63's contextual-fold contribution are retained.
-/
namespace SetTheory.BusyBeaver.ZFC.Routing245Pulse

open FiniteZipper ZipperRuns

private abbrev test := oldStateRouting245 75
private abbrev rollback := oldStateRouting245 112
private abbrev reverseCarry := oldStateRouting245 131

/-- The self-returning pulse reads the one written two transitions earlier. -/
theorem pulse_zero_zero (h : Int) (l r : List Bool) :
    zipRun machineRouting245 (zAt test h l (false :: false :: r)) 3 =
      leftAt reverseCarry h l (true :: true :: r) := by
  rw [zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowRouting245_old75_false,
    zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRouting245_old255_false,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRouting245_old255_true]
  simp only [zipRun]
  congr 1
  omega

/-- The neighboring-one branch restores its initial zero before rollback. -/
theorem pulse_zero_one (h : Int) (l r : List Bool) :
    zipRun machineRouting245 (zAt test h l (false :: true :: r)) 3 =
      leftAt rollback h l (false :: true :: r) := by
  rw [zipRun_first,
    step_right _ _ _ _ _ _ _ _ rowRouting245_old75_false,
    zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRouting245_old255_true,
    leftAt_cons, zipRun_first,
    step_left _ _ _ _ _ _ _ _ rowRouting245_old131_true]
  simp only [zipRun]
  congr 1
  omega

/-- Whole-tape Core transport for both local cases and arbitrary contexts. -/
theorem pulse_core {c : Config 245} (b : Bool) (h : Int) (l r : List Bool)
    (hc : ZipRep c (zAt test h l (false :: b :: r))) :
    ZipRep (machineRouting245.runFrom c 3)
      (leftAt (if b then rollback else reverseCarry) h l ((!b) :: true :: r)) := by
  have hs := zipRun_sound machineRouting245 3 hc
  cases b with
  | false => rw [pulse_zero_zero] at hs; exact hs
  | true => rw [pulse_zero_one] at hs; exact hs

end SetTheory.BusyBeaver.ZFC.Routing245Pulse
