import BusyBeaver.ZFC.ArithmeticControlConstructor254
import BusyBeaver.ZFC.ArithmeticControlSourceRank254

set_option autoImplicit false
noncomputable section

/-!
Actual AX implication constructor at controls433→460. All 27 instruction edges
and 35 successor branches reuse cached full equalities for the existing catalogue.
The generic constructor contract supplies the unbounded internal execution.
This occurrence follows the constructor ending at control433.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor433254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCode254 ArithmeticControlRun254
open ArithmeticControlStep254 ArithmeticControlFrame254
open ArithmeticControlPair254 ArithmeticControlConstructor254
open ArithmeticControlFetch254 (put s1Reg)
open ArithmeticControlRead254 (s2Reg)
open ArithmeticControlUnpair254 (wsReg)
open ArithmeticControlUnpairCore254 (UnpairCoreShape)
open ArithmeticControlMP254 (Scale4Shape)
open FiniteControlTable254 RegisterPath

/-- The next actual AX implication constructor starts at control433. -/
def entry : Control := ⟨433, by decide⟩
/-- Its zero-tag exit is the next constructor, at control460. -/
def exit : Control := ⟨460, by decide⟩

private def c434 : Control := ⟨434, by decide⟩
private def c435 : Control := ⟨435, by decide⟩
private def c436 : Control := ⟨436, by decide⟩
private def c437 : Control := ⟨437, by decide⟩
private def c438 : Control := ⟨438, by decide⟩
private def c439 : Control := ⟨439, by decide⟩
private def c440 : Control := ⟨440, by decide⟩
private def c441 : Control := ⟨441, by decide⟩
private def c442 : Control := ⟨442, by decide⟩
private def c443 : Control := ⟨443, by decide⟩
private def c444 : Control := ⟨444, by decide⟩
private def c445 : Control := ⟨445, by decide⟩
private def c446 : Control := ⟨446, by decide⟩
private def c447 : Control := ⟨447, by decide⟩
private def c448 : Control := ⟨448, by decide⟩
private def c449 : Control := ⟨449, by decide⟩
private def c450 : Control := ⟨450, by decide⟩
private def c451 : Control := ⟨451, by decide⟩
private def c452 : Control := ⟨452, by decide⟩
private def c453 : Control := ⟨453, by decide⟩
private def c454 : Control := ⟨454, by decide⟩
private def c455 : Control := ⟨455, by decide⟩
private def c456 : Control := ⟨456, by decide⟩
private def c457 : Control := ⟨457, by decide⟩
private def c458 : Control := ⟨458, by decide⟩
private def c459 : Control := ⟨459, by decide⟩

/-- Cache each complete catalogue equality before checking finite paths. -/
private theorem source_433 :
    source entry =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, false], .decnz 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 423) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 409) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 395) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 394) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 393) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 392) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 311) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 158) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 79) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 27) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_434 :
    source c434 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, false], .inc 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 424) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 410) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 396) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 395) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 394) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 393) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 312) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 159) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 80) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 28) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_435 :
    source c435 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, false], .decnz 6) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 425) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 411) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 397) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 396) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 395) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 394) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 313) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 160) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 81) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 29) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_436 :
    source c436 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, false, true], .brk 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 426) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 412) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 398) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 397) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 396) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 395) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 314) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 161) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 82) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 30) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_437 :
    source c437 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, false], .decnz 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 427) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 413) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 399) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 398) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 397) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 396) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 315) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 162) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 83) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 31) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 2) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_438 :
    source c438 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, true, false], .inc 6) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 428) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 414) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 400) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 399) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 398) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 397) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 316) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 163) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 84) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 32) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 2) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_439 :
    source c439 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, false, true, true, true], .cont 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 429) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 415) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 401) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 400) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 399) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 398) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 317) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 164) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 85) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 33) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 6) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 2) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_440 :
    source c440 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, false, true, true, true], .cont 3) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 430) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 416) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 402) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 401) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 400) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 399) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 318) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 165) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 86) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 34) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 7) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 6) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 5) (i := 0) (by rfl)
  exact .here _

private theorem source_441 :
    source c441 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, true, false], .decnz 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 431) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 417) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 403) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 402) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 401) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 400) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 319) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 166) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 87) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 35) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 8) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 8) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_442 :
    source c442 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, true, true, false], .inc 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 432) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 418) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 404) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 403) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 402) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 401) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 320) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 167) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 88) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 36) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 9) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 8) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_443 :
    source c443 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, false, true, true, true], .cont 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 433) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 419) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 405) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 404) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 403) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 402) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 321) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 168) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 89) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 37) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 10) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 8) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_444 :
    source c444 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, false], .decnz 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 434) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 420) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 406) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 405) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 404) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 403) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 322) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 169) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 90) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 38) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 11) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_445 :
    source c445 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, false], .inc 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 435) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 421) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 407) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 406) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 405) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 404) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 323) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 170) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 91) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 39) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 12) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_446 :
    source c446 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, false], .inc 6) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 436) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 422) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 408) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 407) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 406) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 405) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 324) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 171) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 92) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 40) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 13) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_447 :
    source c447 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, false, true, true, true], .cont 3) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 437) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 423) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 409) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 408) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 407) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 406) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 325) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 172) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 93) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 41) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 14) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_448 :
    source c448 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, false], .decnz 6) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 438) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 424) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 410) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 409) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 408) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 407) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 326) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 173) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 94) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 42) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 15) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_449 :
    source c449 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, false], .inc 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 439) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 425) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 411) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 410) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 409) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 408) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 327) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 174) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 95) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 43) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 16) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_450 :
    source c450 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, true, false], .decnz 6) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 440) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 426) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 412) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 411) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 410) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 409) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 328) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 175) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 96) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 44) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 17) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 6) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_451 :
    source c451 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, true, true, false], .inc 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 441) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 427) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 413) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 412) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 411) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 410) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 329) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 176) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 97) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 45) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 18) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 7) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_452 :
    source c452 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, false, true, true, true], .cont 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 442) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 428) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 414) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 413) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 412) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 411) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 330) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 177) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 98) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 46) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 19) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 8) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_453 :
    source c453 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, false, true, true, true], .cont 3) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 443) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 429) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 415) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 414) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 413) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 412) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 331) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 178) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 99) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 47) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 20) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 9) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 0) (by rfl)
  exact .here _

private theorem source_454 :
    source c454 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, false], .decnz 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 444) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 430) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 416) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 415) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 414) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 413) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 332) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 179) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 100) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 48) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 21) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 10) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_455 :
    source c455 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, true, false, false, false], .inc 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 445) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 431) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 417) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 416) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 415) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 414) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 333) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 180) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 101) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 49) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 22) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 11) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_456 :
    source c456 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, true, false, false, true], .inc 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 446) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 432) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 418) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 417) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 416) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 415) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 334) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 181) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 102) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 50) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 23) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 12) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_457 :
    source c457 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, true, false, true, false], .inc 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 447) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 433) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 419) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 418) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 417) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 416) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 335) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 182) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 103) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 51) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 24) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 13) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 2) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_458 :
    source c458 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, true, false, true, true], .inc 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 448) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 434) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 420) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 419) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 418) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 417) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 336) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 183) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 104) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 52) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 25) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 14) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 2) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_459 :
    source c459 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true, true, true, true, true], .cont 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 449) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 435) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 421) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 420) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 419) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 418) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 337) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 184) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 105) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 53) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 27) (i := 26) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 15) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 0) (by rfl)
  exact .here _

private theorem source_460 :
    source exit =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false, false, false, false], .decnz 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 450) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 436) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 422) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 421) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 420) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 419) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 338) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 338) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

theorem entry_source : (source entry).2 = .decnz 2 := congrArg Prod.snd source_433
theorem exit_source : (source exit).2 = .decnz 2 := congrArg Prod.snd source_460

/-- Resolve a literal target through its finite tree path, avoiding catalogue search. -/
private theorem literal_target (P : List Bool) (q : Control)
    (hw : RMBisim.twalk ActualTree254.tree P 0 =
      some ((source q).2, (source q).1.length))
    (hc : consume P (source q).1.length = (source q).1) : resolveControl P = q := by
  have hw' : walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 =
      some ((source q).2, (source q).1.length) := by
    rw [RMBisim.walk_root, ActualTree254.tree_eq]
    exact hw
  apply source_injective
  rw [resolve_source _ _ _ hw', hc]

/-- Rewrite only abstract source equalities before checking the finite path. -/
private theorem cached_target {a b : Control} {P Q : List Bool} {e f : Edge}
    (ha : source a = (P, e)) (hb : source b = (Q, f))
    (next : List Bool → List Bool)
    (hw : RMBisim.twalk ActualTree254.tree (next P) 0 = some (f, Q.length))
    (hc : consume (next P) Q.length = Q) :
    resolveControl (next (source a).1) = b := by
  rw [ha]
  apply literal_target
  · simpa only [hb] using hw
  · simpa only [hb] using hc

private def impPop : UnpairCoreShape where
  readEntry := entry
  bodyIncS2 := c434
  bodyTestS1 := c435
  bodyBreak := c436
  bodyMoveTest := c437
  bodyMoveInc := c438
  bodyMoveContinue := c439
  bodyContinue := c440
  restoreMainTest := c441
  restoreMainInc := c442
  restoreMainContinue := c443
  exit := c444
  mainLogical := 2
  mainIndex := wsReg
  main_physical := rfl
  main_ne_s1 := by decide
  main_ne_s2 := by decide
  read_edge := congrArg Prod.snd source_433
  body_inc_edge := congrArg Prod.snd source_434
  body_test_edge := congrArg Prod.snd source_435
  body_break_edge := congrArg Prod.snd source_436
  body_move_test_edge := congrArg Prod.snd source_437
  body_move_inc_edge := congrArg Prod.snd source_438
  body_move_continue_edge := congrArg Prod.snd source_439
  body_continue_edge := congrArg Prod.snd source_440
  restore_test_edge := congrArg Prod.snd source_441
  restore_inc_edge := congrArg Prod.snd source_442
  restore_continue_edge := congrArg Prod.snd source_443
  next_read_positive := cached_target source_433 source_434 incPath (by rfl) (by rfl)
  next_read_zero := cached_target source_433 source_441 (breakPath 1) (by rfl) (by rfl)
  next_body_inc := cached_target source_434 source_435 incPath (by rfl) (by rfl)
  next_body_test_positive := cached_target source_435 source_436 incPath (by rfl) (by rfl)
  next_body_test_zero := cached_target source_435 source_437 (breakPath 1) (by rfl) (by rfl)
  next_body_break := cached_target source_436 source_440 (breakPath 1) (by rfl) (by rfl)
  next_body_move_positive := cached_target source_437 source_438 incPath (by rfl) (by rfl)
  next_body_move_inc := cached_target source_438 source_439 incPath (by rfl) (by rfl)
  next_body_move_continue := cached_target source_439 source_437 (continuePath 2) (by rfl) (by rfl)
  next_body_move_zero := cached_target source_437 source_440 (breakPath 1) (by rfl) (by rfl)
  next_body_continue := cached_target source_440 source_433 (continuePath 3) (by rfl) (by rfl)
  next_restore_main_positive := cached_target source_441 source_442 incPath (by rfl) (by rfl)
  next_restore_main_inc := cached_target source_442 source_443 incPath (by rfl) (by rfl)
  next_restore_main_continue := cached_target source_443 source_441 (continuePath 2) (by rfl) (by rfl)
  next_restore_main_zero := cached_target source_441 source_444 (breakPath 1) (by rfl) (by rfl)

private def impCopy : CopyShape where
  test := c444
  firstInc := c445
  secondInc := c446
  again := c447
  exit := c448
  sourceLogical := 1
  firstLogical := 7
  secondLogical := 6
  sourceIndex := twReg
  firstIndex := s2Reg
  secondIndex := s1Reg
  source_physical := rfl
  first_physical := rfl
  second_physical := rfl
  source_ne_first := by decide
  source_ne_second := by decide
  first_ne_second := by decide
  test_edge := congrArg Prod.snd source_444
  first_edge := congrArg Prod.snd source_445
  second_edge := congrArg Prod.snd source_446
  again_edge := congrArg Prod.snd source_447
  positive_target := cached_target source_444 source_445 incPath (by rfl) (by rfl)
  first_target := cached_target source_445 source_446 incPath (by rfl) (by rfl)
  second_target := cached_target source_446 source_447 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_447 source_444 (continuePath 3) (by rfl) (by rfl)
  zero_target := cached_target source_444 source_448 (breakPath 1) (by rfl) (by rfl)

private def impMove : MoveShape where
  test := c450
  increment := c451
  again := c452
  exit := c453
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_450
  increment_edge := congrArg Prod.snd source_451
  again_edge := congrArg Prod.snd source_452
  positive_target := cached_target source_450 source_451 incPath (by rfl) (by rfl)
  increment_target := cached_target source_451 source_452 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_452 source_450 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_450 source_453 (breakPath 1) (by rfl) (by rfl)

private def impPair : PairShape where
  copy := impCopy
  testS1 := c448
  incS2 := c449
  move := impMove
  again := c453
  exit := c454
  copy_source := by rfl
  copy_first := by rfl
  copy_second := by rfl
  copy_exit := by rfl
  move_source := by rfl
  move_target := by rfl
  move_exit := by rfl
  test_edge := congrArg Prod.snd source_448
  increment_edge := congrArg Prod.snd source_449
  again_edge := congrArg Prod.snd source_453
  positive_target := cached_target source_448 source_449 incPath (by rfl) (by rfl)
  zero_target := cached_target source_448 source_454 (breakPath 1) (by rfl) (by rfl)
  increment_target := cached_target source_449 source_450 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_453 source_444 (continuePath 3) (by rfl) (by rfl)

private def impScale : Scale4Shape where
  test := c454
  inc1 := c455
  inc2 := c456
  inc3 := c457
  inc4 := c458
  again := c459
  exit := exit
  test_edge := congrArg Prod.snd source_454
  inc1_edge := congrArg Prod.snd source_455
  inc2_edge := congrArg Prod.snd source_456
  inc3_edge := congrArg Prod.snd source_457
  inc4_edge := congrArg Prod.snd source_458
  again_edge := congrArg Prod.snd source_459
  positive_target := cached_target source_454 source_455 incPath (by rfl) (by rfl)
  zero_target := cached_target source_454 source_460 (breakPath 1) (by rfl) (by rfl)
  next_inc1 := cached_target source_455 source_456 incPath (by rfl) (by rfl)
  next_inc2 := cached_target source_456 source_457 incPath (by rfl) (by rfl)
  next_inc3 := cached_target source_457 source_458 incPath (by rfl) (by rfl)
  next_inc4 := cached_target source_458 source_459 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_459 source_454 (continuePath 2) (by rfl) (by rfl)

/-- Every field is a literal edge/target equality or interface equality. -/
def occurrence : ConstructorShape where
  pop := impPop
  pair := impPair
  scale := impScale
  tag := 0
  exit := exit
  pop_main := rfl
  pop_to_pair := rfl
  pair_to_scale := rfl
  tag_steps := TagChain.nil exit

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Actual433→460 has the complete implication-constructor file effect. -/
theorem ax_constructor_run (file : V) (h1 : regValue file s1Reg = 0)
    (h2 : regValue file s2Reg = 0) :
    ∃ time : V, 1 ≤ time ∧ controlRun time (liveValue (number entry : V) file) =
      liveValue (number exit : V)
        (put twReg (wim (first (regValue file wsReg)) (regValue file twReg))
          (put wsReg (second (regValue file wsReg)) file)) := by
  simpa only [show occurrence.pop.readEntry = entry from rfl,
    show occurrence.exit = exit from rfl,
    show occurrence.tag = (0 : Fin 4) from rfl,
    constructorFile, Fin.val_zero, Nat.cast_zero, wim] using constructor_run occurrence file h1 h2

end Model
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXConstructor433254
