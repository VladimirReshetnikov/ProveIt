import BusyBeaver.ZFC.ArithmeticControlConstructor254
import BusyBeaver.ZFC.ArithmeticControlSourceRank254

set_option autoImplicit false
noncomputable section

/-!
Actual AX implication constructor at controls406→433. All 27 instruction edges
and 35 successor branches reuse cached full equalities for the existing catalogue.
The generic constructor contract supplies the unbounded internal execution.
This occurrence is the constructor immediately after the AC push.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextConstructor254
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

/-- The next actual AX implication constructor starts at control406. -/
def entry : Control := ⟨406, by decide⟩
/-- Its zero-tag exit is the next constructor, at control433. -/
def exit : Control := ⟨433, by decide⟩

private def c407 : Control := ⟨407, by decide⟩
private def c408 : Control := ⟨408, by decide⟩
private def c409 : Control := ⟨409, by decide⟩
private def c410 : Control := ⟨410, by decide⟩
private def c411 : Control := ⟨411, by decide⟩
private def c412 : Control := ⟨412, by decide⟩
private def c413 : Control := ⟨413, by decide⟩
private def c414 : Control := ⟨414, by decide⟩
private def c415 : Control := ⟨415, by decide⟩
private def c416 : Control := ⟨416, by decide⟩
private def c417 : Control := ⟨417, by decide⟩
private def c418 : Control := ⟨418, by decide⟩
private def c419 : Control := ⟨419, by decide⟩
private def c420 : Control := ⟨420, by decide⟩
private def c421 : Control := ⟨421, by decide⟩
private def c422 : Control := ⟨422, by decide⟩
private def c423 : Control := ⟨423, by decide⟩
private def c424 : Control := ⟨424, by decide⟩
private def c425 : Control := ⟨425, by decide⟩
private def c426 : Control := ⟨426, by decide⟩
private def c427 : Control := ⟨427, by decide⟩
private def c428 : Control := ⟨428, by decide⟩
private def c429 : Control := ⟨429, by decide⟩
private def c430 : Control := ⟨430, by decide⟩
private def c431 : Control := ⟨431, by decide⟩
private def c432 : Control := ⟨432, by decide⟩

/-- Cache each complete catalogue equality before checking finite paths. -/
private theorem source_406 :
    source entry =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, false, false], .decnz 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 396) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 382) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 368) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 367) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 366) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 365) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 284) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 131) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 52) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_407 :
    source c407 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, false, true, false], .inc 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 397) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 383) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 369) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 368) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 367) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 366) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 285) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 132) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 53) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_408 :
    source c408 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, false], .decnz 6) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 398) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 384) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 370) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 369) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 368) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 367) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 286) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 133) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 54) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_409 :
    source c409 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, false, true, true, false, false, true], .brk 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 399) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 385) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 371) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 370) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 369) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 368) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 287) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 134) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 55) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_410 :
    source c410 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, false], .decnz 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 400) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 386) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 372) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 371) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 370) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 369) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 288) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 135) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 56) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 2) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_411 :
    source c411 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, false], .inc 6) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 401) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 387) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 373) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 372) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 371) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 370) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 289) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 136) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 57) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 2) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_412 :
    source c412 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, false, true, true, false, true, true, true], .cont 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 402) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 388) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 374) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 373) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 372) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 371) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 290) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 137) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 58) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 6) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 2) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_413 :
    source c413 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, false, true, true, true], .cont 3) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 403) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 389) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 375) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 374) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 373) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 372) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 291) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 138) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 59) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 7) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 6) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 5) (i := 0) (by rfl)
  exact .here _

private theorem source_414 :
    source c414 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, true, false], .decnz 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 404) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 390) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 376) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 375) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 374) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 373) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 292) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 139) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 60) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 8) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 8) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_415 :
    source c415 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, true, true, false], .inc 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 405) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 391) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 377) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 376) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 375) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 374) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 293) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 140) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 61) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 9) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 8) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_416 :
    source c416 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, false, true, true, true], .cont 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 406) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 392) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 378) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 377) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 376) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 375) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 294) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 141) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 62) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 10) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 8) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_417 :
    source c417 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, false, false, false], .decnz 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 407) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 393) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 379) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 378) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 377) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 376) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 295) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 142) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 63) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 11) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_418 :
    source c418 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, false, false, true, false], .inc 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 408) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 394) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 380) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 379) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 378) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 377) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 296) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 143) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 64) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 12) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_419 :
    source c419 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, false, false, true, true, false], .inc 6) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 409) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 395) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 381) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 380) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 379) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 378) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 297) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 144) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 65) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 13) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_420 :
    source c420 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, false, false, true, true, true], .cont 3) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 410) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 396) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 382) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 381) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 380) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 379) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 298) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 145) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 66) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 14) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_421 :
    source c421 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, false, true, false], .decnz 6) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 411) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 397) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 383) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 382) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 381) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 380) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 299) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 146) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 67) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 15) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_422 :
    source c422 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, false, true, true, false, false], .inc 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 412) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 398) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 384) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 383) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 382) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 381) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 300) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 147) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 68) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 16) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_423 :
    source c423 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, false], .decnz 6) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 413) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 399) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 385) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 384) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 383) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 382) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 301) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 148) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 69) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 17) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 6) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_424 :
    source c424 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, false], .inc 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 414) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 400) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 386) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 385) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 384) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 383) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 302) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 149) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 70) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 18) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 7) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_425 :
    source c425 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, false, true, true, false, true, true, true], .cont 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 415) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 401) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 387) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 386) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 385) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 384) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 303) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 150) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 71) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 19) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 8) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_426 :
    source c426 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, false, true, true, true], .cont 3) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 416) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 402) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 388) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 387) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 386) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 385) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 304) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 151) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 72) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 20) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 9) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 0) (by rfl)
  exact .here _

private theorem source_427 :
    source c427 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, true, false], .decnz 7) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 417) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 403) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 389) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 388) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 387) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 386) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 305) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 152) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 73) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 21) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 10) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_428 :
    source c428 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, true, true, false, false, false], .inc 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 418) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 404) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 390) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 389) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 388) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 387) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 306) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 153) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 74) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 22) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 11) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_429 :
    source c429 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, true, true, false, false, true], .inc 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 419) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 405) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 391) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 390) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 389) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 388) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 307) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 154) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 75) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 23) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 12) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_430 :
    source c430 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, true, true, false, true, false], .inc 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 420) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 406) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 392) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 391) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 390) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 389) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 308) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 155) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 76) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 24) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 13) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 2) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 2) (i := 0) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  exact .here _

private theorem source_431 :
    source c431 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, true, true, false, true, true], .inc 1) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 421) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 407) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 393) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 392) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 391) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 390) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 309) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 156) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 77) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 25) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 14) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 3) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 2) (i := 1) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 0) (by rfl)
  exact .here _

private theorem source_432 :
    source c432 =
      ([true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false, true, true, true, true], .cont 2) := by
  apply ArithmeticControlSourceRank254.source_of_atRank
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 422) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 408) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 14) (i := 394) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 393) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 392) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 391) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 81) (i := 310) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 153) (i := 157) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 79) (i := 78) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 52) (i := 26) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.left
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 11) (i := 15) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 10) (i := 5) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 1) (i := 4) (by rfl)
  apply ArithmeticControlSourceRank254.AtRank.right_count (n := 4) (i := 0) (by rfl)
  exact .here _

private theorem source_433 :
    source exit =
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

theorem entry_source : (source entry).2 = .decnz 2 := congrArg Prod.snd source_406
theorem exit_source : (source exit).2 = .decnz 2 := congrArg Prod.snd source_433

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
  bodyIncS2 := c407
  bodyTestS1 := c408
  bodyBreak := c409
  bodyMoveTest := c410
  bodyMoveInc := c411
  bodyMoveContinue := c412
  bodyContinue := c413
  restoreMainTest := c414
  restoreMainInc := c415
  restoreMainContinue := c416
  exit := c417
  mainLogical := 2
  mainIndex := wsReg
  main_physical := rfl
  main_ne_s1 := by decide
  main_ne_s2 := by decide
  read_edge := congrArg Prod.snd source_406
  body_inc_edge := congrArg Prod.snd source_407
  body_test_edge := congrArg Prod.snd source_408
  body_break_edge := congrArg Prod.snd source_409
  body_move_test_edge := congrArg Prod.snd source_410
  body_move_inc_edge := congrArg Prod.snd source_411
  body_move_continue_edge := congrArg Prod.snd source_412
  body_continue_edge := congrArg Prod.snd source_413
  restore_test_edge := congrArg Prod.snd source_414
  restore_inc_edge := congrArg Prod.snd source_415
  restore_continue_edge := congrArg Prod.snd source_416
  next_read_positive := cached_target source_406 source_407 incPath (by rfl) (by rfl)
  next_read_zero := cached_target source_406 source_414 (breakPath 1) (by rfl) (by rfl)
  next_body_inc := cached_target source_407 source_408 incPath (by rfl) (by rfl)
  next_body_test_positive := cached_target source_408 source_409 incPath (by rfl) (by rfl)
  next_body_test_zero := cached_target source_408 source_410 (breakPath 1) (by rfl) (by rfl)
  next_body_break := cached_target source_409 source_413 (breakPath 1) (by rfl) (by rfl)
  next_body_move_positive := cached_target source_410 source_411 incPath (by rfl) (by rfl)
  next_body_move_inc := cached_target source_411 source_412 incPath (by rfl) (by rfl)
  next_body_move_continue := cached_target source_412 source_410 (continuePath 2) (by rfl) (by rfl)
  next_body_move_zero := cached_target source_410 source_413 (breakPath 1) (by rfl) (by rfl)
  next_body_continue := cached_target source_413 source_406 (continuePath 3) (by rfl) (by rfl)
  next_restore_main_positive := cached_target source_414 source_415 incPath (by rfl) (by rfl)
  next_restore_main_inc := cached_target source_415 source_416 incPath (by rfl) (by rfl)
  next_restore_main_continue := cached_target source_416 source_414 (continuePath 2) (by rfl) (by rfl)
  next_restore_main_zero := cached_target source_414 source_417 (breakPath 1) (by rfl) (by rfl)

private def impCopy : CopyShape where
  test := c417
  firstInc := c418
  secondInc := c419
  again := c420
  exit := c421
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
  test_edge := congrArg Prod.snd source_417
  first_edge := congrArg Prod.snd source_418
  second_edge := congrArg Prod.snd source_419
  again_edge := congrArg Prod.snd source_420
  positive_target := cached_target source_417 source_418 incPath (by rfl) (by rfl)
  first_target := cached_target source_418 source_419 incPath (by rfl) (by rfl)
  second_target := cached_target source_419 source_420 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_420 source_417 (continuePath 3) (by rfl) (by rfl)
  zero_target := cached_target source_417 source_421 (breakPath 1) (by rfl) (by rfl)

private def impMove : MoveShape where
  test := c423
  increment := c424
  again := c425
  exit := c426
  sourceLogical := 6
  targetLogical := 1
  sourceIndex := s1Reg
  targetIndex := twReg
  source_physical := rfl
  target_physical := rfl
  distinct := by decide
  test_edge := congrArg Prod.snd source_423
  increment_edge := congrArg Prod.snd source_424
  again_edge := congrArg Prod.snd source_425
  positive_target := cached_target source_423 source_424 incPath (by rfl) (by rfl)
  increment_target := cached_target source_424 source_425 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_425 source_423 (continuePath 2) (by rfl) (by rfl)
  zero_target := cached_target source_423 source_426 (breakPath 1) (by rfl) (by rfl)

private def impPair : PairShape where
  copy := impCopy
  testS1 := c421
  incS2 := c422
  move := impMove
  again := c426
  exit := c427
  copy_source := by rfl
  copy_first := by rfl
  copy_second := by rfl
  copy_exit := by rfl
  move_source := by rfl
  move_target := by rfl
  move_exit := by rfl
  test_edge := congrArg Prod.snd source_421
  increment_edge := congrArg Prod.snd source_422
  again_edge := congrArg Prod.snd source_426
  positive_target := cached_target source_421 source_422 incPath (by rfl) (by rfl)
  zero_target := cached_target source_421 source_427 (breakPath 1) (by rfl) (by rfl)
  increment_target := cached_target source_422 source_423 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_426 source_417 (continuePath 3) (by rfl) (by rfl)

private def impScale : Scale4Shape where
  test := c427
  inc1 := c428
  inc2 := c429
  inc3 := c430
  inc4 := c431
  again := c432
  exit := exit
  test_edge := congrArg Prod.snd source_427
  inc1_edge := congrArg Prod.snd source_428
  inc2_edge := congrArg Prod.snd source_429
  inc3_edge := congrArg Prod.snd source_430
  inc4_edge := congrArg Prod.snd source_431
  again_edge := congrArg Prod.snd source_432
  positive_target := cached_target source_427 source_428 incPath (by rfl) (by rfl)
  zero_target := cached_target source_427 source_433 (breakPath 1) (by rfl) (by rfl)
  next_inc1 := cached_target source_428 source_429 incPath (by rfl) (by rfl)
  next_inc2 := cached_target source_429 source_430 incPath (by rfl) (by rfl)
  next_inc3 := cached_target source_430 source_431 incPath (by rfl) (by rfl)
  next_inc4 := cached_target source_431 source_432 incPath (by rfl) (by rfl)
  repeat_target := cached_target source_432 source_427 (continuePath 2) (by rfl) (by rfl)

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

/-- Actual406→433 has the complete implication-constructor file effect. -/
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
end SetTheory.BusyBeaver.ZFC.ArithmeticControlAXNextConstructor254
