import BusyBeaver.ZFC.KLeftFrame
import BusyBeaver.ZFC.KTable215
import BusyBeaver.ZFC.KTape
import BusyBeaver.ZFC.KHomeReady

/-! Concrete kernel checks for the inherited 35 round13-left-frame bodies.
    This is template validity, not all-leaf source coverage. -/
namespace SetTheory.BusyBeaver.ZFC.KLeftFrame215
open KZip KRuntimeCore KTableCore KLeftFrame

set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Template where
  steps : Nat
  entry : SConf
  exitRight : List Seg

def templates : List Template := [
  -- Template 0: CC 3, suffix 10111
  ⟨12, (62, false, [.bit true, .bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 1: CC 2, suffix 111
  ⟨8, (13, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 2: CB 1, suffix 1001
  ⟨7, (108, false, [.bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 3: CC 2, suffix 111
  ⟨5, (42, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 4: CC 2, suffix 111
  ⟨11, (138, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 5: CC 2, suffix 111
  ⟨5, (141, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 6: CC 2, suffix 10000011
  ⟨15, (42, false, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 7: CC 2, suffix 1011
  ⟨7, (57, false, [.bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 8: CC 3, suffix 100111
  ⟨14, (62, false, [.bit true, .bit true, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 9: CC 2, suffix 111
  ⟨5, (57, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 10: CC 3, suffix 10111
  ⟨21, (80, false, [.bit true, .bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 11: CC 2, suffix 111
  ⟨8, (72, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 12: CC 2, suffix 111
  ⟨5, (126, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 13: CC 2, suffix 10011
  ⟨9, (42, false, [.bit true, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 14: CC 2, suffix 111
  ⟨5, (47, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 15: CC 3, suffix 1000111
  ⟨13, (83, false, [.bit true, .bit true, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 16: CC 2, suffix 111
  ⟨5, (139, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 17: CC 2, suffix 1000011
  ⟨13, (42, false, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 18: CC 3, suffix 100000111
  ⟨17, (83, false, [.bit true, .bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 19: CC 3, suffix 10000111
  ⟨15, (83, false, [.bit true, .bit true, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 20: CC 2, suffix 1011
  ⟨7, (126, false, [.bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 21: CC 3, suffix 100111
  ⟨11, (83, false, [.bit true, .bit true, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 22: CC 2, suffix 100011
  ⟨11, (42, false, [.bit true, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 23: CC 3, suffix 1111
  ⟨10, (62, false, [.bit true, .bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 24: CC 2, suffix 1000101
  ⟨13, (108, false, [.bit false, .bit true, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 25: CB 1, suffix 0011
  ⟨24, (103, false, [.bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 26: CC 1, suffix 101
  ⟨5, (122, false, [.bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 27: CC 2, suffix 1101
  ⟨7, (108, false, [.bit false, .bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 28: CB 1, suffix 0110111
  ⟨39, (103, false, [.bit true, .bit true, .bit false, .bit true, .bit true, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 29: CC 1, suffix 11
  ⟨3, (122, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 30: CC 2, suffix 1011
  ⟨7, (42, false, [.bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 31: CC 2, suffix 10000101
  ⟨15, (108, false, [.bit false, .bit true, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 32: CB 1, suffix 00111
  ⟨29, (103, false, [.bit true, .bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 33: CB 1, suffix 0011111
  ⟨39, (96, false, [.bit true, .bit true, .bit true, .bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 34: CB 1, suffix 0011
  ⟨24, (162, false, [.bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩
]

def checked (t : Template) : Bool :=
  decide (runLocal tm215 none t.steps t.entry = some (2, true, [], t.exitRight))

theorem template_count : templates.length = 35 := rfl

theorem all_checked : templates.all checked = true := by decide +kernel

theorem local_of_mem {t : Template} (ht : t ∈ templates) :
    runLocal tm215 none t.steps t.entry = some (2, true, [], t.exitRight) := by
  have h := List.all_eq_true.mp all_checked t ht
  exact of_decide_eq_true h

theorem boxes : BoxLemmas tm215 := KTape.boxLemmas (by decide) (.inr rfl)

theorem home_ready : KHomeReady.ready tm215 = true := by decide +kernel

/-- Every listed body works for every gap, every valid register list, and
every finite preserved prefix accepted by the existing Home guard. -/
theorem template_prefix {t : Template} (ht : t ∈ templates)
    (P : List Bool) (n : Nat) {vs : List Nat} (hv : Valid none vs)
    {j : Nat} (hscan : KHome.scanBound 0 (P.reverse.map Seg.bit) = some j) :
    Reach1 tm215 (conc n vs (addLeft (P.reverse.map Seg.bit ++ [.bit true]) t.entry))
      (conc n vs (84, false, [.bit true], P.map Seg.bit ++ t.exitRight)) :=
  local_prefix_sound boxes (KHomeReady.ready_sound home_ready).1
    (KHomeReady.ready_sound home_ready).2 n hv P (local_of_mem ht) hscan

end SetTheory.BusyBeaver.ZFC.KLeftFrame215

#print axioms SetTheory.BusyBeaver.ZFC.KLeftFrame215.all_checked
#print axioms SetTheory.BusyBeaver.ZFC.KLeftFrame215.template_prefix
