import BusyBeaver.ZFC.KLeftFrame
import BusyBeaver.ZFC.KTable215

/-! Generated from the existing formal-label template data.
Input SHA-256: e2b8fd178afba6c85edf17eb647751d90a606541f03b01b76ec309acfdd62238
Every local replay is checked by ordinary `decide` below.
The input generator and JSON are not trusted. -/

namespace SetTheory.BusyBeaver.ZFC.KLeftFrame215
open KZip KRuntimeCore KLeftFrame KTableCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

structure Template where
  start : SConf
  steps : Nat
  right : List Seg

def templates : List Template := [
  -- Template 0: CC 3, suffix 10111.
  ⟨(62, false, [.bit true, .bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 12, [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 1: CC 2, suffix 111.
  ⟨(13, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 8, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 2: CB 1, suffix 1001.
  ⟨(108, false, [.bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 7, [.bit true, .bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 3: CC 2, suffix 111.
  ⟨(42, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 5, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 4: CC 2, suffix 111.
  ⟨(138, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 11, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 5: CC 2, suffix 111.
  ⟨(141, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 5, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 6: CC 2, suffix 10000011.
  ⟨(42, false, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 15, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 7: CC 2, suffix 1011.
  ⟨(57, false, [.bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 7, [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 8: CC 3, suffix 100111.
  ⟨(62, false, [.bit true, .bit true, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 14, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 9: CC 2, suffix 111.
  ⟨(57, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 5, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 10: CC 3, suffix 10111.
  ⟨(80, false, [.bit true, .bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 21, [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 11: CC 2, suffix 111.
  ⟨(72, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 8, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 12: CC 2, suffix 111.
  ⟨(126, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 5, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 13: CC 2, suffix 10011.
  ⟨(42, false, [.bit true, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 9, [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 14: CC 2, suffix 111.
  ⟨(47, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 5, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 15: CC 3, suffix 1000111.
  ⟨(83, false, [.bit true, .bit true, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 13, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 16: CC 2, suffix 111.
  ⟨(139, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 5, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 17: CC 2, suffix 1000011.
  ⟨(42, false, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 13, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 18: CC 3, suffix 100000111.
  ⟨(83, false, [.bit true, .bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 17, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 19: CC 3, suffix 10000111.
  ⟨(83, false, [.bit true, .bit true, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 15, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 20: CC 2, suffix 1011.
  ⟨(126, false, [.bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 7, [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 21: CC 3, suffix 100111.
  ⟨(83, false, [.bit true, .bit true, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 11, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 22: CC 2, suffix 100011.
  ⟨(42, false, [.bit true, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 11, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 23: CC 3, suffix 1111.
  ⟨(62, false, [.bit true, .bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 10, [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 24: CC 2, suffix 1000101.
  ⟨(108, false, [.bit false, .bit true, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 13, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 25: CB 1, suffix 0011.
  ⟨(103, false, [.bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 24, [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 26: CC 1, suffix 101.
  ⟨(122, false, [.bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 5, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 27: CC 2, suffix 1101.
  ⟨(108, false, [.bit false, .bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 7, [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 28: CB 1, suffix 0110111.
  ⟨(103, false, [.bit true, .bit true, .bit false, .bit true, .bit true, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 39, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 29: CC 1, suffix 11.
  ⟨(122, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 3, [.bit true, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 30: CC 2, suffix 1011.
  ⟨(42, false, [.bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 7, [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 31: CC 2, suffix 10000101.
  ⟨(108, false, [.bit false, .bit true, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 15, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 32: CB 1, suffix 00111.
  ⟨(103, false, [.bit true, .bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 29, [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 33: CB 1, suffix 0011111.
  ⟨(96, false, [.bit true, .bit true, .bit true, .bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 39, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩,
  -- Template 34: CB 1, suffix 0011.
  ⟨(162, false, [.bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 24, [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩]

def checked (t : Template) : Bool :=
  decide (runLocal tm215 none t.steps t.start = some (2, true, [], t.right))

theorem template_count : templates.length = 35 := by decide

theorem all_checked : templates.all checked = true := by decide

/-- Each literal template applies to every symbolic left frame. -/
theorem template_reach (B : BoxLemmas tm215) {t : Template}
    (ht : t ∈ templates) (F : List Seg) (n : Nat) {vs : List Nat}
    (hv : Valid none vs) :
    Reach tm215 (conc n vs (addLeft F t.start))
      (conc n vs (addLeft F (2, true, [], t.right))) := by
  have hc := of_decide_eq_true (List.all_eq_true.mp all_checked t ht)
  exact runLocal_sound B n hv F t.steps t.start _ hc

/-- A whole-tape contract for every caller prefix accepted by Home.
The existing engine contracts provide B, rows and hb at the endpoint. -/
theorem template_home (B : BoxLemmas tm215) (rows : KHome.Rows tm215)
    (hb : KHome.Boundary tm215) {t : Template} (ht : t ∈ templates)
    (P : List Bool) {k : Nat}
    (hp : KHome.scanBound 0 (P.reverse.map Seg.bit) = some k)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    Reach1 tm215 (conc n vs (addLeft (P.reverse.map Seg.bit ++ [.bit true]) t.start))
      (zc 84 [true] (P ++ flat n vs t.right)) := by
  have hc := of_decide_eq_true (List.all_eq_true.mp all_checked t ht)
  exact local_home B rows hb hc P hp n hv

#print axioms all_checked
#print axioms template_reach
#print axioms template_home

end SetTheory.BusyBeaver.ZFC.KLeftFrame215
