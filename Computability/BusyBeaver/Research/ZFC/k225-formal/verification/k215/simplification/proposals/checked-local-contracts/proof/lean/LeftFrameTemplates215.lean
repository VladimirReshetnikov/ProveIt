import LeftFrameContract
import BusyBeaver.ZFC.KTable215

/-!
Kernel equations for the 35 inherited round13 local templates.
The source data already uses the maintained table's labels (301 -> 102,
302 -> 120, halt 254 -> 230). No native-table trace is accepted on trust.
This generated file checks runLocal directly against KTableCore.tm215.
Attribution: round13-left-frame/runtime/FORMAL_TEMPLATES.json.
Input SHA-256: e2b8fd178afba6c85edf17eb647751d90a606541f03b01b76ec309acfdd62238
-/

namespace SetTheory.BusyBeaver.ZFC.KLeftFrame215
open KZip KRuntimeCore KLeftFrame KTableCore

structure LocalTemplate where
  id : Nat
  steps : Nat
  start : SConf
  right : List Seg
  suffix : List Bool
  isContinue : Bool
  controlArg : Nat
  result : List Bool
  deriving DecidableEq, Repr

def templates : List LocalTemplate := [
  ⟨0, 12, (62, false, [.bit true, .bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, true, true, true], true, 3, [true, false]⟩,
  ⟨1, 8, (13, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, true], true, 2, [true]⟩,
  ⟨2, 7, (108, false, [.bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, true], false, 1, [true, true]⟩,
  ⟨3, 5, (42, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, true], true, 2, [true]⟩,
  ⟨4, 11, (138, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, true], true, 2, [true]⟩,
  ⟨5, 5, (141, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, true], true, 2, [true]⟩,
  ⟨6, 15, (42, false, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, false, false, false, true, true], true, 2, [true, false, false, false, false, false]⟩,
  ⟨7, 7, (57, false, [.bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, true, true], true, 2, [true, false]⟩,
  ⟨8, 14, (62, false, [.bit true, .bit true, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, true, true, true], true, 3, [true, false, false]⟩,
  ⟨9, 5, (57, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, true], true, 2, [true]⟩,
  ⟨10, 21, (80, false, [.bit true, .bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, true, true, true], true, 3, [true, false]⟩,
  ⟨11, 8, (72, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, true], true, 2, [true]⟩,
  ⟨12, 5, (126, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, true], true, 2, [true]⟩,
  ⟨13, 9, (42, false, [.bit true, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, true, true], true, 2, [true, false, false]⟩,
  ⟨14, 5, (47, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, true], true, 2, [true]⟩,
  ⟨15, 13, (83, false, [.bit true, .bit true, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, false, true, true, true], true, 3, [true, false, false, false]⟩,
  ⟨16, 5, (139, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, true], true, 2, [true]⟩,
  ⟨17, 13, (42, false, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, false, false, true, true], true, 2, [true, false, false, false, false]⟩,
  ⟨18, 17, (83, false, [.bit true, .bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, false, false, false, true, true, true], true, 3, [true, false, false, false, false, false]⟩,
  ⟨19, 15, (83, false, [.bit true, .bit true, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, false, false, true, true, true], true, 3, [true, false, false, false, false]⟩,
  ⟨20, 7, (126, false, [.bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, true, true], true, 2, [true, false]⟩,
  ⟨21, 11, (83, false, [.bit true, .bit true, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, true, true, true], true, 3, [true, false, false]⟩,
  ⟨22, 11, (42, false, [.bit true, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, false, true, true], true, 2, [true, false, false, false]⟩,
  ⟨23, 10, (62, false, [.bit true, .bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, true, true], true, 3, [true]⟩,
  ⟨24, 13, (108, false, [.bit false, .bit true, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, false, true, false, true], true, 2, [true, false, false, false]⟩,
  ⟨25, 24, (103, false, [.bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [false, false, true, true], false, 1, [true]⟩,
  ⟨26, 5, (122, false, [.bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, true], true, 1, [true, false]⟩,
  ⟨27, 7, (108, false, [.bit false, .bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true, false, true], true, 2, [true]⟩,
  ⟨28, 39, (103, false, [.bit true, .bit true, .bit false, .bit true, .bit true, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [false, true, true, false, true, true, true], false, 1, [true, false, false]⟩,
  ⟨29, 3, (122, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, true], true, 1, [true]⟩,
  ⟨30, 7, (42, false, [.bit true, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, true, true], true, 2, [true, false]⟩,
  ⟨31, 15, (108, false, [.bit false, .bit true, .bit false, .bit false, .bit false, .bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [true, false, false, false, false, true, false, true], true, 2, [true, false, false, false, false]⟩,
  ⟨32, 29, (103, false, [.bit true, .bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [false, false, true, true, true], false, 1, [true]⟩,
  ⟨33, 39, (96, false, [.bit true, .bit true, .bit true, .bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [false, false, true, true, true, true, true], false, 1, [true]⟩,
  ⟨34, 24, (162, false, [.bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)], [false, false, true, true], false, 1, [true]⟩
]

def checkTemplate (t : LocalTemplate) : Bool :=
  runLocal tm215 none t.steps t.start == some (2, true, [], t.right)

theorem counts : templates.length = 35 ∧ (templates.map LocalTemplate.steps).sum = 444 ∧
    templates.map LocalTemplate.id = List.range 35 := by
  decide +kernel

theorem all_checked : templates.all checkTemplate = true := by
  decide +kernel

theorem template_checked {t : LocalTemplate} (ht : t ∈ templates) :
    runLocal tm215 none t.steps t.start = some (2, true, [], t.right) := by
  have h : checkTemplate t = true := List.all_eq_true.mp all_checked t ht
  simpa only [checkTemplate, beq_iff_eq] using h

/-- One checked local run serves every admissible prefix, gap and register file.
The premises are the unchanged runtime boxes and Home contracts. -/
theorem every_template_sound (B : BoxLemmas tm215)
    (rows : KHome.Rows tm215) (hb : KHome.Boundary tm215)
    {t : LocalTemplate} (ht : t ∈ templates)
    (P : List Bool) {j : Nat}
    (hs : KHome.scanBound 0 (P.reverse.map Seg.bit) = some j)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) :
    Reach1 tm215
      (conc n vs (addLeft (P.reverse.map .bit ++ [.bit true]) t.start))
      (zc 84 [true] (P ++ flat n vs t.right)) :=
  local_home_sound B rows hb n hv P hs (template_checked ht)

#print axioms counts
#print axioms all_checked
#print axioms template_checked
#print axioms every_template_sound
end SetTheory.BusyBeaver.ZFC.KLeftFrame215
