import LeftFrame
import BusyBeaver.ZFC.KTable215

/-!
Finite local replay data for the maintained K215 table. Every reduction below
is checked by Lean's kernel using decide; no external/native decision oracle.
The source-program binding is supplied separately by caller certificates.
-/
namespace SetTheory.BusyBeaver.ZFC.KFramedTemplates
open KZip KRuntimeCore KLeftFrame KTableCore

structure LocalTemplate where
  steps : Nat
  start : SConf
  returnState : Nat
  right : List Seg
  deriving DecidableEq, Repr, Inhabited

def checked (t : LocalTemplate) : Bool :=
  decide (runLocal tm215 none t.steps t.start =
    some ((t.returnState, true, [], t.right), true))

-- Input SHA-256: 6efe1b47a9387c107f6df5961e10f3843447f46c704b79cbaef68a99303e17c3
def template00 : LocalTemplate :=
  ⟨8, (62, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template01 : LocalTemplate :=
  ⟨6, (13, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template02 : LocalTemplate :=
  ⟨5, (108, false, [.bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template03 : LocalTemplate :=
  ⟨3, (42, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template04 : LocalTemplate :=
  ⟨5, (83, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template05 : LocalTemplate :=
  ⟨11, (138, false, [.bit true, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 2, [.bit true, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template06 : LocalTemplate :=
  ⟨3, (141, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template07 : LocalTemplate :=
  ⟨3, (57, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template08 : LocalTemplate :=
  ⟨19, (80, false, [.bit true, .bit true, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template09 : LocalTemplate :=
  ⟨6, (72, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template10 : LocalTemplate :=
  ⟨3, (126, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template11 : LocalTemplate :=
  ⟨3, (47, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template12 : LocalTemplate :=
  ⟨3, (139, false, [.bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template13 : LocalTemplate :=
  ⟨5, (108, false, [.bit false, .bit true], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template14 : LocalTemplate :=
  ⟨24, (103, false, [.bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 2, [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template15 : LocalTemplate :=
  ⟨1, (122, false, [], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 1, [.bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template16 : LocalTemplate :=
  ⟨39, (103, false, [.bit true, .bit true, .bit false, .bit true, .bit true, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 2, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template17 : LocalTemplate :=
  ⟨29, (103, false, [.bit true, .bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 2, [.bit true, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template18 : LocalTemplate :=
  ⟨39, (96, false, [.bit true, .bit true, .bit true, .bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 2, [.bit true, .bit false, .bit false, .bit false, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def template19 : LocalTemplate :=
  ⟨24, (162, false, [.bit true, .bit false, .bit false], [.bit true, .run false 1 16, .bit true, .box (.plain .none)]), 2, [.bit true, .bit false, .bit false, .bit false, .run false 1 16, .bit true, .box (.plain .none)]⟩

def templates : List LocalTemplate :=
  [template00, template01, template02, template03, template04, template05, template06, template07, template08, template09, template10, template11, template12, template13, template14, template15, template16, template17, template18, template19]

theorem template_count : templates.length = 20 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem all_checked : templates.all checked = true := by decide

theorem checked_of_mem {t : LocalTemplate} (ht : t ∈ templates) : checked t = true :=
  (List.all_eq_true.mp all_checked) t ht

theorem replay_of_checked {t : LocalTemplate} (h : checked t = true) :
    runLocal tm215 none t.steps t.start =
      some ((t.returnState, true, [], t.right), true) :=
  of_decide_eq_true h

theorem replay_of_mem {t : LocalTemplate} (ht : t ∈ templates) :
    runLocal tm215 none t.steps t.start =
      some ((t.returnState, true, [], t.right), true) :=
  replay_of_checked (checked_of_mem ht)

theorem template_sound {t : LocalTemplate} (ht : t ∈ templates)
    (B : BoxLemmas tm215) (hb : KHome.Boundary tm215)
    (n : Nat) {vs : List Nat} (hv : Valid none vs) (P : List Bool)
    (hword : wordEnd tm215 t.returnState (P.reverse ++ [true]) = some 2) :
    Reach1 tm215
      (conc n vs (addLeft ((P.reverse.map Seg.bit) ++ [.bit true]) t.start))
      (zc 84 [true] (P ++ flat n vs t.right)) :=
  runLocal_home_word B hb n hv P (wordEnd_sound hword) (replay_of_mem ht)

#print axioms all_checked
#print axioms replay_of_mem
#print axioms template_sound

end SetTheory.BusyBeaver.ZFC.KFramedTemplates
