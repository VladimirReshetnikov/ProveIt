import BusyBeaver.ZFC.RegisterPath

/-! The control actions of the same 35 inherited templates preserve any left
prefix. These equalities are about exact full paths, not only a suffix. -/
namespace SetTheory.BusyBeaver.ZFC.KLeftFramePaths215
open RegisterPath

structure Action where
  templateId : Nat
  isContinue : Bool
  levels : Nat
  suffix : List Bool
  result : List Bool

def actions : List Action := [
  ⟨0, true, 3, [true, false, true, true, true], [true, false]⟩,
  ⟨1, true, 2, [true, true, true], [true]⟩,
  ⟨2, false, 1, [true, false, false, true], [true, true]⟩,
  ⟨3, true, 2, [true, true, true], [true]⟩,
  ⟨4, true, 2, [true, true, true], [true]⟩,
  ⟨5, true, 2, [true, true, true], [true]⟩,
  ⟨6, true, 2, [true, false, false, false, false, false, true, true], [true, false, false, false, false, false]⟩,
  ⟨7, true, 2, [true, false, true, true], [true, false]⟩,
  ⟨8, true, 3, [true, false, false, true, true, true], [true, false, false]⟩,
  ⟨9, true, 2, [true, true, true], [true]⟩,
  ⟨10, true, 3, [true, false, true, true, true], [true, false]⟩,
  ⟨11, true, 2, [true, true, true], [true]⟩,
  ⟨12, true, 2, [true, true, true], [true]⟩,
  ⟨13, true, 2, [true, false, false, true, true], [true, false, false]⟩,
  ⟨14, true, 2, [true, true, true], [true]⟩,
  ⟨15, true, 3, [true, false, false, false, true, true, true], [true, false, false, false]⟩,
  ⟨16, true, 2, [true, true, true], [true]⟩,
  ⟨17, true, 2, [true, false, false, false, false, true, true], [true, false, false, false, false]⟩,
  ⟨18, true, 3, [true, false, false, false, false, false, true, true, true], [true, false, false, false, false, false]⟩,
  ⟨19, true, 3, [true, false, false, false, false, true, true, true], [true, false, false, false, false]⟩,
  ⟨20, true, 2, [true, false, true, true], [true, false]⟩,
  ⟨21, true, 3, [true, false, false, true, true, true], [true, false, false]⟩,
  ⟨22, true, 2, [true, false, false, false, true, true], [true, false, false, false]⟩,
  ⟨23, true, 3, [true, true, true, true], [true]⟩,
  ⟨24, true, 2, [true, false, false, false, true, false, true], [true, false, false, false]⟩,
  ⟨25, false, 1, [false, false, true, true], [true]⟩,
  ⟨26, true, 1, [true, false, true], [true, false]⟩,
  ⟨27, true, 2, [true, true, false, true], [true]⟩,
  ⟨28, false, 1, [false, true, true, false, true, true, true], [true, false, false]⟩,
  ⟨29, true, 1, [true, true], [true]⟩,
  ⟨30, true, 2, [true, false, true, true], [true, false]⟩,
  ⟨31, true, 2, [true, false, false, false, false, true, false, true], [true, false, false, false, false]⟩,
  ⟨32, false, 1, [false, false, true, true, true], [true]⟩,
  ⟨33, false, 1, [false, false, true, true, true, true, true], [true]⟩,
  ⟨34, false, 1, [false, false, true, true], [true]⟩
]

def applyAction (a : Action) (word : List Bool) : List Bool :=
  if a.isContinue then continuePath a.levels word else breakPath a.levels word

theorem action_count : actions.length = 35 := rfl

theorem prefix_action {a : Action} (ha : a ∈ actions) (P : List Bool) :
    applyAction a (P ++ a.suffix) = P ++ a.result := by
  simp only [actions, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [applyAction, continuePath, breakPath, stripPath, incPath,
    List.reverse_append, List.reverse_cons, stripRev, incRev, List.append_assoc]

end SetTheory.BusyBeaver.ZFC.KLeftFramePaths215

#print axioms SetTheory.BusyBeaver.ZFC.KLeftFramePaths215.prefix_action
