import BusyBeaver.ZFC.TablePrefix246

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

#print axioms SetTheory.BusyBeaver.ZFC.rawTablePrefix246_size
#print axioms SetTheory.BusyBeaver.ZFC.rawTablePrefix246_transition_count
#print axioms SetTheory.BusyBeaver.ZFC.rawTablePrefix246_targets_bounded
#print axioms SetTheory.BusyBeaver.ZFC.rawTablePrefix246_halt_edge_count
#print axioms SetTheory.BusyBeaver.ZFC.rawActionPrefix246_target_bounded
#print axioms SetTheory.BusyBeaver.ZFC.oldLabelsPrefix246_size
#print axioms SetTheory.BusyBeaver.ZFC.oldStatePrefix246_oldLabel
#print axioms SetTheory.BusyBeaver.ZFC.oldLabelPrefix246_injective
#print axioms SetTheory.BusyBeaver.ZFC.startPrefix246_old95
#print axioms SetTheory.BusyBeaver.ZFC.dispatchPrefix246_eq
#print axioms SetTheory.BusyBeaver.ZFC.machinePrefix246_initial_action
#print axioms SetTheory.BusyBeaver.ZFC.machinePrefix246_halt_action
#print axioms SetTheory.BusyBeaver.ZFC.machinePrefix246_halt_iff
#print axioms SetTheory.BusyBeaver.ZFC.machinePrefix246_into_old109_iff
#print axioms SetTheory.BusyBeaver.ZFC.machinePrefix246_into_old255_iff
#print axioms SetTheory.BusyBeaver.ZFC.oldStatePrefix246_95
#print axioms SetTheory.BusyBeaver.ZFC.oldStatePrefix246_83_ne_95
#print axioms SetTheory.BusyBeaver.ZFC.oldStatePrefix246_83_ne_255
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old75_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old75_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old255_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old255_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old60_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old60_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old112_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old131_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old73_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old73_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old83_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old83_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old95_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old95_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old109_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old109_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old112_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old131_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old48_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old48_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old63_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old63_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old20_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old20_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old2_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old2_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old4_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old4_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix246_old6_true

example : rawTablePrefix246.size = 246 := rawTablePrefix246_size

example :
    (rawTablePrefix246.toList.flatMap (fun row => [row.1, row.2])).length = 492 := rawTablePrefix246_transition_count

example :
    rawTablePrefix246.toList.all (fun row =>
      decide (row.1.2.2 ≤ 246 ∧ row.2.2.2 ≤ 246)) = true := rawTablePrefix246_targets_bounded

example :
    ((rawTablePrefix246.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 246)).length = 1 := rawTablePrefix246_halt_edge_count

example : ∀ (q : Fin 246) (b : Bool),
    (rawActionPrefix246 q b).2.2 ≤ 246 := rawActionPrefix246_target_bounded

example : oldLabelsPrefix246.size = 246 := oldLabelsPrefix246_size

example : ∀ q : Fin 246,
    oldStatePrefix246 (oldLabelPrefix246 q) = q := oldStatePrefix246_oldLabel

example {q r : Fin 246}
    (h : oldLabelPrefix246 q = oldLabelPrefix246 r) : q = r := oldLabelPrefix246_injective h

example : startPrefix246 = oldStatePrefix246 95 := startPrefix246_old95

example : dispatchPrefix246 = 88 := dispatchPrefix246_eq

example :
    machinePrefix246.transition startPrefix246 false =
      ⟨true, .right, some (oldStatePrefix246 109)⟩ := machinePrefix246_initial_action

example :
    machinePrefix246.transition (oldStatePrefix246 77) true =
      ⟨true, .right, none⟩ := machinePrefix246_halt_action

example : ∀ (q : Fin 246) (b : Bool),
    (machinePrefix246.transition q b).next = none ↔
      q = oldStatePrefix246 77 ∧ b = true := machinePrefix246_halt_iff

example : ∀ (q : Fin 246) (b : Bool),
    (machinePrefix246.transition q b).next = some (oldStatePrefix246 109) ↔
      q = oldStatePrefix246 95 ∧ b = false := machinePrefix246_into_old109_iff

example : ∀ (q : Fin 246) (b : Bool),
    (machinePrefix246.transition q b).next = some (oldStatePrefix246 255) ↔
      (q = oldStatePrefix246 75 ∨ q = oldStatePrefix246 255) ∧ b = false := machinePrefix246_into_old255_iff

example : oldStatePrefix246 95 = 0 := oldStatePrefix246_95

example : oldStatePrefix246 83 ≠ oldStatePrefix246 95 := oldStatePrefix246_83_ne_95

example : oldStatePrefix246 83 ≠ oldStatePrefix246 255 := oldStatePrefix246_83_ne_255

example :
    machinePrefix246.transition (oldStatePrefix246 75) false =
      ⟨true, .right, some (oldStatePrefix246 255)⟩ := rowPrefix246_old75_false

example :
    machinePrefix246.transition (oldStatePrefix246 75) true =
      ⟨true, .left, some (oldStatePrefix246 63)⟩ := rowPrefix246_old75_true

example :
    machinePrefix246.transition (oldStatePrefix246 255) false =
      ⟨true, .left, some (oldStatePrefix246 255)⟩ := rowPrefix246_old255_false

example :
    machinePrefix246.transition (oldStatePrefix246 255) true =
      ⟨true, .left, some (oldStatePrefix246 131)⟩ := rowPrefix246_old255_true

example :
    machinePrefix246.transition (oldStatePrefix246 60) false =
      ⟨false, .right, some (oldStatePrefix246 20)⟩ := rowPrefix246_old60_false

example :
    machinePrefix246.transition (oldStatePrefix246 60) true =
      ⟨true, .right, some (oldStatePrefix246 60)⟩ := rowPrefix246_old60_true

example :
    machinePrefix246.transition (oldStatePrefix246 112) false =
      ⟨true, .left, some (oldStatePrefix246 131)⟩ := rowPrefix246_old112_false

example :
    machinePrefix246.transition (oldStatePrefix246 131) true =
      ⟨false, .left, some (oldStatePrefix246 112)⟩ := rowPrefix246_old131_true

example :
    machinePrefix246.transition (oldStatePrefix246 73) false =
      ⟨false, .right, some (oldStatePrefix246 83)⟩ := rowPrefix246_old73_false

example :
    machinePrefix246.transition (oldStatePrefix246 73) true =
      ⟨true, .right, some (oldStatePrefix246 73)⟩ := rowPrefix246_old73_true

example :
    machinePrefix246.transition (oldStatePrefix246 83) false =
      ⟨true, .right, some (oldStatePrefix246 95)⟩ := rowPrefix246_old83_false

example :
    machinePrefix246.transition (oldStatePrefix246 83) true =
      ⟨true, .right, some (oldStatePrefix246 73)⟩ := rowPrefix246_old83_true

example :
    machinePrefix246.transition (oldStatePrefix246 95) false =
      ⟨true, .right, some (oldStatePrefix246 109)⟩ := rowPrefix246_old95_false

example :
    machinePrefix246.transition (oldStatePrefix246 95) true =
      ⟨true, .right, some (oldStatePrefix246 95)⟩ := rowPrefix246_old95_true

example :
    machinePrefix246.transition (oldStatePrefix246 109) false =
      ⟨false, .right, some (oldStatePrefix246 75)⟩ := rowPrefix246_old109_false

example :
    machinePrefix246.transition (oldStatePrefix246 109) true =
      ⟨false, .right, some (oldStatePrefix246 95)⟩ := rowPrefix246_old109_true

example :
    machinePrefix246.transition (oldStatePrefix246 112) true =
      ⟨true, .left, some (oldStatePrefix246 112)⟩ := rowPrefix246_old112_true

example :
    machinePrefix246.transition (oldStatePrefix246 131) false =
      ⟨false, .left, some (oldStatePrefix246 48)⟩ := rowPrefix246_old131_false

example :
    machinePrefix246.transition (oldStatePrefix246 48) false =
      ⟨false, .left, some (oldStatePrefix246 7)⟩ := rowPrefix246_old48_false

example :
    machinePrefix246.transition (oldStatePrefix246 48) true =
      ⟨true, .left, some (oldStatePrefix246 63)⟩ := rowPrefix246_old48_true

example :
    machinePrefix246.transition (oldStatePrefix246 63) false =
      ⟨false, .left, some (oldStatePrefix246 48)⟩ := rowPrefix246_old63_false

example :
    machinePrefix246.transition (oldStatePrefix246 63) true =
      ⟨true, .left, some (oldStatePrefix246 63)⟩ := rowPrefix246_old63_true

example :
    machinePrefix246.transition (oldStatePrefix246 20) false =
      ⟨true, .left, some (oldStatePrefix246 2)⟩ := rowPrefix246_old20_false

example :
    machinePrefix246.transition (oldStatePrefix246 20) true =
      ⟨false, .left, some (oldStatePrefix246 2)⟩ := rowPrefix246_old20_true

example :
    machinePrefix246.transition (oldStatePrefix246 2) false =
      ⟨false, .left, some (oldStatePrefix246 2)⟩ := rowPrefix246_old2_false

example :
    machinePrefix246.transition (oldStatePrefix246 2) true =
      ⟨true, .left, some (oldStatePrefix246 4)⟩ := rowPrefix246_old2_true

example :
    machinePrefix246.transition (oldStatePrefix246 4) false =
      ⟨false, .left, some (oldStatePrefix246 6)⟩ := rowPrefix246_old4_false

example :
    machinePrefix246.transition (oldStatePrefix246 4) true =
      ⟨true, .left, some (oldStatePrefix246 4)⟩ := rowPrefix246_old4_true

example :
    machinePrefix246.transition (oldStatePrefix246 6) true =
      ⟨true, .left, some (oldStatePrefix246 4)⟩ := rowPrefix246_old6_true
