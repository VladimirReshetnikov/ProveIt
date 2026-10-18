import BusyBeaver.ZFC.TablePrefix250

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

#print axioms SetTheory.BusyBeaver.ZFC.rawTablePrefix250_size
#print axioms SetTheory.BusyBeaver.ZFC.rawTablePrefix250_transition_count
#print axioms SetTheory.BusyBeaver.ZFC.rawTablePrefix250_targets_bounded
#print axioms SetTheory.BusyBeaver.ZFC.rawTablePrefix250_halt_edge_count
#print axioms SetTheory.BusyBeaver.ZFC.rawActionPrefix250_target_bounded
#print axioms SetTheory.BusyBeaver.ZFC.oldLabelsPrefix250_size
#print axioms SetTheory.BusyBeaver.ZFC.oldStatePrefix250_oldLabel
#print axioms SetTheory.BusyBeaver.ZFC.oldLabelPrefix250_injective
#print axioms SetTheory.BusyBeaver.ZFC.startPrefix250_old97
#print axioms SetTheory.BusyBeaver.ZFC.dispatchPrefix250_eq
#print axioms SetTheory.BusyBeaver.ZFC.machinePrefix250_initial_action
#print axioms SetTheory.BusyBeaver.ZFC.machinePrefix250_halt_action
#print axioms SetTheory.BusyBeaver.ZFC.machinePrefix250_halt_iff
#print axioms SetTheory.BusyBeaver.ZFC.machinePrefix250_into_old97_iff
#print axioms SetTheory.BusyBeaver.ZFC.machinePrefix250_into_old255_iff
#print axioms SetTheory.BusyBeaver.ZFC.oldStatePrefix250_97
#print axioms SetTheory.BusyBeaver.ZFC.oldStatePrefix250_83_ne_97
#print axioms SetTheory.BusyBeaver.ZFC.oldStatePrefix250_83_ne_255
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old75_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old75_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old255_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old255_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old97_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old97_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old112_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old131_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old73_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old73_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old83_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old83_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old95_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old95_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old109_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old109_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old112_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old131_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old48_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old48_true
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old63_false
#print axioms SetTheory.BusyBeaver.ZFC.rowPrefix250_old63_true

example : rawTablePrefix250.size = 250 := rawTablePrefix250_size

example :
    (rawTablePrefix250.toList.flatMap (fun row => [row.1, row.2])).length = 500 := rawTablePrefix250_transition_count

example :
    rawTablePrefix250.toList.all (fun row =>
      decide (row.1.2.2 ≤ 250 ∧ row.2.2.2 ≤ 250)) = true := rawTablePrefix250_targets_bounded

example :
    ((rawTablePrefix250.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 250)).length = 1 := rawTablePrefix250_halt_edge_count

example : ∀ (q : Fin 250) (b : Bool),
    (rawActionPrefix250 q b).2.2 ≤ 250 := rawActionPrefix250_target_bounded

example : oldLabelsPrefix250.size = 250 := oldLabelsPrefix250_size

example : ∀ q : Fin 250,
    oldStatePrefix250 (oldLabelPrefix250 q) = q := oldStatePrefix250_oldLabel

example {q r : Fin 250}
    (h : oldLabelPrefix250 q = oldLabelPrefix250 r) : q = r := oldLabelPrefix250_injective h

example : startPrefix250 = oldStatePrefix250 97 := startPrefix250_old97

example : dispatchPrefix250 = 92 := dispatchPrefix250_eq

example :
    machinePrefix250.transition startPrefix250 false =
      ⟨true, .right, some (oldStatePrefix250 83)⟩ := machinePrefix250_initial_action

example :
    machinePrefix250.transition (oldStatePrefix250 77) true =
      ⟨true, .right, none⟩ := machinePrefix250_halt_action

example : ∀ (q : Fin 250) (b : Bool),
    (machinePrefix250.transition q b).next = none ↔
      q = oldStatePrefix250 77 ∧ b = true := machinePrefix250_halt_iff

example : ∀ (q : Fin 250) (b : Bool),
    (machinePrefix250.transition q b).next = some (oldStatePrefix250 97) ↔
      q = oldStatePrefix250 255 ∧ b = false := machinePrefix250_into_old97_iff

example : ∀ (q : Fin 250) (b : Bool),
    (machinePrefix250.transition q b).next = some (oldStatePrefix250 255) ↔
      q = oldStatePrefix250 75 ∧ b = false := machinePrefix250_into_old255_iff

example : oldStatePrefix250 97 = 0 := oldStatePrefix250_97

example : oldStatePrefix250 83 ≠ oldStatePrefix250 97 := oldStatePrefix250_83_ne_97

example : oldStatePrefix250 83 ≠ oldStatePrefix250 255 := oldStatePrefix250_83_ne_255

example :
    machinePrefix250.transition (oldStatePrefix250 75) false =
      ⟨true, .right, some (oldStatePrefix250 255)⟩ := rowPrefix250_old75_false

example :
    machinePrefix250.transition (oldStatePrefix250 75) true =
      ⟨true, .left, some (oldStatePrefix250 63)⟩ := rowPrefix250_old75_true

example :
    machinePrefix250.transition (oldStatePrefix250 255) false =
      ⟨true, .left, some (oldStatePrefix250 97)⟩ := rowPrefix250_old255_false

example :
    machinePrefix250.transition (oldStatePrefix250 255) true =
      ⟨true, .left, some (oldStatePrefix250 131)⟩ := rowPrefix250_old255_true

example :
    machinePrefix250.transition (oldStatePrefix250 97) false =
      ⟨true, .right, some (oldStatePrefix250 83)⟩ := rowPrefix250_old97_false

example :
    machinePrefix250.transition (oldStatePrefix250 97) true =
      ⟨true, .left, some (oldStatePrefix250 131)⟩ := rowPrefix250_old97_true

example :
    machinePrefix250.transition (oldStatePrefix250 112) false =
      ⟨true, .left, some (oldStatePrefix250 131)⟩ := rowPrefix250_old112_false

example :
    machinePrefix250.transition (oldStatePrefix250 131) true =
      ⟨false, .left, some (oldStatePrefix250 112)⟩ := rowPrefix250_old131_true

example :
    machinePrefix250.transition (oldStatePrefix250 73) false =
      ⟨false, .right, some (oldStatePrefix250 83)⟩ := rowPrefix250_old73_false

example :
    machinePrefix250.transition (oldStatePrefix250 73) true =
      ⟨true, .right, some (oldStatePrefix250 73)⟩ := rowPrefix250_old73_true

example :
    machinePrefix250.transition (oldStatePrefix250 83) false =
      ⟨true, .right, some (oldStatePrefix250 95)⟩ := rowPrefix250_old83_false

example :
    machinePrefix250.transition (oldStatePrefix250 83) true =
      ⟨true, .right, some (oldStatePrefix250 73)⟩ := rowPrefix250_old83_true

example :
    machinePrefix250.transition (oldStatePrefix250 95) false =
      ⟨true, .right, some (oldStatePrefix250 109)⟩ := rowPrefix250_old95_false

example :
    machinePrefix250.transition (oldStatePrefix250 95) true =
      ⟨true, .right, some (oldStatePrefix250 95)⟩ := rowPrefix250_old95_true

example :
    machinePrefix250.transition (oldStatePrefix250 109) false =
      ⟨false, .right, some (oldStatePrefix250 75)⟩ := rowPrefix250_old109_false

example :
    machinePrefix250.transition (oldStatePrefix250 109) true =
      ⟨false, .right, some (oldStatePrefix250 95)⟩ := rowPrefix250_old109_true

example :
    machinePrefix250.transition (oldStatePrefix250 112) true =
      ⟨true, .left, some (oldStatePrefix250 112)⟩ := rowPrefix250_old112_true

example :
    machinePrefix250.transition (oldStatePrefix250 131) false =
      ⟨false, .left, some (oldStatePrefix250 48)⟩ := rowPrefix250_old131_false

example :
    machinePrefix250.transition (oldStatePrefix250 48) false =
      ⟨false, .left, some (oldStatePrefix250 7)⟩ := rowPrefix250_old48_false

example :
    machinePrefix250.transition (oldStatePrefix250 48) true =
      ⟨true, .left, some (oldStatePrefix250 63)⟩ := rowPrefix250_old48_true

example :
    machinePrefix250.transition (oldStatePrefix250 63) false =
      ⟨false, .left, some (oldStatePrefix250 48)⟩ := rowPrefix250_old63_false

example :
    machinePrefix250.transition (oldStatePrefix250 63) true =
      ⟨true, .left, some (oldStatePrefix250 63)⟩ := rowPrefix250_old63_true

