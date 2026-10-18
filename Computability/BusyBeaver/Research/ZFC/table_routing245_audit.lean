import BusyBeaver.ZFC.TableRouting245

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC

#print axioms SetTheory.BusyBeaver.ZFC.rawTableRouting245_size
#print axioms SetTheory.BusyBeaver.ZFC.rawTableRouting245_transition_count
#print axioms SetTheory.BusyBeaver.ZFC.rawTableRouting245_targets_bounded
#print axioms SetTheory.BusyBeaver.ZFC.rawTableRouting245_halt_edge_count
#print axioms SetTheory.BusyBeaver.ZFC.rawActionRouting245_target_bounded
#print axioms SetTheory.BusyBeaver.ZFC.oldLabelsRouting245_size
#print axioms SetTheory.BusyBeaver.ZFC.oldStateRouting245_oldLabel
#print axioms SetTheory.BusyBeaver.ZFC.oldLabelRouting245_injective
#print axioms SetTheory.BusyBeaver.ZFC.startRouting245_old95
#print axioms SetTheory.BusyBeaver.ZFC.dispatchRouting245_eq
#print axioms SetTheory.BusyBeaver.ZFC.machineRouting245_initial_action
#print axioms SetTheory.BusyBeaver.ZFC.machineRouting245_halt_action
#print axioms SetTheory.BusyBeaver.ZFC.machineRouting245_halt_iff
#print axioms SetTheory.BusyBeaver.ZFC.machineRouting245_into_old109_iff
#print axioms SetTheory.BusyBeaver.ZFC.machineRouting245_into_old255_iff
#print axioms SetTheory.BusyBeaver.ZFC.oldStateRouting245_95
#print axioms SetTheory.BusyBeaver.ZFC.oldStateRouting245_83_ne_95
#print axioms SetTheory.BusyBeaver.ZFC.oldStateRouting245_83_ne_255
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old75_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old75_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old255_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old255_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old60_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old60_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old112_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old131_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old73_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old73_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old83_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old83_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old95_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old95_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old109_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old109_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old112_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old131_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old48_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old48_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old63_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old63_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old20_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old20_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old2_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old2_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old4_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old4_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old6_true

#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old44_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old44_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old31_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old31_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old56_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old56_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old38_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old38_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old40_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old40_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old28_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old28_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old64_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old64_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old69_false
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old69_true
#print axioms SetTheory.BusyBeaver.ZFC.rowRouting245_old6_false

example : rawTableRouting245.size = 245 := rawTableRouting245_size

example :
    (rawTableRouting245.toList.flatMap (fun row => [row.1, row.2])).length = 490 := rawTableRouting245_transition_count

example :
    rawTableRouting245.toList.all (fun row =>
      decide (row.1.2.2 ≤ 245 ∧ row.2.2.2 ≤ 245)) = true := rawTableRouting245_targets_bounded

example :
    ((rawTableRouting245.toList.flatMap (fun row => [row.1.2.2, row.2.2.2])).filter
      (fun target => target == 245)).length = 1 := rawTableRouting245_halt_edge_count

example : ∀ (q : Fin 245) (b : Bool),
    (rawActionRouting245 q b).2.2 ≤ 245 := rawActionRouting245_target_bounded

example : oldLabelsRouting245.size = 245 := oldLabelsRouting245_size

example : ∀ q : Fin 245,
    oldStateRouting245 (oldLabelRouting245 q) = q := oldStateRouting245_oldLabel

example {q r : Fin 245}
    (h : oldLabelRouting245 q = oldLabelRouting245 r) : q = r := oldLabelRouting245_injective h

example : startRouting245 = oldStateRouting245 95 := startRouting245_old95

example : dispatchRouting245 = 88 := dispatchRouting245_eq

example :
    machineRouting245.transition startRouting245 false =
      ⟨true, .right, some (oldStateRouting245 109)⟩ := machineRouting245_initial_action

example :
    machineRouting245.transition (oldStateRouting245 77) true =
      ⟨true, .right, none⟩ := machineRouting245_halt_action

example : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = none ↔
      q = oldStateRouting245 77 ∧ b = true := machineRouting245_halt_iff

example : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = some (oldStateRouting245 109) ↔
      q = oldStateRouting245 95 ∧ b = false := machineRouting245_into_old109_iff

example : ∀ (q : Fin 245) (b : Bool),
    (machineRouting245.transition q b).next = some (oldStateRouting245 255) ↔
      (q = oldStateRouting245 75 ∨ q = oldStateRouting245 255) ∧ b = false := machineRouting245_into_old255_iff

example : oldStateRouting245 95 = 0 := oldStateRouting245_95

example : oldStateRouting245 83 ≠ oldStateRouting245 95 := oldStateRouting245_83_ne_95

example : oldStateRouting245 83 ≠ oldStateRouting245 255 := oldStateRouting245_83_ne_255

example :
    machineRouting245.transition (oldStateRouting245 75) false =
      ⟨true, .right, some (oldStateRouting245 255)⟩ := rowRouting245_old75_false

example :
    machineRouting245.transition (oldStateRouting245 75) true =
      ⟨true, .left, some (oldStateRouting245 63)⟩ := rowRouting245_old75_true

example :
    machineRouting245.transition (oldStateRouting245 255) false =
      ⟨true, .left, some (oldStateRouting245 255)⟩ := rowRouting245_old255_false

example :
    machineRouting245.transition (oldStateRouting245 255) true =
      ⟨true, .left, some (oldStateRouting245 131)⟩ := rowRouting245_old255_true

example :
    machineRouting245.transition (oldStateRouting245 60) false =
      ⟨false, .right, some (oldStateRouting245 20)⟩ := rowRouting245_old60_false

example :
    machineRouting245.transition (oldStateRouting245 60) true =
      ⟨true, .right, some (oldStateRouting245 60)⟩ := rowRouting245_old60_true

example :
    machineRouting245.transition (oldStateRouting245 112) false =
      ⟨true, .left, some (oldStateRouting245 131)⟩ := rowRouting245_old112_false

example :
    machineRouting245.transition (oldStateRouting245 131) true =
      ⟨false, .left, some (oldStateRouting245 112)⟩ := rowRouting245_old131_true

example :
    machineRouting245.transition (oldStateRouting245 73) false =
      ⟨false, .right, some (oldStateRouting245 83)⟩ := rowRouting245_old73_false

example :
    machineRouting245.transition (oldStateRouting245 73) true =
      ⟨true, .right, some (oldStateRouting245 73)⟩ := rowRouting245_old73_true

example :
    machineRouting245.transition (oldStateRouting245 83) false =
      ⟨true, .right, some (oldStateRouting245 95)⟩ := rowRouting245_old83_false

example :
    machineRouting245.transition (oldStateRouting245 83) true =
      ⟨true, .right, some (oldStateRouting245 73)⟩ := rowRouting245_old83_true

example :
    machineRouting245.transition (oldStateRouting245 95) false =
      ⟨true, .right, some (oldStateRouting245 109)⟩ := rowRouting245_old95_false

example :
    machineRouting245.transition (oldStateRouting245 95) true =
      ⟨true, .right, some (oldStateRouting245 95)⟩ := rowRouting245_old95_true

example :
    machineRouting245.transition (oldStateRouting245 109) false =
      ⟨false, .right, some (oldStateRouting245 75)⟩ := rowRouting245_old109_false

example :
    machineRouting245.transition (oldStateRouting245 109) true =
      ⟨false, .right, some (oldStateRouting245 95)⟩ := rowRouting245_old109_true

example :
    machineRouting245.transition (oldStateRouting245 112) true =
      ⟨true, .left, some (oldStateRouting245 112)⟩ := rowRouting245_old112_true

example :
    machineRouting245.transition (oldStateRouting245 131) false =
      ⟨false, .left, some (oldStateRouting245 48)⟩ := rowRouting245_old131_false

example :
    machineRouting245.transition (oldStateRouting245 48) false =
      ⟨false, .left, some (oldStateRouting245 7)⟩ := rowRouting245_old48_false

example :
    machineRouting245.transition (oldStateRouting245 48) true =
      ⟨true, .left, some (oldStateRouting245 63)⟩ := rowRouting245_old48_true

example :
    machineRouting245.transition (oldStateRouting245 63) false =
      ⟨false, .left, some (oldStateRouting245 48)⟩ := rowRouting245_old63_false

example :
    machineRouting245.transition (oldStateRouting245 63) true =
      ⟨true, .left, some (oldStateRouting245 63)⟩ := rowRouting245_old63_true

example :
    machineRouting245.transition (oldStateRouting245 20) false =
      ⟨true, .left, some (oldStateRouting245 2)⟩ := rowRouting245_old20_false

example :
    machineRouting245.transition (oldStateRouting245 20) true =
      ⟨false, .left, some (oldStateRouting245 2)⟩ := rowRouting245_old20_true

example :
    machineRouting245.transition (oldStateRouting245 2) false =
      ⟨false, .left, some (oldStateRouting245 2)⟩ := rowRouting245_old2_false

example :
    machineRouting245.transition (oldStateRouting245 2) true =
      ⟨true, .left, some (oldStateRouting245 4)⟩ := rowRouting245_old2_true

example :
    machineRouting245.transition (oldStateRouting245 4) false =
      ⟨false, .left, some (oldStateRouting245 6)⟩ := rowRouting245_old4_false

example :
    machineRouting245.transition (oldStateRouting245 4) true =
      ⟨true, .left, some (oldStateRouting245 4)⟩ := rowRouting245_old4_true

example :
    machineRouting245.transition (oldStateRouting245 6) true =
      ⟨true, .left, some (oldStateRouting245 4)⟩ := rowRouting245_old6_true

example :
    machineRouting245.transition (oldStateRouting245 44) false =
      ⟨false, .right, some (oldStateRouting245 60)⟩ := rowRouting245_old44_false

example :
    machineRouting245.transition (oldStateRouting245 44) true =
      ⟨true, .right, some (oldStateRouting245 44)⟩ := rowRouting245_old44_true

example :
    machineRouting245.transition (oldStateRouting245 31) false =
      ⟨false, .right, some (oldStateRouting245 44)⟩ := rowRouting245_old31_false

example :
    machineRouting245.transition (oldStateRouting245 31) true =
      ⟨true, .right, some (oldStateRouting245 31)⟩ := rowRouting245_old31_true

example :
    machineRouting245.transition (oldStateRouting245 56) false =
      ⟨false, .right, some (oldStateRouting245 31)⟩ := rowRouting245_old56_false

example :
    machineRouting245.transition (oldStateRouting245 56) true =
      ⟨true, .right, some (oldStateRouting245 56)⟩ := rowRouting245_old56_true

example :
    machineRouting245.transition (oldStateRouting245 38) false =
      ⟨false, .right, some (oldStateRouting245 56)⟩ := rowRouting245_old38_false

example :
    machineRouting245.transition (oldStateRouting245 38) true =
      ⟨true, .right, some (oldStateRouting245 38)⟩ := rowRouting245_old38_true

example :
    machineRouting245.transition (oldStateRouting245 40) false =
      ⟨false, .right, some (oldStateRouting245 38)⟩ := rowRouting245_old40_false

example :
    machineRouting245.transition (oldStateRouting245 40) true =
      ⟨true, .right, some (oldStateRouting245 40)⟩ := rowRouting245_old40_true

example :
    machineRouting245.transition (oldStateRouting245 28) false =
      ⟨false, .right, some (oldStateRouting245 40)⟩ := rowRouting245_old28_false

example :
    machineRouting245.transition (oldStateRouting245 28) true =
      ⟨true, .right, some (oldStateRouting245 28)⟩ := rowRouting245_old28_true

example :
    machineRouting245.transition (oldStateRouting245 64) false =
      ⟨false, .right, some (oldStateRouting245 28)⟩ := rowRouting245_old64_false

example :
    machineRouting245.transition (oldStateRouting245 64) true =
      ⟨true, .right, some (oldStateRouting245 64)⟩ := rowRouting245_old64_true

example :
    machineRouting245.transition (oldStateRouting245 69) false =
      ⟨false, .right, some (oldStateRouting245 64)⟩ := rowRouting245_old69_false

example :
    machineRouting245.transition (oldStateRouting245 69) true =
      ⟨true, .right, some (oldStateRouting245 69)⟩ := rowRouting245_old69_true

example :
    machineRouting245.transition (oldStateRouting245 6) false =
      ⟨false, .left, some (oldStateRouting245 9)⟩ := rowRouting245_old6_false
