module
import PA196.Commands.Compiler

/-! A failed or newly axiomatized command proof makes this audit fail. -/

/-- info: 'PA196.Commands.ax_shift9' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Commands.ax_shift9

/-- info: 'PA196.Commands.pop_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Commands.pop_total

/-- info: 'PA196.Commands.push_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Commands.push_total

/-- info: 'PA196.Commands.discard_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Commands.discard_total

/-- info: 'PA196.Commands.generalize_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Commands.generalize_total

/-- info: 'PA196.Commands.mpSuffix_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Commands.mpSuffix_result

/-- info: 'PA196.Commands.compile_result' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Commands.compile_result

/-- info: 'PA196.Commands.haltWord_universal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Commands.haltWord_universal
