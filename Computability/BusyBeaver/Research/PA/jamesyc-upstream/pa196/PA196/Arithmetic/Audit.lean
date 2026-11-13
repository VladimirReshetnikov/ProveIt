module
public import PA196.Arithmetic.CompilerHaltingWord
public import PA196.Arithmetic.CommandStandard
@[expose] public section

/-! The public arithmetic endpoints may use only Lean's three standard
logical axioms. In particular no proof placeholder or native evaluator is
part of these dependency closures. -/

/-- info: 'PA196.Arithmetic.HeadGraphs.formula_graph_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.HeadGraphs.formula_graph_total

/-- info: 'PA196.Arithmetic.Checker.pa_proves_verify_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.Checker.pa_proves_verify_total

/-- info: 'PA196.Arithmetic.CommandStep.step_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.CommandStep.step_standard

/-- info: 'PA196.Arithmetic.CommandStep.word_graph_halts_standard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.CommandStep.word_graph_halts_standard

/-- info: 'PA196.Arithmetic.CommandStep.ax_shift9_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.CommandStep.ax_shift9_value

/-- info: 'PA196.Arithmetic.CommandStep.selectedHead1_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.CommandStep.selectedHead1_value

/-- info: 'PA196.Arithmetic.CommandStep.rho8Word_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.CommandStep.rho8Word_value

/-- info: 'PA196.Arithmetic.CompilerSoundness.accepted_compiler_realizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.CompilerSoundness.accepted_compiler_realizes

/-- info: 'PA196.Arithmetic.CompilerHaltingWord.pa_proves_refutation_word_halts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.CompilerHaltingWord.pa_proves_refutation_word_halts
