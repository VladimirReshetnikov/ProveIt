module
public import PA196.Independence
public import PA196.Arithmetic.Audit
public import PA196.Commands.Audit
public import PA196.Arithmetic.Scheduler.Audit
@[expose] public section

/-! A closed trust audit for the PA196 endpoints. Each command is guarded:
an additional axiom, an admitted proof, or native-evaluation trust changes
the output and makes this module fail to compile. -/

/-- info: 'PA196.machine_nonhalting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.machine_nonhalting

/-- info: 'PA196.Arithmetic.nonhalting_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.nonhalting_true

/-- info: 'PA196.Arithmetic.Transport.FoundationNativeRefutationTransport.original_provable_refutation_transport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.Transport.FoundationNativeRefutationTransport.original_provable_refutation_transport

/-- info: 'PA196.Arithmetic.refutation_implies_literal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.refutation_implies_literal

/-- info: 'PA196.Arithmetic.pa_proves_nonhalting_consistency' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.pa_proves_nonhalting_consistency

/-- info: 'PA196.Arithmetic.nonhalting_unprovable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.nonhalting_unprovable

/-- info: 'PA196.Arithmetic.halting_unprovable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.halting_unprovable

/-- info: 'PA196.Arithmetic.two_sided_independence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.two_sided_independence
