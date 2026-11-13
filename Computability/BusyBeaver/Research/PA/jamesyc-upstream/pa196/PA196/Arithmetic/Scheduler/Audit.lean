module
public import PA196.Arithmetic.Scheduler.SourceEnumerationFromTwo
@[expose] public section

/-! Strict dependency-axiom audit of the new program scheduler. -/


/-- info: 'PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX.decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.Machine.PA.InternalTrace.ModelAX.decoded

/-- info: 'PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal.pa_proves_refutation_enumeration_halts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.Scheduler.SourceCommandEncodingInternal.pa_proves_refutation_enumeration_halts

/-- info: 'PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource.refutation_root_two_halts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms PA196.Arithmetic.Machine.PA.InternalTrace.CodedSource.refutation_root_two_halts
