module
public import PA196.Palomar.Solution
@[expose] public section

/-! Guarded trust checks for every public PA196 presentation endpoint.
A changed axiom set makes compilation fail. The final commands repeat the
same reports outside the guards so the audit log retains readable evidence. -/

/-- info: 'PalomarPA.PA196.pa196Halting_toFoundation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalomarPA.PA196.pa196Halting_toFoundation

/-- info: 'PalomarPA.PA196.pa196Nonhalting_toFoundation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalomarPA.PA196.pa196Nonhalting_toFoundation

/-- info: 'PalomarPA.PA196.nonhalting_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalomarPA.PA196.nonhalting_true

/-- info: 'PalomarPA.PA196.halting_unprovable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalomarPA.PA196.halting_unprovable

/-- info: 'PalomarPA.PA196.nonhalting_unprovable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalomarPA.PA196.nonhalting_unprovable

/-- info: 'PalomarPA.PA196.two_sided_independence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalomarPA.PA196.two_sided_independence

/-- info: 'PalomarPA.PA196.nonhalting_irrefutable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalomarPA.PA196.nonhalting_irrefutable

/-- info: 'PalomarPA.PA196.machine_nonhalting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PalomarPA.PA196.machine_nonhalting

#print axioms PalomarPA.PA196.pa196Halting_toFoundation
#print axioms PalomarPA.PA196.pa196Nonhalting_toFoundation
#print axioms PalomarPA.PA196.nonhalting_true
#print axioms PalomarPA.PA196.halting_unprovable
#print axioms PalomarPA.PA196.nonhalting_unprovable
#print axioms PalomarPA.PA196.two_sided_independence
#print axioms PalomarPA.PA196.nonhalting_irrefutable
#print axioms PalomarPA.PA196.machine_nonhalting
