# Forty-two-variable quartic equivalence

The Lean literal is bound row by row to the pinned 42-variable, 174-operation
candidate in `adaptive-square-sums42-quartic`. `AdaptiveQV42.oriented_exists_iff`
proves in every IΣ₁ model and for arbitrary integer ports that positive zeros
of this literal correspond exactly to positive zeros of the 43-variable
parent whose two V coordinates satisfy `v 26 < v 25`. The forward map takes
the magnitude of that positive difference; the reverse embeds a positive V
as `(V+1,1)`.

The oriented equivalence does not assert that every 43-variable zero has the
required sign. `AdaptiveVSignMachine43.machineOrients` instead constructs a
suitably oriented witness from any internal halting time, using the preserved
auxiliary seed and the 42-to-43 sign transport. This discharges the explicit
premise of the earlier conditional native client. `IPRAQV42Native.literal_equivalence`
states the fixed-port literal equivalence in the specified intuitionistic PRA,
with the negation of the mapped Foundation ZFC refutation predicate.

The [final paired replay](../../reviews/adaptive-qv42-native-final-replay/README.md)
uses a 31-final primary provider and fills absent objects from a conditional
QV42 provider, with primary objects taking precedence. Direct dependencies are
guarded; project-transitive, package-transitive and dynamically loaded ancestry
is inherited. A fully authenticated current-source closure remains open.
