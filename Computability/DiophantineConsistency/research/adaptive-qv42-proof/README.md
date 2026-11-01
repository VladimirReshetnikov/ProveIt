# Oriented 42-variable quartic candidate

The Lean literal is bound row by row to the pinned 42-variable, 174-operation
candidate in `adaptive-square-sums42-quartic`. `AdaptiveQV42.oriented_exists_iff`
proves in every IΣ₁ model and for arbitrary integer ports that positive zeros
of this literal correspond exactly to positive zeros of the 43-variable
parent whose two V coordinates satisfy `v 26 < v 25`. The forward map takes
the magnitude of that positive difference; the reverse embeds a positive V
as `(V+1,1)`.

This is a conditional witness equivalence. It does not prove that an arbitrary
43-variable zero is oriented, nor that an oriented zero exists whenever the
machine halts. Those require a separate witness-construction and sign-transport
argument. In particular no unqualified native iPRA endpoint is asserted here.
A native iPRA client is separately checked with the explicit `MachineOrients` premise: every internal machine halting time gives a positive 43-variable zero with `v 26 < v 25`. The focused replays inherit the parent provider's transitive and dynamic ancestry.
