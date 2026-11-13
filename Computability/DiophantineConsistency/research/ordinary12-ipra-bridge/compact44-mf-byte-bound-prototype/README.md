# Byte-length bound for the once-shifted high port

`CompactShiftedHighBound.shifted_lt_byte_power` proves in Lean that

```
CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat < 256^73759.
```

It bounds beta and the unshifted high mask separately by `(2^67)^8807`,
then bounds twice that radix power by `256^73759` using exponent
monotonicity. This supplies the size premise for the generic radix-window
reconstruction theorem and accounts for the beta addition exactly once.
It does not itself prove a byte-list, file, gzip, PDF or iPRA result.

The bounded mixed-provider author run `observations/attempt02` exited 0 in
2.318 seconds without warnings or `sorryAx`; direct dependency/companion
guards and the separately inventoried generic byte provider were unchanged.
Source SHA-256:
`e0d429c91cd290ebe4f22b56756dededa4beac9e002e1bd8e9553c0ee1186bb7`;
object SHA-256:
`e45ba6ff17c94225badb0192e6b8d515d0570de8e73db815061437e228072659`.
Lean's `[propext, Classical.choice, Quot.sound]` report lists metatheory
dependencies, not object-theory axioms. Attempt01 failed when a power
rewrite selected the wrong occurrence; its source, log and receipt are
retained, and attempt02 rewrites only the right-hand side.

The result is an author-side check over inherited symbolic, package and
dynamic ancestry, not a paired replay or complete ancestry audit. Guard
checks are point-in-time.
