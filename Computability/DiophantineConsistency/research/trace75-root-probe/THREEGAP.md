# Ordered-ring gap for the index-three/index-two case

`Trace75ThreeGap.gap_bounds` is a generic Lean theorem over any commutative
strictly linearly ordered ring. From the explicit hypotheses

```
2 ≤ x,  8 ≤ y,  0 < eta < 8*x*y²+4,
eta + 4*y²*(x*(2*y-x-2)-1) = 4*y*(2*x+1)+3,
```

it concludes `x < 2*y` and `2*y < x+3`. The proof treats both possible
large gaps using nonnegative products and ordered-ring arithmetic. This
module does not mention any graph or model and does not show that an actual
trace75 zero satisfies its hypotheses; it is not yet the main-index-three
exclusion, a trace74 guard, halt equivalence or iPRA result.

Accepted source `Trace75ThreeGap.lean` SHA-256
`ffd5be19ec07ab16df95f92fb8dd248cfe5254a9d6163fbe6922e578ac7fef12`;
`run-gap-v2.py` accepted `observations/gap-attempt02/`, object
`/tmp/trace75-gap-q8gsgr97/Trace75ThreeGap.olean` SHA-256
`3f25660d7a2263e82d60dbdea5815063a74bf29fcdabc3e8dc3c976f6d1a1850`.
`#print axioms` reports the captured Lean axioms in the accepted stdout.
Attempt01 failed on a class name; its source and diagnostics are retained.
Direct selected Mathlib providers are pinned; their package transitive and
dynamic ancestry remain inherited, without a complete closure audit.
