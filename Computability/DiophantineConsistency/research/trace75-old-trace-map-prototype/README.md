# Squared-trace parent to trace75 ring substitution

`Trace75OldTraceMap.value_shift` is Lean checked over every commutative ring,
with arbitrary ports and valuations. It defines a squared-trace parent value
using the actual trace75 registers but replacing V by `f*f*(c*T-rank)-c`,
and the corresponding carrier Z. Updating only T to `f*T-d*rank`, with
`d=2*Delta*i²*c³*E`, makes the actual trace75 value equal that defined parent
value. The proof also establishes the intermediate V and Z identities.

This is a ring identity for the explicitly defined parent, not a binding to an
existing equation file or selected graph. It asserts no positive witnesses,
machine halting or iPRA equivalence. The accepted author run is
`observations/map-attempt01/`, object
`/tmp/trace75-oldtracemap-qm52cj8c/Trace75OldTraceMap.olean` SHA-256
`037f11212356efaa43494a640dbb45af97a437f6cadd2812c955bcdbc6d8ec56`.
The runner pins the direct Lean provider and Mathlib objects; full transitive,
package and dynamic ancestry remain inherited.
