# Corrected first MC boundary window

`CompactLowByteBoundary01.windows` checks the single index in `[16,17)`:
the generated closed Lean recipe's `byteAt j` equals the symbolic low-mask
window `(lowNat / 256^j) % 256`. It replaces the original `interval_cases`
step by an explicit proof that `j = 16`, avoiding the warning that caused
the first wrapper to reject the original attempt. The original source and
warning-bearing result are retained in the sibling boundary-initial packet.

The bounded author run `observations/attempt02` exited 0 in 2.961 seconds
without warnings or `sorryAx`; direct dependency/companion guards and the
separately inventoried generic provider remained unchanged. Source SHA-256:
`475fcd69cd7233002b69f88ac59813e9c24c99b334e5deda535992c80f522e7f`;
object SHA-256:
`9e5afc4103083543aad8485d36e95e1d5b48bd8d44f5bea7da3fbf5927e93711`.
Lean reports `[propext, Classical.choice, Quot.sound]` as metatheory
dependencies, not iPRA axioms.

This author-side theorem is about the generated Lean recipe, not a Lean
theorem about the retained file, gzip, supplement, PDF or iPRA. It is not
a paired replay or a full symbolic/package/dynamic ancestry audit; guards
are point-in-time. The global assembly must select this corrected module,
not the rejected original boundary-01 object.
