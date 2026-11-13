# Decode four abstract byte lists pointwise

`GenericFourBytePorts.map4` proves that mapping `Nat.ofDigits 256` over a
four-element function tuple yields the tuple of the four decoded values.
`tuple4` additionally accepts four independent decoding equalities and
returns equality to the tuple of their right-hand sides. All four lists and
numbers remain abstract throughout the finite-index proof; this avoids
normalizing large concrete lists when the lemma is specialized.

The bounded author run `observations/attempt02` exited 0 in 1.748 seconds
without warnings or `sorryAx`, with recorded direct dependency/companion
guards unchanged. Source SHA-256:
`82f3c7bf35d31b995bd95ab59ec192ad481532f9f11c127ef9fc3007e3a4c78d`;
object SHA-256:
`c4cf66185b18c427a3a95ea1be7f2d093456a8bd5eeec58473fde82be4a9abd2`.
Both Lean axiom reports are `[propext, Classical.choice, Quot.sound]` in the
metatheory, not iPRA axioms. The initial attempt failed because vector
notation and the `fin_cases` tactic were not imported; the source/log are
retained. This is an author-side check, not a paired replay or complete
package/dynamic ancestry audit. No concrete port, file, PDF or iPRA result
follows without separate inputs.
