# Symbolic-mask specialization of the trace75-to-trace73 implication

`Trace75FixedTo73.positive_zero_to_center` is checked in every supported IΣ₁
model. For arbitrary natural ports satisfying `p0=betaNat`, `p2=lowNat`, and
`p3=betaNat+highNat`, existence of a positive trace75 zero implies existence
of a positive literal trace73 zero at the same ports. The kernel port `p1`
remains completely arbitrary; no fourth port equality is required. The proof
uses `Trace75FixedBounds.fixed_bounds` to discharge the beta and mask bounds
of the [one-way normalization theorem](NORMALIZE.md).

This implication does not establish the reverse direction, an unrestricted
73/75 equivalence, machine halting, iPRA derivability, or Lean semantics for
the external JSON/PDF/coefficients. All broader provider qualifications in the
normalization theorem remain in force.

The bounded author check `observations/fixed-attempt01/` and tool session
54643 exited 0; its sole axiom report is
`[propext, Classical.choice, Quot.sound]`. The resulting object
`/tmp/trace75-fixedto73-8wf2ld8l/Trace75FixedTo73.olean` has SHA-256
`7ba08d2cd24c4d3c1e25155a23fc23608607adc995c1ec96e43c295600c7d349`.
The source, runner and terminal SHA-256 are respectively
`5c486b31cd384fa031dc20b07a64e662542812226b79fbfcc4097ecea9a95e9b`,
`6d78f43d8e4dc4a58de5cb83a871149b590beedef12d74aa22fe030f6f6e3b97`, and
`ca2a8cdfdcc52b2f247bd28f01bd5c1861c7d742e11de81d4ba58ab2d7bcc54b`.
The runner pins the fresh trace75 fixed bounds, normalization object, and
selected direct predecessor objects. Full combined 73/75 source/object,
package-transitive and dynamic ancestry remains inherited; the author observed
the tool exit but did not retain a separate outer receipt. No independent Lean
replay is claimed.
