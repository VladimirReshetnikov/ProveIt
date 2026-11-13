# Independent review of bounded-port positive-zero equivalence

`DirectMainEquivalence.positive_zero_iff` proves in every model of IΣ₁ that
the positive-zero existence propositions for the 90-operation direct graph and
the XQ91 graph are equivalent, for a natural port tuple satisfying `0<beta`,
`MC<beta`, and `MF<2*beta` in that model. Witnesses can be nonstandard. The
theorem does not assume an old graph zero and does not itself establish a
fixed-port machine-halt theorem or an iPRA derivation.

The direct-to-XQ91 direction applies the separately checked graph-gap theorem
to show `w<G` for the given positive direct-graph zero. It then uses the
reverse direction of `DirectMainRestricted.exists_iff_restricted`. That
theorem takes `gamma=G-w`, proves it is positive using `w<G`, and verifies
that the forward coordinate update is inverted. The XQ91-to-direct direction
uses `DirectMainForward.exists_direct_of_xq91`, which assigns `G=gamma+w`
and preserves positive coordinates. The bounded-port assumptions are used for
the gap theorem; the two witness maps themselves are stated for arbitrary
natural ports.

The author receipt records exit 0 without reported warnings or `sorryAx`;
the single axiom report is `[propext, Classical.choice, Quot.sound]` in Lean's
metatheory. The independent checker verifies the exact theorem and composition,
the restricted inverse and forward map, the accepted source, object, logs,
Lean binary, and the retained restricted-proof syntax failure. It verifies
the first-resolved gap, restricted and forward producer objects and the pins
for all 21 added producer objects, rehashes all 1,291 selected union paths
before and after, and reruns the prior graph-gap and forward reviews. The
accepted run sampled one existing Lean process before launch and at most two
in its recorded execution samples; sampling is not continuous.

Run `python3 -I -S -B check.py` from this directory or provide its path from
any directory. The captured exit-zero, empty-stderr run and input hashes are
in [`observations/attempt01`](observations/attempt01/). The check requires
the retained `/tmp` providers and does not launch Lean. The selected-object
and producer checks do not authenticate a full serialized-import closure,
historical source-to-object origin, package-transitive or dynamic ancestry,
or a fresh independent kernel replay. The graph's Lean syntax to JSON and
external payload correspondence remains separately checked outside Lean.
