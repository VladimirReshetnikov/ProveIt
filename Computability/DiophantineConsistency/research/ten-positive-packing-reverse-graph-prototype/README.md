# Conditional compact packing to an 80-graph zero

`packing_seed_zero` works in every IΣ₁ model supported by the imported
framework. Given one `PackingInput` and one coherent `SeedRelations` tuple, it
constructs a positive zero of the selected 80-operation Lean graph. Its full
explicit hypotheses include the four model port equalities, positive beta,
positive `sY`, `w`, `eta`, and `zeta`, `4 ≤ r`, phase `(2r+1) % 4 = 3`, the
packing-rank equation, the power relation and the natural transport equation.
The proof derives the mask inequality and identifies rank, `X`, `Y` and
transport from that same packing before applying the earlier reverse-graph
theorem. The chosen valuation is internal to the proof; the exported result is
existence of a positive zero only.

The theorem is conditional: it does not itself derive these inputs from a
machine halt or a 90-graph zero. It also does not establish an iPRA proof, the
external JSON/PDF binding, or equality of the retained 80 coefficient `p 1`
with the symbolic packing coefficient; that coefficient difference remains a
separate open issue.

The accepted guarded run is `observations/graph-attempt03/`, with object
`/tmp/packing-reverse-graph-h2_jcxcd/PackingReverseGraph.olean` SHA-256
`aa879b5d70f582eedce7f0d0665d916c3703fb33540925411d96520e746c021e`.
The source and runner SHA-256 values are
`e34ae2aba88cf951d9e692285ffeeb42fd23b171061569dc5cfd671a1b4f5fda` and
`83bd4e85e2e167fc01bf0125f5380db4d18374d4d27440e5a95616acb2be087e`.
Earlier attempts are failed scratch checks. The accepted check reports the
listed standard Lean axioms and no `sorryAx`. Direct imports are resolved and
pinned before and after the check; the receipt records those selections and
resource samples. Full transitive source-to-object, package and dynamic
dependency provenance remains inherited from prior providers.
