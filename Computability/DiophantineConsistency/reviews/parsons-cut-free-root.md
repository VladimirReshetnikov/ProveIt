# Cut-free theory proof adapter

`ParsonsCutFree` turns any actual finite Foundation `Theory.Proof` over a
language with decidable equality into a cut-free derivation with exactly the
same finite list of theory axioms. Forgetting the cut-free property gives a
proof in the original theory, so provability is equivalent to the existence
of this structure. This is the logical starting point of the proposed
conservation proof; it leaves every arithmetic induction axiom intact.

The main file and focused checks each compiled twice into fresh outputs using
Lean 4.32 with `-M6000 -j1 -DElab.async=false`. Both object hashes and full
logs matched; all four reports use only `propext`, `Classical.choice`, and
`Quot.sound`. The source snapshots, results, logs and independent replay
driver are in [the replay bundle](parsons-cut-free-replay/FILES.json). Both
builds used the existing Foundation and Mathlib object directories as an
inherited boundary; this is not a fresh audit or rebuild of their dependency
closure. The first exploratory command failed to find Foundation because
`lake env` did not include its object directory; the succeeding commands
explicitly prepended that directory.

The accompanying [route note](../research/parsons-cut-free-induction-route-20261029.md)
identifies the height-preserving inversion, parameterized induction-rule case,
and PRA witnessing steps still needed. No PRA calculus, Parsons theorem,
induction-axiom elimination, or PRA proof of the target follows from this
adapter alone.
