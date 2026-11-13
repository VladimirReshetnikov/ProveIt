# Independent review: trace75 carrier sign flip

**PASS.** `Trace75SignFlip.Z_move` is an all-commutative-ring identity for
arbitrary ring-valued ports and valuations: setting slot 7 to `v 7 + 2*d`
changes the actual trace75 register Z to `Z + 2*M*d`. The actual evaluator
`TenPositiveTrace75.value75` uses Z only through its square; Q, M, Gn and V
are definitionally unchanged. `value_flip` explicitly assumes old `Z=-M*d`,
so the new Z is `M*d` and the actual evaluator is unchanged.

The theorem does not assume or produce model positivity, a graph zero, a
positive center or a 73-to-75 witness; those are separate tasks. The source
matches the actual `regs` and `value75` definitions. The documentation's
phrase “all output-relevant registers unchanged” should be read as the other
output-relevant registers Q, M, Gn and V: Z is output-relevant and changes.

The accepted `research/trace73-center-normalization/observations/flip-attempt02/`
terminal SHA-256 is `6ac4b60f6a0efa1a417f8ce02dd90271759e1bd155d3a7e7883e745de4ea827a`;
the regular object `/tmp/trace75-signflip-5t6uw3qf/Trace75SignFlip.olean`
has SHA-256 `853d9841662ae9ae17388da47c4cc684332e99cbdc3346035564c4997ade70af`.
Source, copied source, runner, expected axiom report, current first direct
`TenPositiveTrace75` provider, five pinned selected objects and resource
samples were checked. Failed attempt01 contains an error and `sorryAx` and
is not accepted; attempt02 replaces a failed reduction with explicit `rfl`
register equalities. The tool exit 0 is author-reported; no separate outer
receipt or independent Lean replay is claimed. Full transitive, historical,
package and dynamic provenance remains outside this review.

`check.py` SHA-256 `d93321e25bc5122533402dcdf560fd2b10e0667e902578176e0a6f4cac6a6db8`;
`result.txt` SHA-256 `70b190f2a6ea905a2b3be6c3adb5a97c5f395dc09eb049bbe4632d51499019cb`.
