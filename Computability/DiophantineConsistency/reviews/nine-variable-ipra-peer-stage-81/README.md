# Nine-variable CURRENT2011 peer: stage 81 axiom reports

The bounded peer built the `IPRANineChecks` client after its stage-80
`IPRANineCurrent` endpoint. The author and peer stage-81 source hashes,
output object hashes, complete compiler logs, selected direct dependencies
and recorded candidate/companion guards match after normalizing the two
overlay-root paths. Both guarded ledger checks pass. The direct stage-80
endpoint object hash also matches between the two providers.

The matching log reports all 15 names explicitly listed in the source,
including the native, standard and equality-only `IPRANineCurrent`
equivalences. Each report names only Lean's metatheory axioms `propext`,
`Classical.choice` and `Quot.sound`; this is not a list of object-theory
axioms. The companion stage-80 comparison is documented in the
[stage 76–80 packet](../nine-variable-ipra-peer-stages-76-80/README.md).
The endpoint's transitive chain contains differing-hash stage-70 objects and
other earlier object differences, so this is not an exact paired replay of
the entire endpoint closure.

[`audit.py`](audit.py) checks both live ledgers, exact stage-81 records and
the 15 source-named reports. [`capture.py`](capture.py) retains the source
snapshot, receipts, dependency listings, compiler logs, audit output and
terminal receipt under [`observations`](observations/). Repeating it requires
the live `/tmp` overlays. Guards are sampled; historical project,
package-transitive and dynamic ancestry remains inherited. This packet does
not authenticate the full closure or bind a displayed PDF.
