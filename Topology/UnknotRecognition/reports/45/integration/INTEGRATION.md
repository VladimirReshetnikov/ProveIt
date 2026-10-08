# Integration contract: do not turn a local arithmetic result into an unchecked verdict

## Reviewed interfaces

The audit observed `main` at `c4c23b61d844b465b9ee30d0cebb02af82050306` and read the individual blobs in `data/provenance.json`. It did not checkout or run the whole maintained project. The read-only adapter matches the inspected `WordArena` empty/t/c schema and charges its cooperative `tick()` callback.

The existing `compressed_search._search` success contract is one surviving generator and no nonempty relators. Its wrapper records `remaining_generator`. A two-generator primitive-power terminal must **not** be implemented by returning True under that old contract.

## First integration phase: telemetry only

At an intact search state, before a costly general Whitehead/overlap phase, log rank, root cyclic-reduction flags, support sizes, compressed nodes, length bits, query/replay work, and whether the arithmetic kernel finds a primitive power. Charge input remapping and query work. Keep every original root slot and input-to-presentation trace. The initial source conversion uses free reduction, not necessarily cyclic reduction: explicitly check this precondition before querying.

Measure activations before deciding a dispatch threshold. Preserve zero-activation cases, negative results, and resource-capped cases. Do not quote the shipped literal-baseline kernel ratios as production speedups.

## Second phase: a new positive terminal record

Use a new certificate version or an independently named method. A suggested payload, in addition to the original diagram and verified move prefix, is:

    kind: rank_two_primitive_power
    relator_slot: original current slot identifier
    generators: ordered pair of current generator identifiers
    primitive_vector: two exact signed integers
    exponent: positive exact integer
    width: nonnegative exact integer

The verifier must reconstruct the complete Wirtinger presentation from the validated classical, single-component planar diagram, independently replay the whole prefix, verify exactly two live generators, normalize or validate the selected root under charged resources, and derive/check the arithmetic evidence from that reconstructed root. Reject unknown versions and unexpected fields. Never accept a caller's Boolean assertion that an arbitrary group is torsion-free or is a knot group.

After these checks, the mathematical implication is: a relator `w^d` with primitive `w` and positive `d` kills `w` because the reconstructed knot group is torsion-free; the whole group becomes cyclic; its abelianization is Z; the knot is the unknot. The two generators need not be meridians. Their losing meridian markings still matters to other portfolio terminals and must not silently change those terminals' contracts.

All other relator slots remain part of the provenance chain. They need not individually be proved redundant for this positive theorem, but they may not be dropped before the presentation is certified. Resource exhaustion is inconclusive; it is never `KNOTTED`.

## Third phase: higher-rank projections

For disjoint generator pairs, local evidence supports `a -> t^v`, `b -> t^(-u)`. A fresh or consistently retained label represents t. Build all images before the old-grammar substitution pass. Keep the unselected relators as raw circuits, not implicit reduced words. A selected donor becomes empty only after its independently checked primitive-power projection.

Production adoption needs an independent complete projection-trace replayer, malformed-selection tests, preservation of all relator slots, explicit input normalization charges, and global bit/work/node limits. The supplied prototype checks local evidence but is not that independent whole-run replayer. It should remain outside a production knot-verdict path until this gate is met.

## Fourth phase: complete restricted endpoints

A certified two-generator one-relator endpoint is cyclic exactly when the normalized relator is primitive. The negative direction uses the Magnus normal-closure theorem; it is not valid for arbitrary multi-relator endpoints. A justified deficiency-one starting presentation and all relation deletions require replay evidence. The article proves the braid product-invariance justification, but the included braid demonstration retains every Artin relator and implements only the positive endpoint.

## Quantitative acceptance gate

A successful normalization-free d-round schedule costs a fixed polynomial in initial grammar/rank/relator/bit parameters times `2^O(d)`. To claim an end-to-end class bound, state a producer cost V(n), polynomial initial parameter bounds, a schedule-finding guarantee, and a decisive terminal guarantee. For `d=O(log^2 n)` the contraction contribution is `n^O(log n)`; without a universal producer this is not unrestricted quasi-polynomial recognition.

Before merging: run the maintained full suite; compare fresh randomized-order A/A/B whole recognition queries with replay included; retain timed-out/stalled cases as censored; report memory, grammar growth and activation counts as well as elapsed time. None of these full-maintained-suite or whole-maintained-query gates is claimed completed by this delivery.
