# Data formats and trust boundaries

All JSON is UTF-8. The code rejects unknown top-level schema fields. Signed
integer costs use hexadecimal strings so very large values do not depend on
JSON number limits or Python's decimal-conversion digit limit.

## Grammar: `layered-disk-patches-v1`

`widths` is a nonempty list of positive interface sizes. `initial` and `caps`
are explicit lists of records with exactly `partition`, `cost_hex`, and
`sector`. `layers` has one fewer entry than `widths`; each layer is an explicit
list of patch records with those same fields. A patch at layer i has a partition
of `widths[i]+widths[i+1]` labels, with incoming labels first. Partitions are
canonical restricted-growth arrays beginning with zero. Every nonempty block
represents one disk. `sector` is an integer from zero through three, combined
by XOR. `target_sectors` lists the allowed terminal values without duplicates.
An empty target list admits no successful terminal sector.

All options at a layer are available independently of the current partition.
The source describes an abstract disk-patch language, not a knot diagram.
`examples/grammar.json` is a complete working source.

## Local certificate: `cycle-envelope-reduction-v1`

Fields are `schema`, `mode`, `source_sha256`, `retained`, and `expansions`.
`retained` lists distinct indices in the original candidate list. For every
original row there is an `expansions` list of distinct retained original indices.
Each indexed summand must have the same sector and cost no greater than the
source row. The checker reconstructs feature rows independently and checks the
XOR identity and the graded retained-size bound.

The source digest covers both envelopes and every source partition, hexadecimal
cost, sector, and witness path in order. The mode field is validated separately
and determines which feature identities the checker reconstructs. The checker is given that
source independently. A digest is source binding, not an argument that its
source envelopes safely contain all geometric contexts.

## Whole run: `cycle-envelope-run-v1`

The run binds `grammar_sha256` to the canonical serialized grammar. It records
`mode`, `status`, `cost_hex`, `witness`, `sector`, `stages`, and `statistics`.
A witness is the selected initial index, one option index per layer, and the cap
index. It is null if no assembly is found. `cost_hex` and `sector` are also null
for an unsuccessful complete search.

`check_run` regenerates candidates from the independently supplied grammar,
rebuilds envelopes by an independent whole-graph algorithm, checks every pruning
stage, and checks all terminal choices among the retained final family. Exact
mode uses `exact-dedup-v1` stage records instead of algebraic certificates.
The independent checker shares serialization and the candidate data container,
not the producer's cycle features, transitions, envelope compiler, or solver.

## Resource status and validation

The CLI reports `RESOURCE_LIMIT` with a reason on cooperative budget or
allocation-limit interruption. This is not a complete-run certificate. The
checker returns `(False, reason)` when it cannot verify a certificate, including
its own allocation guard. That outcome is not a negative existence result.
Malformed source input raises a validation exception and is not interpreted as
an empty search language. Cooperative budgets are checked at designated points,
not guaranteed hard real-time cancellation.

`surface_replay.py` checks a selected witness as a literal finite triangulated
surface. Its disk result checks abstract topology only. A production adapter must
add source-certified ambient embedding and boundary essentiality.
