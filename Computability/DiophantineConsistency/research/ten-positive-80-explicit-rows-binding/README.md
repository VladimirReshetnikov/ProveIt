# Explicit 80-row Lean presentation

`DisplayedRows.output_eq` is a checked Lean theorem: for arbitrary four integer
ports, the explicitly listed 80-register `Expr` output is definitionally
equal to the selected `Direct80Graph.graph` output. The ten variable slots and
four port slots are explicit in the Lean source. The accepted guarded check is
`observations/attempt01/`, producing
`/tmp/displayed80-rows-msc3s0w3/DisplayedRows.olean`, SHA-256
`aeafe96a70f42a594e30adaf5397289b5155c98c6d481fcdf4e8bffc30956eff`.
Its axiom report lists `propext`; no `sorryAx` was reported. The runner pins
the direct `Direct80Graph` object, source and Lean executable and samples
resources; project transitive, package, dynamic and source-to-object ancestry
are inherited.

Separately, the read-only `check-rows.py` run in `rows-check.stdout`
externally compares all 80 Lean register definitions, variable and port
slots to the pinned original-kernel JSON and PDF-extracted text. It also
checks the output register. That is an external text comparison, not a Lean
parser theorem about the JSON or PDF. It does not bind printed coefficient
recipes to Lean constants. The file/constant correspondence remains an
external evidence boundary; `output_eq` alone does not state an iPRA
derivation or transfer any result to the distinct direct-BFS K0.

## Explicit-row iPRA endpoints

The later `DisplayedRowsIPRA.lean` applies `output_eq` to the fixed symbolic
80-graph endpoints. It directly states all four no-premise derivability
theorems for the explicit Lean row expression after the single positive shift:
standard and equality-only reference iPRA, each with mapped native refutation
negation or the selected Gödel–Gentzen-translated Foundation consistency
sentence. This is a Lean theorem about the explicitly written Lean rows and
the selected fixed symbolic ports; it does not parse the TeX, PDF, or JSON,
nor prove the printed constant recipes equal those ports. The original-kernel
and direct-BFS coefficients remain distinct.

The bounded author check `observations/ipra-attempt02/` passed with outer
process exit 0, empty stderr, four reports exactly
`[propext, Classical.choice, Quot.sound]`, and object
`/tmp/displayed80-ipra-euiu0tvn/DisplayedRowsIPRA.olean` SHA-256
`128c42d9aeda9fa2cebb1faa84115bf7300d165d9233e5159a1f3685b2d7d547`.
The run selected the checked `DisplayedRows` object and the fixed endpoint
from the audited 127-module rebuilt union, and pinned the shared graph object.
It did not itself independently replay that union or authenticate its entire
project, package-transitive, dynamic, and historical ancestry. The first
attempt is retained: its missing namespace caused errors and incomplete
axiom reports, and it is not accepted. The runner was then adjusted to
recognize Lean's multiline axiom reports and the source was corrected; the
attempt source copies and result files preserve both observations.

Source SHA-256 is
`fd36492f39119d761fb23adf835bc922c8e8ed092aed7e1ec88aac7b4844c585`;
runner SHA-256 is
`a6eca372ba8dc7f091bb926c221d62a7e782f231af2053e1f04b373657d9e839`;
the external-check script SHA-256 is
`f625c008c9d632b724bbc59f2a9464458482ff8834695bb2ec7ced427f281f15`.
