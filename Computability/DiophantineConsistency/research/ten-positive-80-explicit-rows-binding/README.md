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
external evidence boundary; this packet does not itself state an iPRA
derivation or transfer any result to the distinct direct-BFS K0.

Source SHA-256 is
`fd36492f39119d761fb23adf835bc922c8e8ed092aed7e1ec88aac7b4844c585`;
runner SHA-256 is
`a6eca372ba8dc7f091bb926c221d62a7e782f231af2053e1f04b373657d9e839`;
the external-check script SHA-256 is
`f625c008c9d632b724bbc59f2a9464458482ff8834695bb2ec7ced427f281f15`.
