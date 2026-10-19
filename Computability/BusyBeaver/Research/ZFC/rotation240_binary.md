# Checked external endpoint for the literal 240-state machine

`BinaryRotation240` proves that the exact blank-tape binary machine halts if and
only if the specified ZF proof calculus has a refutation, and also if and only if
the specified ZFC proof calculus has a refutation. The corresponding nonhalting
statements are equivalent to consistency of those calculi. These are external
Lean theorems. The internal PA formalization remains open; this result does not
assert unconditional consistency or nonhalting.

The [canonical table](candidate-rotation240/zfc_rotation240.tm) has 240 working
states, including startup, and a separate halt symbol. It has 480 transition
rows, uses only left/right moves, and starts at state 0 with the head at 0 on the
all-zero two-way tape. Its SHA-256 is
`508b55a6dfdf96a42f09c49e410e078ae7478a1d0257d78d25503b4da24541cd`.
The publication check compares every row with the literal `TableRotation240`
source selected by the actual proof. The Lean configuration represents this
blank tape by the empty finite-support tape; the theorem uses that exact start.

The proof combines four checked parents: the positive runtime simulation,
the full-tape frame after 409,691 startup steps, complete decoder coverage for
`SourceRotation240.program`, and the calibrated register-source theorem.
Coverage is the fresh direct240 family: 530 cuts and 529 structural joins over
6,455 leaves and 8,386 guards, represented by 561 generated modules and four
reused direct240 pilots. Its 1,062 probes and 1,066 callers belong to that
separate family. The endpoint imports 801 project prerequisites plus `Init` and
`Lean.Elab.Tactic.Omega`; it selects no earlier-machine decoder-coverage module.

The [endpoint source](../../Lean/BusyBeaver/ZFC/BinaryRotation240.lean) and
[typed audit](rotation240-binary/Audit.lean) passed with nine named axiom probes,
nine typed callers and zero warnings. The source took 0.721152 seconds
and the audit 0.525235 seconds. The check used one shared 120-second
deadline, `-j1 -M4096`, and default proof limits. All 6607 recorded
inputs were checked before and after, and the fresh source object and its first
provider were captured before the audit. The
[raw actual record](results/rotation240-binary-verification.json) has SHA-256
`a4f698c8efac71fb5522078afd5a8c6c0a1ec2bd2503b90f5e3c093ca4f16f65`. Its axiom reports contain only Lean's standard `propext`,
`Quot.sound` and `Classical.choice` boundary, with the exact subsets retained.

The [review wrapper](results/rotation240-binary-review.json) binds the selected
actual review, four-parent freeze, explicit prepare-only receipt and stored
pre-proof preparation. The [publication index](results/rotation240-binary-publication.json)
and [compressed lossless history](rotation240-binary/history.json.gz) preserve
the original records, raw logs, scripts, source/audit snapshots, independent
guard review and unexecuted guard-schema correction drafts. History stores each
distinct text once and retains every original path as an alias. It excludes
compiled objects and symlinked import caches. Publication itself performs no
proof execution.

The [archived guard](rotation240-binary/check.py) and
[manifest](rotation240-binary/endpoint-manifest.json) are the exact executed
bytes. They retain the recorded historical source and cache paths. With those
providers available, a new external `--prepare-only --output /tmp/NEW-DIRECTORY`
checks the boundary without compiling. A clean-checkout dependency rebuild and
fresh attestation of every ancestor cache are separate work.

The original calculus, set theory, source program and 254-state construction
remain credited to Mira-Cult; Jeff Ketchersid's upstream verification,
Andrew James Wade's compiler framework, and ProveIt's earlier source, routing,
startup and fold reductions retain their attribution. The current incoming
report supplies the second transfer-loop rotation and its concrete composition
with the 90-to-72 fold. The [candidate attribution](candidate-rotation240/ATTRIBUTION.md)
and licenses remain unchanged. This endpoint connects those exact supplied
machine bytes to the retained proof-calculus definitions; it makes no priority
claim for the general transformations.
