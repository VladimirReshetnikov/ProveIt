# Checked table interpreter and packed data

Fresh Lean checks complete the remaining three prerequisites for binding the
exact 240-state decoder to its packed register program:

| Module | Checked scope | Axiom probes / typed callers |
|---|---|---|
| `PackedTables` | Packed row lookup implies the corresponding list entry; exact table length | 2 / 4 |
| `ArithmeticControlTable` | Compact lookup, represented step, total internal-time run and exact row semantics | 10 / 12 |
| `BisimCertRotation240` | Existing packed data declarations, row count 6,455 and typed table interface | 2 / 4 |

All **14 probes and 20 callers pass with zero warnings**. These are checks of
the unchanged maintained sources. The certificate-data audit does not evaluate
the full bisimulation certificate or prove equality with the decoder catalogue.
Those are separate propositions.

Actual records: [packed lookup](packed-tables/verification.json),
[interpreter](control-table/verification.json), and
[concrete data](bisim-cert/verification.json).
Their source/audit times were 1.730/1.422, 16.572/2.188 and 9.380/1.398 seconds.
Each check shared a 120-second deadline with one thread and 4,096 MiB. The
interpreter retains its existing local recursion/heartbeat limits of
8,192/4,000,000; the other two sources and all three audits use default proof
limits. Only standard Lean axioms occur.

The guards select respectively 23, 34 and 24 project prerequisites, with
three explicit external cache boundaries and Init/Omega. They reuse actual
completed parent checks, capture fresh objects before their audits and check
input identities afterwards. No dependency rebuild or whole-cache attestation
is claimed. The [publication record](publication.json), per-module guards and
raw logs, and [history](history.json.gz) preserve the exact executions and
source reviews with historical scratch paths.

Together with the [earlier control prerequisites](../control-prerequisites/README.md)
and [counted tree](../counted-tree/README.md), these supply the inputs to the
finite packed-row binding proof. The arbitrary-internal-time binary simulation
and final PA consistency equivalence remain open. Attribution remains with
the original source modules and their cited machine and calculus authors.
