# Checked prerequisites for the arithmetic control interpreter

Three existing Lean modules now have fresh source compilations and typed
client checks. They supply the generic catalogue, register-file algebra and
halting transport needed by the exact 240-state arithmetic simulation.

| Module | Result checked | Axiom probes / typed callers |
|---|---|---|
| [`ControlCatalogue`](../../../../Lean/BusyBeaver/ZFC/ControlCatalogue.lean) | Complete leaf-path enumeration, no duplicates, counted-tree rank and Braun-tree lookup | 6 / 6 |
| [`ArithmeticControlFile`](../../../../Lean/BusyBeaver/ZFC/ArithmeticControlFile.lean) | Nine-register code bijection, projections, writes and live-state encoding in every IOpen model | 9 / 11 |
| [`ArithmeticControlBisim`](../../../../Lean/BusyBeaver/ZFC/ArithmeticControlBisim.lean) | Offset-segment certificate soundness and two-sided halting transport in every IΣ₁ model | 10 / 10 |

The last theorem keeps all certificate, file, step and run laws as explicit
premises. Both simulated clocks advance positively and can exceed every
internal time bound, including nonstandard bounds. A finite certificate check
therefore suffices for the generic halting equivalence once its concrete
premises are supplied. This check does not instantiate the 240-state table or
establish its arithmetic simulation or PA consistency equivalence.

All **25 probes and 27 callers pass with zero warnings**, using only standard
Lean axioms. The exact actual records are
[catalogue](control-catalogue/verification.json),
[file](control-file/verification.json), and
[bisimulation](control-bisim/verification.json).
Source/audit times were respectively 1.983/0.252, 12.645/1.986 and
23.039/2.112 seconds. Each pair shared a 120-second deadline, one thread and
4,096 MiB. Catalogue used default proof limits. The unchanged file module and
the bisimulation module retain their existing local limits of 8,192 recursion
depth and 4,000,000 heartbeats; their audits add no overrides.

The first bisimulation check passed with two unused-simp warnings. Removing
only those two arguments produced the clean second check; theorem statements
and the audit are unchanged. Both attempts and the original source are in
the [history](history.json.gz).

The selected project prerequisite counts are 5, 11 and 22, with respectively
0, 2 and 3 explicit external cache boundaries. Each guard checks actual first
providers and captures its fresh object before the audit, then checks all
input identities afterwards. The existing dependency caches are reused;
there is no dependency rebuild or whole-cache attestation. The records retain
historical scratch paths rather than providing a clean-checkout build package.

The [publication record](publication.json), per-module guards, audits and raw
logs preserve the executions. The compressed history also includes source
reviews and the two-argument cleanup. The generic segment construction follows
`RMBisim` and the upstream work of Mira-Cult and Jeff Ketchersid, as attributed
in the source. The next concrete obligation is to bind the packed 240-state
table to its exact decoder tree; the [W6 route](../w6-route/README.md) records
the remaining arithmetic runtime work.
