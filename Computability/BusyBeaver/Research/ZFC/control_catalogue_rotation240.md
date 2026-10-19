# Exact source/control correspondence for Rotation240

[`ControlCatalogueRotation240`](../../Lean/BusyBeaver/ZFC/ControlCatalogueRotation240.lean)
connects the 6,455 numbered controls to the actual decoded source paths and
four-field packed rows. It reuses the complete table-equality and site-coverage
proofs. Each control has an accepted path of length at most 64. Successor
resolution preserves the exact consumed path, including implicit zero bits,
and cannot select a default or unresolved node.

The [actual check](results/control-catalogue-rotation240-verification.json)
passes 16 axiom probes and 16 typed callers, with zero warnings and only
standard axioms. Source/audit times are 1.904/1.681 seconds under default proof
limits and a shared 120-second, one-thread, 4,096-MiB bound. Its 658 project
prerequisites reuse both completed finite proof families without replaying
them; three direct external providers and Init/Omega are recorded separately.

The [publication record](results/control-catalogue-rotation240-publication.json)
and [history](control-catalogue-rotation240/history.json.gz) preserve the
actual source, audit, logs and direct guard. This supplies the control/path
interface for the arithmetic simulation. Whole tape-frame correspondence
and internal binary execution remain separate obligations. Source, machine
and framework attribution follows the imported modules.
