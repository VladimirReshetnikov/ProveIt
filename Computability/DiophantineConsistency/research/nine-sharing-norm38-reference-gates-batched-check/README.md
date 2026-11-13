# Checked bounded reference-gate batch

Actual outer session `25860` exited 0: all twelve groups and the universal
60-gate assembly compiled. The assembly's axiom report is `[propext,
Quot.sound]`. The [independent terminal audit](../../reviews/nine-sharing-norm38-reference-gates-batched-terminal-independent/README.md)
checks the retained sources, objects, logs and direct provider guards; it did
not replay Lean or independently observe the historical outer exit. Initial
static/reference agreement and the source/seed and iPRA bridges remain open.
The prelaunch description below records the original plan.

This 13-stage runner checks the source-only plan in `../nine-sharing-norm38-reference-gates-batched-draft/`: twelve groups each propose five reference-gate equalities, then a separate assembly proposes the universal 60-gate reference-equation theorem. Each group uses the checked concrete reference-base producer, and the assembly imports the twelve fresh group outputs. Group proofs use `rfl` at recursion depth 4,096. This check alone does not prove static/reference initial agreement, source/seed equivalence or an iPRA endpoint.

The runner checks the successful reference-base source/object/log/direct guards and inherited overlays, source snapshot versus the generated draft, manifest order and imports; it verifies that any dependency produced earlier in this run resolves to the exact recorded fresh object. It captures per-stage logs, exit/monitor states and direct provider guards, rejects errors/`sorryAx`, and stops at first failure. Per-call bounds remain `-M2800`, 4-GiB sampled session RSS, 10-GiB host floor and 120 seconds; package/dynamic ancestry and sampling gaps are inherited. Fresh no-Lean preflight passed; independent prelaunch review and shared-slot coordination precede any Lean execution.

Manifest SHA-256 `f1bcea19ffbb926edaa3cff8e455ff0e0b63b9698f6ab3b28ae7ddbe9fc6ee20`; runner `da96ae87bd9d90819aba563e84e757c090af9d3e4b99acc01e8f2c80d078b589`. The generated source plan's pins and limitations are recorded separately in its README.
