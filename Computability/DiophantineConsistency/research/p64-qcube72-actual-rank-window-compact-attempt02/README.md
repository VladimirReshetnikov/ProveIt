# Compact rank-window specialization attempt02 — failed

This source replaces broad simplification of compact mask constants with targeted `change` and `Nat.cast_add`. The [observed guarded check](observations/attempt02/observation.json) nevertheless exited 1: Lean reported `(kernel) excessive memory consumption detected` at the theorem declaration under `-M2400`, with no sampled resource stop. Its axiom report includes `compact_window` itself, so no theorem is accepted. Exact source, log, runner, result and direct captured-provider guards are preserved; the successful generic actual-window theorem is separate.

A possible next source change is to prove symbolic low/high mask identifications first, then mark the three enormous compact port constants locally irreducible, as existing compact endpoint modules do. That approach has not been checked here and is not guaranteed to resolve the kernel limit. Any further attempt needs a fresh path and coordinated resources.
