/-
Added for ProveIt (not an upstream file; distributed under Apache-2.0).
Compatibility name used by the quantitative port. The proof delegates to
Mathlib v4.32.0's Isometry.lipschitz; no upstream proof text is copied.
-/
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false

theorem Isometry.lipschitzWith {α β : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] {f : α → β} (h : Isometry f) : LipschitzWith 1 f :=
  h.lipschitz
