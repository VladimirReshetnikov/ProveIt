# Changes from the supplied fast/ implementation

## 0.2.0 — 2026-09-18

### New capabilities

- Exact one-sided modular Jones obstruction with boundary-state aggregation.
- Validated visible connected-sum cuts and a replayable decomposition tree.
- Compressed reduced homological polynomial products for connected sums.
- JSON evidence replay for all recognition methods.

### Faster existing algorithms

- Self-inverse unit shortcut in the F2 square-zero endomorphism algebra.
- Identity/endomorphism composition shortcuts.
- Bounded memoization of gluing, topology plans, decorated compositions and
  crossing/delooping entries.
- Lazy fill-in-aware Gaussian cancellation; stack policy retained for ablation.
- Identical greedy crossing order via adjacency updates and a heap.
- Linear sliding-window descending-diagram search in both traversal directions.

### Correctness and safety

- Relative incoming-port crossing signs; Alexander matrix adjusted consistently.
- Raw PD and complete scan-order validation.
- Finite/nonnegative deadline and positive-ceiling argument checks.
- More cooperative deadline checks; object ceiling checked during creation.
- Honest UNKNOWN behavior and explicit no-quasipolynomial metadata.
- Removal of the misleading width-only multiplicity claim from the new source.

### Validation and compatibility

- Preserved the original package/tests for comparisons.
- Retained the original recognize/Diagram/raw khovanov APIs, adding optional flags.
- Default recognition method choices change because of the new filters.
- CLI khovanov now uses visible factorization by default; --no-factor restores
  raw-scan semantics.
- Composition counters have refined semantics; do not compare their absolute
  values with the baseline as identical units.
- 48 final tests passed, with independent reference calculations and cold-process
  measurements. No formal verification or global asymptotic improvement claimed.
