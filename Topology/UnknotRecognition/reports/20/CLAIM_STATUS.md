# Claim status and review checklist

## Written proofs supplied

- Positive-weight nilpotent radical of the ungraded dotted matching category.
- Completeness of same-matching unit cancellation and uniqueness of its minimal
  matching-multiplicity profile.
- Minimal-truncation domination under nonnegative two-term extensions.
- Transfer of the **attributed** Kelomäki–Schütz binomial counts to exhaustive
  scanner cancellation.
- Uniform bit bound and its stated `n**O(log n)` parameter regime.
- Sound three-outcome probes and completeness of uncapped geometric restarts.
- Exact Reidemeister-II padding law for endpoint discrepancy depth.

These proofs are not independently peer reviewed or formally verified. Standard
algebraic ingredients are identified as such; no claim of priority is made for
them. An external reader should especially review the ordinary chain-isomorphism
splitting used before truncation, and the coefficient/grade-forgetting step in
the comparison with Kelomäki–Schütz.

## Implemented and executed in this package

- Readable reference scanner and independent cube-of-resolutions oracle.
- Retained-degree controller, mirror probes, nice-order certificates, CLI.
- 14 unit-test methods (two recorded successful runs).
- Separately counted audit: 100 cube cases, 393 window comparisons, 1,772 nice
  stages, 15 padding cases, zero failures in the recorded run.
- Six-input, three-repetition paired backend benchmark with raw measurements.
- PDF compiled and all 19 pages rendered for layout inspection.

## Prepared, not executed against upstream

- `integration/upstream_adapter.py` for `fastunknot.scan.ScanComplex`.
- Its upstream regression/benchmark acceptance checklist.

## Not supplied / not claimed

- An unrestricted quasi-polynomial unknot recognizer.
- A bound on shallow witnesses after the complete current simplifier.
- A uniformly cheap positive branch for all unknots.
- A complete production checkout, production-suite run, FastScan port, Rust
  port, Lean proof, or GitHub commit.
- An end-to-end speedup on inputs surviving the current production filters.
- Hard OS-level time/memory enforcement: ceilings are cooperative.

## Intended integration

Add this archive as an experimental research subdirectory, preserving its
sources and data. Do not replace the existing exact backend or interpret
`UNKNOWN` as either knot verdict. Enable an upstream window stage only after
its acceptance gates pass.
