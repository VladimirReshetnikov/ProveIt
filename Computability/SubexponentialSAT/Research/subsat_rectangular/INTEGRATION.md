# Integration notes

Suggested destination:

    Computability/SubexponentialSAT/Research/rectangular_streamed_refinement/

Place the archive's inner directory there, retaining relative paths between
report.tex, sections/, code/, and the replay scripts.

## Proposed index summary

Title: Rectangular contraction, multistage streamed conditioning, and
asymmetric Hermite precision barriers.

Reviewed through ProveIt dde01c4a63b822c25b8eb345299346c36f837b49,
including all five packets placed by 450252e9d86c155f188b485629b9755c5c665371.

Two generic normalized-wire refinements:

1. Polynomial space: coefficient 53.9775311981 (safe eventual 54),
   from the newest streamed separator identity combined with a strict
   multistage arity/range schedule. The comparison includes both the
   latest displayed 55.7094783189 and the stronger compatible 55.4046659066.
2. Cached: time coefficient 33.9938908592 and space coefficient
   33.9937208906 (safe eventual 34/34), from a genuine rectangular
   multiplication bound, exact coordinate/CRT arithmetic, binary block
   tables, and fully charged recursive group functions.

All coefficients multiply s/sqrt(log2 s), with s the same normalized
Boolean wire budget. The unrestricted and fixed-density SAT logarithmic
orders remain unchanged. The cached method uses subexponential space.
The reported improvements compare upper-bound functions, not measured
runtimes.

## New research components

- sections/rectangular.tex: rectangular field-to-ring lemma and complete
  cached contraction recurrence, including input/output storage.
- sections/polyspace.tex: strict rational streamed schedule and complete
  polynomial-space proof.
- sections/hermite.tex: extension from symmetric tapers to arbitrary
  node multiplicities for the fixed independent-error Hermite certificate;
  exact finite minimax formula and integer enclosure.
- sections/inventory.tex: adaptive-integral-basis inventory and explicit
  exact-weight table barrier on an actual Cauchy family.
- sections/table_barrier.tex: scoped norm-ball tree/profile certificate
  limitations, carefully distinguishing fixed and adaptive choices.

## Dependencies to preserve

Do not relabel the imported source ETH argument or earlier packet theorems
as independently verified here. Preserve citations to the source contraction,
asymmetric packing, full Cauchy modes, exact precision, latest streamed
conditioning, and matrix multiplication paper.

Do not multiply the newest adaptive packet's sqrt(17/24) streamed saving
into the cached coefficient. It improves a different recurrence.

Do not suppress the epsilon overhead in the near-quadratic rectangular
branch. This is why the exact cached time and space constants differ.

Do not claim optimality over every possible schedule, domination of
unreported constants in the separate Claude manuscript, or dominance
over lower-degree branches under stronger premises.

## Replay and repository policy

Run verify_manifest.py before regenerating certificates. run_checks.py and
build_report.py are local and require no network access. The generated
_build directory is not needed for integration.

MANIFEST.sha256.json is intentionally named to match existing packet
conventions. If repository policy requires an omission, record that
omission explicitly; do not omit imported modules that a replay script uses.

This deliverable did not push a branch, create a pull request, or change
the remote repository.
