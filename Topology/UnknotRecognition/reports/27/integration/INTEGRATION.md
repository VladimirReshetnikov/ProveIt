# ProveIt integration notes

## Baseline

The review target is commit `23893144e3aafd074a23cfb633222ab7e03e6d2e` and
`fast/fastunknot/simplify.py` blob
`2fcaabb51eaa45cf84bdee32cd1b4e18acf2c478`.  The existing default follows only
the most recent RIII move's neighbourhood.  This bundle does not change that
default.

## Files

1. Copy `clustered_r3_snippet.py` to
   `Topology/UnknotRecognition/fast/fastunknot/clustered_r3.py`.
2. Apply `connected_r3_simplify.patch`.
3. Thread `r3_search` and `r3_births` through `recognize.py` and the CLI only
after direct unit tests pass.  Suggested CLI spellings are
   `--r3-search last|clustered` and `--r3-births N`.

## Required checks before enabling by default

- Replay every emitted trace with the existing independent `replay` function.
- Compare reduced diagrams, verdicts, Alexander polynomials, and Khovanov ranks
  with the unchanged path on the maintained random corpus.
- Add adversarial tests in which two footprint-disjoint birth moves are needed
  before a connecting RIII move.
- Test budget exhaustion at every recursive boundary and ensure that failure
  restores the exact dart involution.
- Run the complete maintained test suite (431 tests at the reviewed commit),
  not merely this bundle's abstract tests.
- Benchmark successful and failed searches separately.  Failed deep search was
  already the expensive case in the existing implementation.

## Safety contract

The new search is only a preprocessing accelerator.  A successful trace is a
sequence of legal Reidemeister moves and must be replayed.  Failure is
inconclusive and must fall through to the existing exact recognizer.  No verdict
may be inferred from a depth or birth budget being exhausted.

## Status

The helper and generic prototype are syntax-checked.  Seven bundle tests pass,
including exact adapter restoration and inverse replay on a twelve-dart contract
gadget.  The abstract search was compared with an unrestricted finite oracle on
5,000 generated local rewrite systems and on an exhaustive 608,400-instance
three-site catalog, with zero recorded discrepancies.  The adapter was not
executed inside a full ProveIt checkout or on a validated PD diagram in this
environment, so it is a review artifact rather than a claimed production patch.

## Report 25 audit notes

The delivered helper suppresses only the exact inverse triangle, represented by
`frozenset(d ^ 2 for d in triangle)`.  Suppressing every move on the same three
crossings is a stronger, unproved pruning and is intentionally avoided.

The patch imports `clustered_r3` lazily inside the opt-in branch.  This preserves
the maintained default startup path; the reviewed package had previously found
module import cost to be material.  The generic reference search also keeps the
accumulated footprint in its memo key and does not prune solely on repeated
physical state.
