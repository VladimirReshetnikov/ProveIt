# Additional Lean proof simplifications after the prior proposal corpus

Prepared for Vladimir Reshetnikov, 26 October 2026.

Read `report.pdf` or the matching `report.tex` first. This packet supplies
three proof-only integration candidates and one conditional structural idea.
The three complete candidate modules remove **23 physical lines** in total:
335 to 322, 184 to 178, and 104 to 100. The count includes the new helper and
import. Six affected theorem statements and all executable definitions are
preserved. These are source measurements, not compiled production results.

## Comparison scope

The source measurement pin is
`89226e3921bce3e8949fadd12d3efb6914c7630c`.
The proposal audit was refreshed through
`663fb267f6142ca4c0ea5bcd2d4f607f9a4b0eda`.
The final tree check through
`e429ae09c367c28602613d1d7351a96968aa2f93` found no subsequent change in
either proposal root or any of the four candidate target files.
That refresh contains 23 placed packets (a-w) and five incoming ZIPs. All
their ideas, including deferred designs, are treated as available. The
three patch targets are unchanged between the two pins.

The incoming refresh adds one more proposal archive. See the freshness
supplement in `evidence/`; do not mistake the initial four-ZIP inventory for
the complete final comparison scope.

## Candidates

1. `01-tail-cutoff.patch`: negate the existing strict position/weight iff to
   derive the weak suffix cutoff, then normalize its successor conditional.
   No helper or import; 13 net lines removed.
2. `02-prime-factor-order.patch`: index exact-order tests by the prime
   divisors of the candidate order. One private helper and one import;
   six net lines removed. The closed `by decide` calls require project replay.
3. `03-bounded-complement.patch`: use the existing bounded subtraction
   injectivity theorem with only the required tile-color bounds; four lines
   removed. This is an optional local cleanup.
4. `lean/proposed/ControlSlotInvariant.lean`: a proof-side update view of the
   independent numeric controls at positions 977 and 1004. Its core invariant
   is checked, but its full production binding is uncompiled and its helper
   cost has not been shown to pay back. It is not included in the patches.

The full candidate modules are review references. If earlier proposals have
reorganized surrounding code, rebase the small proof changes; do not overwrite
the updated modules with these snapshots.

## Validation actually performed

- All four `lean/checked/*.lean` files compile with Lean 4.32.0 using only Init.
- Their printed axiom sets are empty or contain only `propext`; no `sorryAx`.
- The exact ordinary modular periods 23 (modulo 47) and 402 (modulo 2011)
  are independently checked, including every smaller positive exponent.
- All three patches and their combined patch pass `git apply --check`.
- Six edited statement headers are textually unchanged. Full module metrics,
  file hashes and compiler logs are included.

**Not performed:** a complete Mathlib-dependent compilation of any changed
production module, the proposed Function.update binding, downstream checks,
or production axiom/performance comparisons. The standalone files take
upstream facts as explicit hypotheses where necessary. They do not replace
or silently certify the repository's imported proofs.

Replay the checks from this packet's directory:

```sh
python3 scripts/verify_core.py --lean /path/to/lean-4.32.0/bin/lean
python3 scripts/check_candidates.py --repo /path/to/pinned/ProveIt
```

## Project integration gate

In a disposable checkout with the repository-pinned dependencies, first run
`git apply --check` on `patches/combined.patch`, then apply it. Build the three
changed modules, their existing check modules, and the affected direct
consumers:

```sh
lake build DiophantineConsistency.CurrentSelectorTail2011 \
  DiophantineConsistency.CurrentSelectorTail2011Checks \
  DiophantineConsistency.CurrentEarlyPadding2011Checks \
  DiophantineConsistency.CurrentControllerData2011 \
  DiophantineConsistency.CurrentControllerData2011Checks \
  DiophantineConsistency.CurrentTileColors2011 \
  DiophantineConsistency.CurrentTileColors2011Checks \
  DiophantineConsistency.CurrentMarkedWindow2011Checks
```

Compare the existing public axiom reports with the unmodified checkout and
record actual elaboration cost for the two finite factor certificates.
If those certificates reduce poorly, retain the same finite-prime interface
but enumerate the three explicit modular tests; recalculate the source cost.
No new claim about the equation's reverse direction, full controller, or
ZFC consistency equivalence follows from these proof-only edits.

## Contents and reproducibility

- `report.tex`, `report.pdf`: complete article.
- `patches/`, `candidates/`: small diffs and complete reference modules.
- `lean/checked/`: four standalone mathematical/proof-pattern checks.
- `lean/proposed/`: explicitly uncompiled production prototype.
- `evidence/`: source pins, comparison inventories, freshness supplement,
  exact metrics, nearest prior ideas, and independent reviews.
- `validation/`: compiler receipts and full logs.
- `scripts/`: read-only candidate checker, standalone replay, PDF build.
- `MANIFEST.sha256`: identities of the delivered files.

The archive contains no toolchain, dependencies, downloaded prior reports,
or source repository checkout. It is intended for review and possible
placement under `docs/incoming`, not automatic publication or application.
