# Post-adoption Lean proof simplification

This third review is pinned to ProveIt commit
`22e020937caa81d0cb72a4f63071d6c0bcc1eba9`. Start with
`report/proof_simplification_report.pdf`; its TeX sources and build script
are included.

## The prior proposals are the assumed baseline

All outcomes advertised in both requested proposal collections, and the
previous delivered study, are treated as already available for novelty
screening. The six proposals here remove remaining proof work beyond that
baseline. `baseline_audit/ASSUMED_APPLIED_BASELINE.md` organizes the prior
outcomes into 18 contracts. Its 115 ledger rows overlap and are not 115
independent ideas.

The exact checkout is documented separately: 27 recent commits, an
authoritative 34-added/32-modified active Lean file delta, and 608 active
Lean files. Observed adoption and the assumed completed baseline are not
conflated. Mutually exclusive old patches are represented by their compatible
semantic outcomes, not falsely claimed to form a buildable combined patch set.

## Proposed work

- `machine/`: equality reflection for halt encoding, a write-location-only
  proof split, and the existing sharp absolute-value interval view.
- `encoding/`: the standard last-slot Option–Fin equivalence for the unchanged
  terminal-state encoding.
- `rows/`: guarded translated integer induction and an optional shared bond
  signal for west/east edge proofs.

Five proposals preserve the old theorem interfaces. The bond-signal variant
normalizes two intermediate edge statements and is a structural tradeoff,
not a line-count saving. Its final horizontal matching statement is unchanged;
compatibility with callers of the old intermediate statements must be reviewed.

## Evidence and limits

Every new Lean candidate is **uncompiled**. No Lean/Lake runtime was available
and none was installed. The source-only checks and mathematical review are
not substitutes for elaboration, kernel checks, actual axiom output, or
performance measurement.

The archive contains 860 verified selected source/configuration/review files
under `sources/`, plus five separately verified BusyBeaver dependency sources.
This remains a focused snapshot, not a standalone Lake project. Six patches
were checked and applied only in disposable copies. The supplied snapshot and
upstream repository were not modified.

`baseline_audit/` contains the prior-work ledger, conflicts, novelty decisions
and source bindings, not copies of all eleven prior archives. Its optional
`verify_baseline.py --repo /path/to/full-pinned-checkout` checks those corpus
bytes in an existing checkout without network or mutation. It cannot run on
the focused `sources/` folder because the prior packets are not bundled.

`validation/` identifies reused support, four future Lean probes, nine named
axiom targets, source checks and negative tests. Its replay requires the full
pinned checkout, existing Lean 4.32.0 toolchain and prepared baseline imports.
It performs no installation; even a successful future probe run would not
replace downstream integration and regression checks.

## Offline checks

Before generating extra files in the extracted package:

    python3 -B verify_bundle.py --strict
    python3 -B provenance/verify_snapshot.py
    python3 -B validation/source_validate.py
    python3 -B -m unittest discover -s validation -p 'test_*.py'
    python3 -B rows/check_semantics.py

The byte manifest checks internal package consistency, not the publisher.
Run strict mode before generating build caches; omit `--strict` later to allow
extra files. Modified listed files still fail their hash check. Individual
proposal directories contain deterministic patch/metric regeneration scripts.

The archive root is `LeanReview3`. The PDF build uses XeLaTeX. Future Lean
replay targets Linux/WSL with Bash and GNU-compatible utilities. Original
repository licensing is retained in `sources/LICENSE`; pinned Mathlib source
and license evidence accompanies the relevant examples.
