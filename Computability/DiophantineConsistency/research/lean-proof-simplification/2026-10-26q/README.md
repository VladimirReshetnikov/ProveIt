# Additional Lean proof simplifications after the existing roadmap

Prepared for Vladimir Reshetnikov, 26 October 2026.

## Start here

Read `report/new-proof-simplifications.pdf` (13 pages). Its complete LaTeX source is
`report/new-proof-simplifications.tex`. The proposals are grounded in ProveIt commit
`9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9`.

All ideas in the six placed packets and five incoming ZIPs are treated as already
applied, including notes-only suggestions. The audit records 56 grouped excluded
mechanisms; it is a scoped nonduplication screen, not a literature novelty claim.

## The five proposals

1. **Remove two unused internal inductions.** Replace zero-sum and zero-product
   inductions by the existing internal zero/successor decomposition. The preferred
   patch moves the decomposition into a low-level module. Semantic core checked;
   actual object-module patches are not compiled here.
2. **Use positive Pell classification to exclude negative norm.** Square a
   hypothetical norm-minus-one solution, use the first-coordinate congruence of
   powers of the existing fundamental unit, and conclude `2*n` divides `2`.
   Standalone proof and both proposed arithmetic modules checked.
3. **Normalize three obstructions to one existing discriminant theorem.** Keep
   `ShortEquation.strong_ne_neg_one`; three ring substitutions replace duplicate
   modulo-four certificates. Exact adapter proofs checked against rebuilt source.
4. **Equality at heterogeneous block minima.** Replace five nonlinear consequence
   searches by one finite-sum equality theorem, retaining the coupled norm block.
   Full modified `MinimumNorm.lean` checked. The old minima75 specialization already
   inherits this theorem; it needs no independent rewrite.
5. **Monotone certificate closure.** A checked, axiom-free generic union/insertion
   interface for `ObjectCodeBound`. Optional: one current client, uncompiled adapter,
   no claimed net source-size benefit yet.

## Measured effects and boundaries

All measurements compare raw pinned source, not an invented tree in which every
previous proposal has been implemented.

- Internal production extraction: **30 fewer physical lines**, including overhead;
  exact patch applies, actual repository module build remains.
- Pell descent and wrapper: **49 -> 33 nonblank declaration/proof lines**. Existing
  unit foundation (34 such lines) moves unchanged and is neither new code nor savings.
- Discriminant reuse: **12 fewer physical lines**, four residue certificates -> one.
- Minimum saturation: theorem body **13 -> 9 lines**, `nlinarith` calls **5 -> 0**;
  helper/import overhead means **7 extra physical lines** at its one current client.
- Combined discriminant/minima patch: two files **866 -> 861 physical lines**.
- Closure prototype: no net-size claim.

There was no full-project build, full `ShortSystem` build, full edited
`NativePellBootstrap` build, or object-model source-patch build. The report and
validation receipts distinguish these from the successful arithmetic module checks.
No repository commit or push was made.

## Directory guide

- `report/`: PDF, LaTeX, and build script.
- `internal/`: axiom-free semantic core; exact minimal and preferred production
  patch alternatives; current originals; complete proposed sources; metrics/logs.
- `pell/`: standalone proof; three-file migration patch; actual proposed modules;
  endpoint axiom audit; mathematical explanation and metrics.
- `minima/`: two sequential patches and a combined alternative; standalone
  mechanisms; complete replay source files; logs and endpoint axiom audits.
- `closure/`: axiom-free generic core and independent adapter review.
- `baseline/`: exact selected current Lean source files, for review only.
- `evidence/`: exclusion audit, corpus manifest, source hashes, independent report review.
- `validation/`: final replay receipts and PDF quality check.
- `scripts/replay_checks.py`: portable replay of precisely the checks claimed.

## Reproduce the checked proofs

Use Lean **4.32.0** and mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`.

With an already configured ProveIt checkout (the script does not edit it):

```sh
python3 scripts/replay_checks.py --project /absolute/path/to/ProveIt --out /absolute/path/to/replay-output
```

Or create a standalone dependency environment from this directory:

```sh
lake update
lake exe cache get
python3 scripts/replay_checks.py --project . --out /absolute/path/to/replay-output
```

The script checks compiler version and records source hashes. Verify the mathlib
revision with `git -C .lake/packages/mathlib rev-parse HEAD`; the included Lake
configuration pins it. Dependency download is not part of the archived receipts.
The two arithmetic replays use separate output directories so the new Pell module
cannot silently replace the old source used in the independent MinimumNorm replay.

**Patch alternatives:** use either `internal/production.patch` (recommended
architecture) or `internal/minimal.patch`, never both. For minima/discriminants,
use either `minima/minima-and-obstruction.patch`, or apply `01-negative-norm-reuse.patch`
then `02-minimum-saturation.patch`; never apply the combined patch in addition.
The Pell patch is separate. Apply only to a disposable checkout when evaluating
integration. `git apply --check` is a text-applicability check, not a Lean proof check.

The `baseline/` and uncompiled candidate source directories are review artifacts;
do not treat them as additional checked results merely because they end in `.lean`.

## Rebuild the report

Run `sh report/build.sh` with a standard TeX Live installation (pdfLaTeX,
Latin Modern, AMS packages, microtype, booktabs, longtable, listings, xurl,
hyperref, fancyhdr). No external images or bibliography downloads are required.

## Licenses and provenance

Repository-derived code retains the ProveIt MIT No Attribution license, reproduced
in `LICENSE-ProveIt.txt`. This package does not redistribute Mathlib itself.
Primary source URLs and immutable revisions are in the report and manifests.
The included `SHA256SUMS` covers final deliverable files except itself.
