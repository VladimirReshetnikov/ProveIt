# Two further simplifications of the GRH development

**Start with `paper.pdf`.** Its editable source is `paper.tex` plus `sections/`.

The recommended first change replaces the real-place majorant's triangular
negative-frame normalization with the original dual frame, its positive Gram
matrix, and a bordered determinant integral. The existing Hua inequality proves
the needed bound with **exactly the current public constant**. The source statement
and its `SchurOrbit` caller can stay unchanged.

A separate theorem recovers the auxiliary-place trace from finitely many
`tr(A T^j)`, rather than all `tr(A^(l+1) T^(j+1))`. It allows nonnormal `T` and
repeated eigenvalues. The complete mathematical proof uses a common zero-constant
interpolating polynomial for logarithmic spectral values.

## Scope and honesty about the implementation

- Pinned ProveIt revision: **f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f**.
- Analyzed directory: `Analysis/GeneralizedRiemannHypothesis/Lean/grh`.
- Comparison corpus: all **28** proposal bundles at that revision, including
  their relevant optional and future directions, plus **three later additions**
  at `51aa1e3b5807c635a6fb6244a9ce4678b9106bc6`. That later snapshot has 29
  current bundles after two retirements; the conservative exclusion review covers
  **31 distinct bundles** across the two snapshots. See `audit/`.
- The report contains general mathematical proofs and concrete source adapters.
- **611 gross affected source lines** are identified for the real-place
  replacement. They are **not** 611 net deleted lines. New helper proofs must be
  included in a future net count. No full module is claimed to disappear.
- Two standalone Lean files contain eight proved supporting declarations, checked
  with Lean 4.35.0 and the pinned Mathlib. They do **not** formalize the central
  spectral trace certificate or the Hua source adapter.
- The final formal trace-transfer theorem takes the two spectral trace identities
  as explicit hypotheses. Its successful compilation does not discharge them.
- The complete GRH project and the proposed source replacements were **not rebuilt**.
  This archive is a mathematical simplification proposal with checked supporting
  artifacts, not a completed source port or independent certification of GRH.

The real-place change has the clearest local shortening potential. The finite
trace theorem improves the mathematical contract; its net Lean line saving is
not yet established because several spectral-calculus adapters remain to be written.

## Contents

| Path | Contents |
| --- | --- |
| `paper.pdf` | Full report and proofs |
| `paper.tex`, `sections/` | Complete LaTeX source |
| `lean/` | Two checked Lean files, pinned Lake dependencies, and detailed scope README |
| `checks/` | Portable SymPy regression checks and a source inventory checker |
| `results/` | Check output, source map, source hashes, and provenance |
| `results/lean/` | Fresh compiler logs, exact commands, and source checksums |
| `audit/` | Baseline 28-row matrix and manifest, late three-bundle audit, and separate review notes |
| `notes/` | Longer source-oriented mathematical notes |
| `SHA256SUMS` | Checksums of the delivered files |

## Reproduce the mathematical checks

Python 3.10 or later and SymPy 1.14.0 are sufficient. A virtual environment is
optional; these scripts do not use network access or modify the source repository.

```sh
python3 -m pip install -r requirements.txt
make check
```

The individual commands, from the archive root, are:

```sh
python3 checks/check_trace_transfer.py --output results/trace_transfer_check_results.json
python3 checks/check_bordered_hua.py --output results/bordered_hua_checks.json
python3 checks/check_bordered_geometry.py --output results/bordered_geometry_checks.json
```

Expected results:

- Trace: **107 assertions, 11 examples**, with one explicitly labelled
  80-digit logarithmic numerical check; the other algebraic checks are exact.
- Bordered integral: **36 positive rational-complex examples**, eight identities
  each; **nine exact real Jacobian checks**; symbolic cancellations; exact
  scalar integral `pi/28`.
- Source-shaped geometry: **248 exact assertions, 11 examples**, including the
  zero-column edge case, positive dimension seven, both level branches, nontrivial
  determinant factors, and actual Bessel-unipotent translations.

These finite tests are regression checks accompanying the general proofs, not
proofs of the universal statements by sampling.

## Reproduce the source audit

Obtain a checkout of the pinned ProveIt revision, then run:

```sh
python3 checks/audit_sources.py /absolute/path/to/ProveIt --output results/source_audit.json
```

It checks the revision, counts **803 Lean modules and 476,849 physical source
lines**, traverses imports from `Main`, records relevant file hashes, and inventories
the proposed source replacement regions. Static import reachability is not a
declaration-level dependency or proof-term analysis.

The repository's proposal text is not duplicated in this archive. The manifest
records exact paths and hashes; the comparison matrix and report provide the
substantive exclusion analysis.

To reproduce the late-update inventory, both pinned commits must be present in
the checkout's Git object database. The checker reads them without changing the
working tree:

```sh
python3 checks/check_latest_proposals.py --repo /absolute/path/to/ProveIt --output audit/latest_proposal_manifest.json
```

It verifies the 28/29/31 directory counts, the 298 unchanged common proposal
files, the six new primary-text hashes, and the 16 unchanged source/dependency
files. It records the 22-file new text inventory. The mathematical overlap
judgment is documented in `audit/latest_proposal_addendum.md`; it is not inferred
automatically from a keyword search.

## Reproduce the Lean support

See `lean/README.md`. With the Lean toolchain manager installed, from `lean/`:

```sh
lake exe cache get
lake build
```

Those are portable reproduction instructions. In the authoring session, the
delivered sources were checked directly with the pinned compiler and a pinned
Mathlib cache plus a separate dependency overlay. The exact commands and both
exit-zero logs are in `results/lean/`. No `lake build` of this delivered package
is claimed to have been run. The six printed theorem endpoints use only
`propext`, `Classical.choice`, and `Quot.sound`.

## Rebuild the PDF

A TeX Live installation containing `latexmk`, pdfLaTeX, Latin Modern,
`microtype`, the AMS packages, `mathtools`, `geometry`, `booktabs`, `longtable`,
`tabularx`, `enumitem`, `xcolor`, `fancyhdr`, `listings`, `needspace`, and
`hyperref`, and `xurl` is sufficient.

```sh
make pdf
```

No shell escape, remote resources, bibliography download, or generated images
are needed to compile the report. All references are embedded in the TeX source.

## Attribution and novelty

The source repository attributes its proof to Levent Alpöge, with Claude.
This proposal analyzes the cited rewriting at the fixed revision above.
The finite interpolation and matrix-integration tools are classical; the
claim is a new local replacement relative to the **specified proposal corpus**,
not historical priority in mathematics.

Prepared 27 November 2026 (America/Los_Angeles).
