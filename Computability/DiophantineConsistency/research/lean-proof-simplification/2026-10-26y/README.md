# Further Lean proof simplifications

This bundle presents seven further recommendations for ProveIt's
DiophantineConsistency development. It treats every prior proposal as already
available and separates exact checked mathematics from uncompleted integration.

## Read first

- `report/report.pdf` is the complete report.
- `report/report.tex` and `report/validation-summary.tex` are its sources.
- `evidence/VALIDATION.json` states each check's scope and result.
- `evidence/EXCLUSIONS.md` and the closing-audit addendum document novelty.

The primary source baseline is
`553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.
The closing review is
`e652d21c413de59e4821f6e8e9b6a3a077bf5bfe`.
The targeted production files are unchanged between those commits. The closing
audit includes the ingestion of the twelve original incoming archives and the
three additional research packets s, t, and u. Toolchain: Lean 4.32.0; mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`.

## Recommendations

1. **Prune non-extremal rows in `index_span`.** For k < 21, the target bound
   already settles the exponent for every natural pair weight. Only the five
   supported entries of row 21 require inspection. This removes 131 of 136
   support-dependent obligations. The complete private declaration is 92 → 11
   physical lines against the actual baseline.
2. **Use integer multiples of a period for the helix.** A single period
   `(w, -1)` of the two-dimensional function replaces the custom integer
   induction in `row_zero_of_helix`.
3. **Prove the geometric width bound `L + R ≤ N`.** Translating the left seam by
   the positive period cannot place it inside the seam-free strip. This gives
   `N > 2` without the early-run halting argument. It adds a stronger reusable
   theorem; it is not a net source-line reduction.
4. **Recover the pairing branch from an output threshold.** With m = max(a,b),
   pair(a,b) < m*m + m iff a < b. After equal maxima are known, only two branches
   remain in the injectivity proof. The original ordered-semiring assumptions
   and the discrete hypothesis needed for equal maxima remain in place.
5. **Use `head_cons` and `add_le_add` for the list-head bound.** This is a small
   concrete cleanup after the earlier internal ordered-semiring interface.
6. **Reuse `mul_geom_sum` and derive the geometric bound algebraically.** Two
   local inductions disappear without changing the polynomial-range interfaces.
7. **Optionally reconstruct the internal order from its strict total order.**
   This reduces local boilerplate but changes how non-strict order unfolds.
   A compatibility bridge and downstream rebuild are required.

The report also explains the supplementary checked Sidon patch under
`arithmetic/`: it retains the original factorization argument and is not counted
as an eighth new mathematical mechanism.

## What was checked

The delivered examples include exact-statement extractions, an exact-data span
fixture, and generic interface fixtures. Their successful logs and source hashes
are supplied. The entire modified supplementary `SidonPositions.lean` was also
checked. The seven headline production candidates have not been compiled as
complete modules: their stated fixtures, theorem segments, or generic core
proofs were checked. The supplementary Sidon module is the full-module
exception. A passing fixture or `git apply --check` does not establish complete
production integration.

Raw line counts refer to the actual pinned files. They are not incremental line
savings over a hypothetical tree with every earlier roadmap item applied. No
performance claim is based on the recorded wall times.

## Files and patches

- `lean/`: helix and geometric-sum theorem checks, plus the original helix proof.
- `arithmetic/`: exact-data span fixture, span candidate and patch, supplementary
  Sidon theorem/full-module checks, successful receipts and provenance.
- `syntax/`: pairing, list-head and order prototypes, candidates, patches, and
  final successful verification receipts.
- `geometry/`: periodic-gap core proof, source integration sketch and width patch.
- `patches/` and `candidates/`: helix and geometric-sum production candidates.
- `evidence/`: audit, snapshot hashes, validation matrix and independent review.

Patches are separate so the optional order-interface experiment can be omitted.
They do not change the literal machine, polynomial data, support tables or
certificate representations. The report discusses the one proposed definitional
interface change explicitly.

## Reproduce

Use an existing checkout at either recorded commit, with its normal Lean and
mathlib dependencies available. Run these commands from the extracted bundle
directory; `--repo` points to the separate repository checkout:

```bash
python3 scripts/check_manifest.py
python3 scripts/replay.py --repo /absolute/path/to/ProveIt
```

For the supplementary Sidon checks, first build the baseline dependency in that
checkout, then run with `--include-supplementary`:

```bash
cd /absolute/path/to/ProveIt
lake build DiophantineConsistency.SidonPositions
python3 /absolute/path/to/bundle/scripts/replay.py \
  --repo /absolute/path/to/ProveIt --include-supplementary
```

The replay script applies no patches. It checks the targeted source hashes,
runs each selected file separately, writes logs, and fails on a nonzero result,
timeout, missing artifact or `sorryAx`. To assess production integration, apply
one patch in an isolated worktree and rebuild the affected module and existing
checks. The order proposal requires broader checking of order clients.

From the extracted bundle directory, rebuild the PDF with:

```bash
bash scripts/build_report.sh
```

The report build requires XeLaTeX and the DejaVu Serif, DejaVu Sans and DejaVu
Sans Mono fonts. The script makes three passes to settle the contents and
cross-references.

No repository commits, pull requests, or external messages were created.
