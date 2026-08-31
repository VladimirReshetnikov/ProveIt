# Inverse Fabius compositional iterates: nowhere analyticity

> **Source-only merge status (2026-08-31).** The current TeX has 1,742 lines
> (SHA-256
> `a9ffad2d6d38212b3434af0a5dec119ffca9f8391a9ef942fde20aa37d993b6d`).
> The retained 26-page PDF was not rebuilt after the notation migration and is
> not claimed to be synchronized with that source. `SHA256SUMS.txt` was
> intentionally not refreshed: its TeX row and this README row are pending,
> while its other thirteen rows pass. Historical build facts below describe
> the preceding checkpoint.

This package is a derived companion to the corrected forward report in
`drafts/representations/fabius_iterates_nowhere_analytic/`.  Its repeated
forward engine is retained to make the inverse argument readable in one
document; it is not independent novelty.

## Result and status boundary

For the bounded Fabius function `F`, its inverse `I`, the forward iterate
`G_n = F^{\circ n}`, and the inverse iterate `K_n = I^{\circ n} = G_n^{-1}`,
the manuscript proves:

1. every positive inverse iterate is nowhere real analytic;
2. formal Taylor-radius zero transports exactly between `G_n` and `K_n` at
   corresponding interior points, giving a co-countable dense zero-radius
   locus for `K_n`;
3. the center jet of `K_n` is the affine series with slope `2^{-n}`, but it
   does not represent the function locally;
4. the leading endpoint logarithmic scale iterates, so every `K_n` fails every
   positive-order endpoint Hölder bound.

The first conclusion already appears as a corollary of the corrected forward
report.  Lean proves the one-fold inverse analytic locus in
`InverseNotElementary.lean` and the one-fold endpoint Hölder obstruction in
`FabiusInverseAsymptotic.lean`.  The `n >= 2` forward and inverse iterate
theorems, formal-radius transport, all-order center jet, and iterated endpoint
scale remain manuscript mathematics with no exact proved Lean counterparts.
Manuscript theorem labels and numerical replay do not establish Lean status.

A hostile post-intake review found no fatal gap in the inverse-transfer or
endpoint-induction arguments and ported four corrections from the forward
report: a uniform weighted-defect estimate, the correct outer-function
neighborhood in the two-spine lemma, an empty-union-safe `n = 1` tie set, and
the live `Monotonicity.lean` module name.

The finite positive-list arithmetic beneath the manuscript defect is now
exhaustively crosswalked to `PartitionDefect.lean`.  Its three definitions are
`pairSum`, `blockPairDefect`, and `partitionDefect`; its thirty-three public
theorems cover the unordered-pair/triangular identities, conventional defect
formulas, excess decomposition, nonnegativity, fixed-block lower bound and
sharp equality case, both zero classifiers, and the first positive shell.
For a positive list of total `m` and length `k`, the formal layer proves

`D(r) = (k-1)∑(r_i-1) + ∑_{i<j}(r_i-1)(r_j-1) ≥ (k-1)(m-k)`,

the exact zero/equality classifications, and—when `2 ≤ k < m`—the sharp
first-shell bound `D(r) ≥ m-2`.  It does not construct set partitions or prove
the manuscript's quadratic `Q_m` factorization, weighted Bell estimate,
two-spine reduction, finite spine expansion, or forward/inverse iterate
theorems.  Those steps remain paper-only.

The normalized report contains 19 nonconjectural labelled manuscript results,
two live conjectures, and three numbered warning quarantines.  Former
Conjecture 14.1 has a false inverse clause: the finite quadratic forward germ
at `1/4` reverts to an infinite convergent square-root/Catalan series, so formal
reversion transports positive radius but not eventual jet-vanishing.  Its
forward-only classification residue remains open.  Former Conjecture 14.2 is
already discharged by exact quarter-point facts plus the binary-transition
lemma.  Former Conjecture 14.4 is the same defect-spectrum conjecture as
Conjecture 14.3 of the forward report and is not a second independent claim.
Only the direct inverse-spine and nested-Lambert statements remain live,
explicitly unformalized conjectures; the finite-order experiment establishes
neither.

## Arrival provenance

The source archive was `inverse_fabius_iterates_nowhere_analytic.zip`
(1,137,032 bytes; outer SHA-256
`8b1c05d59e120ecd20d69cd5aeb0009639f2b3b9a6c9fef32bdf82270eee16bd`).
All 13 submitted payload checksums verified before normalization.  The
submitted ledger had SHA-256
`c270903631b0942aa7f7742b84ea0117bb9f2f4cc0d0eb374889077ba37873a0`
and is preserved byte-for-byte as `SHA256SUMS.arrival.txt`.
`MANIFEST.txt` is the unchanged submitted file list; `SHA256SUMS.txt` is the
unrefreshed 15-entry operational ledger. See `REPOSITORY_AUDIT.md` for the claim audit,
original source/PDF hashes, and replay details.

## Files

- `inverse_fabius_iterates_nowhere_analytic.tex` — current normalized source;
- `inverse_fabius_iterates_nowhere_analytic.pdf` — retained
  preceding-checkpoint PDF, pending rebuild;
- `numerical_experiments.py` — deterministic forward-spine and inverse formal
  reversion diagnostics;
- `figures/` — the five PNG files embedded in the report;
- `numerical_output/` — the submitted CSV and run metadata;
- `requirements.txt` — the submitted unpinned Python dependencies;
- `REPOSITORY_AUDIT.md` — repository provenance, hostile audit, and limitations;
- `SHA256SUMS.arrival.txt` — immutable submitted checksum ledger;
- `SHA256SUMS.txt` — unrefreshed operational checksum ledger; its TeX and
  README rows are pending.

No numerical output is used as a proof premise.

## Reproduce the numerical diagnostics

The submitted command is:

```bash
python -m pip install -r requirements.txt
python numerical_experiments.py \
  --output-dir numerical_output \
  --x0 0.437123456789 \
  --iterate-count 4 \
  --max-order 22
```

Repository replay used `MPLBACKEND=Agg`, CPython 3.12.13, NumPy 2.3.5,
SciPy 1.16.3, Matplotlib 3.10.8, and mpmath 1.4.1. All seven generated
outputs reproduced byte-for-byte before repository line-ending
normalization; the current CSV has the same numerical fields with explicit
LF output. The degree-22 formal-composition residual remained approximately
`1.8991135e-65` at 160 decimal digits.

The script writes five PNGs as well as the CSV and metadata to
`--output-dir`, while TeX reads PNGs from `figures/`; refreshing embedded
figures therefore requires an explicit copy step.  The archived
`numerical_output/` intentionally retains only the CSV and metadata.  Five
anchor values are printed, but only `up(0)` and `F(1/2)` are enforced by
tolerance checks.  Three plots are byte-identical to the forward package and
retain that provenance.

## Rebuild the PDF

From a clean package directory, run exactly three strict serial passes:

```bash
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
  inverse_fabius_iterates_nowhere_analytic.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
  inverse_fabius_iterates_nowhere_analytic.tex
pdflatex -interaction=nonstopmode -halt-on-error -file-line-error \
  inverse_fabius_iterates_nowhere_analytic.tex
```

The TeX uses the primary document's verbatim canonical A4/27 mm preamble,
including Libertinus prose, with only allowed metadata/running-head changes
and used local notation afterward.  Auxiliary build files are not part of the
package.

At the preceding checkpoint, the checked source build completed exactly three
strict serial passes and produced the retained 26-page A4 PDF. Its final log
has no warnings, errors, unresolved
references, rerun requests, or overfull/underfull boxes.  All 24 font rows are
embedded, subset Type 1 fonts; the prose rows are Libertinus, with no Type 3 or
Latin Modern font.  Text extraction and a visual review of every rendered page
were clean.
