# Comb Interpolation and Sampling Frontiers

This directory is the canonical editorial synthesis of the additive-dyadic and
geometric-comb manuscripts in this part of the Fabius--Rvachev frontier
corpus. The source is organized as one article rather than four adjacent
reports: common interpolation algebra is developed once, genuinely different
extensions retain their own proofs, and repeated statements are represented
by their strongest verified human-readable form.

The immutable editorial baseline is Git revision
`73f0b373126ef22a3b5dccadfa7b99d61d445345`. It is recorded in
[`audit/SOURCE_REVISION`](audit/SOURCE_REVISION). All source-disposition and
historical-checksum statements below refer to that revision, not to an
unqualified moving branch.

## What is canonical

- [`comb_interpolation_synthesis.tex`](comb_interpolation_synthesis.tex) is
  the publication driver.
- [`chapters/`](chapters/) contains the proof-bearing geometric core,
  geometric extensions, additive-dyadic theory, reference appendices,
  provenance, and bibliography.
- [`source_disposition.csv`](source_disposition.csv) accounts for all 180
  files in the source-pin subtree: the four pre-synthesis report trees and
  their parent routing README.
- [`post_pin_disposition.csv`](post_pin_disposition.csv) accounts separately
  for all 23 paths added or modified before the mainline reconciliation pin.
- [`assets/`](assets/) contains the unique retained computational evidence and
  the audit of the historical ledgers.
- [`audit/`](audit/) contains the source pin and the deterministic editorial
  tooling. Generated audit products do not replace mathematical proofs.

The source currently distinguishes exact Lean crosswalks from results proved
only in the manuscript. A manuscript theorem label is never, by itself,
evidence of a compiled Lean declaration. Likewise, numerical tables and plots
are checks and illustrations, not proof premises. The current
`FabiusFunction.LagrangeRvachevSynthesis` crosswalk verifies generic scalar
decoder synthesis, node biorthogonality, coefficient factorization, the full
finite interpolation loop, and the unnormalized decoder row-sum law. It does
not claim a formal geometric Gaussian closed-form decoder, the associated
elementary-symmetric/prefactor formula, a `Matrix` wrapper, or decoder
optimization.

The separate `Fabius.twoPowChoose_padicValNat` crosswalk is an exact Lean
counterpart only for the strict-interior formula in `thm:weight-valuation`.
The companion endpoint-flat assertion for `choose(2^m - 2, j - 1)` is stated
separately in the chapter and remains unformalized.

## Sources reconciled

The earlier `Dyadic_Comb_Frontiers` volume had already absorbed nine nested
manuscript packages: six comb-sum/interpolation reports, two
Euler--Maclaurin/exhaustion reports, and the Bernoulli--Ruffa phase-calculus
report. Its provenance appendix names all nine packages and describes what
each contributed. The duplicate nested manuscript documentation was therefore
not an independent publication layer and has been retired.

This synthesis adds the three formerly standalone geometric-comb manuscripts:

- `geometric_comb_q_fabius_report` supplies the strongest finite
  Gaussian-Pascal, Jackson--Newton, Lagrange-residual, and stability spine;
- `geometric_comb_interpolation_report` supplies modal, Mellin,
  regular-variation, spline, and exact boundary-filter extensions;
- `geometric_comb_interpolation_report-3` supplies complementary arbitrary-
  target, Fabius-transform, reciprocal-product, and asymptotic material.

The documentation layers of all twelve noncanonical source packages (nine
nested additive-dyadic packages and three geometric packages), the old report
TeX/PDF pairs, package wrappers, stale checksum ledgers, and generated preview
PDFs are no longer live publications. Original bytes remain
recoverable from the immutable Git baseline. Scripts, exact tables, data,
text outputs, and PNG figures that remain useful for reproduction are retained
under [`assets/companion-evidence/`](assets/companion-evidence/), grouped by
their historical source slug. One byte-identical dependency file shared by
the two interpolation packages is stored once at
[`assets/companion-evidence/shared/requirements-mpmath-matplotlib.txt`](assets/companion-evidence/shared/requirements-mpmath-matplotlib.txt).

See [`PROVENANCE.md`](PROVENANCE.md) for the editorial chain and
[`assets/VALIDATION.md`](assets/VALIDATION.md) for completed checks and
remaining reproducibility work.

## Build the canonical article

Run from this directory. The publication gate requires exactly three strict,
serial passes after the final TeX edit:

```text
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
```

A successful command is not, by itself, the complete publication gate. The
retained incoming publication artifact's build-source and PDF hashes, page,
font, log, and visual-inspection facts are recorded once in
[`assets/VALIDATION.md`](assets/VALIDATION.md). Keeping those mutable
measurements in one record prevents status drift between README files.

Later source-only edits changed `chapters/03_additive_dyadic.tex` to crosswalk
`thm:weight-valuation` to `Fabius.twoPowChoose_padicValNat`, and changed
`chapters/01_geometric_core.tex` and `chapters/99_bibliography.tex` to point to
the consolidated q-series synthesis.  By explicit instruction, none of these
edits rebuilt the PDF.  The recorded measurements therefore describe the
retained incoming publication artifact and do not assert render
synchronization with the current sources.

## Reproduce the computational evidence

The retained scripts have different dependency sets and output conventions;
there is no single package-wide lock file. Work in a disposable copy or send
outputs to a scratch directory so the reviewed evidence is not overwritten.
The principal exact or quick entry points are:

```text
python dyadic_comb_experiments.py --outdir <scratch-output> --max-level 8
python fabius_dyadic_comb_experiments.py --skip-fractional
python fabius_dyadic_interpolation_experiments.py --mode quick --output-dir <scratch-output>
python numerical_experiments.py --task smoke
python fabius_dyadic_interpolation_experiments.py --outdir <scratch-output> --quick
python fabius_em_experiments.py --output-dir <scratch-output> --max-power 10 --max-level 10
python verify_fabius_rvachev_quadrature.py --max-degree 7 --output-dir <scratch-output>
python experiments.py --output-dir <scratch-output> --grid-power 19 --skip-fft
python geometric_comb_experiments.py --output-dir <scratch-output>
```

Those commands are run from the corresponding source-slug directory under
`assets/companion-evidence/`; several filenames intentionally recur in
different packages. Two geometric scripts have no command-line arguments and
write beside themselves. The complete per-package command map, including the
full interpolation replay, is in [`assets/README.md`](assets/README.md).

## Current status

The 180-row source-pin disposition and 23-row post-pin reconciliation are
complete. The deterministic canonical validator passes the structural,
editorial, provenance, theorem-concordance, and exhaustive package-checksum
gates. Its Lean check only confirms that each curated exact or partial-support
declaration name occurs in its nominated module; it is not a live Lean census
or theorem-type checker. Three concordance rows are exact Lean crosswalks; the
compound decoder and biorthogonality rows remain human-proved with narrower
partial-support notes. The root `SHA256SUMS` is the exhaustive ledger for every
other permanent package file. The retained incoming publication PDF's
measurements and inspections are recorded only in
[`assets/VALIDATION.md`](assets/VALIDATION.md); it predates the source-only
valuation crosswalk and is not synchronized with the current chapter. A
fresh-checkout reproduction and a full rerun of every retained numerical
script remain separate reproducibility work.
