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
  files in the four pre-synthesis report trees at the source pin.
- [`assets/`](assets/) contains the unique retained computational evidence and
  the audit of the historical ledgers.
- [`audit/`](audit/) contains the source pin and the deterministic editorial
  tooling. Generated audit products do not replace mathematical proofs.

The source currently distinguishes exact Lean crosswalks from results proved
only in the manuscript. A manuscript theorem label is never, by itself,
evidence of a compiled Lean declaration. Likewise, numerical tables and plots
are checks and illustrations, not proof premises.

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

The twelve noncanonical package READMEs (nine nested additive-dyadic packages
and three geometric packages), the old report TeX/PDF pairs, package wrappers,
stale checksum ledgers, and generated preview PDFs are no longer live
publications. Original bytes remain
recoverable from the immutable Git baseline. Scripts, exact tables, data,
text outputs, and PNG figures that remain useful for reproduction are retained
under [`assets/companion-evidence/`](assets/companion-evidence/), grouped by
their historical source slug. One byte-identical dependency file shared by
the two interpolation packages is stored once at
[`assets/companion-evidence/shared/requirements-mpmath-matplotlib.txt`](assets/companion-evidence/shared/requirements-mpmath-matplotlib.txt).

See [`PROVENANCE.md`](PROVENANCE.md) for the editorial chain and
[`assets/VALIDATION.md`](assets/VALIDATION.md) for completed and pending
validation gates.

## Build the canonical article

Run from this directory. The publication gate requires exactly three strict,
serial passes after the final TeX edit:

```text
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
```

A successful command is not, by itself, the complete publication gate. The
current canonical PDF was built from the final source in exactly three strict,
serial passes on 2026-08-31. It has 155 A4 pages, 2,448,906 bytes, and SHA-256
`d1f89b005bcae9afc9c70b4ccce632aa8c665ed68e98bacb2ff96827dd427095`.
All 33 font rows are embedded and subset, seven are Libertinus faces, and none
is Type 3. Every page has text, A4 geometry, zero rotation, and the same five
page boxes; all pages were reviewed in contact sheets and representative
pages were inspected at full size. The final log has no TeX errors, undefined
references or citations, rerun requests, duplicate destinations, or overfull
boxes. Its 36 package warnings and six underfull boxes are the recorded,
visually checked hyperref/caption/amsmath and paragraph-layout diagnostics.

## Reproduce the computational evidence

The retained scripts have different dependency sets and output conventions;
there is no single package-wide lock file. Work in a disposable copy or send
outputs to a scratch directory so the reviewed evidence is not overwritten.
The principal exact or quick entry points are:

```text
python dyadic_comb_experiments.py --outdir generated --max-level 8
python fabius_dyadic_comb_experiments.py --skip-fractional
python fabius_dyadic_interpolation_experiments.py --mode quick --output-dir reproduced-results
python numerical_experiments.py --task smoke
python fabius_dyadic_interpolation_experiments.py --outdir quick-results --quick
python fabius_em_experiments.py --output-dir reproduced-data --max-power 10 --max-level 10
python verify_fabius_rvachev_quadrature.py --max-degree 7 --output-dir reproduced-data
python experiments.py --output-dir reproduced-data --grid-power 19 --skip-fft
python geometric_comb_experiments.py --output-dir reproduced-output
```

Those commands are run from the corresponding source-slug directory under
`assets/companion-evidence/`; several filenames intentionally recur in
different packages. Two geometric scripts have no command-line arguments and
write beside themselves. The complete per-package command map, including the
full interpolation replay, is in [`assets/README.md`](assets/README.md).

## Current status

The source reconciliation and the 180-row file disposition are complete at the
recorded pin. The eight historical ledgers contribute 151 audit rows: 68
match byte-for-byte, 34 match after CRLF/LF normalization, 29 differ
substantively, and 20 point to files no longer present at that pin. These are
historical facts, not a live checksum certificate. The deterministic canonical
validator passes all structural, source-disposition, theorem-concordance,
reference, citation, historical-ledger, and companion-payload gates. Its Lean
check confirms only that each curated declaration name occurs in its nominated
module; it is not a live Lean census or theorem-type checker. The current root
`SHA256SUMS` is the exhaustive operational ledger for every other permanent
package file. The final PDF and page/font/text/visual inspections are complete;
a fresh-checkout reproduction and a full rerun of every retained numerical
script remain deliberately separate reproducibility work.
