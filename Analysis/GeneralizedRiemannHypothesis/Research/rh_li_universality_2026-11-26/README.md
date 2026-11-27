# Li coefficients and a universal small-time Cauchy law

Research prepared for Vladimir Reshetnikov, 26 November 2026.

Start with **rh_li_universality.pdf**. The complete editable source is
**rh_li_universality.tex**, including the two files in `sections/`.

## Results

1. **An explicit all-order density expansion.** The symmetric jump process
   built from transformed zero ordinates has a Cauchy small-time limit,
   explicit correction profiles at every inverse-logarithmic order, and
   a uniform error after every fixed number of spatial derivatives.
   Primitive Dirichlet characters of equal conductor share the same full
   expansion. The report also proves the circle trace expansion and moment
   formulas, including the critical first absolute moment.
2. **A bounded positive-weight sampling obstruction.** Explicit coefficients
   `0 < a_n < 4` give a remainder zero at every fifth power, while its Mellin
   transform has a simple pole at `s = 3/5` of residue `1/4`. The construction
   extends to every integer power grid `m^p`, `p >= 4`.

The mathematical proofs are complete in the report. The new results are
not Lean-formalized. The precise novelty assessment is in `NOVELTY.md` and
the report; worldwide priority is not certified.

## Reproduce

From this directory, with Python 3 and the dependencies in `requirements.txt`:

```bash
python3 code/verify_results.py
python3 code/make_figures.py
python3 code/verify_sampling_obstruction.py --output data
latexmk -pdf -interaction=nonstopmode rh_li_universality.tex
```

The LaTeX document uses standard packages from a full TeX Live distribution.
`pdflatex` twice is also sufficient; the bibliography is embedded in the
main source. The PDF delivered here was compiled from the included source.

The numerical outputs illustrate and check formulas. They do not replace
the proofs. In particular, the numerical Fourier comparison integral is
the analytic comparison used in the proof, not an exact transition density.
The figures identify their contents accordingly.

## Contents

- `rh_li_universality.tex`, `sections/`: complete written proofs and references.
- `rh_li_universality.pdf`: rendered report.
- `code/`: symbolic, numerical, and figure-generation programs.
- `data/`: reproducible JSON results and 3,000 high-precision coefficients.
- `figures/`: vector PDF and PNG versions of both mathematical figures.
- `sources/source_audit/`: source inspection, internal mathematical review,
  pinned manifest, and 17 upstream repository files.
- `NOVELTY.md`, `PROOF_STATUS.md`: precise provenance and verification status.
- `MANIFEST.sha256`: hashes for the files in this package.

## Repository provenance

The inspected source is `lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
Its theorem scope is RH and GRH for Dirichlet characters. The included
Lean snapshots retain their upstream copyright, NOTICE, and Apache-2.0
license. They are selected source evidence, not a complete build of the
upstream repository or a formalization of the new results.

No changes were made to a remote repository for this deliverable.
