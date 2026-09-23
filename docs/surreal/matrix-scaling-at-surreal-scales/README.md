# Sharp Matrix-Scaling Stability over Surreal and Surcomplex Fields

**Spanning-tree gaps, infinitesimal normalization, and exact multiscale propagation**

Research manuscript prepared for Vladimir Reshetnikov, 22 September 2026.

## Read the article

- `surreal_matrix_scaling.pdf` — the compiled, 26-page article.
- `surreal_matrix_scaling.tex` — standalone LaTeX source with internal bibliography.
- `SOURCE_AUDIT.md` — the repository pin, consulted sources, and limits of the novelty comparison.
- `PROOF_AUDIT.md` — proof dependencies, delicate points, and the verification boundary.

Theorem 5.1 constructs a unique normalization on the entire relative infinitesimal
polydisc over an arbitrary-rank Hahn field. Theorems 6.2 and 6.4 identify the sharp
nonlinear, edgewise valuation gain and the corresponding Taylor coefficient bounds.
The gain is a minimum-spanning-tree deletion gap. Theorem 8.1 gives exact nonlinear
propagation along a bistochastic chain. Theorem 10.1 extends the result to constant
real linear constraints, replacing spanning trees by column bases.

The local results need no divisibility of the value group. The positive global
existence interpretation uses real closedness, explicitly separated in Section 9.
Section 11 transports the results to surreal and surcomplex normal forms.

## Status

The article supplies mathematical proofs, not just conjectures or numerical
observations. The originality claim is a **candidate** conclusion of a targeted,
non-exhaustive literature and repository comparison. No named long-standing open
problem is claimed solved. The manuscript is AI-assisted, not refereed, and not
fully machine-formalized. Classical scaling, implicit differentiation, tree
identities, and foundational Hahn results are credited rather than reclaimed.

## Reproduce the finite checks

Python 3.10 or later and SymPy are required; the recorded run used Python 3.13.5
and SymPy 1.14.0. There are no network requests and no floating-point calculations.

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

The script may be launched from any directory. It writes (and replaces)
`data/verification.json` in its own package. It does not alter the Surreal
repository or any external files. Do not run it with Python optimization (`-O`),
which disables assertions.

The recorded checks cover 2,612 tree-deletion gap comparisons; exact tree
projection identities on 60 graphs; seventh- and sixth-order normalization
examples; 55 chain inverse entries; and closed-form square identities. These
finite checks do not establish the infinite Hahn summability theorem and are
not a substitute for the proofs.

## Build the PDF

A normal TeX installation with `latexmk`, `pdflatex`, Latin Modern, AMS packages,
`microtype`, `geometry`, `hyperref`, `cleveref`, `enumitem`, and the other standard
packages listed in the source is sufficient. No external figures or `.bib` file
are needed.

```sh
latexmk -pdf -halt-on-error -interaction=nonstopmode surreal_matrix_scaling.tex
```

Without `latexmk`, run `pdflatex -halt-on-error -interaction=nonstopmode
surreal_matrix_scaling.tex` three times, then check the log for unresolved
references. On a Unix-like system, `./build.sh` runs both the checks and the build.
The source and the manual commands are also usable on Windows.

The delivered PDF was rendered for visual inspection. The final build record
is in `data/build_validation.json`. Successful compilation is not a proof check.
