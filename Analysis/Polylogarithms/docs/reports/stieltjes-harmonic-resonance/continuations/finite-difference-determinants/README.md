# Finite-Difference Determinants
## Single-zeta closure, repeated-pole classification, and Stieltjes jets

Research continuation for Vladimir Reshetnikov and ProveIt, 11 October 2026.

**Read `Finite_Difference_Determinants.pdf` first.** It is the complete article.
`Finite_Difference_Determinants.tex` is the standalone LaTeX source;
`article.tex`, `sections/`, and `references.tex` are the editable modular source.

### Main results

The article proves an exact residue classification of rank-one harmonic
matrix pencils for proper rational weights on finitely many translated
integer lattices. At nonzero critical decay x^(-(2r-1)), rank one is equivalent
to being a normalized (2r-2)nd finite difference of a proper rational seed.
Repeated poles and multiple residue classes are included.

The spectral family Delta^(2r-2)(n+a)^(-s)/(2r-2)! gives, for every rank r,
an ordered Vandermonde-square sum of the form U_r(s,a)+V_r(s,a)*zeta(s,a),
where U_r,V_r are explicit finite determinants. Independent orders and
independent shifts are handled by polarization, without zeta products.
Integer orders yield complete-harmonic Gamma-weighted identities. A normal
largest-index subtraction supplies every Stieltjes jet and the correct
hard-cutoff constant. A separate rational-weight theorem controls the
polylogarithmic depth of cutoff generators; an explicit Li(2,2) formula
is worked out.

### Scope

The new results are assessed against a targeted inspection of the pinned
repository, not an exhaustive literature or archive audit. Classical
finite differences, rational summability, Cauchy--Binet, Gauss summation,
and standard Hurwitz/Gamma identities are credited as such.
The proofs are ordinary mathematical proofs, not proof-assistant formalizations.
No Gaussian S6 or revised S8 conjecture is claimed proved. No repository
write, commit, archive retirement, or publication was performed.

### Verification and generation

With Python 3.10 or later and the packages in `requirements.txt`, run:

```text
python verify_manifest.py
python verification/verify_exact.py
python verification/verify_numeric.py
python identity_cli.py --rank 3 --order 3 --shift 1
```

The first command verifies the unmodified delivered files. The other commands
regenerate mathematical results; a changed elapsed-time field will change a
result file's checksum. Rerunning the suite is not meant to preserve byte-for-byte
identity of generated records.

The recorded exact suite passes **1,037 assertions**. The numerical suite passes
**29 diagnostics**, including independent elementary Mellin-integral evaluations,
complex parameters, finite cutoff comparisons, and Stieltjes jets. Numerical
checks are not interval-certified. Their individual tolerances are recorded;
the maximum relative discrepancy in the supplied run is approximately 8.83e-13,
from a finite-cutoff derivative test. The ordinary Mellin determinant comparisons
have much smaller residuals. Working precision is not a certified error bound.

`verification/core.py` implements exact endpoint matrices, weights, finite
boundary formulas, residue matrices, and the rank-one test. For several shift
classes, compute the residue matrices for each class and concatenate those
lists before applying `rank_one_type`. The exact mathematical classification
is proved for all admissible input ranks, not only the examples in the suite.

### Build

```text
python build.py
```

This regenerates the standalone source and compiles the modular article using
`latexmk` (or three `pdflatex` runs). The TeX installation needs the standard
packages used in the preamble: geometry, amsmath, amssymb, amsthm, mathtools,
bm, mathrsfs, lmodern, microtype, booktabs, longtable, array, xcolor, hyperref,
and fancyhdr. No external images or bibliography processor are needed.
The standalone `.tex` can also be compiled directly with `pdflatex`.

### Integration and provenance

The exact source pin is `73f18ef013d5b74eafc883efb2c15210642df12a`.
`provenance/sources.json` records the inspection scope and literature sources.
`CLAIM_STATUS.json` records theorem boundaries and exclusions.
`integration/INTEGRATION.md` proposes a destination and cross-links.
`integration/STATUS_UPDATES.md` gives the source-question updates and safeguards.
`results/` contains exact, numerical, build, and document-QA records.
`MANIFEST.sha256` covers the delivered files except the manifest itself.
