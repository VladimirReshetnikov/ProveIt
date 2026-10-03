# Global Fueter Inversion Beyond Finite Connectivity

**Real-axis gluing, arbitrary polynomial periods, and the finite–infinite splitting dichotomy**

Research article prepared for Vladimir Reshetnikov, 30 September 2026.

## Read the article

`article.pdf` is the 26-page typeset article (title, contents, and 24 numbered
text pages). `article.tex` is the complete editable source, with an internal
bibliography and no external figures.

The article extends the Fueter-inversion research report in ProveIt at commit
`cb1646dc442724f8e298cf259195b6c308367d80`. The precise source paths and the
limits of the inspection are recorded in `PROVENANCE.md`.

## Results and where to find them

- **Theorems 4.1 and 4.3:** confluence of the moving Hermite interpolant at the
  real axis, and a complete global inverse criterion including smooth
  even/odd compatibility.
- **Theorems 5.1 and 6.1:** realization of every admissible polynomial homology
  character on arbitrary planar domains. Reflection-fixed holes contribute no
  obstruction; each conjugate pair contributes `2h * dim_R(E)` real coordinates.
- **Theorem 7.3:** a continuous linear normalized inverse on zero-period targets,
  with compact-set estimates that do not divide by the distance to the real axis.
- **Theorem 8.2:** continuous linear, or continuous positively homogeneous,
  realization of arbitrary periods is possible exactly at finite admissible
  period rank. At infinite rank, no section can have a continuous linear
  derivative at even one point.
- **Theorems 9.2 and 9.4:** a continuous nonlinear section for arbitrary period
  sequences and continuous linear sections on every prescribed weighted bounded
  coefficient class, with seminorm tail estimates.

Section 12 develops eight further research directions. Appendix A records
hypotheses and failure modes. The article distinguishes its extensions from
classical Fueter calculus, the repository's existing polynomial current, and
classical Cousin/Eidelheit techniques.

## Status and limitations

These are written mathematical proofs, not independently refereed results.
Historical priority has not been established. No Lean or Rocq verification is
claimed. The Python checks are finite diagnostics, not proofs of the global
or infinite-dimensional statements.

The important stability distinction is between **inverting a target whose
periods vanish** and **choosing a target for arbitrary period data**. The former
has a continuous linear normalized inverse even with infinitely many holes.
The obstruction to a continuous linear section concerns the latter map.

Envelope-controlled realization is proved in compact-set smooth topology.
The article does not characterize period images in fixed Hardy, Bergman,
physical L^p, boundary-Hölder, or Sobolev spaces. The existence proof of the
coordinate lifts does not supply an effective algorithm or sharp geometric
constants on an arbitrary domain.

## Build and verification

With Python 3.10+ and a standard pdfLaTeX installation:

```sh
python -m pip install -r code/requirements.txt
python code/verify.py
./build.sh
```

The build script runs pdfLaTeX three times, writes intermediate files into
`build/`, and copies the finished PDF to `article.pdf`. The bibliography is
internal, so BibTeX and Biber are not needed.

The retained diagnostic run used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.
It passed:

- current closedness, normalization, reflection, injectivity evaluations, and
  the central-imaginary constant check through `h = 8`;
- 55 monomial Hermite identities and 55 real-axis confluence cases through
  `h = 5`, plus 40 calibration monomials;
- 49 reflection homology matrices and the tangent coefficient norm identity;
- nine numerical contour checks at 60 decimal digits and 192 nodes per loop.

The largest observed absolute coefficient error in those contour checks was
below `2.7e-49`. This is an observed numerical error, **not** a certified
quadrature enclosure. Full output is retained in `data/verification.json`
and `data/verification.log`.

Optional diagnostic flags:

```sh
python code/verify.py --skip-numerical
python code/verify.py --max-h 3
```

## Files

```text
article.tex                 Complete LaTeX source
article.pdf                 Typeset article
README.md                   This guide
PROOF_AUDIT.md              Internal proof-dependency and scope audit
PROVENANCE.md               Repository snapshot and source context
build.sh                    Three-pass pdfLaTeX build
code/verify.py              Exact and numerical diagnostic checks
code/requirements.txt       Python dependency versions
data/verification.json      Recorded machine-readable results
data/verification.log       Recorded readable results
data/build_check.json       Final PDF/build checks
```
