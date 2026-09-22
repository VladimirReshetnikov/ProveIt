# Surcomplex Spectral Theory

## Singular Values, Infinitesimal Rank, and Multiscale Stability

A 30-page standalone mathematical article prepared for the Surreal repository.

The selected documentation gap is a systematic finite-dimensional matrix
chapter: the repository's polynomial-algebra report contains Schur-type
arguments, differentiating compressions, and Hermite signatures, but the
inspected package inventories do not develop a unified SVD, conditioning,
or singular-value scale theory. This is a targeted coverage assessment, not
an assertion that every archived source was exhaustively audited.

Repository revision examined:
`e260237db9b71da8b74a0c13c8e6355119091100`.
See `repository_audit.md` for the actual inspection scope.

## Main contents

The article proves the finite spectral theorem and SVD over a real closed
field and its complexification without compactness arguments. It develops
positive square roots, polar decomposition, generalized Hermitian eigenproblems,
variational bounds, least squares, low-rank approximation, and conditioning.

Its scale-sensitive core identifies singular-value valuations with successive
differences of minimum minor valuations. Positive Gram coefficients recover
both these valuations and the leading singular coefficients, one scale block
at a time. Applications include an intrinsic rank filtration, root-free scale
elimination, perturbation precision certificates, nonnormal pseudospectra,
gap-sensitive spectral projectors, Schur-complement corrections, regularization,
and a finite tensor example.

The paper keeps ordered magnitude, Hahn valuation, strong summability, and
workspace-relative topology distinct. All matrix dimensions are ordinary
finite integers. It makes no priority claim, does not claim a solution of a
named open problem, and does not claim an infinite-dimensional operator theory.

## Files

- `article.pdf`: compiled article, 30 pages.
- `article.tex`: complete standalone LaTeX source, with internal bibliography.
- `code/verify_examples.py`: exact symbolic checks and a small rational-function
  valuation/elimination kernel.
- `requirements.txt`: the Python dependency used for the recorded run.
- `data/verification_report.json` and `.txt`: recorded finite checks.
- `data/build_report.json`: build and PDF inspection information.
- `repository_audit.md`: pinned coverage evidence and the choice of topic.
- `build.sh` and `build.ps1`: optional LaTeX build helpers.
- `MANIFEST.sha256`: hashes of the distributed files other than the manifest itself.

## Build the PDF

With TeX Live or MiKTeX and `latexmk`, run from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The source requires ordinary AMS, Latin Modern, microtype, geometry, booktabs,
tabularx, longtable, xcolor, enumitem, fancyhdr, titlesec, hyperref, aliascnt,
and cleveref packages. There are no external images, bibliography files,
custom fonts, or shell-escape requirements. On Windows, `build.ps1` invokes
exactly the same build. Without `latexmk`, run `pdflatex` three times.

## Reproduce the exact finite checks

With Python 3.9 or newer:

```sh
python -m pip install -r requirements.txt
python code/verify_examples.py
```

The recorded execution used Python 3.13.5 and SymPy 1.14.0 and passed
**176 exact assertions across 18 matrix-profile cases**. The matrix generator
uses the fixed seed 20260921. No floating-point sampling is used.

The valuation and elimination kernel is restricted to Q(i)(t,u). Its convention
is `v(t)=(0,1)`, `v(u)=(1,0)`, ordered lexicographically, so u is smaller than
every positive finite power of t in the corresponding Hahn interpretation.
The least polynomial monomial, not SymPy's default leading monomial, determines
the Hahn valuation. Separate finite symbolic checks also use exact square-root
expressions for the two-by-two spectral examples.

These checks verify the listed finite identities and test the implementation
on its stated inputs. They do not machine-verify the general proofs, arbitrary
Hahn supports, proper-class foundations, or an effective representation of
all surreal numbers. Exact symbolic zero tests are not replaced by truncation.

## Integration

Suggested new directory: `docs/surcomplex/spectral-theory/`.
No original repository files were modified. The archive is self-contained;
it does not redistribute the repository's source reports or third-party papers.
