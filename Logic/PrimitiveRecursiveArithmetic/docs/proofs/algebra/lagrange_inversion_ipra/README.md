# Lagrange inversion in intuitionistic primitive recursive arithmetic

This packet develops the mathematical statements on the Wikipedia page
**Lagrange inversion theorem** in a finitary constructive form suitable for
intuitionistic primitive recursive arithmetic (iPRA).

## Main result

The algebraic core works coefficientwise in `R[X]/(X^(N+1))`:

1. the unique solution of `G = X * Phi(G)` is produced by `N+1` primitive
   fixed-point iterations;
2. a finite Laurent-series residue substitution lemma proves both
   Lagrange-Buermann coefficient formulas;
3. all coefficient operations are bounded folds and can be compiled into the
   primitive-recursive function symbols of ProveIt's `ConciseIPRA` library;
4. quantifier-free Boolean-fold invariants allow direct use of `PRA.qfInd`.

The paper derives:

- inverse coefficients around an arbitrary base point;
- the general formula for `H(G)` in both standard forms;
- the Bell-polynomial formula;
- Good's multivariate determinant formula;
- ramified/Puiseux inversion when the first derivative vanishes;
- an explicit constructive analytic inverse radius;
- the series and exact convergence disk for `x^p-x+z=0`;
- both Lambert W expansions on the source page, their radii, and an exact
  rational certificate for `W(1)`;
- the Catalan binary-tree formula;
- the coefficient transformation used in Laplace-Erdelyi asymptotics.

It also corrects a coefficient-normalization mismatch in the page's
associahedron display and proves the standard ordinary-coefficient face
formula plus its correct exponential-coefficient translation.

## Contents

- `paper/lagrange_inversion_ipra.tex` - human-readable source.
- `paper/lagrange_inversion_ipra.pdf` - compiled 24-page paper.
- `lean/LagrangeInversionBlueprint.lean` - detailed Mathlib/ConciseIPRA target
  architecture. It is a blueprint, not a completed kernel-checked proof.
- `lean/LEAN_ROADMAP.md` - staged completion plan.
- `code/verify.py` - exact-rational executable coefficient checks.
- `validation/validation_output.txt` - recorded verifier output.
- `validation/pdf_preflight.txt`, `validation/pdfinfo.txt`, and
  `validation/latex_warnings.txt` - build and PDF checks.
- `STATEMENT_AUDIT.md` - page-by-page theorem status and correction notes.
- `PROVEIT_INTEGRATION.md` - suggested repository placement and build steps.
- `SOURCES.md` - exact source snapshots and bibliography.
- `MANIFEST.sha256` - checksums for all packet files except the manifest itself.

## Reproduce

```bash
./build.sh
python3 code/verify.py
```

`build.sh` requires `latexmk` and `pdflatex`. The verifier uses only Python's
standard library.

## Verification status

The PDF compiled successfully and was rendered page by page at 150 dpi for
visual inspection. The exact-rational verifier completed with
`ALL EXACT CHECKS PASSED`.

The Lean file intentionally contains two opaque object-theory placeholders and
schematic target theorems in comments. A completed Lean proof is not claimed.
