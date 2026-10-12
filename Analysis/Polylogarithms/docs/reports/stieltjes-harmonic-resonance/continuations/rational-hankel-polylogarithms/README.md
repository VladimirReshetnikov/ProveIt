# A Finite Polylogarithm Alphabet for Rational Hankel Sums

Research continuation prepared for Vladimir Reshetnikov and the ProveIt repository, 11 October 2026 (Pacific time).

## Read first

`article.pdf` is the full article. `article.tex` is a self-contained LaTeX source with its bibliography included. No external figures, source archives, font files, or credentials are required to build it.

The central result is a terminating exact multiple-polylogarithm compiler for

    D[r,M] = det(sum(n**(i+j) * R(n), n=1..M), i,j=0..r-1),

when the rational weight has poles at nonpositive integers. A pole of order s contributes the positive marginal sequence s, s-2, s-4, ... . The r largest available marginals determine the proved weight budget. A specified coefficient proves formal sharpness for every rank in the single-pole family and has an explicit Gamma-product evaluation.

Other results include a dilogarithm-only formula for every rank and every rational weight with an integral quadratic denominator; a fixed-size highest-coefficient Hahn determinant; finite exact endpoint cancellation jets; residue-parameter spectral factorizations; and all-order, all-rank Stieltjes–zeta derivative identities. Two completely evaluated ordinary Euler sums are worked out.

The article distinguishes new derivations from classical tools and illustrative Euler-sum reductions. It does not establish historical priority, minimal functional weight or depth, a proof-assistant formalization, or a solution of the unrestricted moment-prefix, S6, or revised S8 conjectures.

## Reproduce the exact and numerical checks

The executed environment was Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0. The source uses Python 3.10+ syntax.

```bash
python -m pip install -r requirements.txt
python verify_all.py
```

Verification refuses Python's `-O` mode so that assertions cannot silently disappear. The programs run locally and require no network connection after dependencies are installed.

The exact checks cover 99 Taylor coefficients/zero anchors across nine generators, 28 single-pole weight checks, 28 sharp coefficient checks, 8 top compressions, 12 independent confluent factorizations, 7 endpoint principal coefficients, 24 all-rank spectral normalizations, and two deliberately corrupted identities. Two zero-weight and three invalid-rank regression checks are also included. The separate numerical suite contains 28 diagnostics at 60 decimal digits, with a scaled tolerance of 1e-48. Numerical diagnostics are not interval certificates and are not used as proofs of the infinite theorems.

```bash
python verification/check_compiler.py
python verification/check_structure.py
python verification/check_spectral_exact.py
python verification/check_numeric.py
```

Each script writes its machine-readable results to `data/`. `compiled_examples.json` contains the complete rational coefficients of the hyperlogarithm formulas, not just numerical samples.

## Use the compiler

```python
from verification.compiler import compile_hankel, encode

# Each entry is (nonnegative integer shift a, order ell, residue c):
# c / (n+a)**ell. Use exact integer, Rational, or symbolic residues.
formula = compile_hankel(2, [(0, 3, 1)])
print(encode(formula))

# An arbitrary polynomial part is allowed; this adds 1+n to the weight.
formula2 = compile_hankel(2, [(1, 1, 2)], polynomial=(1, 1))
```

Words use 0 for dz/z and 1 for dz/(1-z). The empty word means 1. Nonempty output words end in 1. For example `(0,1,0,1)` means Li_{2,2}(z). Apparent rational singularities at zero are removable only after the complete expression is combined.

The integration operators are anchored at zero. This is essential: dropping constants from individual intermediate rational primitives can change the final coefficient identity.

The compiler is finite, not claimed to be polynomial-time. Symbolic determinant size and intermediate expression growth can be substantial at large ranks. Reserved harmonic symbols are named H1, H2, ... . Passing machine floating-point residues does not give the exact arithmetic used by the certificates.

## Build the PDF

```bash
python build_pdf.py
```

Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times. The required TeX packages are standard: amsmath, amssymb, amsthm, mathtools, mathrsfs, lmodern, geometry, microtype, booktabs, enumitem, hyperref, xurl, fancyhdr, and bookmark. No BibTeX step is needed.

## Integration and provenance

`SOURCE_AUDIT.md` gives the exact comparison commit, archive Git blob identifiers, inspected sections, and limitations. The observed comparison commit is `505c62fddea6b4a9eb61fee0c76e6c021e9c7128`; the repository changed during retrieval, so this is not a claim about every later revision of main.

`CLAIM_STATUS.json` separates proved statements, classical ingredients, diagnostics, and questions not settled. `integration/INTEGRATION.md` proposes a placement without modifying the repository. `integration/summary.tex` is an optional short manuscript bridge using prefixed labels. The complete proofs remain in `article.tex`.

All hashes in `SHA256SUMS` refer to the files delivered in this package, excluding the manifest itself. No existing repository file was changed or uploaded.
