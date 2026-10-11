# Exact Harmonic-Tail Reconstruction and Variational Gamma Identities

Research continuation prepared for Vladimir Reshetnikov, 11 October 2026.

The article continues the ProveIt manuscript and all six reports present in
`docs/incoming` at commit
`446dca9bd65c20e409d1d2561d4ffad408103e2a`.
It contains full proofs, an explicit source-status audit, and twelve further
research questions. Historical priority outside the inspected sources is not
asserted. The results are mathematical proofs in the article; no proof-assistant
formalization is claimed.

## Main contributions

1. **Optimal moment prefix for every even pair `q = p + 4`.** A strict ratio
   separation theorem proves nonvanishing of the inherited two-column boundary
   determinant. This resolves the full gap-four subfamily. The first case beyond
   the earlier smaller-order and adjacent-order families is `(p,q) = (8,12)`.
2. **Universal finite telescopers.** Every finite late-coordinate combination
   for arbitrary positive even orders has a polynomial-tail certificate. Its
   even reciprocal coefficients give the exact zeta coordinates and its limit
   supplies the rational term. The `(8,12)` extraction includes all coefficients.
3. **The complete Gamma sector with derivative index at most two.** The Euler
   variational derivative gives a closed formal equation for the projection of
   the canonical normal form onto `u_0,u_1,u_2`. Every `u_2^b` sector has rational
   coefficients with a polynomial numerator of degree `b-2`. The square and cube
   sectors have explicit entire hyperbolic generating functions.
4. **The next two-particle Gamma-weight resonance.** All three moment
   subtractions and their overlap are retained. The report proves the hard
   cutoff, spectral Laurent constant, their exact comparison, and a uniform
   expansion that permits every fixed spectral derivative. A rational
   specialization gives an explicit dilogarithmic generator and ordinary zeta
   evaluations of all convergent Euler-primitive endpoints.
5. **Spatial kernels for every higher spectral coefficient.** A normalized
   Mellin identity gives every logarithmically weighted kernel, higher-pole term,
   and Stieltjes correction. The article includes two explicit convergent
   logarithmic polygamma integrals and arbitrary-anchor Stieltjes identities.

The general unequal-order determinant conjecture, the short Gaussian `S6`
identity, and the current `S8` candidate remain open. The fixed-gap determinant
reduction, classical functional-monomial normal form, and inherited Gamma
scalar bridge are credited as inputs. No new false inherited theorem was found
in the targeted audit.

## Contents

| Path | Purpose |
|---|---|
| `article.pdf` | Complete typeset article |
| `article.tex` and `sections/` | Modular editable source, with unique label prefixes |
| `standalone.tex` | The same complete article in a single TeX file |
| `references.tex` | Bibliography with pinned repository URLs and primary classical sources |
| `verification/` | Exact rational/symbolic checks and independent numerical diagnostics |
| `data/` | Exact coefficient tables, certificates, verification results, and source provenance |
| `VERIFICATION.md` | Scope and interpretation of all checks |
| `integration/INTEGRATION.md` | Concrete manuscript integration and status recommendations |
| `integration/claims.json` | Machine-readable theorem scopes and inherited/open status |
| `tools/make_standalone.py` | Rebuild the single-file source from the modular source |
| `Makefile`, `requirements.txt` | Build and replay entry points |
| `SHA256SUMS` | SHA-256 checksums for the packaged files |

## Build the PDF

The successful build used pdfTeX from TeX Live 2023/Debian and `latexmk` 4.83.
The source uses standard LaTeX packages, including `lmodern`, `amsmath`,
`amsthm`, `mathtools`, `mathrsfs`, `microtype`, `hyperref`, and `bookmark`.
No bibliography processor, external image, network request, or shell escape is
required by the document.

```sh
make pdf
```

Equivalently:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build article.tex
```

To regenerate the single-file source:

```sh
make standalone
```

`standalone.tex` can then be compiled independently with `pdflatex` or `latexmk`.
The modular source is the editing authority; regenerate `standalone.tex` after
editing a section.

## Reproduce the calculations

The supplied replay was run with Python 3.12.14, SymPy 1.14.0, and mpmath 1.3.0.
Use a standard Python environment with the pinned dependencies:

```sh
python3 -m pip install -r requirements.txt
python3 verification/run_all.py
```

Each of the six verification scripts can also run separately. The scripts need
no network access and no source checkout. They write their results beneath
`data/`. The aggregator records exit status, dependency versions, and individual
logs. Exact assertions are part of the replay, so use ordinary Python execution
without assertion-disabling optimization.

The most important distinction is between **proof**, **exact finite
verification**, and **floating-point diagnostic**. The article establishes the
infinite families. Finite rational computations independently check their
normalizations and concrete certificates. Numerical quadratures and cutoff
experiments test alternative analytic representations; their small residuals
are not certified enclosures or substitutes for proof.

## Integration

See `integration/INTEGRATION.md` before moving the material into the canonical
manuscript. In particular, preserve the attribution of DPL's fixed-gap boundary
determinant and the distinction between the newly resolved `q-p=4` family and
the remaining general conjecture. This bundle does not alter or publish the
repository; it supplies reviewable sources and exact artifacts for integration.
