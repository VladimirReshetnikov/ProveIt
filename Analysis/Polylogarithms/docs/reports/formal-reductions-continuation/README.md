# Formal Reductions and Singular Limits in Polylogarithm Arithmetic

Research continuation for Vladimir Reshetnikov and the ProveIt project, prepared on 10 October 2026.

**Read the article:** `article/main.pdf`.

**Main editable source:** `article/main.tex` and `article/sections/`.

**Single TeX source:** `article/standalone.tex`, generated from the same inputs. Its figure paths are relative to `article/`; keep `article/figures/` beside it.

## Results

The article provides complete proofs of the following additions to the inspected manuscript.

1. The exact Gaussian single-product matrix ranks in every weight, including both formulas in `signed:conj:rank`, an explicit full nullspace, and same-point completeness in the specified coefficient system.
2. A canonical same-point splitting at every cyclotomic level, with full level-three rank corollaries using the earlier residual invariant ring.
3. The formal rational-dilogarithm and logarithmic classification of `J(p/q)` for every positive reduced rational argument. It includes a proper-real-subfield theorem for an individual cyclotomic symbol, exact dyadic norms, and all denominator-obstruction relations.
4. Explicit analytic evaluations of the consecutive rational family, `J(3/4)`, `J(4/5)`, and `J(3/5)`, with full logarithmic and pi-squared correction terms.
5. Complete small-parameter Lerch zero counts and Puiseux expansions, a positive initial root velocity at `n=4,k=3`, the sharp uniform threshold `K_2=1`, and nonmonotonicity of the first `n=2,k=1` branch. The larger branch is strictly decreasing; the smaller branch crosses 1 exactly once and increases thereafter.
6. The first singular Abel coefficient and exact endpoint regularity of every simple zero branch.
7. The angular-zero expansion to every fixed exponential accuracy, uniform for all real `b>0`, explicit coefficients, and divergence of the infinite series even after equal bases are combined.

The article also contains a proposed research program and a precise audit register. A small editorial patch is separate from the new theorem insertions.

## Mathematical scope and attribution

The baseline is ProveIt commit:

`a2a4cf58c49c745058c40e4a6748d472a3420f18`.

The manuscript and all five incoming research archives at that snapshot were inspected. The earlier residual Gaussian spaces and the prior `S4` Möbius-duality certificate are credited as antecedents. The adjacent-argument Herglotz functional equation is credited as a reformulation of Choie–Kumar's known equation; the article makes no exhaustive historical-priority claim for equivalent special-value formulas.

The rank theorems concern the stated rational coefficient systems. Formal Herglotz obstructions concern the rationalized five-term calculus. Neither is a theorem of numerical period independence. Explicit real analytic identities have separately fixed branches and constants. Proofs were independently cross-checked within the research workflow; this is AI-assisted research preparation, not a claim of external peer review or proof-assistant verification.

## Reproduce the computations

Use Python 3.10 or later with the packages in `requirements.txt`. The supplied receipt was produced with Python 3.12. The exact Gaussian and Lerch certificate scripts themselves use only the standard library; the complete runner also uses SymPy and mpmath.

From this directory:

```sh
python3 code/run_checks.py
```

This runs the full packaged checks and writes `data/validation_receipt.json`, recording versions, script hashes, return codes, and output hashes. It performs:

- independent exact Gaussian elimination in weights 2–11 and explicit nullvector checks in selected weights through 63;
- universal-lift checks at levels through 12;
- 32,764 exact Herglotz coefficient tests, rational span checks through conductor 101, and 20 independent 100-digit quadratures;
- 152 exact Lerch polynomial identities, 120 rational sign intervals, and all 11 endpoint certificates needed by the proofs;
- exact angular extraction at four cutoffs, with independent Fourier substitution;
- exact divergence coefficient checks and 15 high-precision angular-root diagnostics.

The floating-point checks are identified as diagnostics. The uniform and all-index theorems are proved in the article.

## Build the PDF

A standard TeX Live installation with `latexmk` and the packages in `article/main.tex` is sufficient:

```sh
make pdf
```

No network access or shell escape is needed. The output is `article/main.pdf`.

To regenerate the flattened source after editing the sections:

```sh
make standalone
```

To redraw the zero-branch figure from the supplied CSV:

```sh
make figures
```

To recompute all 102 plotted roots and 14 independent spectral checks:

```sh
make recompute-figure
```

The figure calculation is separate from the theorem certificates and may take longer than the algebraic verification suite. The plotted minimum is a sampled value, not a certified optimizer.

## Package contents

| Location | Contents |
| --- | --- |
| `article/` | Compiled article, modular TeX, flattened TeX, references, vector PDF and PNG figure |
| `code/` | Exact verifiers, numerical diagnostics, figure reconstruction, and build helpers |
| `data/` | Complete coefficient receipts, the weight-five matrix, rational certificates, numerical data, and validation record |
| `integration/` | Exact editorial patch and insertion/dependency guidance |
| `provenance/` | Pinned source manifests, contribution notes, and source notices |
| `CLAIMS.json` | Claim-by-claim status, proof labels, and verification scope |
| `SHA256SUMS` | Checksums for the delivered files, excluding the checksum file itself |

The copied upstream Stieltjes certificate routine is unchanged. Its source path and SHA-256 are documented in `provenance/SOURCES.md` and its output receipt. It is supplied as an imported dependency of `verify_lerch_boundary.py`; use the package runner above rather than the upstream routine's original standalone CLI, which expects its original report's data layout.

## Integrate into ProveIt

Start with `integration/README.md`. The repository has not been modified. The patch and TeX sections are proposed changes against the pinned source. The existing bibliography and chapter theorem-numbering conventions can be retained when the fragments are inserted.
