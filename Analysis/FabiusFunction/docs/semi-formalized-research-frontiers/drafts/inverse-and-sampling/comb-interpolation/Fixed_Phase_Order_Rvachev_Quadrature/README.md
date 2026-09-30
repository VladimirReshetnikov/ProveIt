# Sharp Fixed-Phase Order of Rvachev Quadrature

Research manuscript prepared with ChatGPT, 29 September 2026.

## Main results

For the normalized Rvachev lattice quadrature at mesh parameter M = 2^d,
the maximal polynomial exactness at a fixed phase is exactly d+1. The two
known special phases both fail at degree d+2. The article proves this for
all d >= 0, with a signed leading term and relative error less than 1/4.

For M = 2^(r-1)m with m positive and odd, the article gives an exact
next-defect identity, an explicit sufficient nonvanishing inequality, and
eventual maximality. An entirely elementary sufficient cutoff is

    J = max(2, 1 + ceil(log2(m)))
    r >= 2*J*(m+1) + 4.

The article also proves a stationary-point classification for the first
defect, stability under C^1 perturbations, a parity-dependent exponential
expansion, and sharp-order consequences for deconvolved synthesis and
uniform-grid refinement.

## Files

- `article.tex`: self-contained LaTeX source, including bibliography.
- `article.pdf`: compiled 21-page article.
- `build.sh`: serial three-pass PDF build.
- `reproducibility/verify.py`: independent exact and numerical checks.
- `requirements.txt`: numerical-check dependency used for this run.
- `validation/exact_results.json`: 978 passed exact assertions and rational outputs.
- `validation/numerical_results.json`: 960 passed numerical assertions and diagnostics.
- `validation/artifact_validation.json`: build, rendering, and artifact metadata.

## Build the article

A TeX Live installation with newtx, amsmath/amsthm, mathtools, microtype,
geometry, booktabs, array, longtable, enumitem, fancyhdr, xurl, hyperref,
and cleveref is required. From this directory run:

```sh
bash build.sh
```

The bibliography is embedded in the source; BibTeX is not needed. There
are no external figure or font files in the package.

## Reproduce the checks

The exact component needs only Python's standard library:

```sh
python reproducibility/verify.py --exact-only
```

For the numerical component:

```sh
python -m pip install -r requirements.txt
python reproducibility/verify.py --numeric-only
```

With no option, the program runs both sets. Results are written to the
`validation` directory. The exact dyadic evaluator rejects non-dyadic
arguments rather than silently rounding them.

## Status and boundaries

These are ordinary analytic proofs, not new Lean-verified declarations.
No Lean build was run. The numerical component uses high-precision
floating-point arithmetic, not directed-rounding intervals; its assertions
are diagnostics and are not claimed as certified real-number inequalities.
The main theorems are proved analytically without assuming test success.

The general all-level, all-integer-mesh maximality question remains open in
this manuscript. Every dyadic mesh is settled, and for every fixed odd
part all sufficiently large refinement levels are settled with an explicit
cutoff. A failed sufficient test does not establish an exceptional mesh.

The earlier repository article already proves first-superconvergent phase
completeness and classifies optimal uniform phase filters. Those results
are credited, not claimed as new here. Novelty relative to the entire
literature has not been independently certified.

## Repository provenance

Inspected ProveIt snapshot:

    23dd71d2d3d5e85d2b97a8cc45f55e735d69a4ae

Primary baseline manuscript:

    Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/
    drafts/inverse-and-sampling/comb-interpolation/
    Optimal_Phase_Filters/article.tex

Baseline title: "Complete Superconvergence Phases and Optimal Phase
Filters for Rvachev Quadrature", dated 28 September 2026. It explicitly
leaves fixed-phase next-degree maximality as a further research question.

Relevant Lean module:

    Analysis/FabiusFunction/Lean/FabiusFunction/
    RvachevSuperconvergentSynthesis.lean

The article contains full source references and a proof-dependency ledger.
No repository files were changed.
