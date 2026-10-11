# Bernoulli Determinants, Cubic Tornheim Jets, and Canonical Digamma Integrals

Research continuation for ProveIt, prepared on 11 October 2026 against repository commit `f7e35be357654198c1546fd40f363694c5bcc2cc`.

## Read the article

- `Bernoulli_Tornheim_Digamma_Identities.pdf` is the complete article.
- `Bernoulli_Tornheim_Digamma_Identities.tex` is the complete flattened source. It compiles without the modular files or a bibliography database.
- `article.tex`, `sections/`, and `references.tex` provide the same article in modules for integration.
- `integration/INTEGRATION.md` maps the contributions to the source questions and records their precise limits.
- `integration/source_map.json` records the pinned sources and theorem labels.

The article proves the optimal moment prefix for every unequal even pair with smaller order 2, 4, or 6; explicit rational harmonic-tail identities; a general fixed-size determinant reduction; cubic Tornheim cancellation identities; a complete local ambiguity theorem; and differential-polynomial normal forms with normalized sixth and seventh digamma formulas. It includes twelve further research questions. The remaining unequal-order prefix range is `8 <= p < q`.

The shifted Bernoulli Hankel and differential-algebra machinery have classical antecedents. The height-one Mellin/Gamma bridge is inherited and reproved in the required convention. The article distinguishes these foundations from the new continuations. No historical priority or arithmetic independence claim is inferred from a formal rank calculation.

## Build

Use Python 3 and a TeX distribution providing `pdflatex` and the packages listed in `article.tex`:

```bash
python build.py
```

This writes the flattened `.tex`, compiles it in three passes, and copies the PDF to the package root. Build auxiliaries go into `build/`. To regenerate only the flattened source:

```bash
python build.py --tex-only
```

The distributed PDF was checked for undefined references, overfull boxes, clipping, and page layout. The compiled article uses no generated illustrations, external images, or network resources.

## Reproduce the mathematics

The tested Python environment was Python 3.12.14, SymPy 1.14.0, and mpmath 1.3.0. The two package versions are pinned in `requirements.txt`.

```bash
python -m pip install -r requirements.txt
python verification/verify_all.py
```

The default run replays the exact certificates. Include the independent numerical diagnostics with:

```bash
python verification/verify_all.py --numerical
```

Each constituent program can also be run separately. Most programs write their results to `results/`; the short order-four tail verifier prints its exact-check status. The runner records versions, parameters, exit status, and an output log for every program. Replaying a numerical program can change timings and the last displayed rounding digits.

### What the checks establish

The eleven verification programs check source-matrix constructions, factorization identities, finite parameter-polynomial identities, partition reductions, endpoint constants, and the Tornheim local restriction matrices using exact rational arithmetic, and supply independent numerical diagnostics. The order-six proof uses the explicitly defined integer polynomial recorded in `results/verify_moment_rank_six.json`; its certificate treats b as an indeterminate and proves the needed polynomial identities exactly. The other finite checks complement the uniform proofs in the article.

The numerical programs evaluate convergent harmonic sums, subtracted Mellin integrals, and directly subtracted finite-part integrals by independent routes. Their residuals are diagnostic floating-point comparisons. They are not interval enclosures and are not used as proofs.

The remaining mixed sixth and seventh integrals are defined explicitly. The article does not claim to eliminate them or prove them arithmetically independent. The short Gaussian `S6` and revised `S8` identities are not settled by this continuation.

## Integration

This package is self-contained and does not require a live ProveIt checkout to build or replay. Its source map points to the exact source snapshot used. The existing repository and its incoming archives were not modified by the research process. Suggested theorem and status changes are in the integration guide.
