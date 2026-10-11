# Higher Reflection Identities and Resonant Zeta Calculus

**Complex-power sine kernels, harmonic parity, geometric collisions, and quartic Tornheim derivatives**

Research continuation for Vladimir Reshetnikov's ProveIt project, 11 October 2026.

## Read first

- `Higher_Reflection_Identities.pdf` is the complete article.
- `Higher_Reflection_Identities.tex` is the complete, self-contained LaTeX source. It needs no project-specific input files.
- `article.tex`, `preamble.tex`, `references.tex`, and `sections/` are the corresponding modular sources.
- `SOURCE_AUDIT.md` identifies the pinned sources, inherited results, research questions, and correction status.
- `CLAIMS.md` maps the main results to their precise qualifications.
- `verification/` contains five independently developed check scripts and their recorded JSON results. Its README explains what each check establishes.

The source baseline is ProveIt revision `c2cb285b64273e4cb2c8d7a03c68a4a99ac812d4`, including all nine incoming archives present there. The work continues the integration, harmonic, reflection, Stieltjes-contact, and Tornheim parts of the canonical polylogarithm manuscript. It is supplied for review and integration; it is not a proof-assistant formalization.

## Main results

1. **A completed two-parameter Hurwitz transform.** A complex-power sine weight has explicit Gamma Fourier coefficients and an Euler integral involving a polylogarithm. Its complete crossing polar term generates every coordinate finite-part moment of `gamma_m^(p)(x)` against a power of `log(sin(pi*x)/pi)`. The classical transform ingredients are credited; the completed all-index generator and its consequences are the contribution.
2. **An ordinary-constant cancellation identity.** A linear combination of a digamma cube and a logarithmic sine-square moment cancels the retained harmonic Stieltjes coefficient. The previously established cubic bridge is used explicitly, not relabeled as new.
3. **An exact harmonic-polynomial classification.** Centered Dirichlet regularity at every nonpositive even integer is equivalent to a finite reflection-invariance identity on the numerator polynomial. With algebraic coefficients, the numerator must be independent of all even-index harmonic variables. An all-degree Bernoulli formula evaluates the centered even moments of a trigamma square.
4. **Geometric collision counterterms.** A finite subset/interpolation formula subtracts any cluster of periodic digamma factors, with every argument-derivative order at Stieltjes index zero. The remainder extends analytically through total collision even for hierarchical gap scales. Explicit hierarchical cubic, equally spaced quartic, and derivative-pair formulas are included.
5. **The full quartic Tornheim directional layer.** Every admissible fourth ray derivative is reconstructed from three specified, convergently represented coordinates. Cyclic sums eliminate two of them, and a short weighted difference eliminates all three. A proved all-order formal dimension formula explains the extra cyclic coordinate at order five.

The Gaussian S6 and revised S8 identities remain open. The report does not assert worldwide priority for every specialization, arithmetic independence of retained constants, or completeness of the stated formal relation system among all possible Tornheim identities.

## Build

The PDF uses a standard pdfLaTeX installation with `latexmk`, Latin Modern fonts, and the packages named in `preamble.tex`. No shell escape is required. From the package root:

```bash
python3 build.py
```

This refreshes the standalone TeX source, compiles the modular article in `build/`, and copies the resulting PDF to `Higher_Reflection_Identities.pdf`. To regenerate only the standalone source:

```bash
python3 build.py --tex-only
```

The standalone source can also be compiled directly with pdfLaTeX or latexmk. Bibliography entries are embedded; BibTeX and internet access are unnecessary.

## Reproduce the checks

Use Python 3 with mpmath 1.3.0 and SymPy 1.14.0. See `verification/README.md` for detailed methods and individual commands. To run all five scripts on temporary copies and save fresh records without overwriting the delivered JSON files:

```bash
python3 run_checks.py
```

Fresh records are written to `verification/reproduced/`. High-precision quadratures can take several minutes. The analytic proofs establish the general identities; finite symbolic checks and non-interval floating-point diagnostics provide independent verification of sensitive calculations. The centered tail appendix additionally proves an analytic truncation bound.

## Suggested integration

The report naturally supplements the canonical manuscript's integration/reflection, harmonic, Stieltjes-contact, and Tornheim sections. Preserve the source pin and citations, especially the distinction between the inherited cubic bridge and the new cancellation, and between all-factor spectral completion and the new moving geometric theorem. The all-order dimension theorem concerns exactly its three stated formal conditions. The collision theorem is restricted to Stieltjes index zero and unit frequency. The four-volume manuscript was not exhaustively audited.

No checksum or line-ending normalization work is part of this delivery.
