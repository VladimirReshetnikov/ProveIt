# Integral distribution and reflection

**Unimodular Distribution Certificates and Exact Reflection Torsion for Cyclotomic Polylogarithms**  
Research report prepared for Vladimir Reshetnikov, 9 October 2026.

This package continues the integral-structure research questions in the ProveIt polylogarithm manuscript. It contains a complete article, proofs, integer polynomial certificates, an independent verifier, raw-matrix Smith checks, and proposed integration changes. The source snapshot is pinned in `PROVENANCE.json`.

## Main results

For the complete prime-distribution presentation on the grid `(q^{-1} Z)/Z`, with independent weights `A_p`, an explicitly selected set of original rows has a determinant-one minor. A fixed set of original point symbols is therefore a basis over `Z[A_p]` and remains a basis over **every commutative coefficient ring**. The full unreflected matrix is equivalent to an identity block and zeros; its nonzero integer Smith factors are all one.

Reflection is a separate operation. After imposing either `e_{-x}=e_x` or `e_{-x}=-e_x`, the integral quotient can have two-torsion. The article proves its complete multiplicity for arbitrary integer weights and for arbitrary one-variable integral jets. More generally, it identifies the reflection torsion with explicitly specified binary Koszul homology. A worked example shows why a reflected torsion-free abelian quotient need not be free over the jet ring.

The normal forms also give exact polylogarithm identities at every complex order, including two short level-12 and level-30 formulas. A pole-cancelled differentiation theorem supplies all order derivatives at `s=1`, with the endpoint correction that ordinary product differentiation would miss.

## Read the article

- `article/integral_distribution.pdf`: compiled article.
- `article/integral_distribution.tex`: self-contained LaTeX source, including references.
- `RESULTS.md`: theorem and verification map.
- `integration/`: a manuscript insertion, bibliography entry, and targeted correction notes.

The suggested repository location is:

```
Analysis/Polylogarithms/docs/reports/integral-distribution-reflection/
```

No GitHub files were modified and no pull request was opened. The integration files are proposals, not an assertion that the report has already been incorporated.

## Reproduce the exact core

Python 3.10 or later is required; the delivered runs used Python 3.13.5. The core uses only the standard library. Run from this directory, without `-O`:

```sh
python code/run_checks.py
python code/check_resolution.py
python code/check_short_identities.py
python code/verify_certificates.py data/normal_forms_q12.json
```

The independent verifier does **not** import the generator. It reconstructs the original distribution rows, checks the triangular unit minor, and proves each recorded point identity by exact polynomial back-substitution. It additionally checks every raw row against the recorded normal forms. Assertions are deliberate validation gates; verifier entry points reject optimized execution.

Generate another certificate with:

```sh
python code/distribution.py 24 --output data/normal_forms_q24.json
python code/verify_certificates.py data/normal_forms_q24.json
```

## Optional independent checks

```sh
python -m pip install -r requirements-optional.txt
python code/check_smith.py
python code/check_products_and_controls.py
python code/numerical_checks.py
```

The raw Smith checker uses SymPy and does not import the normal-form generator. The product checker certifies the two displayed cyclotomic products by integer polynomial division and rejects three intentionally corrupted certificates. The numerical checks use mpmath at two working precisions, with a finite Hurwitz Fourier evaluation and a Stieltjes-coefficient evaluator for derivatives.

**Numerical residuals are diagnostics, not interval certificates and not proofs of equality.** The all-level theorems and all-order identities have written algebraic and analytic proofs. The finite checks test their implementations. No result is represented as proof-assistant formalized.

## Build

Install a TeX distribution providing the packages in the article preamble, then run:

```sh
python code/build_article.py
```

The builder uses pdfLaTeX, checks final reference and overfull-box warnings, and saves `logs/latex_final.txt`. The supplied PDF was also rendered and visually reviewed. The optional Makefile groups the same commands.

## Verification inventory

The delivered run checked 119 polynomial levels, 3,317 raw polynomial rows, and 7,259 point normal forms. Seven frozen files supply 414 point identities independently replayed against 366 raw rows. There are 2,348 scalar parity cases, 1,635 finite-jet cases, 136 reflected and 68 unreflected direct Smith computations, and 498 resolution checks over finite fields. Two short raw-row certificates, two exact cyclotomic product certificates, three corruption controls, and twenty floating-point diagnostics are also included. Individual records are in `data/`; console receipts are in `logs/`.

## Scope and attribution

The ordinary universal distribution, universal norm distributions, and Anderson-type resolutions are established literature. The article cites Kubert and Ouyang and gives complete proofs for the precise weighted presentation used here. The contribution is a concrete strengthening and completion of this manuscript's integral, modular, reflection, and jet questions; worldwide priority for the entire formulation has not been established.

A formal point-symbol basis does not imply numerical independence of evaluated periods. The Gaussian `S_6` conjecture is not proved here. Higher-depth relations and arithmetic evaluation kernels remain separate questions. Corrections are limited to the inspected portions of the pinned manuscript, not a claim of a comprehensive audit of every chapter.

`MANIFEST.sha256` records the delivered file contents, excluding itself. Rerunning generators or the PDF builder can legitimately change metadata or compiler logs; create a fresh manifest after intentional changes. No font files or third-party source PDFs are included.
