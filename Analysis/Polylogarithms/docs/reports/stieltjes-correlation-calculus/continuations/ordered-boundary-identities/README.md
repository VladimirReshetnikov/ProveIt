# Ordered Boundary Identities and Gamma-Kernel Reconstruction

Research continuation prepared for the ProveIt polylogarithm manuscript, 11 October 2026.

## Main results

This package supplies full ordinary mathematical proofs of two complementary advances:

1. An ordered two-particle finite-difference identity on an open complex domain. It gives the complete polar coefficients, directional values at vanishing-weight parameters, finite integer-order polygamma formulas, one digamma master generating all convergent positive orders, a Gamma primitive, a cutoff polylogarithm identity, and ordinary all-order Stieltjes transforms.
2. An explicit Gamma-integral basis of the harmonic-tail fixed-gap null equation. Its normalization and signed determinant asymptotic prove eventual optimal first-prefix reconstruction for every fixed even gap. The first relative correction is an explicit harmonic-number formula.

The higher-rank part gives a constructive finite collision-block reduction with at most floor((r+1)/2) free ordered indices. All stated convergence restrictions and collective-continuation conventions are retained.

The results are new relative to the inspected source material. No global historical priority, external peer review, or proof-assistant formalization is claimed. The full unequal-even reconstruction conjecture, complete gap-six coverage, and Gaussian S6/revised S8 remain open here. The fixed-gap theorem does not provide an effective threshold.

## Contents

| Path | Purpose |
|---|---|
| Ordered_Boundary_Identities_and_Gamma_Kernels.pdf | Complete typeset article |
| Ordered_Boundary_Identities_and_Gamma_Kernels.tex | Standalone TeX, requiring no external source fragments |
| article.tex, sections/, references.tex | Modular editable source |
| build.py | Standalone assembly and clean PDF build |
| ordered_identity.py | Exact integer-order identity evaluator |
| verification/ | Portable exact checks, numerical diagnostics, and complete JSON results |
| evidence/ | Independent audit notes, runtime, source map, build and visual-review records |
| CLAIM_STATUS.json | Machine-readable theorem scope and remaining questions |
| integration/INTEGRATION.md | Proposed placement, dependencies, and status updates |
| integration/remove_duplicate_readme_paragraph.patch | Optional narrowly scoped README correction |

The pinned source revision is **e3d7ec5d3f9be259c1f91edaea4389f4e79b5b03**. The canonical manuscript and all seven incoming polylogarithm archives present at that snapshot were inspected for current questions and overlap. The source map specifies the relevant paths and dependencies. The source checkout was not changed.

## Build the article

With Python 3.10 or newer and a standard TeX Live installation containing latexmk:

~~~bash
python build.py
~~~

This assembles the standalone TeX from the modular files, compiles it, checks the final TeX log for unresolved references and overfull boxes, and places the PDF beside the source. Intermediate compiler files go in build/latex/. To assemble without compiling:

~~~bash
python build.py --assemble-only
~~~

The standalone TeX can also be compiled directly with latexmk -pdf. After substantive edits, repeat visual review; a successful compile alone is not a layout review.

## Reproduce the mathematics checks

Python dependencies are SymPy and mpmath (see requirements.txt). The supplied results were produced with Python 3.12, SymPy 1.14.0, and mpmath 1.3.0. Exact checks use rational/integer arithmetic.

~~~bash
python verification/run_verification.py
~~~

This runs the exact finite cutoff, partial-fraction, parity, generator-coefficient, directional-table, digamma-master, Stieltjes-jet, localization, and Gamma-normalization checks. Two normalization corruption controls and the altered contact-table control must be detected.

To include original ordinary sums, Stieltjes integrals, arcsine integrals, and the Gamma basis:

~~~bash
python verification/run_verification.py --full
~~~

The optional determinant-asymptotic replay also propagates exact rational recurrences through b=120:

~~~bash
python verification/run_verification.py --asymptotics
~~~

Every script can be run separately from any working directory. JSON output is written beside the corresponding program (the exact Gamma checker also accepts --output). The default exact runner and every individual numerical suite were exercised during preparation. The supplied optional asymptotic results were regenerated after replacing an intermediate binary-float power by an mpmath power.

The numerical results are floating-point diagnostics, not interval certificates. Positive analytic tail envelopes, convergent Taylor-tail estimates, and observed quadrature differences are labelled separately. The article supplies the proofs of the infinite identities and eventual assertions.

## Generate a specific identity

~~~bash
python ordered_identity.py 2 3
python ordered_identity.py 2 2 --a 1 --b 2 --latex
~~~

The arguments are positive integer orders p>=1, q>=2 and positive rational shifts. The evaluator uses the proved finite polygamma formula, including removable confluence. It does not approximate the original double sum.

## Integration scope

The package is intended for review and integration into ProveIt. It does not itself promote incoming claims to canonical acceptance. In particular, the previously supplied smaller-order-ten and smaller-order-twelve theorems belong to their existing incoming reports; they are not claimed as new here. The new reconstruction theorem controls the different regime in which both tail orders tend to infinity at fixed gap.
