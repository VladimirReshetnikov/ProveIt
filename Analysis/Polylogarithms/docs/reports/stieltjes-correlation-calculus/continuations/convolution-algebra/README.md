# A Convolution Algebra of Stieltjes Functions

**Research continuation for Vladimir Reshetnikov / ProveIt, 10 October 2026.**

The package contains a 20-page article with ordinary analytic proofs, exact finite-algebra certificates, independent high-precision diagnostics, and repository-integration notes. It is identity-focused, not a bounds or zero-geometry report.

## Main results

The canonical periodic finite parts of the generalized Stieltjes functions form a free one-generator convolution algebra. An all-index Bell normal form and a bivariate Gamma quotient give every multiplication coefficient. The article converts these distribution identities into explicit absolutely convergent subtracted integrals, identifies the exact contact terms needed when differentiating finite parts, and proves a finite reduction for all convolutions of differentiated Stieltjes functions. In the polygamma case only two Hurwitz-zeta jets remain off the integer point.

At the integrated end, every circular convolution power of centered log Gamma reduces to finitely many zeta jets at one negative integer. Reflection produces an all-shift log-Gamma correlation formula using polylogarithmic order derivatives. The correlation formula at zero shift recovers the classical second moment, rather than claiming it anew.

## Provenance and scope

Repository: `VladimirReshetnikov/ProveIt`.

Pinned snapshot: `0efdbaa6944357e578a8839ec88d040c6e05681c`.

Primary manuscript area: `Analysis/Polylogarithms/docs/manuscript/`.

The integration, differentiation, reflected-moment, and discovery chapters and the incoming inventory/intake instructions were inspected. The binary incoming archives were **not** individually extracted or exhaustively reviewed. The snapshot already describes S4 as proved; this package does not claim to solve S4 again or settle the remaining S6 or period-independence questions.

The nonsingular normalized Hurwitz convolution law is already stated in Zhi-Hong Sun, *On the properties of invariant functions*, arXiv:2209.14625, Remark 3.2. It is explicitly attributed. The current contribution develops its singular finite-part algebra, normalization corrections, and explicit derivative/integral consequences. Literature priority for every specialization has not been established. No proof-assistant verification is claimed. No remote repository files were modified.

## Files

- `article.tex` and `article.pdf`: complete self-contained article and compiled PDF.
- `verification/verify.py`: replayable exact and numerical suites; no network access needed.
- `verification/identity_catalog.json`: 25 exact Stieltjes convolution rules and six log-Gamma convolution-power coefficient lists.
- `verification/exact_results.json`: 229 passed exact assertions.
- `verification/numeric_results_40dps.json`, `verification/numeric_results_50dps.json`: 31 passed checks at each precision.
- `verification/numeric_results.json`: latest numerical run (50 decimal digits).
- `verification/results.json`: compact combined verification summary.
- `verification/NUMERICAL_NOTES.md`: independent representations, cancellation controls, and limitations.
- `SOURCE_AUDIT.md`: inspected material, classical antecedents, and novelty boundaries.
- `integration/INTEGRATION.md`: proposed report placement and manuscript-section mapping.
- `integration/CORRECTIONS.md`: narrowly scoped corrections and editorial clarifications.
- `requirements.txt`, `Makefile`: dependencies and build commands.
- `package_metadata.json`: source pin, proof status, and artifact summary.

## Verification actually run

Tested environment: Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0.

The exact suite passed all **229 assertions**. The numerical suite passed **31 checks at 40 decimal digits**, with maximum scaled residual approximately `8.43e-37`, and **31 checks at 50 decimal digits**, with maximum scaled residual approximately `7.04e-47`. Scaled residual means `abs(lhs-rhs)/(1+abs(rhs))`.

The exact assertions concern finite polynomial identities relative to the stated Gamma, Bell, and derivative formulas. Numerical residuals are floating-point diagnostics, not rigorous enclosures or equality certificates. The all-index analytic results are established by the proofs in the article, not by a finite collection of tests.

## Reproduce

```sh
python -m pip install -r requirements.txt
python verification/verify.py --exact-only
python verification/verify.py --numeric-only --dps 40
python verification/verify.py --numeric-only --dps 50
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, use `make pdf`, `make exact`, or `make numeric`. A fresh LaTeX build may need a third pass for a fully settled table of contents. The final delivered PDF was compiled until there were no unresolved-reference or overfull-box warnings.

The verifier writes outputs beside itself. Use a working copy when preserving delivered evidence. The precision-stamped numerical output files are preserved records; ordinary reruns overwrite only `numeric_results.json` unless explicitly copied.

## Important conventions

All stars denote convolution on the unit circle, **not pointwise products**. The unit of the mean-zero convolution algebra is `I = delta_0 - 1`, not the scalar function 1. Finite parts use the exact one-sided cutoff in the article. Spectral derivatives of zeta and polylogarithms are different from derivatives in their arguments. Convolution powers of log Gamma are not its ordinary pointwise moments; the cubic Tornheim-moment reduction problem is not claimed solved.
