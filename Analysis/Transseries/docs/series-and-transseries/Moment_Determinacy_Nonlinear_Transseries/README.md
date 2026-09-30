# Moment Determinacy and Nonlinear Transseries

**A sharp Gevrey threshold, exact flat defects, convergent ambiguity sectors,
and Lambert–W folds**

Research report prepared for Vladimir Reshetnikov, 29 September 2026.

## Contents

- `moment_determinacy_transseries.tex`: standalone article source.
- `moment_determinacy_transseries.pdf`: the 25-page compiled article.
- `verify.py`: exact finite algebra and high-precision consistency checks.
- `verification_results.json`: output of the recorded successful run.
- `CLAIM_LEDGER.md`: result-by-result scope and status.
- `SOURCE_NOTES.md`: repository comparison, primary literature, and limits.
- `build.sh`: a three-pass PDF build.
- `requirements.txt`: the numerical dependency used in the recorded run.

## Results

The report studies positive Stieltjes transforms

    S_mu(t) = integral 1/(1+t*lambda) dmu(lambda)

and the positive inverse defined by `T_mu(y) = y*S_mu(T_mu(y))`.

Theorem 3.2 identifies uniqueness of the analytic inverse realization with
Stieltjes moment determinacy. A cancellation-free Lagrange formula preserves
the exact factorial-growth order of moments. Theorem 3.5 gives a sharp
universal guarantee: a realizable formal inverse of coefficient-Gevrey order
at most two has one positive Stieltjes realization, whereas each order above
two permits a continuum of distinct realizations.

The generalized gamma family has an exact exponential defect. A bilateral
geometric family has an exact reciprocal-theta defect, with a nonconstant
log-periodic amplitude, comparable to the least moment-remainder bound.
A separate shifted-lattice family remains nonunique even under the same
exact first-order q-difference equation, and its inverse curves cross
infinitely often.

Sections 6–8 develop quantitative nonlinear results: relative gap corrections,
an information floor for coefficient-only methods, convergent expansions in
the hidden parameter with explicit tails, and the asymptotically exact
parameter radius. A scaled deformation map tends to v*exp(-v), giving
Cayley-number sector limits and a Lambert-W fold. The first fold correction
retains the gamma parameters or the theta phase.

## Mathematical status

The report contains conventional mathematical proofs. It does not contain
Lean formalizations. Classical moment indeterminacy, the Hardy-type
factorial-square criterion, the Stieltjes–Wigert setting, Jacobi's triple
product, and Lagrange inversion are explicitly attributed rather than
claimed as new discoveries.

The quantitative nonlinear synthesis is developed in this report; exhaustive
historical priority is not established. The repository comparison is targeted,
not a full audit. The paper does not claim to solve the general Hahn-series
realization question described in the repository.

The Gevrey threshold refers to formal coefficient growth in a specified
positive-measure inverse class. It is not a uniqueness theorem for arbitrary
smooth functions or all sectorial analytic functions. The least moment bound
is not identified with an exact minimum of actual remainder errors. The
leading parameter radius is proved, but the real fold is not asserted to be
the exactly nearest singularity for every fixed positive y.

## Build

A TeX Live installation with pdfLaTeX and the standard packages declared in
the source is sufficient. There are no external image or bibliography files.

```sh
sh build.sh
```

The delivered PDF was compiled in repeated pdfLaTeX passes. The final build
had no errors, unresolved references, or overfull/underfull box warnings.
All 25 pages were rendered for a visual review; representative mathematical
and tabular pages were also inspected at full rendering size.

## Reproduce the checks

Python 3.10 or later and mpmath are required.

```sh
python -m pip install -r requirements.txt
python verify.py --output verification_results.json --dps 130
```

The recorded run used Python 3.13.5 and mpmath 1.3.0 at 130 decimal digits.
All assertions passed. Do not run with Python's `-O` flag, which disables
assertions. The script rejects a precision below 115 digits because several
checks subtract extremely close values.

Checks include twelve exact cubic inverse coefficients and independent
formal substitution; even/odd q-lattice moments through order twelve;
shifted-lattice moments through order eight and the exact first-order
q-equation; direct-sum, product, and Gaussian-theta evaluations of the flat
defect; gamma signed-integral quadratures; inverse-gap corrections; local
fold corrections; and the first two parameter sectors with their analytic
tail bound.

**Numerical qualification:** the analytic checks use high-precision
floating-point arithmetic, not outward-rounded interval arithmetic. They
are consistency tests, not rigorous numerical enclosures or proofs of the
infinite statements. The article provides the mathematical proofs.
