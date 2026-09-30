# Moment Determinacy and Nonlinear Transseries

**A sharp Gevrey threshold, exact flat defects, convergent ambiguity sectors,
and Lambert–W folds**

Research report prepared for Vladimir Reshetnikov, 29 September 2026.

## Contents

- `moment_determinacy_transseries.tex`: standalone article source.
- `moment_determinacy_transseries.pdf`: the 26-page compiled article (25
  pages as delivered; see the amendments below).
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
at most two has one positive Stieltjes realization, whereas for each order
above two some formal inverse of exactly that order has a continuum of
distinct realizations (not every one does; see the remark after Theorem
3.5).

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
and tabular pages were also inspected at full rendering size. The filed PDF
was rebuilt on filing with editorial notes (see the amendments below).

## Reproduce the checks

Python 3.10 or later and mpmath are required.

```sh
python -m pip install -r requirements.txt
python verify.py --output verification_results.json --dps 130
```

The recorded run used Python 3.13.5 and mpmath 1.3.0 at 130 decimal digits.
All assertions passed. Run from the package directory, the command above
rewrites the recorded `verification_results.json` (a rerun on a copy on
2026-09-29, on Windows, reproduced it byte for byte). Without `--output`, a
run at another precision writes `verification_results_dps<N>.json` instead
(editorial amendment below), so the recorded file is not replaced by
different digits. Where bare `python` does not resolve, use `py` or
`uv run --no-project --with mpmath==1.3.0 python`. Do not run with Python's
`-O` flag, which disables assertions. The script rejects a precision below 115 digits because several
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

## Editorial amendments (ProveIt, 2026-09-29)

These changes were made on filing, after the batch-51 delivery. Every change
to the article text is marked in `moment_determinacy_transseries.tex` by a
comment beginning `% ed. (2026-09-29)`; visible additions are headed
"Editorial note (ProveIt, 2026-09-29)" or, in the bibliography,
"[Editorial addition, ProveIt, 2026-09-29.]".

- `moment_determinacy_transseries.tex`:
  - an unnumbered `ednote` environment for editorial notes (no numbering
    changes);
  - end of Section 1.1: an editorial note on the repository results at the
    determinate side of Theorem 3.2: the canonical volume's
    `p8:thm:bell` (a Stieltjes transform with Bell-number moments,
    Gevrey order at most one, hence the only positive representation by
    Lemma 3.4) and the certified q-to-1 package's `thm:stieltjes` and
    `thm:pade` (a determinate measure at the factorial-square boundary,
    with two-sided Padé bounds); the inverse-digamma package's
    representation lies outside the class used here; "realization" here is
    not the Hardy-field sense of the volume's `plt:def:cmp-realization`;
    the Lambert limit of (8.5) is the volume's Cayley tree function
    `p1:def:cayley`;
  - end of Section 10.3: an editorial note naming the Lean modules alluded
    to (`Analysis/Transseries/Lean/Transseries/TransseriesFlat.lean`,
    `TransseriesWellBased.lean`, `TransseriesScale.lean`) and two related,
    unused machine-checked facts (`Fabius.exists_eq_in_residual_interval`,
    `Fabius.cayleyTree`); no statement of the article is formalized;
  - three editorial bibliography entries (`ed:tai`, `ed:ciq`, `ed:ids`),
    appended after the delivered ones.
- `moment_determinacy_transseries.pdf`: rebuilt from the amended source (26
  pages; the delivered PDF had 25; no errors, undefined references, multiply
  defined labels, duplicate destinations or box warnings).
- `verify.py`: without `--output`, a run at a precision other than 130
  digits writes `verification_results_dps<N>.json`. A default run on a copy
  reproduced `verification_results.json` byte for byte, and a `--dps 120`
  run left it untouched.
- `README.md`: the Gevrey-threshold sentence now matches the remark after
  Theorem 3.5 (some, not every, formal inverse of each order above two has a
  continuum of realizations); the rerun behaviour is documented; the page
  count is updated; this section.
