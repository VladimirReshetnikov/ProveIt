# Resonant Lerch Limits and Shifted Gamma Correlations

**Uniform Herglotz asymptotics and nonseparable distribution jets**  
Research continuation for Vladimir Reshetnikov's ProveIt repository.  
Prepared with OpenAI ChatGPT, 10 October 2026.

## Read first

The complete article is `polylogarithms_resonance_correlations.pdf`; its
entry-point source is `polylogarithms_resonance_correlations.tex`.
The article contains the definitions, full proofs, bibliography, numerical
scope statements, source audit, and sixteen further research questions.

The baseline is pinned at ProveIt commit
`570b0567f311cf1890865065896be2665f469e4f`. The supplied `docs/incoming`
entry point is an intake ledger at that revision; relevant earlier reports
are already integrated or preserved in the thematic reports tree.

## Mathematical contributions

1. **Uniform positive-integer resonance.** A centered Lerch normalization
   admits an all-orders expansion uniform in every integer order, including
   orders tending to infinity. Its coefficient formula separates generalized
   Stieltjes constants from polygamma data.
2. **Shifted Gamma correlations.** An exact convergent expansion proves
   strict convexity of the periodic autocorrelation of log Gamma, identifies
   its unique half-shift minimum, and gives a one-sided truncation bound.
   Shifted Hurwitz products, all-order cusp polynomials, and balanced
   negative-polygamma correlations are also proved.
3. **Herglotz joint-limit theory.** An exact gamma-mixture identity gives
   the complete transition expansion at x = r lambda and an explicit
   finite-order Taylor bound. The profile has divisor, Bessel, Gamma,
   and dilogarithm representations; its centered reciprocal continuation
   has completely classified interlacing imaginary zeros.
4. **Nonseparable formal jets.** A local Frobenius-algebra argument proves
   the binomial colength law whenever the active ideal needs at most two
   generators. An explicit three-generator example disproves the
   unrestricted extrapolation, and a two-generator example distinguishes
   dimensions from module structure.

The existing S6 special-value conjecture is not proved. Classical identities
and already integrated fixed-order results are credited separately.
No exhaustive worldwide-priority claim is made. This package contains
mathematical proofs and replayable checks, not a Lean formalization.

## Build the PDF

A standard TeX Live installation with pdfLaTeX, AMS packages, Latin Modern,
geometry, microtype, booktabs, xurl, enumitem, fancyhdr, and hyperref suffices.
The figure PDF is already included, so building does not require Python
plotting libraries.

```sh
python3 code/build.py
```

The helper runs three LaTeX passes, checks for unresolved references and
overfull boxes, and records `data/build_info.json`. Alternatively, run
`pdflatex -interaction=nonstopmode -halt-on-error
polylogarithms_resonance_correlations.tex` three times from this directory.

## Replay the evidence

Python 3.12 was used. The exact algebra check needs only the standard library:

```sh
python3 code/run_checks.py --suite exact
```

For the analytic diagnostics and figure, install the versions in
`requirements.txt` in your preferred Python environment. Then run any
selected suite:

```sh
python3 code/run_checks.py --suite resonance
python3 code/run_checks.py --suite gamma
python3 code/run_checks.py --suite herglotz
python3 code/run_checks.py --suite all
python3 code/plot_gamma_correlation.py
```

The Herglotz suite includes hundreds of high-precision complex Bessel
evaluations and can take substantially longer than the other suites. All
recorded outputs are supplied, so readers can inspect them without replaying.
The plotting source writes the two figure formats and its data metadata.

### What the checks establish

- `verify_nonseparable_jets.py` independently constructs the original
  point/monomial relation matrices and the Koszul differential matrices,
  using exact binary elimination. The general algebra theorem is proved
  in the article; these calculations additionally prove the finite ranks
  of the displayed examples.
- `check_resonance.py` checks six direct Lerch identities, three Stieltjes
  finite parts, the coefficient recurrence, and an asymptotic sample grid.
- `check_gamma_correlations.py` compares split quadrature, polylogarithm
  order derivatives, Hurwitz jets, and the convergent odd-zeta series.
- `gamma_correlation.py` is a reusable evaluator with a mathematically
  proved omitted-series bound and a separate independent self-check.
- `check_herglotz.py` compares high-order Hurwitz evaluations, finite
  central-moment inequalities, the Bessel formula, and both primitives.

The analytic checks use arbitrary-precision floating-point arithmetic.
They are diagnostics, not interval proofs. An analytic tail bound controls
omitted terms in exact arithmetic and does not automatically bound
floating-point roundoff. Asymptotic residuals are labeled separately from
identity residuals. Root approximations in `herglotz_checks.json` are not
certified decimal enclosures; their existence, location intervals, simplicity,
and completeness are proved analytically.

## Integration and provenance

See `INTEGRATION.md` for canonical placement and important scope boundaries.
`SOURCE_MANIFEST.json` records the frozen revision and SHA-256 hashes of the
reviewed local source snapshots. `ARTIFACT_MANIFEST.json` inventories this
package with file hashes. The `audits` directory contains supporting proof
notes and the precise external-literature normalization correction.

The external typo is in Gay–Sebbar (2024), printed page 4, immediately after
Eq. (1): with their definition, the correct relation is
`Li_s(z) = z Phi(z,s,1)`. The pinned ProveIt manuscript already has the
correct normalization. No change to that repository formula is proposed.

