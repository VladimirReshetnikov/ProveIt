# Vertical-Line Hurwitz Pairings and Exact Stieltjes–Gamma Calculus

Research continuation for Vladimir Reshetnikov's ProveIt project.
Version 1.0, 10 October 2026 (Pacific date).

## Article

`article.pdf` is the compiled, 22-page paper. `article.tex` and `sections/`
are the modular sources. `article_standalone.tex` is an equivalent single-file
source with the bibliography embedded; it requires no local section files.

The paper proves an exact all-order calculus for *ordinary absolutely
convergent integrals in the imaginary part of the Hurwitz argument*. This is
not a periodic finite-part correlation and not an integral in the zeta order.

The principal results are:

- A closed compensated Hurwitz pairing and arbitrary-index Stieltjes coefficient formula.
- Arbitrary-depth Bernoulli compensation, exact negative-order pairings, and normalized antiderivatives of Stirling remainders.
- Rationally related vertical scales, finite Hurwitz residue grids, and a pole-free all-order coefficient formula.
- Polygamma and finite generalized-harmonic pairings, colored Lerch products, polylogarithm order derivatives, and finite root-of-unity Gamma formulas.
- A complex-safe Hermite formula and a reproduced, version-specific mpmath 1.3.0 nonreal Stieltjes limitation.

The three headline normalized integrals (all with factor 1/(2 pi)) are
`log(2 pi) - 3/2`, `zeta'(-1) + zeta(3)/(2 pi^2) + 1/9`, and a two-scale
quarter-Gamma value. Domains, branches, factorials, and removable limits are
specified in the paper.

## Reproduce

Use Python 3.10 or newer and a LaTeX installation with `latexmk`, `newtx`,
`amsmath`, `amsthm`, `mathtools`, `microtype`, `hyperref`, and `cleveref`.

```sh
python -m pip install -r requirements.txt
python verification/exact_checks.py
python verification/numerical_checks.py core
python verification/numerical_checks.py extensions
python verification/complex_safe_replay.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

`make checks` and `make pdf` provide the same entry points. The numerical
core is slower than the other checks because it independently evaluates
complex spectral Cauchy coefficients and full vertical integrals.

`verification/vertical.py` is a reusable formula/evaluation module. In
particular, `J_at_integer` evaluates the removable integer resonances by
finite Laurent arithmetic and returns `(constant_term, residue_sum)`.
Use it instead of substituting a singular integer into `J_formula`.
For nonreal Stieltjes arguments use `G_hermite` or `stieltjes_cauchy`; the
`K_derivative_at_one` helper routes nonreal arguments through the safe
Hermite formula. Prefer string-initialized `mp.mpf`/`mp.mpc` values when
working at high precision.

## Verification and limitations

The supplied replay records 538 exact algebraic assertions and 76 numerical
comparisons at 60 working decimal digits, all passing. The numerical
acceptance tolerance is 1e-35 in the scale recorded in the paper. Numerical
checks are **not interval certificates** and do not replace the analytic
proofs. The deliberately failing dependency behavior is retained as a
negative control; it is not counted as a passing mathematical identity.

No proof assistant formalization is supplied. No theorem here claims to
settle S6 or revised S8. No exhaustive priority claim or complete audit of
all incoming archives is made. See `PROOF_STATUS.md` and `SOURCE_AUDIT.md`.

## Integration

`INTEGRATION_NOTES.md` proposes placement and labels. No repository write was
performed. The package may be preserved as an incoming provenance archive
and audited before its results are promoted into the canonical manuscript.

`SHA256SUMS` covers the deliverable members other than itself. Build byproducts
and Python cache files are not included.
