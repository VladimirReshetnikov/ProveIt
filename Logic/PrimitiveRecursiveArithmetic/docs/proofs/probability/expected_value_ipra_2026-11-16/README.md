# Expected value in intuitionistic primitive recursive arithmetic

Prepared 16 November 2026.

## Deliverables

- `paper/expected_value_ipra.pdf` - compiled 51-page human-readable manuscript.
- `paper/expected_value_ipra.tex` and `paper/sections/*.tex` - LaTeX source.
- `THEOREM_LEDGER.md` - statement-by-statement coverage of the Wikipedia article.
- `LEAN_ROADMAP.md` - implementation order and object-language endpoint.
- `lean/ExpectedValueFinite.lean` - ambient finite-probability blueprint.
- `lean/RegularExpectation.lean` - effective simple-function / regular-real blueprint.
- `lean/ObjectLanguageTargets.lean` - `PRAAx` target interface.
- `code/validate_expected_value.py` - exact `Fraction`-arithmetic validation.
- `validation/validation.json` - recorded validation output.
- `provenance/SOURCES.md` - source inventory and trust boundary.

## Main result

The exact kernel is a finite weighted law with natural weights and rational-valued
observables.  Every expectation identity is reduced to bounded sums, products,
order, and quantifier-free induction.  This yields iPRA proofs of finite
expectation, LOTUS, linearity, monotonicity, indicator expectations, tail sums,
variance, Cauchy--Schwarz, Markov and Chebyshev, independence/product formulas,
finite conditional expectation, sample-mean unbiasedness, variance reduction,
and a quantitative finitary strong-law statement.

Countable and continuous claims are represented by primitive-recursive finite
approximants carrying explicit absolute-tail, integration, or L1 moduli.  This
produces constructive versions of absolute convergence and reordering,
extended expectations, geometric/Poisson/uniform/exponential/normal/Pareto/Cauchy
examples, effective monotone/Fatou/dominated-convergence principles, and finite
Fourier inversion.  Classical existence-only claims are not silently treated as
effective.

## Formalization status

The manuscript is a fully developed human proof and formalization plan.  The
Lean files are uncompiled blueprints: they contain definitions and proof-package
interfaces, not a completed kernel-checked development.  The exact Python
validation passes 148,317 rational-arithmetic assertions; it is regression
evidence, not a proof oracle.  Completion means
constructing explicit derivations of the target formulas in
`LeanProofs.ConciseIPRA.Prf PRAAx` and transporting them through
`pra_iff_native`.

## Build

```sh
python3 code/validate_expected_value.py --output validation/validation.json
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error expected_value_ipra.tex
```
