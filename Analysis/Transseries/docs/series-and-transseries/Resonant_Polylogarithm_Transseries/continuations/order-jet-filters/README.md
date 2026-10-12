# Order-Jet Filters for Polylogarithmic Transseries
## Sharp cancellation costs, Stokes-neutral curves, and a Stieltjes–digamma inverse

Research report prepared for Vladimir Reshetnikov and ProveIt, 12 October 2026.

**Status:** conventional proofs, not independently refereed or Lean-formalized.
The exact classification and analytic specializations are proposed contributions,
not certified claims of worldwide priority. Numerical checks are not interval
certificates. No remote repository files were changed.

## Main results

For `F_s(x) = -Li_s(-exp(x))`, a real order polynomial `Pi` turns the exact
lateral-completion coefficients into evaluations at `-log(n) +/- i*pi`.
The report proves the complete joint cancellation ideal, separate sharp degree
costs (including integer and half-integer resonance), and the equivalence between
joint cancellation and first-order robustness of jump cancellation under detuning.
Cancelling both data at the first N actions costs exactly degree 2N; its unique
monic minimal filter is

    product_{n=1}^N ((u + log(n))^2 + pi^2).

For each N, a normalized degree-(N+1) jump filter also admits a unique analytic
moving-order curve whose **whole jump is exactly zero**, yet whose physical
completion still starts at exp(-x). Its leading detuning is an explicit positive
logarithmic product times `-exp(-N*x)/pi`.

At order zero, every jet is expressed in generalized Stieltjes constants and in
independently regularized Fermi integrals. The first jet H is a positive, strictly
increasing real-analytic bijection R -> (0,infinity). An exact digamma core yields
an ordinary meromorphic Borel kernel, a convergent small-target logarithmic /
square-root inverse chart, and convergent large-core exponential inverse sectors.
The arithmetic inverse-average error is asymptotic to `pi^2*w^2*exp(-2*w)`, larger
by an unbounded factor than the physical core-inverse correction
`log(2)*w*exp(-2*w)`.

## Read and reproduce

`article.pdf` is the 21-page article; `article.tex` is its self-contained source.
`theorem_map.csv` records stable labels, numbers, pages, and claim status.

```sh
python -m pip install -r requirements.txt
python code/verify.py --output-dir replay
python code/design_filter.py joint 3
python code/design_filter.py jump 2 --output replay/jump-filter-2.json
make pdf
```

The retained verification used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0,
with 70 decimal digits. All six groups passed: **165 exact assertions and 46
numerical assertions**. The largest recorded numerical discrepancy was below
`2e-68`. Asymptotic tables are diagnostics, not assertions certifying a limit.
The Stieltjes checks use a positive endpoint-subtracted integral as their
independent physical reference, rather than tiny-step polylog order derivatives.

The default verification writes a new `replay/` directory, preserving delivered
records. Existing outputs are refused unless `--overwrite` is explicitly used.
A group can be selected with `--group`, and precision with `--dps` (at least 50).

## Provenance and integration

The repository snapshot is `8f5afd4d7565df808359f6a0c22f87f79a119bb9`.
The prior `Resonant_Polylogarithm_Transseries` article already contains the
positive-integer Gamma kernel, full harmonic Bell coefficient formulas, and
sharp dilogarithm reversion. These are credited, not rediscovered as new here.
The generic inverse-transport / arithmetic-averaging mechanism is also credited
to the existing transport article.

The three ZIPs in the pinned incoming directory were listed but their binary
contents could not be inspected. This limits the nonduplication audit; the names
alone are not treated as evidence of theorem content. See `SOURCE_AUDIT.md`.
No new mathematical error was established in the accepted source statements
actually inspected. `CORRECTIONS_AND_SCOPE.md` contains precise safeguards and
extension notes, not invented accusations about unseen material.

Suggested placement:
`Analysis/Transseries/docs/series-and-transseries/Polylogarithm_Order_Jet_Filters/`,
with a backlink from the Polylogarithms reports. See
`integration/INTEGRATION.md` for the proposed entry and proof-dependency map.
