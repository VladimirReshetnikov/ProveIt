# Uniform Resurgent Crossover for Gaussian Binomial Coefficients

**Exact remainders, a sharp modular-visibility threshold, and certified inversion**

Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Contents

- `article.pdf`: compiled research article with proofs, numerical tables, source audit, and nine further research questions.
- `article.tex`: standalone editable LaTeX source, with references embedded.
- `verify.py`: exact symbolic checks and 110-digit numerical checks; no network access is needed.
- `verification_results.json`: actual output of the full supplied verification run.
- `requirements.txt`: numerical package versions used for that run.

## Main results

For the central Gaussian interpolation with q = exp(h), tau = h*x, the article derives an exact positive Bernoulli remainder, an all-order expansion uniform through tau = 0, and the explicit meromorphic Borel transform with even axial poles cancelled. Its principal quantitative result is

    min_K r_K(tau/x, tau) = exp(-2*pi*x)/(pi*sqrt(x)) * (1 + O_T(1/x)),

uniformly for 0 <= tau <= T, with every minimizing K = pi*x + O_T(1).
Comparison with the exact modular term exp(-4*pi^2/h) resolves the boundary layer

    tau = 2*pi - log(x)/(2*x) + s/x,
    minimum remainder / modular term -> exp(-s)/pi.

This is a precision threshold for ordinary Bernoulli truncations, not a Stokes transition and not an impossibility result for all numerical algorithms. Exact remainder evaluation can go below this threshold. Inversion about the exact Borel-summed carrier has a convergent modular expansion with explicit coefficients and geometric error bounds.

## Mathematical and provenance status

The paper contains conventional proofs. It is not peer reviewed or Lean verified, and global novelty or priority has not been established. General q-Pochhammer resurgence is explicitly credited to existing literature. The main new-to-the-reviewed-repository contribution is the uniform sharp-remainder and inverse-certification package.

Repository snapshot:
`VladimirReshetnikov/ProveIt`, commit
`04e06e032dff1966513bfba316966d52db3646b4`.

Directly inspected source: the singular q -> 1 chapter of
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/series-and-transseries/Combinatorial_Transseries_Inverses/Combinatorial_Transseries_Inverses.tex`
and the group/package READMEs. The oversized canonical `transseries_and_inversion.tex` could not be read through the available endpoint; no exhaustive audit of that entire volume is claimed.

The companion explicitly leaves uniform endpoint matching and finite-size-tail beyond-all-orders control outside its stated results. The paper gives precise versions of these advances. No repository files were changed.

## Rebuild the PDF

With a standard TeX Live installation, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Run another pass if LaTeX requests updated cross-references. The source does not depend on any notation file from ProveIt.

## Reproduce the checks

Python 3.10 or later is required.

```sh
python -m pip install -r requirements.txt
python verify.py
```

`python verify.py --quick` omits the larger numerical cases. The JSON output is written beside the script by default; use `--help` for options.

The script checks all six displayed endpoint coefficients, eight endpoint Borel coefficient identities, ten rational pole cancellations, four independent finite-product normalizations, three exact-remainder comparisons, four slope brackets, seven near-optimal remainder cases, eight boundary-layer cases, and one inverse displacement. The JSON includes actual computed values, not fabricated expected output.

The positive-sum and modular-tail inequalities are proved in the article. Their implementation uses ordinary mpmath rounding, not outward-rounded intervals. The numerical run is supplementary evidence and is not a substitute for the mathematical proofs or an interval-certified computation.
