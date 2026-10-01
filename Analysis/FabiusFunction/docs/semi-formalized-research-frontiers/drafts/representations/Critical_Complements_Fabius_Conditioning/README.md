# Critical Complements in Fabius Conditioning

**Logarithmic overlap, finite-memory corrections, and the order-zero Rényi crossover**

A 24-page research article prepared for Vladimir Reshetnikov, dated September 30,
2026. This package extends the fixed-critical-complement regime explicitly posed
as a research question in ProveIt's *Sharp Conditioning Laws for Uniform Random
Series*.

## Main mathematical content

For S_q = sum(q^k U_k), tilt at t_n = rho q^(-n), condition the original law on
S_q <= E_Q[S_q], and observe coordinates r+1 through n, where r is fixed.
The omitted variance remains bounded while the observed variance is n + O(1).

The article proves an eventually exact likelihood-ratio reduction to the density
h_r of a tilted geometric boundary tail plus Gamma(r+1, 1). If
Lambda_n = log(2*pi*n)/2 and K = 1/E[exp(-rho*S_q)], the overlap satisfies

    sqrt(2*pi*n) * (1 - TV)
      = Lambda_n + r*log(Lambda_n) + log(K) - log(r!) + 1 + o(1).

A one-dimensional clipped-kernel formula has error O((log n)^3/n) on this scaled
level. An exact polynomial-tail identity supplies an all-orders inverse-logarithmic
expansion and isolates a smaller endpoint defect.

For every fixed positive Rényi order, the divergence is Lambda_n minus the
corresponding differential entropy of h_r, up to a vanishing error. At order zero
it instead tends to log(2). The article proves the crossover when alpha*sqrt(n)
tends to c: its limit is -log(exp(c^2/2)*Phi(-c)).

For r = 0, the residual from Lambda_n + log(K) + 1 is eventually positive and its
logarithm is asymptotic to -sqrt(log(1/q)*log(n)). This transfers Fabius endpoint
flatness into the overlap statistic.

The final section contains eight proposed research questions, including growing
complements, explicit finite-n remainders, sharper endpoint defects, inverse
reconstruction, uniform Rényi-order matching, multiple constraints, other digit
laws, and formal/interval verification.

## Files

- `article.tex`, `article.pdf`: complete manuscript source and compiled PDF.
- `code/verify.py`: exact algebra checks and numerical diagnostics.
- `data/`: exact rational records, CSV diagnostics, generated LaTeX tables, and
  the executed verification receipt.
- `figures/`: the three figures used in the manuscript.
- `CLAIM_STATUS.md`, `provenance.json`, `validation.json`: proof, novelty,
  source-inspection, and artifact-validation boundaries.
- `requirements.txt`, `Makefile`: reproduction support.

## Build the PDF

With pdfLaTeX, latexmk, and the required TeX Live packages installed:

```sh
make pdf
```

The source uses `libertinus` and `libertinust1math`, together with standard math,
layout, and hyperlink packages. The table fragments and figures are already
included, so building the PDF does not rerun the numerical calculations.
Font files themselves are not distributed.

## Reproduce the diagnostics

```sh
python -m pip install -r requirements.txt
python code/verify.py
make pdf
```

The delivered run passed 228 exact symbolic assertions: 72 moment/cumulant
comparisons, 72 tail-polynomial differential identities, and 84 finite-simplex
integral identities. It also ran 24 geometric and 24 simplex crossover cases.
The sampled boundary mesh-refinement difference was approximately 7.20e-10.

The numerical work is deterministic, but floating-point libraries can produce
slightly different last digits and rendered figures on different platforms.
All figures use Matplotlib's default color cycle; there is no Monte Carlo run.

## Scope and status

The article supplies conventional mathematical proofs. The proposed new results
have not been compiled in Lean or independently refereed. Worldwide priority is
not certified. The fixed-r bounded-complement case is resolved here; a growing
number of omitted coordinates is not covered by the uniform error claims.
Classical tilting, gamma/simplex formulas, and leading small-deviation estimates
are not claimed as new.

The numerical calculations use ordinary floating point and are not interval
certificates. The infinite boundary is approximated by midpoint convolution,
and very large caps are removed from the bulk numerical surrogate. Exact
algebra checks must not be confused with verification of the asymptotic proofs.
