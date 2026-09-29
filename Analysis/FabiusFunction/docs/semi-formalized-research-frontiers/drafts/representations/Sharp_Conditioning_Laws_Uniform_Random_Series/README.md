# Sharp Conditioning Laws for Uniform Random Series

**Variance thresholds, boundary phases, Brownian bridges, and rare-event sampling**

A 26-page research article prepared for Vladimir Reshetnikov, dated
28 September 2026. The paper develops conditional configuration results
connected to the Fabius–Rvachev endpoint program in ProveIt.

## Main result

For S = sum_k w_k U_k, with independent uniform U_k and any positive
summable weights, choose the exponential tilt Q_t and condition the original
law on S <= E_{Q_t} S. A deterministic coordinate block is asymptotically
unchanged relative to its tilted product marginal, in total variation or
relative entropy, **if and only if its share of the total tilted variance
vanishes**. No monotonicity, regular spacing, or nonconcentration assumption
on the weights is needed.

At a limiting variance fraction alpha in (0,1), the paper proves an explicit
normal-CDF total-variation profile and the entropy limit
[-log(1-alpha)-alpha]/2. At fraction one, total variation tends to one and
relative entropy diverges.

The geometric specialization includes the classical Fabius law. Additional
results give an infinite phase-dependent boundary law, independent
exponential slack, a Brownian-bridge limit, and an exact-real lazy sampler
with asymptotic expected draw count sqrt(2*pi)*n^(3/2). Polynomial and
stretched-exponential weights illustrate the general variance criterion.

## Contents

- `article.tex`, `article.pdf`: source and compiled article.
- `code/verify_conditioning.py`: symbolic checks, exact-formula simplex
  comparisons, finite floating-point geometric experiments, and figure generation.
- `code/make_tables.py`: LaTeX table fragments generated from the CSVs.
- `data/`: CSV results, table fragments, numerical environment, and check receipts.
- `figures/`: four vector PDF figures with embedded TrueType fonts.
- `CLAIM_STATUS.md`: proof and novelty boundaries.
- `provenance.json`: pinned repository reference and source-inspection scope.
- `validation.json`: build and presentation checks.
- `requirements.txt`, `Makefile`: reproduction support.

## Build the PDF

From this directory, with pdfLaTeX and standard TeX Live packages installed:

```sh
make pdf
```

The figures and table fragments are already included, so this does not rerun
Monte Carlo. The LaTeX font packages are `libertinus` and `libertinust1math`;
font files themselves are not distributed.

## Rerun the diagnostics

```sh
python -m pip install -r requirements.txt
python code/verify_conditioning.py --proposals 160000
python code/make_tables.py
```

The delivered run passed five symbolic identities and 72 exact polynomial
integral checks. It also compared independent numerical evaluations of
simplex TV, simplex relative entropy, and truncated-exponential moments.
The geometric experiment used 160,000 tilted proposals at each of n = 32,
128, and 512, q = 1/2, rho = 1.25, with seeds 280926 + n.

`data/environment.json` records the actual numerical versions. Fixed seeds
do not guarantee byte-identical figures across different library versions.

## Important distinctions

The proofs in the article, not the Monte Carlo data, establish the stated
results. The new results have not been compiled in Lean or externally
refereed. Global research priority is not certified, and classical Gibbs
conditioning, log-concavity, and simplex geometry are not claimed as new.
The article frames and resolves precise questions arising from the scalar
endpoint program; it does not claim to settle a named famous conjecture.

The sampler theorem is exact in a stated real-arithmetic/lazy-output model.
The supplied Python experiments truncate a tail and use ordinary floating
point. They are not an interval-certified exact sampler, and the paper does
not prove a random-bit complexity bound or sampler optimality.

Eight further research questions concern quantitative error bounds, critical
complements, phase-sensitive corrections, quantitative log-concave local
limits, multiple constraints, other endpoint densities and random weights,
nongeometric transition fields, and certified random-bit complexity.
