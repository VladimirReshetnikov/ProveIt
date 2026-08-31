# Exact Information Geometry and New Frontiers for the Fabius--Rvachev System

This archive accompanies the report
`fabius_information_frontier.pdf` and its complete LaTeX source
`fabius_information_frontier.tex`.

## Main results

The report studies the geometric-uniform law

```text
X_q = (1-q) sum_{j>=0} q^j U_j,       U_j iid Uniform[-1,1].
```

Its first `m` scales form `S_{q,m}` and satisfy the independent decomposition

```text
X_q = S_{q,m} + q^m X_q'.
```

The new corpus-relative results include:

- the exact mutual-information law `I(X_q;S_{q,m}) = m log(1/q)`;
- exactly `log(1/q)` nats from each additional geometric digit;
- an exact translated/rescaled posterior, including quantiles, cumulants,
  Bell moments, Renyi entropies, Fisher information, and Legendre transport;
- exact MMSE `q^(2m) Var(X_q)` and a non-Gaussian channel satisfying the
  Gaussian correlation formula for mutual information;
- a rate-distortion bracket and high-resolution prefix-code gap determined by
  the Gaussian entropy deficit;
- a dyadic Thue--Morse signed-spline / infinite-Rvachev-product KL identity;
- an information-density limit equal to a difference of independent
  surprisals, with limiting variance twice the varentropy;
- the finite-sinc entropy correction
  `h(X_q)-h(S_{q,m}) ~ Var(X_q) J(f_q) q^(2m)/2`;
- the inverse-Fabius Fisher identity
  `J(up)=integral_0^1 [y(1-y)G'(y)]^(-1) dy`;
- lower-Lambert endpoint tail-entropy asymptotics;
- exact Bernoulli standardized cumulants and a numerically tested entropic
  Edgeworth conjecture as `q -> 1`.

## Reproducing the numerical experiments

Python 3.11 or newer is recommended.

```bash
python -m pip install -r requirements.txt
python experiments.py --output . --grid-points 200001 --sample-size 180000
```

The deterministic density calculation iterates the exact fixed-point CDF
operator. The Monte Carlo information-spectrum check uses the fixed random seed
`20260830`.

## Compiling the report

A current TeX Live installation with `latexmk` is sufficient:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  fabius_information_frontier.tex
```

The source expects the vector figures under `figures/`.

## File map

- `fabius_information_frontier.tex`: complete report source.
- `fabius_information_frontier.pdf`: compiled 30-page report.
- `experiments.py`: documented experiment and figure generator.
- `requirements.txt`: Python dependencies.
- `CORPUS_AUDIT.md`: repository-relative nonduplication audit.
- `numerical_summary.txt`: principal numerical constants.
- `data/q_entropy_table.csv`: entropy, Gaussian deficit, Fisher information,
  and varentropy for selected `q`.
- `data/dyadic_prefix_entropy.csv`: finite-prefix entropy convergence and MMSE.
- `data/information_spectrum_summary.csv`: Monte Carlo convergence diagnostics.
- `data/thue_morse_signs.csv`: exact signs through depth eight.
- `data/symbolic_edgeworth.txt`: exact SymPy derivation of the first entropy
  coefficients.
- `figures/*.pdf`: vector figures used in the report.
- `figures/*.png`: raster previews.
- `SHA256SUMS`: integrity hashes.

The exact theorems do not depend on the numerical experiments.
