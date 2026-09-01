# Exact Information Geometry and New Frontiers for the Fabius--Rvachev System

> **Source-only merge status (2026-08-31).** The current TeX has 2,139 lines
> (SHA-256
> `d1b90d107a38219a2ff64bbae883d6172b49b70721b631b58cd3b6072781c6dd`).
> The retained submitted 30-page PDF was not rebuilt after the notation
> migration and is not claimed to be synchronized with that source.
> The refreshed 19-entry `SHA256SUMS` verifies the current TeX and README
> together with the retained PDF and other payloads; it does not assert
> source/PDF synchronization.

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
- `fabius_information_frontier.pdf`: retained submitted 30-page report, not
  rebuilt from the current source.
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

## Repository filing and status

This package was quick-gate filed on 2026-08-30 from
`fabius_information_frontier_report.zip` (751,588 bytes; SHA-256
`41f9aba6eb85bb173827f13cb6b7b1d54b7ea9346faf7c9e5b1af859bbd42ec7`).
The archive was path-safe and passed its CRC test.  Its submitted 18-entry
ledger verified 18/18 before normalization and is preserved byte-for-byte as
`SHA256SUMS.arrival.txt`.  Four CSV files are stored with repository-standard
LF endings. `SHA256SUMS` is the refreshed 19-entry operational ledger; it
verifies the current package while retaining the submitted PDF as a distinct
historical payload.

This is an archival intake, not a claim-level acceptance.  The theorem labels
record manuscript statements and do not assert Lean formalization.  A hostile
mathematical audit, numerical replay, exact Lean crosswalk, canonical-preamble
normalization, figure-font regeneration, and PDF rebuild are deliberately
deferred to a later commit.  In particular, the submitted PDF remains an
A4/Latin-Modern artifact with Type 3 plot-font rows and is not yet the
repository's canonical publication artifact.
