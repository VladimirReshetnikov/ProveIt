# Exact Information Geometry and New Frontiers for the Fabius--Rvachev System

> **Current publication receipt (2026-09-04).** The synchronized
> `fabius_information_frontier.tex` has 2,138 lines and 78,310 bytes (SHA-256
> `57a06279153b6e4c97ea0c084a193867b2f5c60a0163983149f36453eb196c9d`).
> From absent auxiliaries, three successful serial halt-on-error passes produced
> 28 pages/778,760 bytes, 29 pages/790,804 bytes, and finally 29 pages/790,802
> bytes. The final PDF has SHA-256
> `3af03cd4dcc7fb1a502976f47edb56ee7d5c2b8dc9a8da537e79f8382ef885d5`.
> Its log has no TeX error, unresolved reference or citation, or rerun request;
> title, author, subject, and keywords metadata are present. All 29 pages are A4
> at rotation zero, render, and contain extractable text. All 23 font rows are
> embedded and subset, six are Libertinus, and none is Type 3; representative
> title, body, figure, table, and final pages passed visual inspection. Generated
> sidecars were removed. The former 19-entry operational ledger remains retired
> and Git-recoverable; it is not a live publication gate.

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
- `fabius_information_frontier.pdf`: synchronized 29-page canonical report;
  the distinct submitted 30-page payload remains recoverable from Git history.
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
- Former checksum ledgers: verified at intake or their recorded checkpoint,
  since retired and recoverable from Git.

The exact theorems do not depend on the numerical experiments.

## Repository filing and status

This package was quick-gate filed on 2026-08-30 from
`fabius_information_frontier_report.zip` (751,588 bytes; SHA-256
`41f9aba6eb85bb173827f13cb6b7b1d54b7ea9346faf7c9e5b1af859bbd42ec7`).
The archive was path-safe and passed its CRC test. Its submitted 18-entry
ledger verified 18/18 before normalization and was filed byte-for-byte as
`SHA256SUMS.arrival.txt`. Four CSV files are stored with repository-standard
LF endings. The arrival and later 19-entry operational ledgers are now retired;
their bytes and checkpoints remain recoverable from Git. The submitted PDF
remains a distinct historical payload.

This remains an archival intake, not a claim-level acceptance. The theorem
labels record manuscript statements and do not assert Lean formalization. The
canonical-preamble normalization, figure-font repair, and synchronized PDF
rebuild are complete under the receipt above; a hostile mathematical audit,
numerical replay, and exact Lean crosswalk remain deferred. The submitted
A4/Latin-Modern PDF with Type 3 plot-font rows remains a distinct historical
payload, not the current repository publication artifact.
