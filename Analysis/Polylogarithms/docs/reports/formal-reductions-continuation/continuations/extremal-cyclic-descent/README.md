# Sharp Gaussian Bounds, Cyclic Distribution Torsion, and Extremal Lerch Zeros

Research continuation prepared for ProveIt, 10 October 2026 UTC.

**Read `article.pdf`.** The canonical source is `article.tex` plus `article/`.
`article_single_source.tex` contains the entire text and bibliography in one
file; it uses the two supplied PDF figures in `figures/`.

Baseline: VladimirReshetnikov/ProveIt commit
`a0a90ef31877f98be437191c48b46f02d5456867`.

## Main results

1. Strict allocation monotonicity for Gaussian double polylogarithms at every
   positive total order. This proves the incoming critical Euler conjecture,
   with sharp constant `pi/4 + log(2)/2`.
2. A unique nondegenerate maximum of `C(w) = beta(w) + 2^(-w) eta(w)`, rigorous
   root and value enclosures, strict Turan inequalities, and a complete
   coefficient formula for the inverse generalized-power expansion.
3. A positive secant identity for all Euler remainders and absolute Euler
   convergence for **all positive real orders**, including below the finite
   signed-measure threshold. Normalized errors need not decrease off the
   critical line; an exact `(a,b)=(1,1)` example is included.
4. Integral coinvariants and every one-variable finite jet for the specified
   prime-order cyclic action. The full torsion is determined by an arithmetic
   character compatibility condition. All hypotheses are stated in the paper.
5. A finite resolvent comparison moving the largest Lerch zero left, an
   all-order index-two lower-branch dichotomy, and exact certificates showing
   a second-order minimum and third-order decrease of both branches.
6. An integer functional separating the current S6 target from 5,131
   specified weight-seven relations in 2,546 coordinates. **S6 remains
   conjectural.** The result excludes exactly the stated finite relation span.

## Build

Requires a standard TeX Live installation with `latexmk`, pdfLaTeX, Latin
Modern, the AMS packages, `mathtools`, `microtype`, `graphicx`, `booktabs`,
`longtable`, `enumitem`, `xurl`, `hyperref`, and `fancyhdr`.

```sh
make all
```

Or run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build article.tex
python code/flatten_tex.py
```

## Replay the exact checks

Tested with Python 3.12.14 and SymPy 1.14.0. Install `requirements-exact.txt`
in your preferred environment, then run:

```sh
python code/replay_all.py
```

The Gaussian and Lerch interval verifiers and the S6 separator use only the
Python standard library. SymPy is used for exact Smith forms and a symbolic
inverse-series check. No network, PSLQ, floating polylogarithm evaluation,
or modular rank inference is needed for these certificates.

The replay writes `results/replay_summary.json` and `results/replay_log.txt`.
The individual raw receipts and certificates remain in `results/`.

For optional numerical diagnostics and figure regeneration, install
`requirements-diagnostics.txt`, then run:

```sh
python code/replay_all.py --diagnostics
```

Numerical plots and sampled minima are explicitly diagnostic. The exact
maximum intervals and branch-shape conclusions rely on separate rigorous
certificates and analytic arguments.

## Package contents

| Path | Contents |
| --- | --- |
| `article.pdf` | Complete research article |
| `article.tex`, `article/` | Modular LaTeX source and bibliography |
| `article_single_source.tex` | Complete text source in one file; figures supplied separately |
| `code/` | Exact verifiers, diagnostic programs, replay runner, source flattener |
| `results/` | Exact integer/rational certificates, replay receipts, diagnostic data |
| `figures/` | Vector PDF and raster PNG figures |
| `integration/` | Proposed manuscript addendum, claim-status ledger, integration guide |
| `provenance/` | Pinned source inventory, hashes, reused-code attribution, validation record |
| `MANIFEST.sha256` | Hashes of distributed files, excluding the manifest itself |

## Status and integration

The report gives ordinary analytic proofs and explicitly identified exact
computations. It does not claim completed proof-assistant formalization,
external peer review, or exhaustive priority research. New contributions are
identified relative to the inspected repository snapshot and classical
antecedents are cited.

The main source reconciliation is to promote the critical constant
conjecture, retire the already settled first-order Lerch-minimum question,
retain the established S4 theorem, and retain the conjectural S6 status.
See `integration/INTEGRATION.md` for the precise destinations and limitations.
