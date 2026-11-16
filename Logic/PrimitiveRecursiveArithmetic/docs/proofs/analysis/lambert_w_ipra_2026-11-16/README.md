# Lambert W in intuitionistic primitive recursive arithmetic

This packet develops a constructive, finitary treatment of a large fraction of
the mathematical assertions on the Wikipedia page **Lambert W function**.  The
main report is `lambert_w_ipra.pdf`; its editable source is
`lambert_w_ipra.tex`.

The central distinction is between:

- exact finite identities in coded rational/truncated-series algebra;
- analytic statements interpreted through primitive-recursive rapidly
  convergent rational names with explicit moduli;
- results conditional on a separately named effective theorem;
- claims that are corrected, audited, or deliberately deferred.

## Contents

- `lambert_w_ipra.tex` — 33-page human-readable proof development.
- `lambert_w_ipra.pdf` — compiled report.
- `THEOREM_LEDGER.md` and `claims.json` — 82 claim-level status records.
- `lean/LambertWHostBlueprint.lean` — host-level constructive-real interfaces.
- `lean/LambertWObjectBlueprint.lean` — object-language proof graph using
  ProveIt's actual `PR`, `PTm`, `PRAAx`, `PRA.qfInd`, and `pra_iff_native`
  interfaces.
- `lean/ROADMAP.md`, `lean/STATUS.md` — module order and exact formalization
  status.
- `scripts/verify_lambert_w.py` — exact rational finite-series checks and
  high-precision diagnostics.
- `evidence/verification_report.txt` and `.json` — 185/185 passing checks.
- `SOURCE_AUDIT.md` — source and reuse audit.
- `SHA256SUMS` — checksums for the distributable packet.

## Main mathematical coverage

The report proves constructively:

- the two real branches, domains, ranges, multiplicities, monotonicity, and
  effective interval evaluation;
- branch-safe identities and special values, including the omega constant;
- first and higher derivative formulae, curvature, antiderivatives, and the
  displayed gamma-family definite integrals;
- finite Lagrange–Bürmann inversion, the Maclaurin and power coefficients,
  exact radius `1/e`, and absolute boundary convergence;
- Puiseux expansions at `-1/e` with effective finite-order remainders;
- finite-order logarithmic asymptotics for `W_0` and `W_{-1}`;
- the principal- and secondary-branch inequality families displayed on the
  reference page;
- nested exponential/logarithm representations with contraction witnesses;
- branch-complete solutions of the main transcendental equations;
- the rooted-tree interpretation and certified Newton/Halley evaluation.

The report does **not** claim a full constructive proof of the Poisson and
Kalugin–Jeffrey–Corless integral representations, the displayed continued
fraction's global convergence, or the page's implementation/physical-history
claims. Those exclusions are listed individually in the ledger.

## Rebuild

From this directory:

```bash
python3 scripts/verify_lambert_w.py
latexmk -pdf -interaction=nonstopmode -halt-on-error lambert_w_ipra.tex
```

Or run:

```bash
./build.sh
```

The Python verifier requires `mpmath`. The TeX build uses standard TeX Live
packages. The Lean files are blueprints and are not part of `build.sh`.

## Formalization status

A completed kernel-checked Lean formalization is **not** claimed. The supplied
Lean files contain explicit `sorry` obligations and no user-defined axioms. No
Lean or Lake executable was present in the artifact environment, so they were
not compiled. The object-language file is tied to the current ProveIt
`ConciseIPRA` declarations and identifies the first kernel-checked milestone:
the coefficient identity in every finite truncation.

## Reproducibility result

At packet creation:

- LaTeX compiled without undefined references, overfull boxes, or underfull
  boxes;
- the PDF opened successfully and had 33 US-letter pages;
- all 185 exact/numerical verifier checks passed;
- rendered-page inspection found no clipping or unreadable content.
