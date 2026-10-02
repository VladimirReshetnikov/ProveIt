# Portable numerical and symbolic checks

From the extracted report directory, run:

```sh
bash code/run_checks.sh
```

The command can also be invoked with an absolute path from any working
directory. It uses only this package's files. No network request, downloaded
paper, other workspace, private notes, or user-specific path is required.
The two third-party Python dependencies are pinned in `requirements.txt`:
mpmath 1.3.0 and SymPy 1.14.0. The replay was tested with Python 3.12.14.
If needed, install them in your own virtual environment with
`python3 -m pip install -r code/requirements.txt`; the replay itself never
installs software. Expected runtime is a few seconds on an ordinary computer.

## Files and independent computations

- `triangle.py` regenerates the entire exact integer triangle through n=160
  directly from equation (47) of Agranat-Tamir et al.,
  [arXiv:2601.08062](https://arxiv.org/abs/2601.08062), using S=G/(1-G).
  It never reads stored triangle data. All divisions by two are checked for
  integrality. `data/triangle-160.json` is its reference output, not an input
  needed to compute the rows.
- `data/first-rows.json` gives the 13 low-order reference rows indexed by n=1
  through 13. These are a regression anchor for A399421 and the published
  generating function, not an independent enumeration proof of every row.
- `critical_jets.py` independently builds Wedderburn–Etherington coefficients
  U and calculates four implicit critical Taylor coefficients. It does not
  use the galled-tree triangle. H0, V=[e]H, and W=[e²]H supply the nested input
  through e⁴; higher nested powers cannot affect the requested derivatives.
  `data/constants-220.json` and `data/constants-320.json` contain independent
  truncation runs at 110-digit working precision.
  `data/audit-reference-constants.json` preserves the earlier independent
  numerical audit snapshots; replay compares against those too. Provenance
  hashes are recorded in `data/provenance.json`.
- `all_orders.py` is a finite-K symbolic generator. Only the expansion in
  t=n^(-1/2) is truncated. exp(q z²) is retained exactly by conjugating the
  Euler operator to z*d/dz+2q z². Symbols hL_J represent
  h_L^(J)(0)/(J! h_0(0)), and pM represents [e^M]psi(e). The module also
  supplies gamma-ratio transfer coefficients and a generic nondegenerate
  square-root Puiseux builder. The latter expects the caller to provide a
  characteristic solution and sufficient finite jets of analytic nested
  inputs. It is verified on y=w+y²/2. This is a formal finite-order generator,
  not a numerical computation of all orders at once.
- `ratios.py` generates 16 exact-count comparisons at n=40,80,120,160 and
  target lambda=0.5,1,1.5,2. The actual integer deficiency and lambda are
  recorded. Its C1 and C2 approximations use additive multipliers, not an
  exponentiated correction. Exact counts are decimal strings to avoid
  spreadsheet or JSON-client integer precision loss.
- `inversion.py` checks the K=2 finite log model at d=100,1000,10000 and
  x=d². It tests both the principal real Lambert W carrier and its
  logarithmic overflow-avoiding evaluation, the exact fixed-d derivative,
  and two Newton steps. It also checks all 6320 available inequalities
  g[n+2,k+1] >= g[n,k] and verifies that the only equality pairs (n,k) in
  this finite table are (1,0) and (3,1). These are finite-model and exact
  finite-triangle tests; they do not bound the asymptotic inverse error.
- `verify.py` recalculates, rather than merely loads, all these results. It
  checks the stored integer triangle, 13 first rows, the zero-gall U column,
  H0(w)=U(w²)/w, support and parity through n=160, and every coefficient of
  the transformed rational equation through w-degree 16. It also verifies
  C1/C2 symbolically, tests falling-factorial operators through order 4 on
  monomials of degrees 0 through 9, and checks gamma-ratio coefficients.
  Results are written under `checks/`; pass `--output-dir PATH` to change it.

## Numerical limits

The integer checks and zero symbolic residuals are exact. The decimal
constants are **not interval-certified**. The full stored decimal strings
support reproducibility, not a claim that every digit is reliable. Agreement
between two truncations is a stability diagnostic and is not itself a proof
of an error bound. The report should display at most 15 significant digits
for constants and at most 12 for ratios. The test uses absolute tolerance
10^(-35) for 220/320 agreement, 10^(-55) for same-truncation replay, and
10^(-45) against the earlier independent audit snapshots.

Finite-n ratio tables do not prove the asymptotic theorem or guarantee
monotonic improvement as terms are added. In particular n=40,d=13 still has
a large second-correction error. The inversion checks do not certify true
count recovery or threshold rounding. They require the exact deficiency
to be supplied and held fixed, as in the report's conditional theorem.

## Additional commands

```sh
python3 code/triangle.py --limit 160 --output /tmp/triangle.json
python3 code/critical_jets.py --truncation 320 --output /tmp/constants.json
python3 code/all_orders.py --order 4 --output /tmp/C0-to-C4.json
python3 code/all_orders.py --verify
python3 code/ratios.py --output /tmp/ratios.json --csv /tmp/ratios.csv
python3 code/inversion.py --output /tmp/inversion.json
```

Order K is fixed and caller-selected; symbolic expressions grow rapidly
with K. The theorem's uniformity is only on a fixed compact positive lambda
interval. No growing-order, lambda-to-zero, or lambda-to-infinity uniformity
is implied by the executable generator.
