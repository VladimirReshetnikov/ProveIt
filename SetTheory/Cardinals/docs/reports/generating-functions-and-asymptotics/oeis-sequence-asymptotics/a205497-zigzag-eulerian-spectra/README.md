# Spectral collisions and boundary asymptotics for zig-zag Eulerian numbers

Research report prepared for Vladimir Reshetnikov, 1 October 2026.
The principal sequence is OEIS A205497, with rectangular indexing
M[i,k] = z(i+k+2,k).

## Read first

`zigzag_spectral_research.pdf` is the complete article.
`zigzag_spectral_research.tex` is the editable source (bibliography embedded).

The main additional results developed in the article are:

* The exact reduced column denominator R_k = lcm_{1<=m<=k+1} D_m^(k+2-m),
  complete spectral-collision classification, and an explicit totient formula
  for the minimal recurrence order.
* r_k = 40/(27*pi^2) (k+1)^3 + O(k^2 log k); the asymptotic ratio to the
  unreduced order is 80/(9*pi^2), approximately 0.9006327435.
* Uniform Perron asymptotics for k+1 <= c n/log n, for any fixed 0<c<1.
* A crossover factor exp(-exp(-s)) when n/(k+3/2)-log n -> s.
* Strict log-concavity at all indices k>=1 with k+2 <= c n/log n, for any
  fixed 0<c<1/2 and sufficiently large n; also at reflected right-edge indices.

These are ordinary mathematical proofs in an unrefereed manuscript, not Lean
proofs. Full-row log-concavity, real-rootedness, and interlacing are NOT proved.
The literature search was targeted, not an exhaustive novelty certification.

## Prior-work boundary

The old fixed-column rational formulas and their growth rates were already
proved by Xin and Zhong. Their Remark 5.7 already notes a denominator
cancellation. The report does not claim those facts as new.
Petersen and Zhuang provide the relevant order-polynomial framework and the
full log-concavity / real-rootedness conjectures.

Two entry-level corrections are documented: the unreduced numerator degree
uses A005586(k-1), not A005586(k), and the last term in the column-three
numerator is +x^14, not the -x^14 printed in A205497. The positive sign already
appears in Xin--Zhong, Example 5.11. No OEIS edit was submitted.
No ProveIt repository file was changed.

## Reproduce

Use Python 3.10 or newer, a LaTeX installation with `latexmk` and `pdflatex`,
and the Python dependencies in `requirements.txt`. The exact final run used
Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.

    python -m pip install -r requirements.txt
    python verify.py --out-dir data
    python illustrate.py
    latexmk -pdf -interaction=nonstopmode -halt-on-error zigzag_spectral_research.tex

`build.sh` runs the last three steps on Unix-like systems. `build.ps1` does
so in PowerShell. The scripts themselves make no network requests.
The PDF can be compiled without rerunning the Python computations because
all needed figure data and source tables are included.

## Exact verification

The final default run passed:
- direct matrix determinants for m=1..9;
- 820 polynomial gcd comparisons through m=40;
- 28 direct weak-word enumeration comparisons;
- direct alternating-permutation/big-return enumeration for n=0..9;
- exact rational certificates for columns k=0..12, with polynomial gcd,
  degree, and at least 2*r_k+26 coefficient checks for each column;
- positivity, symmetry, and finite log-concavity checks through row n=100.

The script deliberately detects and documents the erroneous printed sign
in the A205497 column-three numerator; it does not silently redefine the
external datum to force agreement. Finite checks are not proofs of the
unbounded claims; those proofs are in the article.

## Data

- `data/verification_report.json`: successful run and test scope.
- `data/rational_certificates.json`: numerator and denominator coefficients
  in ASCENDING powers, for columns 0 through 12. All coefficients are integers.
- `data/minimal_orders.txt`: pairs k,r_k for k=0..1000. No new OEIS number
  is claimed or assigned.
- `data/triangle.json`: rows z(n,k) for n=0..100.
- `data/crossover_diagnostics.json`: high-precision crossover examples.
- `data/order_ratio.pdf` and `.png`: exact-order ratio plot.
- `data/*_table.tex`: generated copies of the numerical tables embedded in
  the manuscript source.

Numerical error-bound expressions are evaluated in ordinary multiprecision
floating point, not interval arithmetic. The analytic tail bounds in the
crossover file exclude floating-point rounding error. In particular, a very
small tail bound is NOT a claim of that many certified digits.

## Scope and review

`SOURCE_AUDIT.md` records the prior-work and source boundary.
The package includes no external article PDFs, font files, or untested Lean
files. It is intended for mathematical review and possible later integration
into ProveIt.
