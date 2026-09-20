# Binary carries and the divisibility of A000139

**Research article, 19 September 2026.**

The 20-page article proves the parity conjecture recorded by Peter Bala in
OEIS A000139 on 24 July 2025, and develops exact valuation distributions,
recurrences, asymptotics, extremal formulas, and limit laws.

For

    a(n) = 2 (3n)! / ((n+1)! (2n+1)!),     n >= 0,

its central conclusion is:

    a(n) is odd iff n is odd and its binary expansion contains no 11.

Equivalently, `(n & 1) != 0 and (n & (n << 1)) == 0`.

The complete valuation is

    v2(a(n)) = popcount(n) + popcount(n+1) - popcount(3*n).

The exceptional constant term is deliberately retained: a(0)=2, so v(0)=1.
All histogram bounds are exclusive. Least indices are **positive** indices.

## Contents

- `research.pdf` — the complete typeset article, with two independent parity
  proofs and detailed derivations of the stronger results.
- `research.tex` — self-contained LaTeX source, including the bibliography.
- `code/carries.py` — standard-library exact evaluation, finite-state
  valuation automaton, dyadic recurrence, arbitrary-bound digit dynamic
  programming, and least-index formulas.
- `code/verify.py` — standard-library finite verification and data generation.
- `code/verify_symbolic.py` — optional exact symbolic identity checks.
- `data/verification.json` — the recorded full execution report.
- `data/symbolic_verification.json` — the symbolic execution report.
- `data/initial_terms.csv` — indices 0 through 200, including exact a(n).
- `data/dyadic_histograms.csv` — **not distributed** (1.8 MB). Complete
  distributions for lengths 0 through 256; `python code/verify.py` rebuilds it.
- `data/least_indices.csv` — least positive indices for valuations 0 through 64.
- `data/histogram_below_10_pow_100.json` — the complete distribution for
  0 <= n < 10^100, computed without enumerating that interval.
- `notes/source_audit.md` — source provenance and limits of the priority claim.
- `notes/verification_scope.md` — independent checks, boundary cases, and
  the distinction between finite tests and proofs.
- `Makefile` — convenience targets for building and checking.
- `requirements-optional.txt` — the optional symbolic dependency.

## Reproduce

The main implementation needs Python 3.10 or newer and no external packages.
The recorded full run used Python 3.13.5. Run from this directory:

```sh
python code/verify.py
python code/carries.py --n 13
python code/carries.py --dyadic 100
python code/carries.py --bound 1000000000000000000000000
python code/carries.py --least 1000
```

The first command regenerates the standard-library data and its verification
report. It does not touch the mathematical article. A reduced test is
available as `python code/verify.py --quick --out /tmp/a000139-quick`.
Use an alternate output directory for a quick run to preserve the full report.

For the optional symbolic checks:

```sh
python -m pip install -r requirements-optional.txt
python code/verify_symbolic.py
```

The exact SymPy version used was 1.14.0. No included program makes network
calls. Installing a dependency is a separate, optional action.

Build the PDF with a TeX distribution containing amsmath, amsthm, mathtools,
newtx, geometry, microtype, booktabs, enumitem, needspace, fancyhdr, titlesec,
listings, tcolorbox, hyperref, and cleveref:

```sh
pdflatex -interaction=nonstopmode -halt-on-error research.tex
pdflatex -interaction=nonstopmode -halt-on-error research.tex
pdflatex -interaction=nonstopmode -halt-on-error research.tex
```

The bibliography is embedded; BibTeX is unnecessary. `make pdf`, `make verify`,
and `make symbolic` are equivalent convenience targets. The supplied PDF was
compiled with pdfTeX from TeX Live 2025/dev/Debian and visually inspected after
rendering. No font files are distributed in this archive.

## Mathematical scope

The article establishes a rational bivariate generating function for
V_m(y) = sum_{n<2^m} y^{v2(a(n))}, a third-order recurrence in m starting at
m=4, exact fixed-level denominators and asymptotics, Fibonacci counts of
maximal-valuation indices, an explicit least-index formula, exact first and
second moments, and central and uniform local Gaussian limit theorems.
A six-state nonnegative weighted automaton also yields an arbitrary-bound
algorithm using O(log(N)^2) integer coefficient updates. This complexity
statement is an arithmetic-operation count, not a unit-cost bit-complexity
claim.

## Status and limits

The OEIS entry inspected for this work still described the parity assertion
as a conjecture. The article supplies proofs of the assertion. This does not
establish that these are the first proofs, nor that every refinement is new:
the targeted literature search was not exhaustive. The classical factorial
quotient, its combinatorial interpretations, and the ternary-tree generating
function are explicitly credited rather than claimed as discoveries.

The computational comparisons all passed, but they are finite checks, not
formal verification of the proofs. No Lean formalization or independent peer
review is claimed. The local limit theorem is an absolute-error assertion;
it does not assert relative Gaussian accuracy in rare fixed-valuation tails.
