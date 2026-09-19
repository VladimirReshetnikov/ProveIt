# A Sharp Convergence Theorem for the q-Newton Series of Subcritical Tetration

Research manuscript dated 19 September 2026.

## What this package contains

- `article/tetration_qnewton.pdf`: the complete article with detailed proofs.
- `article/tetration_qnewton.tex`: standalone LaTeX source with bibliography and numerical tables.
- `code/tetration.py`: high-precision positive-series and scaled Newton algorithms.
- `code/verify.py`: reproducible exact rational identities and numerical checks.
- `code/requirements.txt`: Python dependency.
- `data/`: actual outputs of the verification run, including raw CSV and JSON data.
- `notes/proof_audit.md`: the proof's delicate steps and how they are addressed.
- `notes/literature_status.md`: sources, attribution, and limits of the novelty claim.
- `build.sh`: PDF rebuild command.

## The selected question

The target is the explicit q-binomial interpolation series in Vladimir
Reshetnikov's 2017 MathOverflow question 259278. The manuscript develops a proof
of convergence for every real base 1 < a < exp(1/e), with q in (0,1) defined by
log(a) = q exp(-q). It also proves a sharp boundary classification, strict
complete monotonicity, and uniqueness under an eventual log-convexity condition.

The grouped series converges absolutely and locally uniformly for Re(z) > -2.
On Re(z) = -2 it converges conditionally except at z = -2 + 2*pi*i*k/(-log(q)).
At those points P_N(z) = -log(N)/log(a) + B_q + O(1/N). For Re(z) < -2 its
terms do not tend to zero. "Grouped" means that each finite inner sum is
computed before taking the infinite outer sum.

## Research status

This is an unreviewed mathematical manuscript, not a certification of a new
published result. The proofs are intended to be complete, and computations are
supporting checks rather than evidence replacing proof. Classical Koenigs
linearization and previously discussed positivity methods are explicitly
credited. No complete proof of the sharp boundary theorem was located in the
sources examined; this is not an exhaustive novelty or priority determination.
The full global continuation conjecture, the critical base, bases 2 and e,
and arbitrary higher hyperoperations are outside the results proved here.

## Reproduce the computations

Python 3.10 or newer is recommended. The included run used Python 3.13.5 and
mpmath 1.3.0.

```sh
python -m pip install -r code/requirements.txt
python code/verify.py
```

The script writes to `data/` and stops with an AssertionError if a check fails.
The included run completed 58 aggregate checks, including 312 exact rational
identities, 12 functional-equation checks, 24 derivative-sign checks, and 12
comparisons with a separately evaluated original double sum. Three values of q
were used for numerical work: 1/2, log(2), and 0.9.

The production checks used 110 decimal digits and 700 spectral coefficients;
the original alternating double sum was independently recomputed at 420 digits
for modest orders. No interval arithmetic is used. The Koenigs tail enclosure
is an analytic truncation bound evaluated in floating point, excluding
roundoff. The finite spectral and Newton routines do not provide automatic
error certificates. `data/convergence.csv` reports differences against a
finite high-precision spectral reference, not interval-certified true errors.
The manuscript discusses normalization/truncation plateaus and large transient
boundary partial sums, rather than suppressing those effects.

## Basic example

```python
import sys
sys.path.insert(0, "code")
from mpmath import mp
from tetration import TetrationModel

mp.dps = 100
model = TetrationModel.build(mp.log(2), terms=500)
print(model.evaluate(mp.mpf("0.5")))
# Approximately 1.2436216276685218042950989836094029
```

Set precision before model construction. Raising mp.dps afterward does not
recover digits absent from stored coefficients. Increase precision and the
coefficient count together when checking numerical stability.

## Rebuild the PDF

With a normal TeX Live installation, including latexmk, newtx, amsmath,
amsthm, mathtools, tcolorbox, and the other packages listed in the source:

```sh
./build.sh
```

Alternatively, run pdflatex repeatedly on the standalone source until all
cross-references resolve. No external bibliography database or network access
is needed. No font files or checksum files are included.
