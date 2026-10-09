# Deterministic Fourier approximation of total variation

Research manuscript and reproducibility package, October 8, 2026.
Prepared for Vladimir Reshetnikov.

## Main result

For two finite product laws with N marginal-table entries per law and total
variation distance d > 0, the manuscript derives a deterministic relative-epsilon
approximation using

    O((N / epsilon) * log^2(2 / (epsilon * d)))

elementary real operations. The proof includes a polynomial-bit implementation
for rational input. For fixed accuracy and b = O(log N) input bits per marginal
numerator/denominator, the bit complexity is N times a fixed power of log N.

The main new analysis proposed here is a total-variation-relative bound on the
variation of a logarithmic-frequency integrand. Classical intersection-kernel
Fourier features are explicitly credited to prior work. Global priority has not
been established by the literature search, and the manuscript has not been
externally refereed or formalized in a proof assistant.

The source repository openai/math supplied motivation through its heat-bath
cutoff manuscript. No unverified theorem from that repository is an input to any
proof in this package.

## Contents

- `article/fourier_total_variation.pdf`: the 19-page research manuscript.
- `article/fourier_total_variation.tex`: standalone LaTeX source; bibliography is
  embedded, so BibTeX is not required to build it.
- `article/references.bib`: reusable bibliographic records.
- `code/fourier_tv.py`: product and fully observed Markov-path implementations;
  relative interval certificates, a fast prototype, periodic additive
  certificates, and Bayes-risk certificates.
- `tests/run_checks.py`: exact-enumeration comparisons and analytic-identity
  numerical checks.
- `tests/benchmark.py`: descriptive dimension-scaling experiment.
- `data/`: recorded exact rational certificates, readable CSV summaries,
  environment metadata, and run logs.
- `AUDIT.md`: mathematical dependencies, literature comparison, and limitations.
- `Makefile`, `requirements.txt`, `SHA256SUMS`: build/reproduction aids.

## Install and reproduce

Python 3.10 or later is recommended. The recorded run used Python 3.13.5,
NumPy 2.3.5, and mpmath 1.3.0. A virtual environment is recommended.

```bash
python -m pip install -r requirements.txt
python tests/run_checks.py
python tests/benchmark.py
make paper
```

`make paper` needs a normal LaTeX installation with `pdflatex` and the packages
listed in the source preamble. It runs pdflatex twice. It does not require
BibTeX, an Internet connection, or any external image/font files.

## Certified relative example

```python
import sys
from fractions import Fraction
sys.path.insert(0, "code")
from fourier_tv import ProductPair, relative_certificate

pair = ProductPair.create(
    [["1/5", "4/5"], ["2/3", "1/3"], ["4/7", "3/7"], ["1/10", "9/10"]],
    [["1/3", "2/3"], ["1/2", "1/2"], ["3/7", "4/7"], ["1/7", "6/7"]],
)
cert = relative_certificate(pair, epsilon="1/5", dps=40)
print("Estimate:", float(cert.estimate))
print("Readable interval:", float(cert.lower), float(cert.upper))
print("Exact certificate:", cert.as_dict())
```

The result includes exact rational lower and upper endpoints. Converting these
to ordinary floats is only a display convenience and does not preserve outward
rounding. For machine checking, retain the rational endpoints.

The requested guarantee is relative, not additive: the estimate differs from
the exact TV distance by at most epsilon times that distance. The code intersects
its analytic interval with a known cylinder-event lower bound and projects its
estimate into the resulting interval.

## Input and support rules

Use `Fraction`, integer, decimal-string, or rational-string probabilities.
Binary float inputs are rejected by the certified constructors. Every row must
sum exactly to one, and both laws must use matching alphabet/state sizes.
Zero probabilities are allowed. A zero factor is handled without taking a
logarithm of zero. Markov laws refer to complete state trajectories, not hidden
observations; differing transitions at unreachable states need not change a law.

## Numerical trust boundary

`relative_certificate`, `periodic_tv_certificate`, and
`bayes_risk_certificate` use `mpmath.iv` directed interval elementary arithmetic.
The implementation checks rational endpoints against exact enumerations in the
recorded finite tests. The interval backend is trusted software, not a formally
verified arithmetic kernel. Its precision context is global: concurrent calls
from multiple threads are not supported without external synchronization.

`relative_fast` uses NumPy floating point. It is explicitly NOT roundoff
certified. Its displayed interval is an analytic-error diagnostic that ignores
roundoff. It may underflow or lose accuracy for extreme input probabilities or
near equality. Use the interval implementation for those cases.

The relative reference code increases precision until its finite evaluation has
width at most epsilon*ell/2. It raises an exception when a configured resource
limit is exceeded; it never silently loosens the tolerance. The periodic table
functions return valid error enclosures conditional on the interval backend,
but do not automatically refine precision to meet any desired final interval
width. Inspect the returned width and rebuild at higher precision as necessary.

## Secondary results

The manuscript also proves:

1. The same relative transform-oracle algorithm for fully observed finite-state
   Markov path laws, costing O((r + k*r^2)/epsilon * log^2(2/(epsilon*d))).
2. A dimension-independent additive scheme with
   O(N/eta * log(1 + 1/eta)) elementary operations.
3. One periodic Fourier table giving an additive approximation of the entire
   normalized Bayes-risk curve, uniformly over every prior in [0,1].
4. A sharp normalization-weighted periodization bound, an exact alias-defect
   identity, and a positive spectral representation with multiplicative control
   before truncation.
5. A restricted obstruction to fixed finite bounded-frequency positive rules.

These do not imply an algorithm for general mixtures, hidden Markov observation
laws, or arbitrary interacting spin systems.

## Literature comparison

The cited deterministic algorithm of Feng, Liu, and Liu (SODA 2024) has a
quadratic dimension factor. The present bound reduces this factor to linear,
with additional logarithmic accuracy/distance factors and a stated
transcendental-operation/bit model. The randomized algorithm of Anand, Benford,
and Guo (2026) is already linear in dimension and has no distance-dependent
logarithm; the manuscript does not claim to improve that randomized result in
all parameters. The proposed deterministic bound is not uniformly smaller than
the cited bound in every joint regime.

See the article for full proofs, explicit constants, assumptions, further
research questions, and primary-source references.
