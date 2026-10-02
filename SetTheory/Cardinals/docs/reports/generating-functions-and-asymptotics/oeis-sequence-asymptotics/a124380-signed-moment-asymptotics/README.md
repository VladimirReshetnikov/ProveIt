# A124380 asymptotics and inversion

This package contains a self-contained research report and reproducibility scripts for the integer sequence

    sum(a_n z^n, n >= 0) = sum(z^k product(1+jz, j=1..k), k >= 0).

## Main results

- An exact signed-moment decomposition a_n = I_n + (-1)^n J_n
- A genuine multiplicative equivalent and arbitrary fixed-order positive-sector expansions
- An exponentially smaller oscillatory sector, with both exact-saddle and elementary coefficient recurrences and amplitude-scaled remainders
- The relation q_j^-(L) = (-1)^j q_j^+(L-i*pi) between the two elementary coefficient families
- A canonical smooth inverse, with a Lambert W normalization, explicit coefficients through the 1/X^3 term, and an arbitrary finite-order inverse recurrence
- Eventual strict log-convexity and a careful conditional certification rule for integer thresholds

The report credits the partial-matching model of Chen, Fan, and Zhao (2010), the later restricted-growth model of Cerbai, Claesson, and Sagan, and the earlier Stirling asymptotics of Temme. It does not claim publication priority, convergence, a complete exponential transseries, or unconditional rounding of the smooth inverse.

The oscillatory error is normalized by its exponential amplitude, not by a possibly tiny or zero sine. Finite algebraic truncation of I_n usually has an error much larger than J_n. The smaller sector describes the exact difference a_n-I_n.

## Deliverables

- `a124380-asymptotics.pdf`: fourteen-page report
- `a124380-asymptotics.tex`: editable source
- `code/`: portable symbolic and numerical scripts
- `receipts/`: saved exact coefficient output and diagnostic logs
- `SHA256SUMS`: checksums for the distributed files other than this manifest

## Requirements

Tested with Python 3.12.14, SymPy 1.14.0, and mpmath 1.3.0. The Python scripts use no network services. To install the two Python dependencies in your own environment, use:

    python -m pip install -r requirements.txt

## Replay the mathematical checks

Run these from the package directory:

    python code/independent_checks.py
    python code/verify_all.py
    python code/verify_oscillatory.py
    python code/check_sector.py

`independent_checks.py` uses independent finite-product exponentiation, explicit Gaussian moments, formal inverse composition, and checks every polynomial printed in the inverse appendix.

`verify_all.py` independently checks direct integrand expansion and the positive coefficient generator, substitutes the inverse into the forward series, reproduces exact sequence values, and compares moment quadrature and asymptotic approximations. The moment-identity tests use 70-digit working precision and require 60 relative decimal digits of agreement.

`verify_oscillatory.py` checks the negative phase independently, verifies the complex-shift identity exactly, and prints amplitude-scaled quadrature diagnostics for the elementary expansion. `check_sector.py` independently checks the first correction at the negative real saddle. The numerical integrations truncate Gaussian tails twenty units from the saddle; they are diagnostics, not interval-arithmetic certificates.

## Generate further finite orders

    python code/replay_coefficients.py --order 6
    python code/replay_inverse.py --order 4
    python code/replay_oscillatory.py --order 4

These commands print JSON. The inverse generator's constant `c` means `1/2-log(2)`. The oscillatory generator's symbol `p` means pi. Any requested order is finite; large symbolic orders can be expensive. Asymptotic series need not improve at every successive order for a fixed input.

## Rebuild the PDF

A TeX distribution with pdfLaTeX and the standard packages listed in the preamble is required:

    sh build.sh

The script runs three passes. On minimal read-only TeX installations that have source packages but lack generated format/font caches, it regenerates local caches inside `.build/`. It installs nothing and writes only inside the extracted package. On ordinary TeX installations, compiling the source directly with pdfLaTeX twice is also sufficient. The PDF's metadata timestamp may change on rebuilding, so the PDF checksum is not expected to remain identical after a rebuild.

## Verify the distributed checksums

On a system with GNU coreutils:

    sha256sum -c SHA256SUMS

The displayed numerical errors and asymptotic O bounds are not certified finite-n error intervals. The proofs in the report establish fixed-order asymptotics. To certify a particular integer threshold, use the additional interval bounds explained in Section 7.3.

## Further research questions

1. How far can the bivariate identity be made uniform when the record-count fugacity varies with n? Determine the maximal parameter ranges, transitions between them, and resulting limiting or local-limit laws for the number of records. These questions extend beyond the fixed-fugacity results in this report.
2. Can explicit remainder constants and interval quadrature turn the smooth inverse into an efficient certified integer-threshold algorithm, including levels exponentially close to an integer crossing?
3. What is the large-order growth of the positive and signed coefficient families, and what truncation minimizes the error? Relate that behavior to the exponentially small sector without assuming a complete transseries or convergence.
4. How small can the signed moment be along integer subsequences, and how are its sign changes and near-cancellations governed by the slowly varying phase? The present amplitude-scaled expansion does not establish uniform relative accuracy near oscillatory zeros.
