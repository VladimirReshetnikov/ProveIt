# OEIS A293239: research report and exact certificates

**Status: the principal all-order closed formula is not proved in this
report.** Its precise missing nonvanishing statement is isolated. The
recurrence printed with the range n > 6 is disproved at n = 8. For the
proposed sequence, its correct eventual range is n >= 14; asserting this
corrected recurrence for the actual derivative count remains conditional on
the principal conjecture.

## Contents

- `article.pdf`: the 16-page article.
- `article.tex`: complete, self-contained LaTeX source, including bibliography.
- `build.sh`: builds the PDF with two pdfLaTeX passes.
- `verify.py`: standard-library Python verifier, with independent derivative
  and shifted-product checks, exact column identities, and prime-adic checks.
- `verify_gmp.cpp`: C++17/GMP exact triangle computation and CSV generation.
- `verify_diagonals.py`: standard-library rational-polynomial construction
  and verification of all-integer nonvanishing certificates for offsets 1..16.
- `data/counts.csv`: exact derivative term counts for n = 0..3000, the
  candidate values, row counts, and cumulative unexpected-zero counts.
- `data/zeros.csv`: every zero (m,r) with 1 <= r <= m <= 3000, classified as
  symmetry or exceptional.
- `data/diagonal_certificates.json`: complete polynomial coefficients,
  factorizations, certifying primes, and exhaustive nonzero residue values.
- `data/gmp_report.txt`, `data/python_report.json`, `data/diagonal_report.txt`:
  outputs from verification runs.
- `oeis_notes.txt`: a compact statement of the range correction and the
  distinction between proved and conjectured assertions.
- `SHA256SUMS`: integrity hashes for the included files (not including itself).

## Principal unconditional results

Let b(m,r) be the coefficient of u^r in

    product_{h=0}^{m-1} (u+r-h).

Then a(n) = 1 + n(n+1)/2 minus the number of zeros of b(m,r) in
1 <= r <= m <= n. The symmetry zeros b(4h+1,2h)=0 and the exceptional
zero b(8,5)=0 are proved. If E(n) counts all other zeros in that region,
then exactly a(n)=q(n)-E(n), with q defined in the article.

In particular:

    n+1+floor(n^2/4) <= a(n) <= q(n),

so the growth is Theta(n^2), without a proof here of the sharper equivalent
n^2/2. For every prime p and every m >= p, b(m,m-p+1) is nonzero, and its
p-adic valuation is v_p(floor(m/p)). Additional zeros are also ruled out in
the first three columns and on all offsets m-r <= 16.

The modular certificates for a fixed diagonal cover **every integer row
index**, not just the finite triangular region in the CSV. They do not
cover all diagonals. No priority or global novelty claim is made for the
individual results in this report.

## Reproduction

Python 3.10 or later; no third-party Python packages are required:

```sh
python3 verify.py --max-n 1500 --data-dir data
python3 verify_diagonals.py --output-dir data --check-only
```

To regenerate the certificates rather than compare the saved copies:

```sh
python3 verify_diagonals.py --output-dir data
```

To regenerate the complete count and zero-position tables (this overwrites
`data/counts.csv`, `data/zeros.csv`, and `data/gmp_report.txt`):

```sh
c++ -O3 -std=c++17 verify_gmp.cpp -lgmpxx -lgmp -o verify_gmp
./verify_gmp 3000 data
```

This requires a C++17 compiler and GMP development headers/libraries. The
C++ computation uses signed arbitrary-precision integers, not machine-word
approximations or floating point. Increasing the limit can significantly
increase time and memory requirements.

Build the paper using a TeX installation with the packages named at the top
of `article.tex`:

```sh
sh build.sh
```

The source uses pdfLaTeX and an inline bibliography; BibTeX is not needed.

## Actual verification results

The completed C++ run checked rows through 3000: 4,501,500 relevant triangle
entries, 750 zeros, no unexpected zeros, and a(3000)=4,500,751.
The independent Python run checked rows through 1500, all 54 values directly
displayed in OEIS, 61 full derivative polynomials through order 60, 496
shifted-product entries through row 30, 177 column-formula values, and 11,865
prime-offset valuation instances. All checks passed. The count tables agree
between implementations at all 1501 overlapping indices. All 16 diagonal
polynomial certificates were reconstructed and checked successfully.

These finite triangle checks are **not** a proof for n > 3000. The document
states exactly which results hold unconditionally for all indices and which
remain conditional.

Verified environment: Python 3.13.5; GCC C++ 14.2.0; GMP 6.3.0;
pdfTeX 1.40.26. The PDF compiled without unresolved references or overfull
boxes and was rendered for visual inspection.

## Sources

The primary problem statement is OEIS A293239:
https://oeis.org/search?q=id:A293239&fmt=text

The coefficient triangle is OEIS A008296:
https://oeis.org/A008296

The article includes a bibliography and discusses Jeong's 2026 preprint,
https://arxiv.org/abs/2607.26613, for the known symmetry zero family.
The full linked OEIS b-file was not used as independent verification; only
the values displayed in the entry were compared.

No original third-party papers or font files are included.
