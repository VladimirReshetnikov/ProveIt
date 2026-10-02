# Regular cyclic word covers

Research article and reproducibility package, 2 October 2026.

## Read first

Open `article/regular-cyclic-word-covers.pdf`. The editable source is the adjacent `.tex` file.

The model is a set (sign −1) or multiset (sign +1) of rotation necklaces of fixed length ell on n labeled letters. Every letter occurs exactly r times. Letters may repeat inside a word in both models. The leading equivalents of A108242, A110105, A110104 and A110106 were already posted; this article does not claim those constants as new.

The article proves every-fixed-order expansions with analytic remainder control, critical-degree crossover and parity, and fixed-degree inverse/lattice theorems. The executable tests are separate finite or formal checks. Numerical diagnostics are high-precision floating-point values, not interval-certified bounds. The literature comparison is a targeted applicability screen, not an exhaustive priority certification.

## Verify archive integrity

From the package directory, before running anything:

    sha256sum -c MANIFEST.sha256

Or, on systems without sha256sum:

    python3 verify_manifest.py

The manifest covers all distributed package files except itself. Replays regenerate designated outputs and may change timing fields and executable files, so verify the original archive before replay.

## Dependencies

- Python 3.10 or later (tested with Python 3.12)
- SymPy 1.14.0 and mpmath 1.3.0 (`requirements.txt`)
- C++17 compiler, tested with g++, and GMP development headers/libraries
- A standard LaTeX installation for rebuilding the PDF, including amsmath, amsthm, mathtools, geometry, lmodern, microtype, booktabs, xcolor, hyperref and enumitem

If a Python environment is needed, create your own virtual environment and install `requirements.txt`. No network access is required after dependencies are installed. The package does not install software automatically.

## Ordinary replay

    bash reproduce.sh

This runs:

1. All 54 saved OEIS term comparisons and degree-three rational coefficients through order eight
2. A frozen expected-coefficient comparison
3. Thirty signed literal-necklace versus logarithmic-product comparisons across lengths 3, 4 and 5
4. An independent cubic symbolic computation through the third critical order
5. A C++ exact counter, checked against literal products and a Python recurrence in 24 signed cases, plus 17 numerical cases
6. A quartic symbolic/finite-object diagnostic
7. The pure-Python finite general-length coefficient algorithm against cubic, quartic and prime/composite regression targets, plus additional-length and partition-count tests
8. Sixteen extra length-5/6/8/9 regressions and 34 Stirling-number partition-count tests
9. Degree-two normalization and cubic logarithmic/inverse formal checks

The ordinary replay *reuses* the saved exact integer count for (n,r)=(48,7). Its output explicitly has `extended_case_recomputed_in_this_run: false`. This is a saved exact input, not a claimed recomputation. Smaller cases are recomputed.

## Extended replay

    bash reproduce.sh --extended

This also recomputes the full (48,7) case. That computation has 6,727,282 memoized states and can require several GB of memory. The original recorded timing was approximately 72 seconds, but timing depends on hardware. Do not run the extended mode in a memory-constrained environment.

## Standalone standard-library checks

The fixed-degree and finite general-length coefficient algorithms need only Python's standard library:

    python3 code/fixed/cyclic_covers.py
    python3 code/general_coefficients.py
    python3 code/general_coefficients.py --ell 3 --order 3 --sign -1
    python3 code/general_coefficients.py --ell 4 --order 2 --sign 1

The last commands return a Laurent polynomial as a JSON dictionary: keys are powers of lambda and values are rational coefficients. This reference algorithm is finite but intentionally unoptimized; high orders can be expensive. It does not numerically fit coefficients. A simple restricted-growth enumeration generates each admissible slot partition exactly once.

## PDF build

With a normally configured TeX Live or equivalent installation:

    bash build_pdf.sh

The script invokes pdflatex three times to resolve cross-references and the table of contents. All caches and build intermediates stay in the package-local `.build/` directory. If the installed TeX files lack a generated format or font map, the script creates those in `.build/` from the installed distribution; it never writes system or home-directory configuration. A fallback handles Debian-style installations with missing filename databases. It does not install missing packages. PDF timestamps are fixed for reproducibility. No third-party paper is needed to compile the article.

## Directory map

- `article/`: final PDF and editable TeX source
- `code/fixed/`: exact sums and numerical OEIS term excerpts
- `code/critical/`: independent symbolic and exact cubic implementations; saved extended exact count
- `code/general/`: quartic exact-product and coefficient diagnostic
- `code/models/`: independent small-model literal-product/logarithm comparison
- `code/general_coefficients.py`: finite all-length critical coefficient algorithm
- `code/check_degree_two_and_inverse.py`: degree-two and inverse formal checks
- `data/`: source attribution and frozen rational reference outputs
- `results/`: recorded reproducibility results, exact counts and diagnostics
- `REPRODUCIBILITY.md`: run scope and quality checks for this release

Some original checker scripts regenerate their JSON outputs beside the code. The `results/` directory retains the release outputs for comparison. Runtime-generated executables and `__pycache__` directories are not distributed.

## Method and source limits

The general-length theorem uses actual lambda=r/n^((ell−2)/2), restricted to a fixed compact positive interval. It retains the exact factorial carrier. Fixed-degree Stirling formulas must not be reused unchanged at growing degree. Even lengths have only integer powers of 1/n. The fixed-degree threshold theorem has an asymptotic lattice enclosure with an unspecified sufficiently large remainder constant; it is not a numerical certification algorithm for every finite target.

Source links and sequence attribution are in `data/SOURCES.md` and the article bibliography. Only necessary numerical OEIS excerpts are included, not full entry exports. No full third-party papers or external publication claims are included.
