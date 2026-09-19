# Tetration, perfect powers, and frozen decimal digits

**Research article and reproducible exact-arithmetic artifacts**  
Prepared 19 September 2026.

Start with `article.pdf` (18 pages). The editable, self-contained LaTeX source is
`article.tex`; the bibliography is included directly in that file.

## Problem and result

For an integer base `a > 1` not divisible by 10, let `V(a)` denote the eventual
number of additional terminal decimal digits shared by successive tetrations.
The problem asks for the smallest nth perfect power `rho(n) = x^n > 1` for which
`V(x^n) = n`.

The result is `rho(1) = 2`, `rho(2) = 49`, and `rho(n) = B(s)^n` for `n >= 3`, where
`s = n - v_2(n)` and

```text
s mod 4       B(s)
   0          2^s - 1
   1        3*2^s - 1
   2          2^s + 1
   3        3*2^s + 1
```

The proof constructs the smallest admissible root divisible by 5 and rules out
all other roots with a deterministic quadratic size barrier. An elementary
inequality covers all `n >= 25`; the remaining comparisons are certified by
small exact integers. These finite certificates are part of the proof, not
statistical evidence or an extrapolation from a long initial segment.

For the stricter condition that the maximal perfect-power degree be exactly n,
the answer changes only at n = 3: `55^3 = 166375` replaces `25^3 = 15625`.

For n >= 10, the last ten digits of rho(n) are `1787109375` when n is 1 modulo 4
and `8212890625` otherwise. The article also proves a general decimal-tail
formula, a two-parameter extremal result, exact densities, and asymptotics.

## Provenance and proof status

The target is Marco Ripa's February 2025 MathOverflow question 487698 and the
all-n pattern described in Max Alekseyev's answer. The foundational speed
formula is prior work, rederived in the article. The explicit global minimum,
its proof and refinements are the results developed in this report.

The report presents a complete elementary argument for its stated theorem.
It has not been externally peer reviewed or verified by a proof assistant.
The consulted sources leave the all-n pattern conjectural, but the source
search is not a comprehensive guarantee of bibliographic priority. See
`sources.md` for precise attribution, links, and distinctions from older
results about unrestricted minima and existence of perfect powers.

## Reproduce the checks

Requirements: Python 3.10 or newer; standard library only. The included run
used Python 3.13.5. No network access or computer algebra system is required.
Run from the archive directory:

```sh
python3 code/verify.py > data/verification.log
```

**Do not run with `python -O` or `PYTHONOPTIMIZE` set:** the verification suite
uses assertions. A successful run ends with a JSON record whose `status` is
`ALL CHECKS PASSED`. It regenerates the data tables and `data/verification.json`.
Elapsed time is descriptive of a particular run, not a performance guarantee.

The suite includes:

* Agreement with a separately transcribed published case formula for 17,999
  bases, and 13,470 comparisons of the power-transfer identity with actual
  integer powers.
* Exhaustive minimum searches for n = 1,...,20, plus exhaustive searches of the
  exact-degree variant for n = 1,...,15. These are genuine searches of all
  smaller admissible roots, not merely evaluations of the proposed answer.
* Admissibility checks through n = 10,000, comparison with all 50 published root
  values, and modular tail checks through n = 2,000. Admissibility alone does
  not establish minimality; the article provides the all-n proof.
* All finite proof certificates, checks of the perfect-power exception through
  s = 200, 88 comparisons against literal small towers, separate modular tower
  computations for 17 bases, and density checks over six full residue periods.

## Compute values

```sh
# The minimum root for n=15: prints 98305.
python3 code/tetration_minima.py 15 --root-only

# Full minimum with maximal perfect-power degree exactly 3: prints 166375.
python3 code/tetration_minima.py 3 --strict

# Last ten digits only: prints 8212890625.
python3 code/tetration_minima.py 100 --digits 10

# Write a root table.
python3 code/tetration_minima.py --table roots.csv --count 1000
```

The full answer has order n^2 bits, whereas its root has order n bits. Printing
large answers incurs the corresponding memory and output costs. The CLI lifts
Python's decimal-string digit limit so that intentionally requested large
integers can be printed.

For very large n when only d <= n trailing digits are needed, import
`predicted_tail(n, d)` from `code/tetration_minima.py`: unlike forming the full
root, its calculation uses n only through the residue n modulo 4 (after checking
the domain).

## Build the article

A standard TeX Live or MiKTeX installation with pdfLaTeX and the packages in the
preamble is sufficient. Fonts use the ordinary TeX Latin Modern distribution;
no font files are bundled.

```sh
sh build.sh
```

The script reruns the Python checks and runs pdfLaTeX three times. Temporary
TeX output is placed in `.build/`; the finished PDF is copied to `article.pdf`.
Set `PYTHON=/path/to/python3` to select another Python interpreter.

## Archive contents

```text
article.tex                        Complete article source
article.pdf                        Compiled 18-page article
README.md                          This file
sources.md                         Bibliographic provenance and source status
build.sh                           Verification and PDF build script
code/tetration_minima.py            Exact arithmetic and command-line interface
code/verify.py                      Independent checks and certificate generator
data/minimum_roots_1_1000.csv        First 1,000 minimizing roots and parameters
data/rho_1_50.txt                   First 50 full values rho(n)
data/finite_certificates.csv        Exceptional-case proof certificates
data/small_range.csv                All finite-range barrier comparisons
data/verification.json             Structured verification results
data/verification.log              Captured output of the verification run
```

Third-party articles are linked, not redistributed. All tables in this archive
are regenerated by the supplied code; the separately recorded 50-term published
list is used as a consistency check, with attribution in the code and article.
