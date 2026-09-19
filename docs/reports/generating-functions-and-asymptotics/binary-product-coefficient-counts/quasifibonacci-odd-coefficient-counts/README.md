# Odd coefficients in quasifibonacci products

A signed-cancellation proof of the statement of Stanley's Conjecture 6.3,
with a seed-independent extension, asymptotics, and exact algorithms.

Prepared September 19, 2026. Read `RESEARCH_STATUS.md` for the precise scope
and limitations of the literature/priority claim. The proof has not been
independently refereed or formalized in a proof assistant.

## Main theorem

Fix k >= 2. Choose positive integer seeds w_1,...,w_k such that each seed
exceeds the sum of all preceding seeds. Continue by the k-term recurrence
w_n = w_(n-1) + ... + w_(n-k). If h_k(n) counts odd coefficients of
product_(i=1)^n (1+x^w_i), then

    H_k(z) = (1+2z^k)/(1-2z+2z^k-2z^(k+1)),
    h_k(n) = 2^n                                  (0 <= n <= k),
    h_k(n) = 2h_k(n-1)-2h_k(n-k)+2h_k(n-k-1)       (n >= k+1).

The answer is independent of the particular seeds. The central proof
constructs periodic signs with block length k+1 and block product -1,
proves that every signed finite product is flat (all coefficients in
{-1,0,1}), and derives the count recurrence by an exact overlap calculation.

## Contents

- `article.pdf`: full article, with proofs, examples, and bibliography.
- `article.tex`: editable LaTeX source.
- `code/kbonacci_parity.py`: dependency-free exact algorithms and command line.
- `code/verify.py`: direct polynomial checks and numerical-data generation.
- `code/test_api.py`: boundary cases and input-validation tests.
- `code/make_tex_tables.py`: generates the article's table fragments.
- `data/verification.json`: exact coverage and outcome of the recorded checks.
- `data/verification_console.txt`: console output from the verification run.
- `data/api_tests.txt`: boundary/validation test output.
- `data/counts.csv`: h_k(n), 2 <= k <= 20 and 0 <= n <= 200.
- `data/b_k*.txt`: two-column index/value data for k=2,...,10; these are not
  assigned OEIS b-files and do not claim new OEIS identifiers.
- `data/growth.csv`: growth constants computed at 80-digit working precision;
  these decimal approximations are not certified interval enclosures.
- `data/large_values.json`: complete h_k(10000) values at six orders and
  large-index modular checkpoints.
- `data/*_table.tex`: generated table fragments, required for PDF compilation.
- `RESEARCH_STATUS.md`: source provenance and result boundaries.
- `Makefile`: rebuilding and verification commands.

## Run

Python 3.10 or newer; no third-party Python packages are required.
Do not use `python -O` for verification, because the checks use assertions.

```sh
python code/verify.py
python code/test_api.py
python code/kbonacci_parity.py 3 20 --prefix
python code/kbonacci_parity.py 3 10000
python code/kbonacci_parity.py 3 1000000000000 --modulus 1000000007
python code/kbonacci_parity.py 3 8 --coefficient 105
```

The last two commands return `699562826` and
`{"parity": 1, "signed_coefficient": -1}`, respectively.
The signed coefficient refers to the canonical coherent signing, not to
the original all-plus product's integer coefficient.

### Python interface

```python
import sys
sys.path.insert(0, "code")
from kbonacci_parity import count_fast, count_prefix, CoefficientOracle

assert count_fast(3, 20) == 76576
assert count_fast(3, 10**12, modulus=1000000007) == 699562826

# Nonstandard superincreasing seeds, and a noncanonical initial sign block.
oracle = CoefficientOracle(3, 50, seeds=[2, 7, 15], initial_signs=[-1, 1, -1])
parity = oracle.parity(1000)       # 0 or 1
signed_value = oracle.signed(1000) # -1, 0, or 1
assert parity == abs(signed_value)
```

`count_fast` takes O(k^2 log(n+1)) ring operations, including for composite
moduli. This is not a bit-complexity claim: an exact result has Theta(n)
bits for fixed k. The coefficient oracle uses at most O(n) arithmetic steps
per query after O(n+k)-entry preprocessing; it does not expand an
exponentially long polynomial. For direct small-instance checking,
`parity_bitset` has a default degree cap of 8,000,000. The sparse checker is
also intended only for small products and can require exponential memory.

## Build the PDF

A TeX distribution providing amsmath, amsthm, newpxtext/newpxmath, geometry,
microtype, mathtools, booktabs, array, enumitem, xcolor, fancyhdr, titlesec,
listings, hyperref, and cleveref is required. No font files are bundled.

```sh
make all
```

Or run:

```sh
python code/verify.py > data/verification_console.txt
python code/test_api.py > data/api_tests.txt 2>&1
python code/make_tex_tables.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

`make clean` removes only TeX build intermediates and Python bytecode;
it retains the PDF, source, and generated data. The recorded verification
uses a fixed pseudorandom seed. Timings and the recorded Python version may
change on another system.

## Verification is not the proof

The article's argument proves all indices and all orders. Direct polynomial
multiplication checks only finite instances. Agreement between the two
recurrence-based counting algorithms checks their implementation, not the
combinatorial theorem. The verification report gives the actual maximum
factor count per order in the capped bitset sweep; at the largest orders
that sweep reaches only the nonoverlapping seed block.
