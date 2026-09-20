# A290268: rigorous partial results and finite certificates

**Status: the full conjecture is not proved in this archive.**

The article proves that the conjectured expression is an upper bound for the
number of collected terms in the nth derivative of `x^(x^2)`. It explains all
of the predicted cancellations, proves positivity in a large coefficient
region, and proves that there are no additional zeros on the first two
logarithmic-deficit diagonals. It identifies a precise remaining nonvanishing
lemma. It also proves explicit quadratic lower bounds, hence quadratic-order
growth, but does not establish the conjectured leading constant for all n.

The exact computations certify the complete proposed zero pattern for every
integer `0 <= n <= 3000`. They do not provide an induction beyond this range.

## Main files

- `A290268_partial_results.pdf`: the 15-page article.
- `A290268_partial_results.tex`: its complete LaTeX source.
- `code/`: exact Python verifier, C++ modular verifier, and certificate combiner.
- `data/`: all retained finite results, exceptional modular zero lists, explicit
  nonzero witnesses, run logs, and machine-readable summaries.
- `Makefile`: PDF and verification build targets.
- `SHA256SUMS.txt`: integrity hashes for the distributed files.

The starting point is OEIS A290268. The article gives references and
self-contained derivations of the coefficient identities and support bounds.

## What is proved

Write the derivative as

`f^(n)(x) = f(x) x^(-n) sum c[n,k,j] x^(2k) (log x)^j`.

The integer coefficient recurrence is

`c[n+1,k,j] = (2k-n)c[n,k,j] + (j+1)c[n,k,j+1]`
`             + c[n,k-1,j] + 2c[n,k-1,j-1]`.

Inside `1 <= k <= n, 0 <= j <= k`, the following coefficients are zero:

1. `j = k` and `n > 2k`.
2. `j < k`, `k` even, and `n = 4k - 2j + 1`.

Counting these two disjoint families gives the proposed formula as an upper
bound. It is an equality exactly when there are no other zeros.

Strict positivity is proved for `n <= 2k`, and for `n = 2k+1, j < k`.
All remaining coefficients with `k-j = 1` or `k-j = 2` are classified by
explicit sign formulas. The still-unproved case is `k-j >= 3, n >= 2k+2`,
excluding the reflection zeros.

## Finite verification scope

The arbitrary-precision Python calculation checks every potential coefficient
through `n = 200`. It independently checks three coefficient formulas for all
969 triples with `0 <= n <= 16, 0 <= j <= k <= n`.

Each modular run checks all 4,509,002,501 potential cells through `n = 3000`,
including the single initial cell. The moduli are 1,000,000,007 and 1,000,000,009.
There are respectively three and four zero residues outside the two proved
zero families. Those lists are disjoint. Every such coefficient has a nonzero
residue in the other modulus, and hence is a nonzero integer. This is a
deterministic finite certificate, not a probability estimate.

The algorithms use no modular division, so primality of the moduli is not a
premise. No floating-point arithmetic is used to decide whether a coefficient
vanishes. These are ordinary executable computations, not Lean or other
proof-assistant formalizations.

## Requirements

Python 3.10 or later and a C++17 compiler are sufficient for verification.
Python code uses only the standard library. The large modular calculation uses
two arrays of approximately 36 MB each, plus small overhead. The article uses
ordinary LaTeX packages listed in its source preamble.

## Reproduce

From this directory:

```sh
make exact        # Exact integer checks through 200; independent formulas to 16.
make modular      # Complete modular runs through 3000 under both moduli.
make certify      # Combine the complete modular zero lists.
make verify       # Run all of the above in the required order.
make pdf          # Rebuild the article using pdflatex.
```

The explicit commands are:

```sh
python3 code/verify_exact.py --max-n 200 --formula-n 16
mkdir -p build
g++ -O3 -std=c++17 -Wall -Wextra code/verify_modular.cpp -o build/verify_modular
build/verify_modular 3000 1000000007 data/p1000000007 data/watch_coordinates.csv
build/verify_modular 3000 1000000009 data/p1000000009 data/watch_coordinates.csv
python3 code/combine_certificates.py
```

The optional watch file extracts residues at seven specified coordinates; it
does not filter or restrict the complete search. To run a smaller test, omit
that file:

```sh
build/verify_modular 100 1000000007 data/test100
```

The combiner reads the two main `p1000000007_*` and `p1000000009_*` result sets.
It can validate the included logs without rerunning the recurrence, but an
independent reproduction should run both modular searches first.

Integrity of the distributed archive can be checked using:

```sh
sha256sum -c SHA256SUMS.txt
```

Rebuilding a PDF or rerunning logs may change files and their hashes; the hash
list describes the distributed version, not all possible rebuilds. The hashes
are integrity checks, not proofs of the mathematical conjecture.
