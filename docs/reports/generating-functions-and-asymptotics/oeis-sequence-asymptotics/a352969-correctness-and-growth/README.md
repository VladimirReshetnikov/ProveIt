# OEIS A352969: correctness and quantitative growth

**Article:** `article.pdf` (typeset) and `article.tex` (complete source).
Prepared for Vladimir Reshetnikov, September 20, 2026.

Starting with S_0 = {1}, set

    S_(n+1) = {x+y : x,y in S_n} union {x*y : x,y in S_n},
    a_n = |S_n|.

Equal operands are allowed. Both operations use the previous set; this
is a simultaneous step, not repeated closure within a stage.

## Results established

The article proves the correctness of the OEIS Python algorithm under
its intended nonnegative-integer input and cache-integrity assumptions.
It explains the `A353969` wrapper-name typo and why returning an immutable
set prevents external mutation from corrupting memoized results.

Write `lg` for log base 2. For n >= 16, put

    t = ceil(lg(2*n))
    r = smallest nonnegative integer such that t <= r*(r+1)/2.

The article proves the explicit bounds

    2**(2**(n-r-4)) <= a_n <= 2**(2**(n-1)),

and hence

    lg(lg(a_n)) = n + O(sqrt(log(n))),
    log(a_(n+1)) / log(a_n) -> 2.

More precisely, `a_(n+1) = a_n**(2-epsilon_n)`, where
`0 <= epsilon_n <= n**(-1+o(1))`.

The construction first represents every integer with at most 2**t binary
digits at height at most `t+r(t)+2`, using only 1, addition, and
multiplication. Balanced products of prime multisets give a family of
distinct reachable values by unique factorization. An elementary uniform
divisor bound controls one-step multiplication collisions. All needed
number-theoretic estimates are proved in the article.

### Precision of the conclusion

The normalized logarithms `lg(a_n)/2**n` decrease to a limit theta >= 0.
This work does **not** determine theta or prove theta > 0, and does not
claim a multiplicative asymptotic equivalent for a_n. It establishes the
stated double-logarithmic and successive-logarithm growth laws. The finite
tests supplement, rather than replace, the proofs for all n.

## Reproduce the computations

The code uses only the Python standard library and targets Python 3.9+.
From this directory, run:

    python code/reproduce.py
    python -m unittest discover -s code -p "test_*.py" -v

The supplied run used Python 3.13.5 and passed all 16 tests. Enumeration
was independently performed through n=6:

    1, 2, 4, 11, 52, 678, 67144.

The value `a_7 = 357306081` is from OEIS and was **not recomputed**. Fields
based on that value are explicitly marked as reported data. The exact
maximum at stage 7 and the number of candidate pairs are derived without
enumerating stage 7.

`reproduce.py` writes the data files and the runtime metadata. Capture its
stdout separately to replace `verification/reproduction.txt`. Test output
is captured in `verification/tests.txt`. Elapsed times, runtime metadata,
PDF build metadata, and gzip timestamps can differ on a rerun; numerical
sets, statistics, bound parameters, and expression witnesses are the
reproducible mathematical content. The random expression tests use a fixed
seed.

### API examples

Run these from the `code` directory, or add that directory to `sys.path`:

```python
from a352969 import (
    reachable, reachable_cached, counting_bound_parameters,
    ExpressionBuilder, check_certificate,
)

assert len(reachable(6, pair_budget=1_000_000)) == 67144
assert reachable_cached(4) == reachable(4)

# Returns exponents and parameters, not astronomically large integer values.
print(counting_bound_parameters(1_000_000))

builder = ExpressionBuilder()
root = builder.integer(123456789)
witness = builder.certificate(root)
value, height = check_certificate(witness)
assert value == 123456789
```

The pair budget limits unordered pairs **per stage**. It is a guard against
accidental very large enumerations, not a byte-memory limit. The default
reproduction stops at n=6. At n=7 there are already 2,254,191,940 unordered
input pairs and 4,508,383,880 sum/product candidates.

### Build the article

Install a TeX distribution providing `pdflatex` and the packages named in
`article.tex` (standard TeX Live/MiKTeX packages). Then run:

    python build.py

The build script uses `latexmk` when available, otherwise three `pdflatex`
passes. Auxiliary files are kept in a temporary directory. The PDF is
written to `article.pdf`; the transcript goes to
`verification/latex-build.txt`. A precompiled PDF is already supplied.

## File map

- `article.tex`, `article.pdf`: full proofs, explicit estimates, program
  analysis, computational results, references, and scope limitations.
- `code/a352969.py`: iterative and immutable-cached enumeration, exact
  height dynamic programming, bound parameters, constructive expression
  builder, and independent certificate evaluator.
- `code/test_a352969.py`: 16 tests, including independent ordered-pair,
  two-iterator, and value-indexed checks.
- `code/reproduce.py`: regenerates the mathematical data.
- `data/sets_0_to_6.json.gz`: all independently computed sets, sorted.
- `data/sequence_statistics.csv`: cardinalities, maxima, initial interval,
  prime counts, candidate counts, sum/product set counts, and source status.
- `data/counting_bounds.csv`: exact parameters for the explicit theorem.
- `data/expression_witness.json`: a 256-bit integer represented by 165
  nodes, of height 14, with leaves all equal to 1. The stored directed
  acyclic graph unfolds to a legal binary formula of the same height.
- `verification/`: run transcripts, metadata, proof-audit notes, and build
  output.
- `SHA256SUMS`: integrity hashes for the other package files.

## Source and attribution

The definition, listed values, Python-program attribution, and wrapper
spelling were read from the OEIS A352969 text record, revision 30 dated
April 26, 2022, accessed September 20, 2026. The sequence was entered by
Vladimir Reshetnikov; the OEIS program is credited to Chai Wah Wu. The
article describes that listing; the executable implementation in this
archive was independently written. Primary Python documentation supports
the iterator, integer, set, and caching semantics. Full citations appear
in the article. No claim of priority over all prior literature is made.
