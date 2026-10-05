# Exact finite checker for the minimal binary DFA report

This is a self-contained Python checker for the report's algebra and finite
counting data. It requires Python 3.10 or later and SymPy 1.14.0 (see
`requirements.txt`). No network access, external program, numerical Airy root,
or proprietary system is used. The two companion dependency files must remain
at the report-relative paths recorded in `data/dependencies.json`.

## Replay

From the unpacked report directory:

```sh
bash checks/replay.sh
```

The replay runs `verify.py` and `negative_tests.py` in both normal Python and
`python -O`. `PYTHON=/path/to/python3 bash checks/replay.sh` selects an interpreter.
The script never installs packages, generates expected answers, or modifies any
source/input/dependency. Its only writes are `checks/logs/`. Use an environment
with the pinned requirement already installed. Run `python3 checks/verify.py
--help` for individual sections; even section-specific runs enforce all input,
source-manifest, and dependency integrity checks.

The delivered logs are actual captured program output. `logs/run_records.json`
records the successful commands, environment versions, log SHA-256 digests, and
source-manifest digest. The four checks must all exit zero for the final record
to be written. The previous success record is removed before replay begins; a failed run
exits nonzero without writing a new success record.

## Exact, inspectable inputs

- `data/exact.json`: Proposition 5 coefficients, negative-index seed, first ten
  diagonal counts, uniform normalization, startup sites, rotated coefficients,
  the signed three-lag coefficients/support, and squared gauge formulas
- `data/formal_7.json`: all polynomial pairs through profile index 5 and all
  scalar coefficients through degree 7, over the exact ring Q[k,x]
- `data/endpoint_7.json`: log and multiplicative corrections through degree 4,
  and consecutive-ratio coefficients through degree 7, over Q[a]
- `data/inverse.json`: inverse transcription constants and tested exponent range
- `data/dependencies.json`: report-relative paths and SHA-256 pins for the
  unchanged relaxed-tree PDF and its source ZIP

These files are immutable expected values: their SHA-256 digests are embedded in
`verify.py`. The release source manifest additionally covers the eleven source,
README, script, requirement, and data files. The manifest is an integrity aid,
not a digital signature or proof of an artifact's authorship. The checker does
not regenerate it. Deliberate changes require a new reviewed release.

The parser accepts only exact integer/rational arithmetic, the listed symbols,
and bounded nonnegative integral powers. It does not evaluate code embedded in
JSON; it rejects floating-point constants, calls, unknown fields, missing or
extra entries, duplicate keys, nonfinite values, and malformed expressions.
Every acceptance condition uses an explicit exception rather than a Python
`assert`, so optimization cannot disable verification.

## What is checked

1. Integer Proposition 5 triangle through row 36, the `b(-1,0)=1` seed, the ten
   printed counts, uniform `B(n,m)=b(n,m)/2^m`, startup including `e(2,0)=1/2`
   and `e(3,1)=3/4`, forbidden/parity support, the diagonal conversion, and
   `0 <= B <= R`. The rotated recurrence is checked at all 357 admissible sites
   with `3 <= N <= 36`, including the factorial top edge and origin row.
2. Symbolic even/odd substitution and all five elimination identities; the
   negative second lag, positive third lag, exceptional `1/(2n)` origin entry,
   zero third-lag origin row, and actual input supports. Exact counting values
   satisfy the three-lag equation at all 180 sites with `4 <= n <= 18`.
   Nonnegativity is tested only on actual entries through `n=36`; a deliberately
   inadmissible raw negative coefficient is also checked to expose why support
   matters.
3. Symbolic squared identities for the factorial gauge, adjacent Jacobi entry,
   gauge ratio, and cancellation in `P/j` and `W/j`. Factorial evaluation checks
   1,848 conjugated memory entries through `n=36`. Squaring introduces no sign
   ambiguity because actual coefficients and factorial gauges are nonnegative.
4. Exact rational transformation to the DFA formal equation; substitution of
   both finished Airy-pair components through `t^7`; all boundary and gauge
   conditions. Five fresh coefficient stages are constructed twice, once by
   triangular polynomial inversion and once by a generic exact linear solve,
   and compared with the immutable coefficients. The polynomial operator's
   triangular diagonal is checked on basis degrees 0 through 12.
5. Formal discrete integration of the scalar carrier, endpoint Taylor
   expansion, all stored logarithmic/multiplicative coefficients, and ratio
   coefficients obtained both from the log expansion and directly from the
   two-step carrier and endpoint factors.
6. Inverse transcription of the `11/8` combined logarithmic coefficient, `d1`,
   the next Taylor correction, the elementary Lambert-W leading-inverse
   algebra, and the derivative of the four-term `F_J`. Newton error-exponent
   recurrence and the selected Newton/Stirling truncation inequalities are
   checked with exact integer/rational arithmetic for `0 <= J <= 128`.
7. Byte-for-byte integrity of both pinned relaxed dependencies. Hash equality
   does not verify their analytic statements or establish their applicability.

## Deliberate-corruption tests

`negative_tests.py` first passes a valid semantic baseline. It then independently
corrupts counts, startup, normalization, a rotated coefficient, row zero, a lag
sign, support, gauge cancellation, formal scalars/profiles, endpoint coefficient
families, inverse constants/exponents, schema, and expression syntax. Corrupt
input bytes, altered dependency pins, and altered bytes of each copied relaxed
dependency or checker source must also be rejected. Semantic mutations use separate in-memory
copies after the hash gate, so the algebraic checks themselves are exercised;
no release file is edited. Temporary dependency copies are discarded. Only the
expected verification exception counts as rejection; unexpected exceptions or
incorrect acceptance fail the test. The scripts are also parsed to check that
none contains a Python `assert` statement.

## Scope and limits

Finite checks are not analytic proof. In particular this package does not prove
uniform remainder bounds, infinite-dimensional spectral estimates, positivity
of the amplitude, convergence of its defining limit, all-depth formal
existence, validity of the inverse asymptotics, or convergence of an infinite
asymptotic series. Those are mathematical arguments in the report and its
explicitly pinned dependency. No numerical estimate of the amplitude or inverse
is certified here. Exact identities and independent finite constructions are
useful reproducibility checks, not replacements for those arguments.
