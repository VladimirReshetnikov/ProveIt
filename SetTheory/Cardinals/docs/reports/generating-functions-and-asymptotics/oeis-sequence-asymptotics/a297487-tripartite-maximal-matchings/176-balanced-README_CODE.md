# Report176 exact-code guide

## Files

- `verify.py`: independent exact derivations and certificate comparison
- `regenerate.py`: recompute the certificate; write only to a new explicit path
- `guard_tests.py`: positive checks and intentionally malformed certificates
- `build.py`: isolated offline PDF/ZIP build with normal/optimized checks
- `test_build.py`: fail-closed path, manifest, archive and overwrite checks
- `verify_manifest.py`: exact file inventory and SHA-256 verification
- `data/certificates.json`: all rational polynomials and integer counts
- `data/verified_results.json`, `data/guard_results.json`: reproducible receipts
- `references/independent_results.json`: frozen, independently computed symbolic
  results, used as arithmetic cross-checks; no code from it is executed
- `report.tex`, `SOURCES.md`: manuscript and bounded source/overlap assessment

## Certificate conventions

All univariate polynomial arrays are in ascending powers. Every rational is a
canonical reduced string such as `"13/96"`; integer rational values are strings
such as `"1"`. Polynomial trailing zeroes are forbidden by exact comparison.
Combinatorial counts are JSON integers. Booleans and floating values are never
accepted in their place. Negative power dictionaries identify their exponents
explicitly. Here `h=1/lambda`, `y=1/lambda^2`, and `lambda=sqrt(n/2)`.

The `d_polynomials` arrays use `z=k/lambda`. The `q_polynomials` arrays use the
positive marking parameter `v`. A `shifted_q_polynomials` entry with key `r`
means the Poisson expectation after the factorial shift `P -> P+r`, normalized
by the same Gaussian factor. The factorial-moment quotient still needs its
prefactor `lambda^r`; therefore its constant coefficient is one.

`elementary_carrier` is the expansion of `A_n/L_n`, with the exact elementary
carrier specified in the report. `log_elementary_carrier` omits the elementary
logarithm itself. The rare-event arrays multiply the even prefactor
`(2/3) exp(-lambda+3/8)` and odd prefactor `2 lambda exp(-lambda+3/8)`, respectively.

## Exact algebra

1. Build Bernoulli numbers by their rational triangular recurrence. Taylor-
   expand log Gamma in its shift, using the ordinary digamma asymptotic. This
   derives `d_0,...,d_5` without numerical fitting.
2. Exponentiate the finite rational-polynomial series. Gaussian differentiation
   is the polynomial operation `p -> p' - 3zp/4`.
3. Compute exact centered Poisson moments from
   `mu_(r+1)(t)=t(mu_r'(t)+r mu_(r-1)(t))`. Insert them into the finite Taylor
   expansion. Separately form the cumulant differential-operator recurrence;
   both constructions must agree coefficient-by-coefficient through order five.
4. Expand `D(h,z+rh)` for `r=1,2` before averaging. The exact Poisson factorial-
   shift identity then gives direct factorial-moment numerators. Divide series,
   retain the needed powers and form the variance with exact cancellation.
   This does not differentiate an unqualified asymptotic remainder.
5. Obtain the fixed odd shift using Bernoulli polynomials. Independently
   substitute `z=h` in the central Gamma algebra through `h^8`; the two logarithms
   must agree. Exponentiate and multiply by the inverse of `Q(1,h)` for the rare
   maximum-matching probability coefficients.
6. Compare all six `d_j`, all six `q_j`, their values at one, and the recursive
   histograms against the separate reference results. Reference expressions are
   parsed by a closed arithmetic AST supporting only integer constants, a single
   specified variable, arithmetic and bounded nonnegative powers. `eval` is not
   used.

## Inverse coefficients and finite rounding checks

The inverse-refinement certificate derives the two displayed coefficients from
`x=2 lambda^2`, `lambda'=1/(4 lambda)` and `H''=3/(2x)`. The Laurent products
`g'g` and `-H''g^2/2`, with the leading `g=lambda`, have exponent zero and
coefficients `1/4` and `-3/8`, respectively. These multiply `D^(-2)` and
`D^(-3)` in the report. This algebra does not certify the analytic Taylor
remainder or the omitted constant terms.

The certificate also records 48 exact rational rounding cases: centers 1 through
8, displacements `-1/1000`, zero and `1/1000`, and positive widths `1/1000` and
`1/2000`. Each checks

`ceil(x-epsilon)-1 < x-epsilon <= ceil(x-epsilon)`

and the corresponding upper inequality, including eight exact lower-integer
boundaries and eight exact upper-threshold equalities. The lower endpoint
`ceil(x-epsilon)-1` preserves the strict inequality even at an integer where
`floor(x-epsilon)` would not. Recorded endpoint margins are also the exact
inequalities for a linear increasing comparison model with errors bounded by
`epsilon`. This is a bounded finite check of the rounding mechanism. It is not
an effective asymptotic proof, a certification of the report's unknown onset,
or a numerical evaluation of Lambert W.

## Combinatorics and boundaries

The positive histogram uses

`t(n,k)=(n!)^3/[k!((n-k)/2)!^2((n+k)/2)!]`

for `0 <= k <= n` of the same parity as `n`. Its weight is `3t(n,k)` when `k>0`
and `t(n,0)` when `k=0`. Every division is checked for zero remainder. Totals are
computed through `n=100`, including `A_0=1`. The first 16 positive-index totals
are compared with the frozen source list. The code separately checks positivity
and strict increase on this finite range.

An independent memoized recursion picks the first remaining labeled vertex. It
can remain unmatched only in the already selected unmatched part, or be paired
with each vertex of either other part. It returns the whole unmatched-count
histogram and agrees through `n=8`.

Parameter tests reject booleans, noninteger/negative/out-of-range part sizes,
invalid expansion orders, invalid factorial shifts, zero formal divisors,
nonpositive/reversed/nonfinite marking intervals and invalid recursion sizes.
Empty and small graphs and exact marked moments are checked explicitly. The
marking compact is enlarged to `[a/2,2b]`, preserving a strict interior margin.
These tests do not extend the theorem to markings tending to zero or infinity.

## Manuscript-to-certificate consistency

The verifier reads `report.tex` without changing it. It locates the unique prose
marker `The first values for $n=0,\ldots,8$ are`, requires the immediately following
`\[...\]` display, removes only the permitted TeX comma/space commands, and
accepts only a comma-separated list of nine nonnegative decimal integers with
an optional final period. Every value must equal the corresponding exact
certificate count. This checks the manuscript's displayed prefix itself rather
than just the independently stored data.

The corruption suite uses isolated manuscript copies to reject the previous
`n=6` transcription error, short/long lists, arithmetic or decimal values,
negative values, unexpected TeX commands, missing/duplicated markers, and a
missing display terminator. The author's manuscript is never edited by tests.
This narrowly scoped extraction is not a general TeX parser.

## Guards and regeneration

No correctness or validation check uses Python `assert`; `python -O` must
produce the same results. Both cached public functions (`bernoulli` and
`recursive_histogram`) use type-sensitive cache keys. After the main derivation
has populated the caches, 54 additional tests first warm the exact corresponding
valid integer key, then require rejection of equal-valued booleans, floats and exact Fraction(0).
These cover every size and unmatched-part argument, plus Bernoulli indices,
with positional and keyword calls. A cached result therefore cannot bypass an
integer-type guard. The certificate comparison checks exact JSON types,
complete keys, array lengths and all values. Duplicate keys, nonfinite constants,
extra/missing fields, alternative fraction spellings and altered scope claims
are rejected. Corruption tests exercise each main result family in both modes.

`regenerate.py` uses the same exact derivation engine as `verify.py`, so its
purpose is reproducibility, not a second proof. Independent evidence comes from
the second Poisson construction, the matching recursion, the fixed-shift
cross-check and the separately prepared reference. The reference producer used
symbolic software; running or rebuilding this package does not require it.

```sh
python -B regenerate.py --output new-certificates.json --compare data/certificates.json
```

Existing files and symlink destinations are refused. No default write occurs.
All paths used by the programs are relative to their own package or explicitly
supplied by the caller. There are no machine-specific output directories.

The build manifest provides integrity and complete-file-set checking, not a
digital signature or authentication of the sender. Analytic proofs, literature
scope and effective error bounds require separate mathematical assessment.
