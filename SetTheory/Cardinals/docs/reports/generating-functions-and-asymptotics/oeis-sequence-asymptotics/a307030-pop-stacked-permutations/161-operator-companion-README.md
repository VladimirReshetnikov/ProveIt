# Report161 bounded exact companion

Python 3.10 or later; standard library only. This standalone companion
computes pop-stacked permutation counts, OEIS A307030, by the published
endpoint recurrence. It separately tests the literal pop-stack map and the
position-poset normalization of the report's run representation.

All commands print deterministic JSON to standard output. The production
module has no network, input-file, or file-writing API. All authoritative
finite source data and attribution are embedded in `pop_stacked.py`.
There is no dependency on another report, the research workspace, or an
installed mathematical package.

**Scope:** finite checks test definitions, indexing, normalization, and exact
identities. They do not prove the analytic asymptotic theorem; certify any
decimal value of rho or C; find a spectral crossing; bound an analytic
remainder or its onset; or implement a certified asymptotic integer inverse.
No fitted, floating-point, or experimental constants are used by this code.

## Commands

From the report directory:

```sh
python -B companion/pop_stacked.py counts
python -B companion/pop_stacked.py verify
python -B companion/pop_stacked.py sources
python -B companion/pop_stacked.py threshold --value 1000000 --max-n 70
python -B -m unittest discover -s companion -p 'test_pop_stacked.py' -v
python -B -O -m unittest discover -s companion -p 'test_pop_stacked.py' -v
```

The module can also be imported from its own directory as `pop_stacked`.
The public mathematical APIs reject booleans and non-integer arguments for
integer parameters. Bounds are enforced before expensive computation. The
CLI accepts canonical nonnegative ASCII decimal integer tokens only: no
signs, spaces, leading zeroes except `0`, decimal points, or Unicode digits.
Every correctness check uses explicit exceptions and remains active under
Python's `-O` optimization mode.

- `counts --max-n N`: exact counts for `0<=n<=N`, with `0<=N<=70`, default
  `N=70`. The additional convention `p_0=1` counts the empty permutation;
  the OEIS source itself has offset one
- `verify --max-n N --brute-to B --poset-to P --direct-to D`: finite checks,
  with `B<=9`, `P<=10`, `D<=12`, and each at most `N`. Omitted limits shrink
  automatically to `min(N,cap)`. Explicit limits exceeding `N` are errors.
  Default bounds are `(N,B,P,D)=(70,9,10,12)`. The fixed, bounded
  cross-condition examples also run when `N` is small
- `sources`: the embedded 25-term OEIS numeric excerpt and 45-term paper
  table, with attribution, retrieval date, locations, and snapshot hashes
- `threshold --value V --max-n N`: find the first `n>=0` with `p_n>=V`
  by an exact bounded count scan. `1<=V<=10^200`, `0<=N<=70`. In particular,
  `V=1` has first index zero. If the bound is insufficient, `reached` is
  false and `first_n` is null: the sole conclusion is `N(V)>max_n`.
  No continuous approximation, floating-point comparison, or asymptotic
  rounding is used

The optional imported helper `low_order_inverse_coefficients(u,b)` accepts
actual `fractions.Fraction` values only, each with absolute numerator at
most 1000 and denominator at most 100, and `u>0`. It returns the exact
rational tuple `(d0,d1,d2)` at formal test parameters. This helper does not
calculate `u` or `b` from asymptotic constants.

Invalid CLI arguments give exit status 2 without JSON on stdout. A failed
mathematical check gives status 1, also without a partial JSON result.
Success gives status 0. The serialized JSON is capped at 2 MiB. Exact
potentially large counts and rational numerator/denominator values are
written as decimal strings to avoid precision loss in JSON consumers.

The default verification took approximately two to three seconds on the
build machine. Each full 17-test suite took approximately five to seven
seconds. These timings are observations, not runtime guarantees.

## Endpoint recurrence and its independent checks

Let `f_n(c,d)` count permutations whose final maximal ascending run has
minimum `c` and maximum `d`. Entries outside `1<=c<=d<=n` vanish. With empty
sums equal to zero, the published recurrence is

```text
f_n(c,d) = [c=1 and d=n]
  + [c=d] sum_{a=1}^{c-1} sum_{b=c}^{n-1} f_(n-1)(a,b)
  + [c<d] sum_{ell=0}^{d-c-1} binom(d-c-1,ell)
            sum_{a=1}^{d-ell-2} sum_{b=c}^{n-ell-2}
              f_(n-ell-2)(a,b).
```

The count is the sum over `c,d`. The optimized implementation uses
conventional southwest two-dimensional prefix sums as in equations (4)-(5)
of Claesson, Gudmundsson, and Pantone. It needs `O(N^4)` integer arithmetic
operations and `O(N^3)` integer cells. The independent literal implementation
uses the displayed nested sums without any prefix-sum transformation and
compares every refined endpoint table through `n=12`.

The default verification also checks:

1. All 25 displayed OEIS terms, `n=1,...,25`, and all 45 printed terms in the
   primary counting paper's Table 1
2. The literal push/flush pop-stack image equals the overlapping-maximal-run
   predicate **as sets** for every `n=0,...,9`. Each method processes all
   permutations; there are 409,114 input permutations across those sizes.
   At `n=9`, both sets have 95,991 elements. The final-run endpoint table is
   also compared and included in the JSON, rather than just the total
3. Reversing each maximal ascending run of every accepted permutation is
   a valid canonical preimage under the literal stack procedure. There
   are 109,850 such checks, including the empty permutation
4. Appending the new largest value preserves acceptance, is injective,
   and is reversed by deleting that final value, on all 109,850 accepted
   permutations in those finite sets
5. Every composition through `n=10`, including the empty composition,
   gives an independent position-poset linear-extension calculation.
   There are 1,024 compositions in total. Their sums agree with the
   recurrence, and their complete run-number distributions agree with
   direct enumeration through `n=9`. Each contribution to the exponential
   generating function is the exact rational `count/n!`
6. The one-run count is one at each positive checked size; all-singleton
   compositions vanish for `n=2,...,10`
7. Counts are nondecreasing through `n=70`; they lie between one and `n!`;
   they obey the finite disjoint-decreasing-quadruple bound
   `p_n*24^floor(n/4)<=n!*23^floor(n/4)`; even indices obey
   `p_(2m)>=(m!)^2`. The lower/upper-half interlacing construction is checked
   separately through `m=4`, including its injectivity
8. The displayed formal continuous-inverse coefficients `d0,d1,d2` are
   substituted into the truncated formal equation through degree `t^2`,
   using independent exact polynomial multiplication at 25 rational
   parameter pairs `(u,b)`. Every residual coefficient is zero. This
   checks the low-order algebra only, not an asymptotic remainder, a
   logarithm evaluation, or an actual inverse at numerical rho/C

The tests additionally compare the literal stack procedure to an independent
implementation that reverses maximal decreasing runs, through `n=6`. They
cover invalid argument types, every workload cap, exact threshold boundaries,
cyclic position constraints, and fault injection that forces validation
failures. An AST check excludes production `assert` statements. Normal and
optimized CLI outputs are compared byte for byte.

## What the normalization check means

Positions are numbered within a proposed composition of the permutation.
The poset imposes increasing order inside each block and **both** cross
inequalities for neighboring blocks:

```text
lo(left) < hi(right)       (overlap)
lo(right) < hi(left)       (a descent, hence maximality of the blocks).
```

Exact subset dynamic programming counts the linear extensions. The number
of admissible rank orders divided by `n!` is the volume of their disjoint
rank-order simplices. No approximate integration, extra multinomial factor,
or extra run-length factorial is inserted. For a single run of length `l`,
its interior-coordinate simplex at endpoints `a<b` has volume
`(b-a)^(l-2)/(l-2)!`; the singleton is its own one-dimensional component.
The finite program checks the discrete position constraints and counts,
not an infinite-dimensional operator identity or a measure-theoretic proof.

Two examples prevent silently losing a cross inequality:

- The proposed blocks `12|34` satisfy the first inequality but are not
  maximal ascending runs
- The proposed blocks `34|12` satisfy maximality but do not overlap

At `n=4`, summing position-poset extensions over compositions gives 11 with
both conditions and 24 with either condition alone. The latter equality of
totals is incidental; overlap-only decompositions are not asserted to be a
unique decomposition of every permutation. The allowed permutation `14325`
contains the decreasing triple `432` and has canonical preimage `41352`.
The four-term decreasing permutation `4321` is rejected. The exhaustive
image check also confirms that no accepted permutation through `n=9`
contains a consecutive decreasing quadruple. Three decreasing entries
must not be substituted for four in the avoidance argument.

## Sources and provenance

The numerical excerpt and recurrence are from:

- [OEIS A307030](https://oeis.org/A307030), displayed `%S/%T/%U` terms,
  snapshot retrieved 3 October 2026; entry revision `#63`, 18 November 2021
- Claesson, Gudmundsson, Pantone,
  [Counting pop-stacked permutations in polynomial time](https://akc.is/papers/033-Counting-pop-stacked-permutations-in-polynomial-time.pdf),
  [arXiv:1908.08910](https://arxiv.org/abs/1908.08910), equations (2), (4),
  and (5), pp. 4-5, and Table 1, p. 7
- Asinowski, Banderier, Billey, Hackl, Linusson,
  [Pop-stack sorting and its image: Permutations with overlapping runs](https://lipn.fr/~cb/Papers/popstack.pdf),
  Theorem 1 and proof, pp. 2-3, for the image characterization

The OEIS and paper data are independently transcribed into separate constants
in the script; the first is not generated from the second. The linked OEIS
b-file is not embedded and is not claimed checked. Full third-party papers
and full OEIS entry text are not redistributed. Source snapshot hashes refer
to the inspected historical files, not to hashes of these generated JSON
outputs, and do not imply the program fetches current versions online.

The report-specific implementation was developed against independent exact
recurrence and normalization audits. All 71 resulting values were also
compared with that independent recurrence computation during preparation.
The released program and tests do not depend on those audit files.

## Deterministic outputs and reproduction

| Command | Packaged deterministic output |
|---|---|
| `counts` | `data/counts.json` |
| `verify` | `data/finite_checks.json` |
| `sources` | `data/source_data.json` |

There are no clock readings, floating-point values, random seeds, absolute
workspace paths, or execution timings in these JSON outputs. Regeneration
uses exact arithmetic and is reproducible across supported Python versions.
The unit-test logs are execution receipts and contain variable elapsed times;
they are not deterministic computational data.

To compare regenerated outputs without overwriting a release, use a new
directory and shell no-clobber mode, from the report directory:

```sh
mkdir reproduction
set -C
python -B companion/pop_stacked.py counts > reproduction/counts.json
python -B companion/pop_stacked.py verify > reproduction/finite_checks.json
python -B companion/pop_stacked.py sources > reproduction/source_data.json
cmp data/counts.json reproduction/counts.json
cmp data/finite_checks.json reproduction/finite_checks.json
cmp data/source_data.json reproduction/source_data.json
```

The production module writes only to stdout. Any redirection is performed
by the caller's shell, so choose a fresh destination or use no-clobber mode.
The test suite reads only the local script and its three packaged snapshots
in the sibling `data/` directory;
it does not mutate them or make network requests.
