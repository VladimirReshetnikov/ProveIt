# Exact finite verification

Run from any working directory:

```sh
sh /path/to/bounded_ascent_report/run_checks.sh
```

Requirements: Python 3.9 or newer and a POSIX shell. The exact suite uses only the
Python standard library, makes no network requests, and needs no installation.
Set `PYTHON=/path/to/python3` to choose the interpreter. Expected runtime is tens
of seconds on an ordinary machine; the measurements are not a performance claim.
Any failed condition produces a nonzero exit. The runner stops immediately.

The runner executes the entire exact suite both normally and with `python -O`.
It then executes the regression harness itself under `-O`; that harness runs
64 bad-input cases in 128 subprocesses, with and without `-O`. None of our Python
programs contains a removable `assert` statement. The regression harness checks
this syntactically, as well as checking real failure exit codes and diagnostics.

## What is checked

1. Literal enumeration generates actual ascent words from the definition:
   `a[1]=0` and `0 <= a[k] <= 1+asc(a[1:k-1])`. Each value may occur at most `r`
   times. It does not use either residual-capacity transition rule.
2. An unsorted dynamic program retains the ordered list of residual capacities;
   it deletes exhausted labels but never sorts labels.
3. A compact dynamic program uses the category-count transition in the report.
   Its implementation does not call the unsorted transition implementation.
4. For every `r=2,3,4,5,6` and `0 <= n <= 10`, all three total counts agree with
   each other and with the frozen integer values. For every nonempty length
   `1 <= n <= 10`, every bin of the complete endpoint vector
   `X=(X_1,...,X_r)` agrees among all three models and with the frozen fixture:
   50 full histograms, containing 985 nonzero bins altogether. This is the full
   category-count marginal, not a claim that sorted and unsorted last-threshold
   distributions agree. Empty length has count one and no nonempty-state vector.
5. The same three-model and full-histogram comparisons are also run through
   `n=11` for `r=2`. Its `n=11` total is compared with the published value 77451;
   no frozen endpoint-histogram fixture at `n=11` is claimed.
6. The literal enumerator separately records the full joint distribution of
   `(N_1,...,N_r, distinct, ascents)`. The compact endpoint identities recover
   exactly that distribution. The exact extension identity
   `c[n+1,r] = sum_X (sum_j X_j) h[n,r](X)` is checked whenever both lengths were
   computed: `n=1..9` for `r=3..6`, and `n=1..10` for `r=2`.
7. All 12,220 adjacent-capacity swap cases are checked for `r=2..4`, initial
   capacity-list lengths `2..4`, all capacities in `1..r`, thresholds `2..d`,
   every adjacent pair strictly below the threshold, and suffix lengths `0..4`.
   Each equality compares the full joint distribution of final `X` and the
   number of new ascents, strengthening a total-count-only test. Equal-capacity
   swaps and zero-length suffixes are included in this stated case count.
8. There are 78,570 deterministic buffered-path checks: `r=2..6`, block lengths
   `3..8`, six specified category-count patterns, all middle permutations, and
   three starting thresholds. They check category retention, exact drift,
   the ascent formula, and final threshold closure. The observed ascent bins
   equal independently computed Eulerian numbers. Five additional constructions,
   one for each `r=2..6`, have strictly positive drift in every coordinate.
   No pseudorandom sampling is used.

The literal runs visit 919,973 nonempty prefixes in total (including `r=2,n=11`).
All arithmetic used by these checks is exact integer arithmetic.

## Reference data and strict coverage

- `data/expected_counts.json`: all 55 count values for the fixed rectangle
  `r=2..6`, `n=0..10`. These reproduce the earlier independent original-word
  audit's count output.
- `data/expected_histograms.json`: all 50 full endpoint histograms. These were
  frozen using a separate literal-word audit implementation and then compared
  with all three implementations shipped here. They are regression fixtures,
  not an independent mathematical theorem or a published dataset.
- `data/published_counts.json`: 57 published count entries: 12 for `r=2,n=0..11`
  from [OEIS A202058](https://oeis.org/A202058), and 45 entries from the displayed
  square array in [OEIS A294220](https://oeis.org/A294220), namely `r=2..6,n=0..8`.
  Overlapping entries intentionally appear in both source records.
  A294220 is the entire array; its `r=3` column is A317784. The `r=3,n=9,10`
  entries in the frozen local fixture are not described as independently
  published values in this package. Source pages were checked on 2026-10-02.

Each schema requires its exact fields, integer types (excluding booleans),
nonnegative coordinates, positive counts, exact dimensions, and exact coverage.
Duplicate JSON object keys, source records, `(r,n)` rows, and endpoint vectors
are errors. Missing or extra rows, truncated value lists, altered claimed
coverage, out-of-range indices, unknown fields, impossible endpoint statistics,
and mismatched histogram totals are errors. The required rectangle and source
coverage are fixed in the validator, not taken on trust from fixture metadata.
Reference values are compared with freshly recomputed values; the test does not
merely check that some overlapping subset agrees.

The negative regressions include syntactically valid but wrong count values
(with the histogram total modified to match), wrong histogram bins preserving
their total, and a wrong published value. These reach the mathematical comparison
and fail in both interpreter modes. Other cases exercise malformed/truncated JSON,
duplicate keys/records, missing coverage, invalid types/ranges, and nonfinite
constants. `--validate-only` checks structure, coverage, and internal consistency;
it intentionally does not recompute the mathematics. Use the default command for
full verification.

To run just the finite enumeration without swap/block checks:

```sh
python3 checks/bounded_exact.py --enumeration-only
```

To validate another dataset against exactly the same required schema and coverage:

```sh
python3 checks/bounded_exact.py --data-dir /path/to/data
```

A successful run only shows agreement on the finite cases stated above. It does
not prove the exchange lemma for all states, the block bounds for all lengths,
the root or ratio limit, concentration, a coefficient equivalent, or a convergence
rate. Those claims require the mathematical arguments in the report.

## Optional numerical diagnostics, separate from verification

`diagnostic_characteristic.py` requires `mpmath`. It is never imported or run by
`run_checks.sh` and can be ignored entirely. If desired, install `mpmath` in your
own virtual environment using your normal trusted Python package workflow, then:

```sh
python3 checks/diagnostic_characteristic.py --dps 35
python3 checks/diagnostic_characteristic.py --r 2 --dps 35 --drift
```

This prints approximate integral values, endpoint proportions, and (with
`--drift`) finite-difference residuals. It reports the dependency version and
working precision. The output is not interval-certified and contains no rigorous
quadrature error bound. Small residuals or many displayed digits are diagnostics,
not proof. Changing precision is useful for experimentation but does not convert
the output into a certificate. The finite-difference step stays at `1e-7`, so
raising arithmetic precision alone does not remove truncation error.

## Optional exact large-cap algebra

`analytics/` contains a separate SymPy-based replay of the report's finite
sector-coefficient formula. It checks the printed rational coefficients through
order three for sectors one, two, and three, the first-correction formula at
seven sector indices, and 26 invalid-input cases. Its own runner executes both
normally and under `-O`; it is not part of the default standard-library suite.
See `analytics/README.md` for dependencies, commands, and the precise scope of
these algebraic checks. A further mpmath sector diagnostic is explicitly numerical
and is excluded from both exact runners.

For an additional non-certified numerical check of the continuous cap inversion,
with mpmath installed, run:

```sh
python3 checks/analytics/diagnostic_cap_inversion.py
```

It uses 85-digit working precision and a finite integration cutoff, without a
rigorous tail or arithmetic error bound. See `analytics/README.md`; it is not
part of either exact runner and does not certify integer-cap rounding.
