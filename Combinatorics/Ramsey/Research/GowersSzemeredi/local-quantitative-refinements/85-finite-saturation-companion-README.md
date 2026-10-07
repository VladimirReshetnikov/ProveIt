# Exact finite saturation companion

classify.py is an unchanged copy of the independently derived and audited classifier. It imports only the Python standard library. It neither imports nor runs the Report 295 companion. Runtime guards are explicit exceptions and remain active with Python -O.

The main certificates are:

- compact_certificate.json: 19 quotient rows, with 27 nontrivial signed boundary comparisons, five automatic initial wins, and the exact cutoff inequalities
- finite_certificate.json: all 1,184 orders from 3 through 1,186 and all 351,648 allowed branches, their unique winners, separately computed candidates, runner-up values, strict gaps and all 77 saturation triples

At n=3 there is only one allowed branch; the runner-up and corresponding gap are null. A positive winner-minus-runner-up gap is a lower bound on the gap to every other branch. The all-order proofs and analytic exclusion of the infinite tail are in Report297.tex, not supplied by finite computation alone.

## Read-only verification

From the distribution root:

    python3 -I -B companion/exact_checks.py
    python3 -I -B -O companion/exact_checks.py
    python3 -I -B tests/test_companion.py
    python3 -I -B -O tests/test_companion.py

The wrapper always recomputes and verifies both committed certificates. It additionally checks the possible rational support orders using integer square tests and the displayed sample gaps at n=27 and n=81. It accepts no arguments and writes no files. Its stdout is deterministic.

The 14 grouped regression tests cover exact regeneration, both certificate corruptions in both Python modes, incompatible write/verify modes, missing inputs, sample gaps, clipping, candidate-domain rejection, full search counts, compact gap counts, explicit runtime guards, absence of floating-point constants, wrapper source immutability, identical normal/optimized stdout, wrapper argument rejection and rational support cases.

To regenerate explicit copies outside this tree:

    python3 -I -B companion/classify.py --write /tmp/report297-certificates

To verify those copies:

    python3 -I -B companion/classify.py --verify /tmp/report297-certificates

The write command is an explicit regeneration utility and may replace identically named files in its chosen directory; use a fresh external destination. Write and verify modes cannot be combined. The default classifier invocation recomputes but does not compare committed files, so use the wrapper or --verify for integrity verification.

## What the computation does not establish alone

The inherited complete fourth-norm equality theorem, all-order adjacent no-tie argument, initial-interval monotonicity, all-group Fourier positivity argument, strict-gap compactness argument and rational-density argument are mathematical proofs in the article or the explicitly cited predecessor. The code is not a general optimizer, not a proof assistant, and does not determine actual nonsaturating energy minima or all equality weights for nontrivial subgroup kernels.
