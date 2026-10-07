# Exact companion scope

Run from any current directory with a standard-library Python 3 interpreter:

    python3 -I -B companion/exact_checks.py
    python3 -I -B -O companion/exact_checks.py

The diagnostic is offline, read-only and deterministic. It never imports or executes upstream repository code and does not approximate any real logarithm, exponential, or original threshold.

## Exact symbolic certificate

A tuple (u, v) represents the monomial 2^u alpha^v. Exact pair arithmetic reconstructs a, mu, b, s, t and beta from the displayed formulas for each of d_old=2^76 and d_fejer=2^42. The checker recomputes every certificate field and rejects a different value, field inventory or JSON type. It verifies the ratio degrees 1, 24718 and 12362, the source exponent ordering, P3=2359296, the exponent 25378984, the density denominator 64000, the interval constant 12801, and 12<4^3. It does not expand numbers like 2^(2^88).

These are exact identities and sufficient discrete inequalities used by the written proof. They are not a standalone proof system for real exponentiation, logarithms, maxima or ceilings.

## Explicit finite regression scope

The rational beta set contains the 45 distinct fractions a/d with 2<=d<=12 and 1<=a<d. Every ordered pair beta_old<beta_fejer yields 990 ceiling comparisons, including 30 equal-ceiling cases. Three fixed positive denominator pairs produce 2,970 coefficient comparisons. Eighteen small maximum comparisons include ten equal common-dominant maxima. The log-free iteration mechanism is tested in 480 cases: n_fejer=1,...,16, count difference 0,...,4, gain in {4,5,8}, and Q_fejer in {64,128}, with fixed exact A_fejer=3/2<A_old=7/3.

These rational examples are mechanism regressions, not evaluations of the original alpha-dependent parameters. Finite sampling does not prove a statement for every positive real density; Report296.tex contains that proof.

## Source records and data limits

The companion verifies 48 exact source excerpts totaling 133 source lines, associated with 34 complete-file identity records. Each excerpt has its own UTF-8 SHA-256, inclusive line range, and commit-specific link. The manifest's full-file SHA-256 and Git blob SHA-1 identifiers refer to complete upstream source files; those bytes are not bundled or refetched by the checker. Complete source dependencies are not compiled.

The three bundled JSON files have pinned package digests in exact_checks.py. This is consistency checking, not a digital signature. The loader rejects leaf symlinks, hard-linked or special files, oversized files, duplicate JSON keys, noninteger numeric literals, noncanonical encodings, oversized integers, and excessive container/node depth. JSON input is at most 128 KiB, at most 2,048 opening containers, depth at most 16 and at most 10,000 traversed nodes. The builder additionally rejects symlink ancestors and unexpected source-tree entries.

Exponents are exact integers bounded by 2^120; monomial power multipliers are bounded by 30,000; diagnostic density exponents are at most 2^88; iteration test counts are bounded by 128. Validation uses explicit runtime conditions and remains active with -O. The command has no input-path or network options and writes only deterministic JSON to standard output.
