# Status and verification boundaries

## Mathematical status

This is a proof-bearing, AI-assisted, unrefereed research draft. All new
universal statements are supported by written proofs in `article.tex`.
They have not been encoded in Lean or Rocq. Independent expert review is
appropriate before treating the manuscript as a published result.

The main result answers the full-dimensional Zariski-density question in
Section 12.4 of the pinned prior ProveIt arithmetic report. Stronger
all-slice and S-integer statements are proved. The counting result resolves
the completely split sector of the target-height question, for fixed `c`.
It does not assert uniformity in `c`, a power-saving error term, or a count
of nonsplit cubic fibers.

## What was executed

`code/verify_results.py` was run successfully. Its twelve groups check:

1. the original polynomial Jacobian;
2. the inverse chart identities;
3. the numerator-root cubic factorization;
4. the dominant three-parameter Jacobian;
5. the dyadic cancellation identity;
6. the independent modulo-eight image (176 of 512 target classes);
7. combined bad-prime densities for nine values of `c`;
8. the odd-prime coefficient-integrality residue lemma on 9,668 cases;
9. the local criterion against exact rational denominators on 951 integral
   distinct split fibers from a fixed-seed sample;
10. the dense universal family on 108 signed-slice parameter choices;
11. the complete divisor-based enumeration of integral split exceptions
    for seven selected slices;
12. exact modular witnesses for eight moduli, including 18,144,000.

`code/count_heights.py` was run for `c=1,2,3,4,8` and
`T=1,000; 10,000; 100,000`. All membership decisions use checked integer
arithmetic. The original map, root chart, and finite exception formula
are explicit; no numerical root approximations are used. Decimal values
of constants and ratios are illustrative, not rigorous interval bounds.

The source and output record the versions actually used. Timings are
machine-dependent and are not part of the mathematical certificate.

## What these checks do not establish

Finite samples do not prove a universal valuation theorem, Zariski
density, or an asymptotic. Those rely on the written arguments. SymPy is
not a proof-assistant kernel. The existing ProveIt Lean/Rocq developments
were not rebuilt here. Global priority was not independently certified.
