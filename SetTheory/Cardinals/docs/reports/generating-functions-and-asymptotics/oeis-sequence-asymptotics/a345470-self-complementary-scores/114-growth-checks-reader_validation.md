# Exact validation: scope, methods, and replay

## Recorded result

The archived `results.json` reports PASS using Python's standard library only: arbitrary-precision integers and `fractions.Fraction`. The clean output is identical with and without `-O`. The accompanying campaign records 37 named semantic or fixture-schema mutations, each rejected normally and under `-O` with the intended explicit diagnostic (74 rejections). Syntax errors and unhandled crashes are not accepted as successful mutation tests.

This is finite validation and algebraic bookkeeping. It does **not** numerically certify the Denisov–Wachtel survival theorem or weak convergence, a cone/endpoint order estimate, the resulting Theta laws, an asymptotic equivalent, a leading constant, or a general inverse asymptotic. Finite bijection tests do not prove a bijection for every size. The report supplies the mathematical arguments separately.

## Independent exact counts

For both weak and strict proper Landau inequalities, the validator compares three separately implemented formulations at every n from 0 through 38:

1. Half-score dynamic programming on `(last score, total score)`
2. Composition dynamic programming on `(used gaps, weighted gap sum)`
3. Integrated-walk dynamic programming on `(velocity, area)`, with the future minimum increment bounding reachable velocities and with the final slack step explicitly included but not area-tested

There are 156 pairwise comparisons. A fourth method enumerates full nondecreasing score lists and tests every proper full Landau inequality, symmetry, and total score for n=0 through 9, giving 20 additional checks. The n=0 and n=1 values are the stated sequence conventions; no large-n theorem is applied to them.

The 35 terms of A345470 (n=0..34) and 39 terms of A351869 (n=0..38) in `fixtures.json` were checked against the OEIS entry pages on 2026-10-02:

- https://oeis.org/A345470
- https://oeis.org/A351869

Both offsets are 0. These are entry-page prefixes, not a claim to have rechecked the complete linked b-files. The range, length, integer types, offset, identity, provenance fields, rational reductions, and complete fixture key sets are enforced. Booleans are not accepted as integers; duplicate and unknown JSON keys are rejected.

## Exhaustive representation and boundary checks

For n=2..17, all 26,364 nondecreasing candidate half-score lists and, independently, all 26,364 corresponding weak compositions are enumerated. Checks include:

- Full reflection symmetry, total score, and the exact excess identity A(n-r)=A(r)
- Equivalence of half and full weak/strict Landau tests
- Both directions of the finite gap/slack correspondence
- V(r)=s(r)-r+1 and equality of integrated area to Landau excess
- Weak integer area positivity after the exact +1 area shift
- Final velocities -1 (even) and 0 (odd), and increment-sum endpoints -2 and -1
- Equal composition probability 2^-n
- 22,987 valid even-to-odd or odd-to-even injection checks, including ordering, score bounds, and preservation of the new last excess
- 16 exact frozen-class identities with G1=1, G(m+1)=0, their factor 1/8, start (1,1), and tested-time target 0 (even) or 1 (odd)

The strong sequence has D(1)=1>D(2)=0; its monotonicity claim begins at n=2. The weak sequence is nondecreasing from n=1. The checker explicitly retains the strong exception.

The smallest extra-final-test counterexamples are recorded: the weak n=2 half-list (0) has tested area 0 and untested next area -1; the strict n=4 half-list (1,1) has tested area 1 and untested next area 0. Imposing another area test would incorrectly discard them.

## Distribution and exact algebra

There are 2,080 negative-binomial cases (lengths 1..32, geometric totals 0..64). Each checks the two mass formulas, consecutive-mass ratio, modal atom, and exact finite-sum-plus-tail normalization. A separate geometric convolution checks lengths 1..8 at totals 0..16. Geometric-series rational identities give E[X]=0 and E[X^2]=2. The exponential-moment certificate is E[(3/2)^|X|]=7/4, including 65 exact finite-sum-plus-tail checks; positive masses at -1 and 0 certify span one.

A standard-library multivariate Laurent-polynomial computation checks the Gaussian exponent difference identically as

    12*a*w/t^2 - 4*b*w/t = 4*w*(3*a-b*t)/t^2.

This is an exact coefficient identity, not a floating-point sample. Integer bridge split and area-protection inequalities are checked at lengths 2..1000 (999 lengths), with 149,285 endpoint-window cases. The area bound uses the equivalent integer comparison 16*t^3 > ell^3, avoiding square-root approximation.

The formal inverse bookkeeping includes 112 exact power identities and 200 finite threshold/minimality tests on the computed count arrays. No value for the inverse's bounded error or for a leading asymptotic constant is inferred.

## Hardened replay and mutation campaign

From this directory, run:

    python3 validate.py
    python3 -O validate.py
    python3 mutation_campaign.py

The package-level `replay.py` additionally checks archive integrity. `validate.py --output PATH` and `mutation_campaign.py --output PATH` write JSON; outputs are otherwise printed. Every guard uses an explicit exception, with zero Python `assert` statements in the validator.

The campaign first runs clean normal and optimized validation in two fresh temporary directories containing only the checker and fixture. Their complete output hashes must match. Every mutation is then run in a separate fresh directory; it must exit with code 2 and the intended `VALIDATION_FAILURE` diagnostic. Every mutant's before/after hashes are recorded, as are the original input hashes before and after the campaign. The originals and each mutant input must remain unchanged during their validation runs.

Named attacks cover terminal parity, extra slack positivity, old/new velocity integration, weak/strict boundaries, weighted compositions, reflection, slack omission, the +1 shift, the frozen target and factor, the odd-to-even injection, negative-binomial ratio/normalization/mode, Gaussian cross-term sign, split and area bounds, altered reference terms, variance and exponential moments, formal inverse coefficient, and malformed or weakened fixtures. The archived mutation JSON is deterministic for the frozen three inputs (`validate.py`, `fixtures.json`, `mutation_campaign.py`), and can be reproduced without network access.
