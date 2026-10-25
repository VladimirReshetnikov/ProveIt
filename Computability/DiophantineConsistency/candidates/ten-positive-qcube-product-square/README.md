# Ten positive unknowns in 81 operations: the materialized circuits

Two complete equations N = 0 in ten strictly positive integers, each with
an ordinary proof (PROOF.md) that it has no solution if and only if the
inherited syntactic refutation calculus derives no contradiction from ZFC.
The fixed coefficients are the whole indexed compact44 tuple delivered with
wave-14 package 133, in `coefficients/` (byte-identical to the copies in
`research/ten-positive-doubled-product-square/coefficients/`).

| Equation | Operations | ×/+/− | Exact degree | Parent |
|---|---:|---|---:|---|
| `equations/qcube_product_square_81.json` | **81** | 48/19/14 | 750 | 133's 84 / 436 (weight V²) |
| `equations/qcube_product_square_82.json` | 82 | 49/19/14 | 560 | 133's 85 / 328 (weight bV) |

## Priority

The construction is q-cube normalization applied to 133's product-square
kernel. It was found twice on 24 October 2026, independently and within
minutes. The research session committed it first, as the code-free proposal
[research/ten-positive-qcube-doubled](../../research/ten-positive-qcube-doubled/PROPOSAL.md)
(`a576e152f4`, 22:07), with the same polynomials, the same 81 / 750 and
82 / 560 schedules and the same leading forms, approved in
`reviews/ten-positive-qcube-doubled-ordinary-peer.md`. This package was
written here at 22:01–22:05 without knowledge of it and committed afterwards.

What this package adds is the finite material that proposal does not
supply: the emitted circuits, a deterministic build from 133's pinned
schedules, and the checks below. On the operations / degree frontier the two
points sit before 133's 84 / 436, 85 / 328 and the lower-degree points
89 / 288 to 97 / 254 (119, 121), 102 / 253, 104 / 252 (132) and 121 / 246
(130), which all remain.

## How they are made

Package 133 replaced the two-root norm by a single product-square equation
Q(Z² − RG·V²) + (RG − Z²) = 0, homogeneous of degree 2 in the centre
numerator Z and denominator M. The research session's q-cube normalization
(Y = q³·s, then cancel the common q³; `research/ten-positive-qcube-normalization`)
therefore applies unchanged: Z = q³Z′, M = q³M′, and q⁶ divides out. The term
Y/q³ = s of the centre moves into n, and the denominator P = q³(q − 1)
becomes q − 1. In the schedule this adds the row Y = q³·s, deletes
P1 = q³·h, and replaces the eight low-bracket rows by five:
84 + 1 − 1 − 8 + 5 = 81, at a higher degree.

The proof (PROOF.md) is a transfer: q⁶·N(n′, s, …) = N133(n′ − s, q³s, …)
as polynomials. 133's soundness bounds n after discarding −κ − s, so the
same bound holds for n′ = n + s; its completeness, with the actual canonical
bound R > 3q ≥ 96 recorded in the research session's accepted repair
(`research/ten-positive-doubled-product-square`, `a223b3e174`), gives
n′ = n133 + s > 0.

## Files and checks

- `build.py` derives both circuits from 133's schedules, pinned by SHA-256;
  `py -I build.py --check` rebuilds and compares.
- `verify.py` (`py -I verify.py`, writes `CHECKS.json`) checks:
  - the coefficient binding and the port box;
  - counts and liveness of every row, input and port;
  - exact degrees: measured on random lines modulo 2^127 − 1 and 2^89 − 1,
    and equal to the syntactic degree bound, so both bounds hold;
  - the transfer and centre identities against 133's circuits, at 16 points
    over two primes and at 30 exact-integer points with small ports (18 of
    them with n′ − s ≤ 0);
  - rejection of two mutations;
  - the leading forms along rays.
- `INDEPENDENT_REVIEW.md`: the adversarial review and its resolution.
- `UNKNOWN_ACCOUNTING.md`: why this kernel family spends one unknown on each
  of ten independent quantities (a heuristic record, not a minimality proof).

Scope: relative to package 133's calibration and tuple. No Lean theorem,
internal-ZFC certificate, consistency claim or minimality claim.
