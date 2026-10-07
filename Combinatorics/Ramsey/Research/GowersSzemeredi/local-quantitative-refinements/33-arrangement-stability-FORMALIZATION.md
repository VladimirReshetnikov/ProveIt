# Proposed formalization interface

**Status: plan only. No Lean file is provided or claimed to compile.**

The source labels in `article.tex` are the stable references. Use finite
additive commutative groups for G, H and K. First state count identities
and rational normalized inequalities; defer real square roots to an
optional corollary.

## Definitions and normalization

Define the balanced horizontal tuple domain for even `s >= 4`, with
`s/2` positive and `s/2` negative slots. Define arrangements as that tuple,
one common `h : H`, and `s` independent base points in H. The count is
`|G|^(s-1) |H|^(s+1)`. Include repeated occurrences and `h = 0`.

Define `VerticalModel` using an arbitrary function `a : G -> K`, a
biadditive map B, and a homomorphism `ell : H -> K`. Do not accidentally
replace the arbitrary row function by an affine one.

## Recommended dependency sequence

1. `ras:lem:independence`: solve a balanced equation for any omitted
   coordinate. Use the resulting constant-fiber count to establish
   independence of every proper coordinate subset.
2. `ras:lem:cycle`: for a probability vector, nonconstant labels on a
   cycle have at least two disagreeing neighboring pairs. Add one extra
   atom for a subprobability vector and use `b^r <= (r/2)b^2`. No limit
   argument is needed.
3. `ras:lem:noisy-hom`: retain the auxiliary labels. Prove collision
   probability at least `1-2e`, existence and uniqueness of the mode,
   additivity via three simultaneous mode events, and repair
   `e/(1-2e)` under `e < 1/6`.
4. `ras:lem:noisy-affine`: average over one anchored query. Keep query
   labels independent even when horizontal coordinates repeat.
5. `ras:lem:separation`: a nonzero affine difference vanishes on an empty
   set or a coset of a subgroup of index at least two.
6. `ras:thm:coarse`: synchronize affine derivatives using the cocycle.
   Distinguish equality as functions from equality at a random point.
   Convert pointwise error to function-level error using separation.
7. `ras:lem:profile`: optimize each row constant, retain collision error,
   and prove `t_h <= 2 delta`, `mean_h t_h >= delta`.
8. `ras:lem:one-error`: prove the finite inclusion-exclusion identity with
   the unknown full joint moment retained. Its sign depends on even s.
9. `ras:thm:profile-local` and `ras:lem:quadratic`: prove the local
   inequalities, checking nonnegativity before replacing the average
   derivative error by delta.
10. `ras:prop:moment`, `ras:prop:cross-order`, and
    `ras:cor:gowers-amplification`: use finite Fourier orthogonality and
    Parseval. Partial-domain counts are normalized by the full ambient
    count, not by the number of valid arrangements.
11. `ras:thm:main`: establish the small branch using the coarse theorem;
    conclude the rational quadratic inequality on the increasing
    interval. Add the radical expression only afterward.
12. Sharp examples and erasures: establish cyclic model parameterization,
    modal optimality, example power sums, and the extension union bound.

## Traps to prevent

A random section in place of independent per-occurrence labels changes
the distribution at repeated horizontal coordinates. A local polynomial
bound does not select its own inverse branch. A bound on invalid
arrangements cannot be omitted when extending a partial function. The
arbitrary `a(x)` gauge is genuinely invisible to the vertical test.
The conservative activation thresholds are sufficient, not known optimal.

The Python suite is useful for generated finite regression examples, but
its execution should not be used as a trusted axiom. No existing formal
status should be changed on the strength of this plan alone.
