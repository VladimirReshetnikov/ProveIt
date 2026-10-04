# Independent fixed-lane occurrence review and affine sharing

**PASS, with a further five-addition saving.** The three complete quartics in
the [author packet](fixed_lane_boolean_occurrence38.md) correctly represent
their fixed-lane occurrence query over natural witnesses. Sharing the affine
forms before their congruence blocks lowers the best complete polynomial from
**114=42M+72A to 109=42M+67A**, with the same 23 natural witnesses and exact
degree four. For each of the three forms, this change preserves its entire
polynomial on the same coordinates over every commutative ring.

This is an occurrence component on an **externally certified lane**. The
packet supplies neither an actual turmite realization nor a first-hit
minimality certificate, and it does not improve a universal bound. The
established universal polynomial remains 84 operations.

## 1. Independent review of the complete source

The [checker](review_fixed_lane_boolean_occurrence38_affine.py) pins the
author's source, receipt and proof and all six inherited data/proof files.
It reads their bytes or JSON only; no author or predecessor Python executes.
The full author source and proof were read. There is no requested change to
the frozen author trio.

The external signed integer is n. The lane metadata give x=2n+1, y=3n−2,
and time t=5n+2. The domain is 0≤n≤50. Its four congruence truth values are

| Atom | Affine expression | Modulus |
| --- | --- | ---: |
| A | x+y−1=5n−2 | 4 |
| B | 2x−y−3=n+1 | 5 |
| C | x=2n+1 | 3 |
| E | y−1=3n−3 | 7 |

Writing H=A∨B and K=¬H, the query is
`domain ∧ ((H∧C) ∨ (¬H∧E))`. No claim about which physical machine realizes
this lane is used in the arithmetic theorem.

For an integer L and positive modulus d, each atom has five natural
coordinates qp,qm,b,s,h and the five residuals

```
qp*qm,
L−d*(qp−qm)−b*(s+1),
b*(s+1)+h−(d−1),
b*(1−b),
(b−1)*s.
```

At a common zero, b is zero or one. If b=0, the last residual forces s=0;
if b=1, the remainder is s+1>0. In both cases the third residual bounds
the remainder between zero and d−1. Euclidean uniqueness then determines
the quotient and remainder even for negative L. The first residual and
naturality make qp,qm their unique disjoint positive/negative parts. The
remaining coordinates are determined as well. Thus 1−b is precisely the
congruence truth value and the witness fiber is unique. This also covers
d=1 in the general atom construction, although the four fixed moduli here
are larger.

The domain uses n−lo and 50−n−hi with natural lo,hi. It has one zero exactly
when 0≤n≤50. The residual `K−b_A*b_B` uniquely fixes the common Boolean K.
In the shared form, left and right are the two gated branch values. In the
expanded form, AC,BC,KE and joined are their uniquely determined Boolean
products and union. In the optimized form, the sole final residual is
`C+K*(E−C)−1`. The two branches are disjoint. Each complete sum of squares
therefore has one natural zero for each accepted n, and no other natural
zeros. The maps between forms keep all domain/atom coordinates and compute
or forget their determined internal coordinates.

These maps between different forms are **zero-set bijections**. The three
forms have different witness interfaces and different complete polynomials.
The formal DNF/multiplexer identity itself needs Boolean C: its difference
is `A*B*C*(1−C)`. No all-value equality between the different forms is claimed.

The independent checker reconstructs every residual directly, using sparse
polynomials with exponent vectors rather than the author's repeated-name
monomials. It verifies all 78 original residuals and all 413 saved complete
polynomial coefficients. Every original paid gate and supplied port is live.
The exact quartic coefficient of `A_qp²*A_qm²` is one in every form.

## 2. Six additions for the complete affine interface

The author's first eleven paid additions/subtractions can be replaced by
the following six:

```
L_B = n+1
x = n+L_B
three_n_plus_one = x+n
L_E = three_n_plus_one−4
L_A = x+L_E
upper = 50−n
```

Their outputs are exactly n+1, 2n+1, 3n−3, 5n−2 and 50−n as required.
The suffix consumes only these affine outputs. The coordinate y has no
independent output requirement after the congruence expressions are
composed; time was already metadata rather than a paid output. All suffix
rows, residuals, witnesses and final sum-of-squares operations are retained
literally. Consequently this rewrite is a complete polynomial identity for
each form, with the identity map on its full witness tuple. It is stronger
than a statement merely about zeros or Boolean assignments.

| Complete polynomial | Parent M+A | New M+A | Natural witnesses | Residuals |
| --- | ---: | ---: | ---: | ---: |
| Shared multiplexer | 45+76=121 | 45+71=116 | 25 | 26 |
| Expanded DNF | 49+81=130 | 49+76=125 | 27 | 28 |
| Optimized multiplexer | 42+72=114 | **42+67=109** | 23 | 24 |

The common producer prefix becomes 56=16M+40A operations. Every new gate
and port remains live. The final sum-of-squares assembly is included in
each displayed count. Degree remains exactly four because the complete
polynomial itself is unchanged. No claim of optimality among all circuits
or all occurrence representations is made.

## 3. Saved evidence and scope

The [receipt](review_fixed_lane_boolean_occurrence38_affine.json) contains
all three new complete instruction arrays and all polynomial coefficients
with explicit variable order. It checks 715 old/new paid gates, 156
old/new residual coefficient comparisons and 413 complete coefficient
entries. The independently derived accepted indices are

```
1,4,8,10,15,19,22,34,36,43,46,49.
```

There are 624 complete numeric evaluations: 516 evaluations of canonical
natural tuples at signed n values (including ±10²⁰) and 108 rational
evaluations. These include 72 full zero evaluations. Exact coefficient
identities, rather than those samples, establish the all-value rewrite;
the Euclidean and Boolean argument establishes the unbounded fiber theorem.

From any working directory, after installation:

```sh
python3 review_fixed_lane_boolean_occurrence38_affine.py --repo-root ABS_REPO --expect ABS_RECEIPT
python3 -O review_fixed_lane_boolean_occurrence38_affine.py --repo-root ABS_REPO --expect ABS_RECEIPT
```

During staging add `--author-root /tmp`. The helper uses explicit exceptions
and recursively type-exact receipt comparison. The fixed-lane arithmetic
and five-addition identity leave lane certification, global machine history,
first-hit minimality and a universal compiler outside this packet.
