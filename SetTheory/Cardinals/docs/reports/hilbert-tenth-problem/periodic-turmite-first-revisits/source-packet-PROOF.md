# Complete exact first-hit implementation for one-visit turmites

Extension dated 2026-10-03. The original sibling packet `one-visit-turmite-boundary-20261003` remains frozen and unchanged. This note closes its explicitly identified implementation gap, without installing or invoking a general Presburger solver.

## 1. Scope and executable interface

The input and pre-departure time convention are the same as in the frozen boundary theorem: a finite cyclic L/R rule, explicit doubly periodic colour tile, finite defect map, starting lattice position and heading. The first-revisit decision returns an exact finite set of affine lanes

    p(n)=a+n*d,  time(n)=t+n*l,  0<=n<=N,

where l>0, N may be infinity, and heading is constant on a lane. On a no-revisit run the lanes cover all times; otherwise they cover times through the first repeated arrival, inclusive. The original proof establishes this representation. No later observation on a repeat-producing run is claimed.

The new `observations.solve` constructs that path and returns the exact first hit or `None` of a supplied finite union of `Clause` objects. Each clause combines:

- an optional finite allowed set of headings;
- finitely many integer linear coordinate congruences `cx*x+cy*y == residue (mod q)`, q>0;
- an optional finite set of absolute allowed head positions;
- an exact finite head-relative colour stencil, including possible repeated or contradictory entries.

Clause fields are materialized to immutable tuples once at construction, so repeated validation or execution cannot consume a one-shot iterable. An omitted heading/site restriction is unrestricted; an explicitly empty one is false. An empty stencil is true; an empty union of clauses is false. Palette size 1 is allowed.

The lower-level `first_hit` accepts a previously computed Result, with the documented precondition that it is the certified Result for the same rule/tile/defects. The end-to-end `solve` entry point guarantees this pairing. A hand-forged or mismatched Result is outside the lower-level contract.

## 2. Interval-congruence atoms

An atom is a subset of the nonnegative integers of the form

    A(lo,hi,r,q) = { n : n>=0, lo<=n<=hi, n==r (mod q) },

where q>0 and hi may be infinity. Its canonical representation stores the first allowed integer, the last allowed integer if finite, and the positive step q. Empty atoms disappear; singleton atoms use step 1. All bounds are attained endpoints, not merely loose bounds.

### Intersection closure

For residues r1 mod q1 and r2 mod q2, set g=gcd(q1,q2). The intersection is empty if g does not divide r2-r1. Otherwise extended Euclid gives the unique combined residue modulo lcm(q1,q2). Intersect the two closed intervals and round inward to that residue class. This is again an atom or empty. The algorithm handles modulus 1, non-coprime moduli, negative input residues and arbitrarily large endpoints using integer arithmetic only.

### Exact bounded counts

Intersect an atom with a finite interval [L,H]. If its first surviving point is f and f<=H', where H' is the smaller upper endpoint, its count is

    1+floor((H'-f)/q).

Otherwise its count is zero. Computing this does not enumerate points or a period.

## 3. Projecting a lane relation yields one atom

Fix a prospective observed location lane A (possibly shifted by a stencil offset), and an earlier-head lane B. We require indices n,k satisfying

    a_A+n*d_A = a_B+k*d_B,
    0<=n<=N_A, 0<=k<=N_B,
    t_B+k*l_B < t_A+n*l_A.                 (1)

The strict inequality is omitted for static target or defect membership. The desired set is the projection onto n. It is one interval-congruence atom or empty:

- **Rank two:** the two spatial equations have at most one rational solution. Test integrality and all bounds; retain the singleton n or return empty.
- **Rank one:** solve one nonzero equation with extended Euclid. All integer solutions are `n=n0+s*z`, `k=k0+r*z`. Check the other spatial equation. Every index or chronological bound becomes a linear inequality in z, whose conjunction is one integer interval. In particular strict chronology is converted with the exact integer `-1` adjustment. If s=0, a nonempty feasible interval projects to the singleton n0. Otherwise its image is an arithmetic progression of step |s| with endpoints obtained from the interval endpoints. The n>=0 constraint gives a finite lower projected endpoint even if a parameter endpoint is infinite.
- **Rank zero:** unequal spatial bases give the empty set. Equal stationary bases allow the earliest old index k=0. Without chronology every allowed n works; with chronology the condition is exactly `n>=ceil((t_B+1-t_A)/l_A)`, together with n>=0 and the new endpoint. This is an interval atom.

This proves the implementation contract of `relation_indices`. A different heading at an earlier equal position does not exempt that visit.

A coordinate congruence restricted to a head lane is `A*n==B (mod q)`. The gcd divisibility test and a modular inverse reduce this to one residue class or the empty set. Finite head-site and defect membership reduce to the spatial relation above with a singleton static target.

## 4. Boolean closure without residue enumeration

Represent a set indicator as a finite signed sum

    F(n) = sum_A c_A * 1_A(n),

where each c_A is an integer and each A is an atom. The essential invariant is that F(n) is either 0 or 1 for every n>=0. Individual coefficients need not be positive.

Public construction begins only with the empty set, a single atom, or the nonnegative universe U. Boolean operations are implemented by

    1_(F AND G) = F*G,
    1_(NOT F) = 1_U-F,
    1_(F OR G) = F+G-F*G.

Products distribute over the finite sums and use `1_A*1_B=1_(A intersect B)`. Atom intersection is closed by Section 2. Combine equal canonical atoms and delete zero coefficients. Structural induction proves both finite representability and the Boolean indicator invariant for every constructed expression. No enumeration of an lcm's residues is used.

The program's public `IndexSet` constructor accepts only a validated atom or empty. Internal coefficient construction is private and used only by these invariant-preserving Boolean operations. An arbitrary externally injected signed sum would not have the invariant and is not part of the public set contract.

## 5. Emptiness and exact minimum of the represented set

The number of members in [L,H] is exactly the signed sum of the atom counts. By the Boolean invariant it is a nonnegative integer, and it is zero exactly when the represented set has no member in that interval. This conclusion would be false for arbitrary signed functions.

For a finite signed representation define

    B = max(0,
            first endpoints of all unbounded atoms,
            last endpoints + 1 of all bounded atoms),
    Q = lcm(steps of all unbounded atoms),

with empty lcm 1. For n>=B all bounded atoms are false, and every unbounded atom is the unrestricted residue class of its step. Consequently F is Q-periodic on [B,infinity). The finite interval

    [0, B+Q-1]                             (2)

contains the entire exceptional prefix and one whole eventual period. Count (2) exactly. A zero count proves the set empty globally; a positive count brackets its minimum. Binary search with the monotone predicate

    count([0,H]) > 0

then returns the exact least index. B, Q and search endpoints are arbitrary-size integers; neither (2) nor a full residue period is expanded into a list. This takes O(log(B+Q+1)) exact counting calls, each a finite signed sum over the representation's atoms.

There can be exponentially many signed terms under Boolean expansion, and large coefficients/intermediate integers. This note makes no polynomial-complexity claim for general observation compilation/minimization. It is a complete terminating algorithm that does not enumerate a long flight or a complete residue period; cost can depend on bit lengths and the expanded term count. A separate optional complexity note concerns only the first-revisit engine.

## 6. Exact compilation of the colour predicates

For a fixed head lane A and stencil offset f let `y(n)=a_A+n*d_A+f` and `t(n)=t_A+n*l_A`. On the certified path domain the pre-departure board satisfies

    c_t(y) = [c0(y) + V(y,t)] mod m,

where V is the indicator that some earlier time s<t has head position y. No cell has had two departures before any time in this domain; at the first repeated arrival its second departure has not yet happened.

For each previous-path lane B, Section 3 computes the index atom describing `p_s=y(n)` and `s<t(n)`. Their finite union is the exact `Visited(n)` set, with strict chronology excluding current and future arrivals even though those arrivals are present in the whole-path representation.

For each colour q, compute `Initial_q(n)` by the following finite Boolean expression:

1. Union of exact defect-site matches whose override colour is q;
2. OR the conjunction of no defect-site match and a background-tile match of colour q.

A background-tile match uses two scalar coordinate congruences in n, so is representable by Section 3. Defect overrides take precedence even when redundant or when their colours equal another residue's background colour.

The desired colour alpha is the set

    (Initial_alpha AND NOT Visited)
    OR
    (Initial_((alpha-1) mod m) AND Visited).

It is exact also for m=1. Intersect these sets over the requested offsets with the lane domain, the heading check, the finite head-site set and the requested congruences. This produces the exact satisfying index set for one lane and clause.

Find the minimum index of each such set by Section 5. Time on a lane is strictly increasing because l>0, so its minimum index gives its minimum event time. The minimum over the finitely many lane/clause candidates is precisely the global first event time, with an exact position, heading and witnessing clause. No endpoint, target/defect/revisit tie, or time zero is discarded.

## 7. Implementation and assurance boundary

`one_visit.py` is an extension-local copy of the original first-revisit engine. Removable assertions were replaced with explicit ValueError/RuntimeError checks; the frozen original is untouched. `observations.py` implements the entire algorithm in this note using only the Python standard library. Its release library contains no `assert` statements. Public input errors are rejected in both ordinary and optimized Python modes. Test gates use `unittest` assertion methods, which remain executable under `python -O`.

The test program exercises independent truth functions for random Boolean expressions, direct geometric membership checks for rank-0/1/2 projected lane relations, independent evolving-board queries, empty/contradictory forms, first-collision observations, palette size 1, invalid inputs and huge first-hit values. The new release also reruns the original first-revisit regressions against the hardened copy. Normal and optimized logs are retained separately. Independent review and an independent checker are recorded separately rather than conflated with author tests.

No general Presburger engine, external solver, upstream repository code or arithmetic schedule is executed. No original packet file is overwritten and no publication is performed here.
