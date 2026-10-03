# An effective one-visit boundary for periodic turmites

Technical proof and implementation record, 2026-10-03. This is a lower-side result; it does not claim a new priority result or a completed literal two-visit universal loader.

## 1. Exact statement and conventions

Let `m >= 1`, and let `w : {0,...,m-1} -> {L,R}` be a finite cyclic turmite rule. The input also gives positive integers `u,v`, an explicit `u by v` colour table `b`, a finite map `D : Z² -> {0,...,m-1}`, an initial lattice position, and one of four headings. Put

    c0(x,y) = D(x,y) if (x,y) is in dom(D),
              b(x mod u, y mod v) otherwise.

Redundant entries of D are permitted. Integers and coordinates may be binary-encoded. At time `t` the configuration `(p_t,h_t,c_t)` is observed **before departure**: read `c_t(p_t)`, turn according to w, increment that cell modulo m, and move one unit in the new heading. Set

    tau = min {t >= 1 : there is s < t with p_s = p_t},

with tau infinite if the set is empty. Equality of positions, regardless of headings, is a revisit.

**Theorem.** There is a total effective algorithm on all these inputs which does the following.

1. It decides whether tau is finite. If so, it returns its exact value, `p_tau`, an earlier time s with `p_s=p_tau`, and an exact compressed description of `(p_t,h_t)` for `0 <= t <= tau`.
2. If tau is infinite, it returns an exact compressed finite prefix and integers `T >= 0`, `1 <= L <= 4uv`, a nonzero vector `delta in uZ x vZ`, and arrays `(a_i,g_i)`, `0 <= i < L`, such that

       p_(T+i+nL) = a_i + n delta,    h_(T+i+nL) = g_i    (n >= 0).

3. On the no-revisit branch it decides occurrence and computes the exact first time of any finite union of clauses combining:
   - a specified heading or a finite allowed set of headings;
   - finitely many linear coordinate congruences (in particular x/y residue-addressed ports);
   - an optional finite set of allowed absolute head positions;
   - an exact finite head-relative colour stencil `c_t(p_t+f)=alpha_f` for each f in a supplied finite set.
   The same query is decidable on the bounded interval `0 <= t <= tau` on the revisit branch. If there is no occurrence in the relevant domain, the answer is explicitly "none".
4. On the no-revisit branch each fixed finite head-relative colour observation is eventually periodic with period L in absolute time. Adding coordinate congruences gives another computable period, a multiple of L. A sufficient transient bound is effectively computable without expanding the long prefix.

There is no promise that the run is one-visit: the first part verifies this. The theorem does **not** decide arbitrary observations after a first repeat; it also does not say that the entire infinite board configuration is translated-periodic. The growing visited trail and original defects remain behind. Ordinary turmites continue moving and do not physically halt.

## 2. Static-shadow lemma

Define a shadow walk which reads c0 at every departure and never changes the board. For every `t <= tau`, its head position and heading equal those of the actual turmite. Indeed, every departure at time `s < tau` is from a cell not previously departed from, so the actual colour there is c0. Induction establishes equality through the arrival at tau, inclusive. Conversely, if the shadow has its first repeated position at tau, this induction establishes the actual first repeated position at exactly tau.

Thus the first-revisit problem is a static deterministic walk problem. Board updates still matter to colour queries, and are accounted for separately in Section 6.

## 3. Defect-free excursions are affine cycles

Ignore D temporarily. On the periodic background, the projected state is

    (x mod u, y mod v, heading),

of which there are `S=4uv`. Its successor is computable from b and w. In fact this successor map is a **permutation**: given the successor position q and successor heading h', the predecessor position is `q-e(h')` modulo the periods; reading the background colour there determines the inverse quarter-turn and hence the unique predecessor heading.

Consequently, from any start, the projected orbit is a pure cycle of length `1 <= L <= S`. Compute its first L positions and headings and the displacement delta after L moves. The defect-free lifted walk then satisfies

    p_(r+i+nL) = a_i+n delta,    h_(r+i+nL)=g_i,

for `0 <= i < L`, `n >= 0`; `delta in uZ x vZ`. If delta is zero this hypothetical walk has a repeated position no later than time `r+L`. Different phases may overlap even earlier, so one must check all phase pairs rather than only zero drift.

For robustness the reference code permits the more general finite-state transient-plus-cycle form, but in this model its transient is always empty. Keeping that generality does not affect the proof or bound.

## 4. Compressed history and exact intersection primitive

A **lane** is a tuple `(a,d,t,l,N,g)` describing positions and headings

    a+n d at time t+n l, heading g, for integers 0 <= n <= N,

where `l >= 1` and `N` can be infinity. A singleton uses N=0. Every completed finite excursion is represented by at most S bounded lanes; an unbounded prospective excursion uses at most S unbounded lanes. Cutting an excursion off at an integer time B only changes the endpoint of each lane to

    min(N, floor((B-t)/l)),

and deletes negative endpoints. No long flight is expanded.

### Exact earliest intersection

For new lane A and old lane B minimize `t_A+l_A n` subject to

    a_A + n d_A = a_B + k d_B,
    0 <= n <= N_A, 0 <= k <= N_B,
    t_B+l_B k < t_A+l_A n.                  (1)

The final inequality is omitted when B is a static point being tested as a defect. For internal self-intersections, both lanes come from the prospective excursion; strict time inequality avoids comparing a visit with itself and makes both same-phase and cross-phase overlaps correct.

This two-variable problem is solved explicitly, without an unbounded search:

- **Rank two.** The two coordinate equations form a nonsingular 2 by 2 integer system with columns `d_A,-d_B`. Cramer's rule gives its unique rational solution. Reject nonintegral or out-of-range solutions; otherwise test the chronological inequality.
- **Rank one.** Choose a nonzero coordinate equation `A n+B k=C`. Let `g=gcd(A,B)`. There is no solution if g does not divide C. Extended Euclid provides one integer solution `(n0,k0)`; all solutions are

      n=n0+(B/g)z,  k=k0-(A/g)z,  z in Z.

  Test the other coordinate equation. Because the matrix has rank one, it either holds identically on this family or is inconsistent. Each index bound and (1) is a linear inequality in z, so compute one integer interval, possibly unbounded, by floor/ceiling division. Reject an empty interval. Otherwise minimize n at the appropriate interval endpoint. If its coefficient is zero, any feasible z works. The n>=0 bound guarantees a finite minimizing endpoint whenever that coefficient is nonzero.
- **Rank zero.** Both spatial steps vanish. Reject unequal base positions. If equal, choose the earliest old index k=0. Without chronology choose n=0; with chronology choose

      n=max(0, ceil((t_B+1-t_A)/l_A)),

  and check its endpoint. This handles stationary lanes, in particular zero-drift projected cycles.

All arithmetic is exact integer arithmetic, including negative coordinates, zero displacements and parallel lines. The primitive returns a minimizing new time and an old witness time.

## 5. Total accelerated first-revisit algorithm

Maintain a restart time r, its current `(p_r,h_r)`, and a list H describing **exactly the head arrivals at times s<r**. Thus H excludes the current position at time r. Initially r=0 and H is empty. The invariant is that these arrivals are distinct, all departures before r were made from distinct cells, and the maintained walk equals the actual and shadow walks up to r.

At each stage:

1. Build the defect-free prospective excursion E from `(p_r,h_r)` as in Section 3.
2. Compute the earliest of every E/H intersection using (1), and every E/E intersection using (1). Call its time C, or infinity. This tests positions, not complete head states.
3. Compute the earliest E arrival at any point in dom(D), omitting chronology in the primitive. Call its time F, or infinity.
4. If `C <= F` and C is finite, output the repeated coordinate and old witness, with H plus E truncated through time C, and stop.
5. If both C and F are infinite, output H plus E. This certifies global one-visit. Retain the excursion starts, their at-most-S projected-state cycles, each finite cut time and defect departure, and the final unbounded cycle as a certificate. Each local transition and cut is finitely checkable. Check each finite excursion against every defect to confirm that its cut is its first defect arrival, and check that the final tail avoids every defect. The intersection primitive additionally checks pairwise disjointness of the complete returned path, including unbounded lanes. Its delta is necessarily nonzero, since zero drift would have produced C. Stop.
6. Otherwise `F<C`. The defect at E(F) is a fresh position: a past arrival, or two arrivals within E before F, would have produced an earlier or tied collision. Append the E arrivals at `r <= s <= F` to H. Read the initial defect colour at E(F), execute its actual quarter-turn and move, and restart at `r=F+1`. The board increment need not be stored for this head-path calculation.

### Correctness

Before the earliest defect hit, E follows c0. Before the earliest computed collision, E and H have distinct positions by the exhaustive pair checks. Thus the static-shadow lemma validates every processed departure. At a fresh defect its current colour is precisely its input colour, so the single special departure in step 6 is correct. The new history ends at time F, making its current-position exclusion at F+1 exact. If F+1 is already in H, the next iteration detects collision at local time zero.

Collision takes precedence over a tied defect hit: the arrival is already a revisit, irrespective of the colour that would be read afterward. Several representations producing the same earliest time cause no ambiguity; time determines a unique head position. Observations at that same time use the pre-departure board and are addressed in Section 6. Defects which are never encountered need not be removed or processed.

### Termination and operation accounting

Every step 6 processes a distinct defect position. A second arrival at a previously processed defect would be an H collision at or before that hit and hence would terminate in step 4 instead. There are K=|dom(D)| such positions. Therefore there are at most K defect departures and at most K+1 excursion constructions. Each requires at most S=4uv projected states.

The history has at most KS lanes, and the final compressed path at most (K+1)S lanes. A simple implementation performs at most

    S² (K+1)(K+2)/2 + SK(K+1)

pair-intersection calls, allowing all ordered E/E phase pairs, all E/H pairs and all E/defect pairs on every stage. It also performs O((K+1)S) finite-state successor steps. These are counts of operations on arbitrary-size integers, **not** a polynomial bit-complexity claim. The procedure never simulates a number of steps proportional to the distance of a far-away defect, the first-revisit time, or a lane endpoint. Large values occur only as integers in the representation.

## 6. Exact colour and first-occurrence queries

Let the returned valid path domain be all nonnegative times on the no-revisit branch, or `0 <= t <= tau` on the revisit branch. For every t in this domain and every position y,

    c_t(y) = [c0(y) + V(y,t)] mod m,          (2)
    V(y,t) = 1 iff there exists s<t with p_s=y.

Every cell has been departed from at most once before t, including at the first repeated arrival t=tau. Formula (2) is generally invalid after the departure at tau, and no claim is made there.

### Concrete Presburger formula

Suppose the returned lanes are `A_1,...,A_M`. For a head lane A with index n, set

    x(n)=a_A+n d_A,   t(n)=t_A+n l_A,
    Dom_A(n) := n>=0 and (n<=N_A if N_A is finite).

The head at this index has the lane's stored heading. At a head-relative offset f, define

    Visit_(A,f)(n) := OR over j=1,...,M of
      EXISTS k [Dom_j(k)
                AND a_j+k d_j = a_A+n d_A+f
                AND t_j+k l_j < t_A+n l_A].             (3)

Vector equality in (3) means two integer linear equalities. It excludes the current visit and all future visits, even though the path representation includes them.

For colour q, the input-board predicate at y is explicitly

    Initial_q(y) :=
       OR over z in dom(D), D(z)=q of (y=z)
       OR [AND over z in dom(D) of (y!=z)
           AND OR over tile residues (i,j) with b(i,j)=q
                    of (y_x == i mod u AND y_y == j mod v)].   (4)

At offset f, the desired colour alpha is therefore

    [Initial_alpha(x(n)+f) AND NOT Visit_(A,f)(n)]
    OR
    [Initial_((alpha-1) mod m)(x(n)+f) AND Visit_(A,f)(n)].       (5)

This remains valid for m=1, when the two initial-colour predicates coincide. Heading predicates are constant on each lane. Absolute-site constraints and linear coordinate congruences are integer linear equalities/disjunctions and congruences in n. Combine (5) over the finite stencil, then take the finite union of allowed clauses and lanes. This produces a concrete first-order Presburger formula `Hit(t)` including the equation `t=t_A+n l_A` and the path domain.

### Effective decision and exact least time, without expanding cycle counts

Presburger arithmetic with congruence predicates is decidable by constructive quantifier elimination; Cooper (1972), cited below, supplies an explicit procedure. Apply a fixed such procedure to `exists t>=0 Hit(t)`. If false, return none. If true, test `exists t<=B Hit(t)` for B=0,1,2,4,8,... until true, then binary-search the first valid B. The result is exactly the minimum hit time because these bounded-existence tests are monotone in B. This uses logarithmically many decision calls in the numerical first-hit time rather than enumerating its predecessors. Once time is known, lane equations provide the head and (3) can provide visit witnesses.

This is a fully effective subroutine, not an appeal to a termination oracle. One concrete implementation route for the fixed Presburger decision procedure is finite-word binary automata: linear equalities have finite carry automata; comparisons can be expressed by nonnegative slack variables; fixed congruences use finite remainders; conjunction/disjunction/complement and existential track projection are effective automata operations (with leading-zero padding closure); emptiness is finite graph reachability. Integers can be reduced to differences of nonnegative variables. Alternatively, use an explicit quantifier-elimination implementation in the expanded congruence language. The formula above has at most M existential lane tests per stencil site per head lane, plus an explicit finite table and defect disjunction. No polynomial complexity assertion is made; Boolean negation of (3), automata determinization and quantifier elimination may be expensive.

## 7. Effective eventual periodicity of finite head-relative observations

Assume the no-revisit branch and write its final tail as in the theorem. Fix phase i and offset f. Its observed site is

    y(n)=a_i+n delta+f.

Because delta is a background period, the background colour at y(n) is constant in n. Since delta is nonzero, y(n) meets each initial defect at most once and meets the finite pre-tail visited set at only finitely many n. These exceptions are effectively bounded from the compressed lanes, with no expansion:

Choose a coordinate q with delta_q nonzero. Compute the minimum m0 and maximum M0 of that coordinate over every bounded pre-tail lane and every defect. Each lane's extrema occur at its two endpoints. If there are no such points, set the exception threshold to zero. Otherwise, writing `z=(a_i+f)_q`, a sufficient exception threshold is

    max(0, floor((M0-z)/delta_q)+1)       if delta_q>0,
    max(0, floor((z-m0)/(-delta_q))+1)    if delta_q<0.

Beyond it, y(n) lies strictly beyond every relevant finite point in that coordinate.

For a visit belonging to the tail, equality with phase j, index k, is equivalent to

    a_j-a_i-f = d delta,   k=n-d,

for an integer d, necessarily unique when it exists. Its time is earlier precisely when

    j-i-dL < 0.

If this condition holds, the visit exists exactly when `n>=max(0,d)`; otherwise it never contributes. Thus each candidate tail visit is a threshold condition in n. Taking the maximum of the finitely many valid thresholds and finite-exception bounds makes every stencil colour constant within phase i. Taking the maximum over i and f gives an effective global N (an empty maximum is zero); the complete stencil and heading are L-periodic in absolute time from `T+NL` onward.

For a coordinate congruence `ell(p_t) == r mod q`, increasing n adds `ell(delta)`. Its period in n divides `q/gcd(q,ell(delta))`. The least common multiple over the finite requested congruences supplies a valid Q (the empty least common multiple is one). Hence a finite union of the requested clauses, without a bounded absolute-site restriction, is periodic from the computable transient with period LQ. A finite absolute-site restriction is eventually false because the head drifts; its additional exceptions can be bounded by the same coordinate argument. This is stronger than merely asserting eventual semilinearity.

## 8. Consequence for universality claims

Fixing a rule and periodic background only restricts the input family of this total theorem. Therefore no computable reduction of an undecidable language can map every input to a **globally one-visit** finite-defect run and characterize acceptance by one of the finite phase/heading/stencil predicates above: composing the reduction with this algorithm would decide that language. The class itself is decidable, so this statement does not hide an undecidable one-visit promise.

The complementary upper-side literature is Maldonado, Gajardo, Hellouin de Menibus and Moreira, *Nontrivial Turmites are Turing-universal*, arXiv:1702.05547. Their construction uses periodic backgrounds and finite perturbations, and their Section 5 explicitly states a global at-most-two-visits property. This is relevant evidence for an adjacent threshold. It does **not** itself supply the companion project's still-needed literal coordinate tile, finite input loader and correctly guarded accepting-port specification. In particular neither an ordinary ant stopping nor returning to one chosen absolute site follows automatically. The lower theorem aligns with finite unions of phase-addressed head ports plus optional exact colour stencils; the physical upper interface must independently establish an iff acceptance event in that class.

Targeted read-only literature/repository inspection found no exact first-revisit theorem in the inspected sources; this limited check establishes no novelty or priority claim. The existing repository's bounded-board history/MRDP machinery is a separate certificate layer and is not rederived here.

## 9. Independent review and executable checks

The mathematical reviewer independently checked the shadow argument, defect-event ownership, integer minimization cases, pattern formula, endpoint conventions and eventual periodicity. It supplied the permutation simplification and confirmed that the query domain includes the first repeated arrival but excludes later dynamics. Its complete review is in `review.md`. The targeted read-only source and repository check, including query scope and fetched content hashes, is in `source-audit.md`.

The original standard-library reference program is `one_visit.py`; `test_one_visit.py` exercises exact lane arithmetic against finite enumeration, complete small binary boards/rules, randomized multicolour boards and defects, independent evolving-board colour snapshots, unreachable defects, zero drift, defect/revisit ties and a far-away defect at `(10^100,10^100)`.

The implementation covers the accelerated first-repeat decision, compressed path evaluation, exact visited-before and colour-at-time queries. The general Presburger first-hit decision subroutine in Section 6 is specified and proved, **not implemented** in this reference program. The final test output and counts are recorded separately in `test-results.txt`; experimental tests supplement rather than prove the theorem.

## References

- Diego Maldonado, Anahí Gajardo, Benjamin Hellouin de Menibus, Andrés Moreira. *Nontrivial Turmites are Turing-universal*. https://arxiv.org/html/1702.05547 and https://arxiv.org/pdf/1702.05547. Theorems 2.1/3.1 and Section 5; accessed 2026-10-03.
- D. C. Cooper. *Theorem Proving in Arithmetic without Multiplication*. Machine Intelligence 7 (1972), pp. 91–99. Primary scan: https://www21.in.tum.de/teaching/logik/SS16/Exercises/Cooper.pdf. This is the algorithmic Presburger reference; Kracht's 2002 exposition was also inspected, but its bounded-interval display has typographical mistakes, so it is not used as an algorithm specification here.
- Project comparison targets: https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_ANT_CHECKERBOARD_HISTORY.md and https://github.com/VladimirReshetnikov/ProveIt/blob/main/Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_TOGGLE_ROUTER_UNIVERSALITY.md.
