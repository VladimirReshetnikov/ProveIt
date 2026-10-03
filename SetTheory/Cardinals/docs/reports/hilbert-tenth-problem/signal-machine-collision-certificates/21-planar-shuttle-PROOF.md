# A binary four-particle planar shuttle of radius at most six

Research successor packet, 3 October 2026. This is a standalone construction;
no earlier report or release is changed. No reversibility, least-radius,
least-mass, novelty, or global classification claim is made.

## 1. Definition and principal conclusions

Work on the binary full shift `{0,1}^{Z²}`. An occupied site carries exactly
one unit of mass. For a support `S⊆Z²`, join distinct occupied sites whenever
their Chebyshev (max-norm) distance is at most two. For every resulting connected
component that is a translate of one of the following four input shapes, apply
the indicated replacement. Every other component stays unchanged.

| Name | Input coordinates | Output coordinates |
|---|---|---|
| E | `(0,0),(1,0)` | `(1,0),(2,0)` |
| W | `(0,0),(2,0)` | `(-1,0),(1,0)` |
| R | `(0,0),(1,0),(3,0)` | `(-1,0),(1,0),(4,1)` |
| L | `(0,0),(2,0),(4,0)` | `(0,1),(3,1),(4,1)` |

The replacements use translates only. Reflections and rotations are not
implicitly included. Denote the map by `G`.

For every integer `k≥7`, start at

`S_0={(0,0),(3,0),(4,0),(k,0)}`.

**Theorem.** The map G is a well-defined binary, quiescent, translation-
equivariant CA of Chebyshev radius at most six. It conserves mass on every
finite input, including malformed inputs. Its specified orbit always has four
distinct occupied sites. Define `T_n=n²+(2k−11)n`. Then

`G^{T_n}(S_0)={(0,n),(3,n),(4,n),(k+n,n)}` for every `n≥0`.

The full set of distinct sites visited by that orbit is exactly

`V_k={(0,n):n≥0} ∪ {(x,n):n≥0, 2≤x≤k+n−2} ∪ {(k+n,n):n≥0}`.

Writing `C_G,k(N)=|V_k∩[-N,N]²|` for integer `N≥0`,

```
C_G,k(0) = 1,
C_G,k(N) = N(N+1)                              if 1≤N≤k−2,
C_G,k(N) = [N²+(2k−1)N−k²+3k−4]/2             if N≥k−1.
```

In particular, its sharp leading coefficient is `1/2`, and its generalized
inverse centered-box radius is `sqrt(2M)+O_k(1)`.

There is also an original-frame version `F=τ∘G`, where τ shifts every occupied
site up one row. This F likewise has radius at most six and conserves finite
mass. Its all-time distinct-site centered-box count satisfies the exact formula
in §8 and the asymptotic

`C_F,k(N)=4N−4sqrt(N)+O_k(1)`.

Consequently its generalized inverse is

`R_F,k(M)=M/4+sqrt(M/4)+O_k(1)`.

## 2. Unambiguous recognition, matching, and global mass conservation

Every input shape in the table is connected in the specified graph. An exact
translate of a shape has a unique anchor: its smallest x-coordinate and its
common y-coordinate. The two pair shapes differ in their gap, and the two
triples differ in their gap lists, so distinct rules never recognize the same
component. Larger components, nonhorizontal components, isolated sites, and
infinite components are unrecognized and freeze.

Within each primitive replacement, the following source-to-target matching is
a bijection, and every displacement has max norm at most one:

```
E: (0,0)→(1,0),  (1,0)→(2,0)
W: (0,0)→(-1,0), (2,0)→(1,0)
R: (0,0)→(-1,0), (1,0)→(1,0), (3,0)→(4,1)
L: (0,0)→(0,1),  (2,0)→(3,1), (4,0)→(4,1)
```

Use the identity matching on every unrecognized component. Two distinct input
components have all mutual distances at least three. If two matched outputs
from different components coincided, their respective sources would have
distance at most two by the triangle inequality, a contradiction. This also
covers collisions against unchanged sites of finite or infinite frozen
components. Outputs within one component are distinct by the displayed
matching. Thus all output sets are pairwise disjoint, and the combined
matching is a bijection from the old occupied sites to the new occupied sites.

In particular, every finite input has exactly the same number of particles
after one step. On infinite inputs the same construction is well-defined and
has a bounded-displacement bijection; no subtraction of infinite cardinalities
is used as a conservation argument. Distinct output components are allowed to
join after a step. The next step then recognizes or freezes the new components
in the usual way; this does not affect the current-step proof.

## 3. A genuinely local rule on the entire full shift

For an input shape A and anchor a, write `H(A+a)=A+a+[-2,2]²`. The predicate

`P_A,a(S): (S∩H(A+a))=A+a`

depends on finitely many bits. It is equivalent to saying that A+a is exactly
one occupied connected component: A+a is connected; if an occupied path left
it, the first new site would be in its radius-two halo. This equivalence works
equally well in infinite configurations. In particular, a fragment of a large
or infinite component can never be falsely rewritten merely because a local
window truncates the rest of that component.

To determine G(S) at z, consider only anchors for which z belongs to an input
or output shape of one of the four rules. These are finitely many anchors.
Check the corresponding predicates. If the old bit at z is zero, turn it on
exactly when an isolated primitive rewrite creates z. If the old bit is one,
turn it off exactly when its primitive rewrite removes z. Otherwise preserve
it. Unambiguous recognition and disjointness from §2 prove that this Boolean
rule agrees with the component definition on every full-shift input.

For every such candidate z and every p in its primitive input A+a,
`||p−z||∞≤4`. Therefore every halo bit needed to check P lies at distance at
most six from z. This proves the claimed radius bound. More precisely, the
changed-site recognition cylinders use the rectangle

`[-6,6]×[-3,2]`

relative to z, as all primitive inputs have y=0 and all outputs have y=0 or 1.
The unchanged central bit is in the same rectangle. This refinement is used
for F below.

The formulas commute with every integer translation. In the empty
configuration no recognition predicate can hold, so G fixes the vacuum. The
local expression is defined for all `2^169` radius-six neighborhoods; the
provided certificate gives its sixteen birth/removal cylinders instead of
attempting to enumerate that enormous truth table. The proof, not a finite
test sample, establishes agreement on the whole full shift.

## 4. Complete cycle description and timing

Suppose the n-th section holds, and set `d=k+n≥7`.
The east-moving pair travels along row n. At every relative time
`0≤j≤d−6`, the support is

`{(0,n),(3+j,n),(4+j,n),(d,n)}`.

For `j<d−6` the pair is an isolated E-component, separated by at least three
columns from both markers, and one E step increments j. At `j=d−6` the right
marker joins exactly the R-triple `{d−3,d−2,d}` on row n. The left marker is
still separated, since `d−3≥4`. One R step gives

`{(0,n),(d−4,n),(d−2,n),(d+1,n+1)}`.

The returning pair now has gap two. Crucially, the newly lifted marker is
three columns beyond its rightmost member: `(d+1)−(d−2)=3`. Its row difference
one does not reduce the max-norm distance. Therefore it is a separate
component; the horizontal separation only increases during the return.

After `q` W steps, for `0≤q≤d−6`, the support is

`{(0,n),(d−4−q,n),(d−2−q,n),(d+1,n+1)}`.

For `q<d−6` the leftmost pair site is at least three, so the left marker is
separate and W applies. At `q=d−6` the lower component is exactly the L-triple
`{0,2,4}`. Its separation from the upper marker is at least `d−3≥4`. One L
step gives the next section

`{(0,n+1),(3,n+1),(4,n+1),(d+1,n+1)}`.

Thus a cycle uses `(d−6)+1+(d−6)+1=2d−10` steps. Summing these lengths yields

`T_n=Σ_{i=0}^{n−1}(2(k+i)−10)=n²+(2k−11)n`.

These phase descriptions are inclusive at their pre-bounce endpoints and
exclusive of the next section. In particular they also cover the shortest
case k=7 without empty or ambiguous bounce intervals.

## 5. Exact visited set and first arrivals

On row n the moving pair visits every integer from 2 through d−2, where
`d=k+n`. The east phase visits `[3,d−2]`; the west phase additionally visits
2 and never visits 1. The left marker visits 0 and the right marker visits d.
The right marker on this row may appear before the n-th section, but no other
extra sites appear. Later cycles only use higher rows. This proves the exact
set V_k in §1.

The full wedge `{(x,n):n≥0,0≤x≤k+n}` therefore has exactly two missing families:
`x=1` on every row and `x=k+n−1` on every row. It would be incorrect to count
the full wedge without removing both.

For n≥1, the exact first-arrival time at each visited site on row n is

```
x=0,3,4:             T_n
x=2:                 T_n+2(k+n)−11
5≤x≤k+n−2:           T_n+x−4
x=k+n:               T_n−(k+n−6).
```

For row zero the same formulas hold except that the right marker x=k arrives
at time zero. All other sites are never visited. The formulas partition the
visited row into disjoint branches, including k=7. The last branch follows
from the preceding R transition at `T_{n−1}+(k+n)−6`; since
`T_n−T_{n−1}=2(k+n)−12`, this equals the displayed expression. The interior
first-arrival times follow from the leading east-moving member, except x=2,
which is first reached in the last pre-L return state. These give explicit
piecewise-quadratic first-arrival data without importing any normal-form or
certificate compiler theorem.

## 6. Exact stationary-frame centered-box count

All visited coordinates are nonnegative. For `1≤N≤k−2`, each of the N+1
included rows contributes exactly N sites in `[0,N]`: x=0 and x=2 through N.
At N=0 only the origin contributes. For N≥k, first count the entire wedge:

`(N+1)²−(N−k)(N−k+1)/2`.

Then subtract the N+1 sites with x=1 and the N−k+2 sites on
`x=k+n−1`. The result is

`[N²+(2k−1)N−k²+3k−4]/2`.

At the remaining boundary N=k−1 the complete square loses its N+1 sites at
x=1 and one upper-edge hole, giving `N(N+1)−1`, which agrees with the same
quadratic. This proves the complete piecewise count.

If `M>(k−2)(k−1)`, its exact generalized inverse is

`R_G,k(M)=ceil((sqrt(8M+8k²−16k+17)−(2k−1))/2)`.

The threshold ensures this inverse lies in the quadratic branch. Consequently
`R_G,k(M)=sqrt(2M)−k+1/2+O_k(1)`; the O(1) includes unavoidable integer rounding.

## 7. The original-frame vertical drift and its four disjoint traces

Let τ translate by `(0,1)` and define `F=τ∘G`. Translation equivariance gives
`F^t(S_0)=τ^t(G^t(S_0))`. Translation preserves finite mass and quiescence.
To evaluate F at z, evaluate G one row below z; the precise read rectangle
from §3 becomes `[-6,6]×[-4,1]`. Hence F, too, has Chebyshev radius at most six.

Let n(t) be the unique integer with `T_n≤t<T_{n+1}`. Call the left marker and
the two matched moving particles the three bulk trajectories. Their F-height
is `h(t)=t+n(t)`. The right marker has G-row r(t) in `{n(t),n(t)+1}`, so its
F-site is `(k+r(t),v(t))`, where `v(t)=t+r(t)`. Both height functions are
strictly increasing. The bulk share h and have different x-coordinates at
each time, so their traces are pairwise disjoint and have no self-repetitions.

The marker never intersects a bulk trace either. If its site at time t equals
a bulk site at time u, set `r=r(t)` and `n=n(u)`. Every bulk x is at most
`k+n−2`; equality of x therefore gives `n≥r+2`. Equality of heights gives
`u=t+r−n≤t−2`. But monotonicity implies `n(u)≤n(t)≤r(t)=r`, a contradiction.
Thus every time step contributes four genuinely new distinct visited sites,
although their entry into a centered spatial box is not synchronous.

Each bulk trajectory visits every nonnegative height except its upward-jump
skip levels

`a_n=T_n+n−1=n²+(2k−10)n−1`, `n≥1`.

The right marker rises into row n+1 at time `ρ_n=T_n+k+n−5`. It skips precisely

`b_n=ρ_n+n=n²+(2k−9)n+k−5`, `n≥0`.

Both sequences are strictly increasing. They interlace: `b_0<a_1`, and
`a_n<b_n<a_{n+1}` for n≥1, since the successive differences are `n+k−4`
and `n+k−5`. Thus no bulk skip level is a marker skip level.

## 8. Exact drifted centered counts and the square-root correction

Every F-visited site `(x,y)` satisfies `x≤max(k+1,y)`.
For bulk sites in rounds n=0 or 1, `x≤k+n−2≤k−1`. For n≥2,
`T_n≥T_2=4k−18≥k−2`, so `x≤k+n−2≤T_n+n≤y`. For the right marker with row
r≤1, `x=k+r≤k+1`. For r≥2 its first time is
`ρ_{r−1}=T_{r−1}+k+r−6`, and

`y−x≥T_{r−1}+r−6≥T_1−4=2k−14≥0`.

It follows that for every integer `N≥k+1`, horizontal truncation is inactive
among sites of height at most N. The initial transient cannot be omitted:
the first lifted marker is at x=k+1, so the weaker cutoff N≥k would fail.

Define

`A_k(N)=#{n≥1:a_n≤N}`, `B_k(N)=#{n≥0:b_n≤N}`.

The disjoint-trace and skipped-height proofs give the exact count

`C_F,k(N)=4(N+1)−3A_k(N)−B_k(N)` for N≥k+1.

With `α=2k−10`, `β=2k−9`, these are explicitly

```
A_k(N)=floor((sqrt(α²+4(N+1))−α)/2),
B_k(N)=1+floor((sqrt(β²+4(N−k+5))−β)/2).
```

The stated cutoff makes both expressions nonnegative. The implementation uses
integer square roots, so it introduces no floating-point ambiguity at exact
squares. Each count is `sqrt(N)+O_k(1)`, proving

`C_F,k(N)=4N−4sqrt(N)+O_k(1)`.

For the generalized inverse `R_F,k(M)=min{N≥0:C_F,k(N)≥M}`, put
`m=M/4` and `u=m+sqrt(m)`. Then `u−sqrt(u)=m+O(1)`, and integer rounding
changes the asymptotic count by O_k(1). Beyond the transient, each integer
increment of N adds between one and four sites, since a_n and b_n never
coincide. Therefore an O_k(1) counting discrepancy requires only O_k(1)
additional radius, establishing

`R_F,k(M)=M/4+sqrt(M/4)+O_k(1)`.

## 9. Executable evidence and its limits

`code/component_rule.py` is a direct connected-component simulator.
`code/local_rule.py` is a separate pointwise evaluator: it imports neither
the component simulator nor its rule dictionary, and recognizes independently
encoded occupied/empty cylinders. It supplies radius-six evaluators for both
G and F. `local-rule-certificate.json` exports all exact integer bitmasks.

`code/check_shuttle.py` uses explicit exception checks, so its tests remain
active under Python -O. It covers every support in a 4×3 planar rectangle,
every support in a 13-site line, random full local contexts with arbitrary
exterior data, one-site halo perturbations, unions of active/malformed
templates, a full-radius search for unwanted births, large translations,
complete orbit phases, exact first arrivals, both centered counts, trace
disjointness, and integer-root boundary cases. The normal and optimized runs
must produce identical receipts and local certificates.

Independent proofs and independently written executable checks are retained
under `audit/`. None of these finite checks purports to enumerate all full-
shift inputs or all radius-six windows; §§2–3 give the all-input argument.
The complete construction is binary, uses mass exactly four on the specified
orbit, and needs neither weighted particles nor an implicit orientation tag.
