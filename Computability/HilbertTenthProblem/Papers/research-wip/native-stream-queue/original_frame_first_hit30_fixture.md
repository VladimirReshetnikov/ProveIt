# One complete original-frame first-hit quartic: the expanding planar shuttle

For one explicit mass-four orbit, the final source is a complete
**35-operation quartic with three natural witnesses and eight squared rows**.
It is obtained from seven fully paid comparison sources: generic square-lift,
shared-cycle, and direct common-quadratic clocks; their phase-coordinate
projections; and a unified-domain direct clock. These are specified schedules,
not an optimality assertion or a uniform compiler bound. This fixed-input
example belongs to the decidable mass-four class, not a Turing-complete substrate.

The [helper](original_frame_first_hit30_fixture.py) and
[receipt](original_frame_first_hit30_fixture.json) contain all seven complete
source arrays, coefficient checks, and 616 complete natural zero tuples. No
archived or predecessor Python was imported or executed. No general
CA-to-normal-form compiler or Presburger elimination engine was implemented.

## 1. Timed dependency audit and provenance

This continues the scoped
[Report30 intake](review_original_frame_first_hit30_intake.md), whose earlier
unreviewed timed dependency is now read in full. The timed proof's conditional
arithmetic argument passes the following independent check:

- Positive cycle lengths give disjoint half-open cycle and transition intervals.
  Flight charts exclude contact; local-prefix or next-transition charts own it.
  A shared synchronized clock handles multiple terminal objects. No independent
  clocks introduce multiplicity.
- Original-frame drift cancels from pairwise position differences. Permutation
  and first-differing-coordinate refinements therefore have affine domains.
  Distinct occupied sites have a unique sorted order even with repeated labels.
- `Lift_i(f)=f(z_i)−f(0)+f(0)e_i` gates only the literal constant, leaving residual
  degree at most two. At a natural zero, one selector is active; inactive gates
  force every private parameter and slack to zero because they are natural.
  Pooled outputs require one common denominator per coordinate. These facts
  prove the claimed canonical fibers, conditional on the input chart theorem.
- Padded unoccupied coordinate slots are literal zero, without adding drift.
  Canonical signed external encodings require their complementarity equations.
  Translated-pattern tie breaking selects one successful placement; an all-zero
  pattern does not have a purported least translation.

No gap was found in these points or the recurrence limitation. The general
orbit normal form remains an inherited dynamical hypothesis. Its input-dependent
materialized prefix and chart counts remain unbounded over inputs. Witness and
squared-row counts in that theorem are not paid arithmetic counts.

The helper authenticates the following unchanged repository bytes. The four
proof files lie under
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/`.
The timed proof, original-frame proof, and first-visit proof were read completely;
the geometry proof was read through its explicit example and original-frame
sections, with the four-rule construction in §6 checked directly.

| File | SHA256 |
|---|---|
| `19-mass-four-zd-timed-PROOF.md` | `103fe38f7c6d941995e579d7d73dd42ab3836a012666ba16858b158ff698d4c5` |
| `20-orbit-geometry-original-frame-PROOF.md` | `385c455537ee7c4631fd5400918b57602bc08c26383fe71f99b3345791964a8f` |
| `20-orbit-geometry-first-visit-PROOF.md` | `3247951ca7afa4d65bd3eb90d99bfb48fcb43dbf0eaa067c3e9380cdfbcebbda` |
| `20-orbit-geometry-geometry-PROOF.md` | `3f05b484cd3c0035422df431f571bb2b56c85a31d5f49ae681033ffb2ca6e4fa` |
| `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_original_frame_first_hit30_intake.md` | `96d0e1fef873ea4d2ef8fcf8139fb047a52b4535786e7860183de882b27c33a6` |

## 2. Actual fixed orbit and external interface

Use geometry §6's alphabet `0,u,E,W`, of weights 0,1,2,2. In its stationary-unit
frame G, an isolated E head moves right through vacuum, reflects as W against a
unit and moves that unit one step right and up; W moves left through vacuum and
reflects against the left unit by moving itself and that unit up. The printed
vacancy guards are retained. Head isolation at distance four makes simultaneous
rewrite supports disjoint; each rewrite preserves its written mass. Thus the
printed radius-six rule is conservative on all finite configurations. The
fixture always has exactly one head, so its isolation guard always holds.

Set **F=vertical_shift composed with G**, and start with u at (0,0) and (3,0), E
at (1,0). This is a nonzero original-frame drift, not a stationary-frame target
silently renamed. At cycle n≥0 put T(n)=n²+3n. For 0≤j≤n+1 the complete support
and labels are:

| Phase | Time | Sorted occupied sites and labels |
|---|---|---|
| E | T(n)+j | u:(0,n+t), E:(1+j,n+t), u:(n+3,n+t) |
| W | T(n)+n+2+j | u:(0,n+t), W:(n+2−j,n+t), u:(n+4,n+1+t) |

The E interval is `[n²+3n,n²+4n+1]`; the following W interval ends at
`n²+5n+3`, immediately before T(n+1). They partition all natural times. The last
state of each phase is the state before its reflection; the next phase owns the
post-reflection state. These explicit charts combine any equal-form flight and
local-prefix states, rather than claiming to reproduce a generic compiler's
raw phase subdivision.

The seven signed external inputs are `(Lx,Ly,Hx,Hy,Rx,Ry,phase)`. They denote
exactly three occupied sites, with unit labels first and last; phase=0 denotes E
and phase=1 denotes W. The phase field is not a vacuum symbol code. Every other
site is vacuum. No variable site-count or padding field is needed for this
particular orbit. The inequalities below imply strict x ordering, hence also
lexicographic ordering.

For a given complete target, phase determines the head state, and
`n=Rx−3−phase`; Hx then determines j. Therefore a reachable complete target has
exactly one occurrence. Its clock witness is automatically the first-hit time.
This direct injectivity proof needs no general normal-form algorithm. It does
not concern a single site, finite window, or configurations up to translation.

## 3. Identical membership constraints in the first three sources

Take eight common natural witnesses

```
e, sEn, sEj, sEk, sWn, sWj, sWk, t.
```

Let f=1−e, a=Rx−4, b=Rx−3, h=Hx−1,
`v=Rx−Hx−1`, and `n0=a+e`. The twelve common residuals are

```
B=e(e−1);
e*b−sEn; e*h−sEj; e*v−sEk;
f*a−sWn; f*(v−1)−sWj; f*h−sWk;
Lx; Hy−Ly; Ly−t−n0; Ry−Ly−f; phase−f.
```

Their sum of squares is the membership part of each full polynomial. At a
natural zero B forces e∈{0,1}. For E, the three active slacks enforce
`n=Rx−3≥0, j=Hx−1≥0, n+1−j≥0`. For W they enforce
`n=Rx−4≥0, j=Rx−Hx−2≥0, n+1−j≥0`. Every inactive slack is uniquely zero.
The five common equalities are exactly the displayed original-frame geometry
and head label. Thus n0 is nonnegative on every accepted natural tuple, although
it need not be nonnegative on arbitrary off-zero signed inputs.

This uses the two-selector elimination already allowed by the timed proof:
replace the second selector by 1−e and retain Booleanity. Equalities valid on
both phases are shared explicitly. These manually derived cells require no
unexecuted quantifier elimination.

## 4. Three complete clocks and exact relationships

Both phases have the same quadratic part:

```
E: t=Rx²−3Rx+Hx−1;
W: t=Rx²−3Rx−Hx.
```

Define the direct residual

```
C=t−Rx*(Rx−3)−(2e−1)*Hx+e.
```

It has ordinary total degree two even when e is a witness. The direct polynomial
is the membership sum plus C². No clock lift is required for this fixture.

The generic-square source adds a natural U and residuals

```
J=U−Rx²;
C_generic=t−U+3Rx−(2e−1)*Hx+e=C−J.
```

Only one square lift is needed: no other quadratic coordinate product occurs.
Using the general upper bound of 21 lifts for seven external fields would be an
artificial baseline. The exact full-polynomial correction is

```
P_generic−P_direct=2J²−2CJ.
```

In particular U=Rx² gives an unconditional polynomial pullback. On integers U is
natural, and this gives a bijection of the full natural zero tuples.

The shared-cycle source instead adds natural N and residuals

```
L=N−n0;
C_cycle=t−N²−3N−[e*(Hx−1)+(1−e)*(2Rx−4−Hx)].
```

The bracketed offsets are the exact E and W within-cycle offsets. Put
`Delta=B+L*(N+n0+3)`. Algebra gives `C_cycle=C−Delta`, so

```
P_cycle−P_direct=L²+Delta²−2C*Delta.
```

Substituting N=n0 leaves `B²−2CB`, not identically zero. Only after the retained
Boolean equation is used do the clocks agree. Natural zeros nevertheless
correspond bijectively: the membership inequalities establish n0≥0, and L fixes
N uniquely. No unconditional nonnegative restoration is claimed off zeros.

## 5. Exact phase-coordinate projection

The external phase field already determines e. In each of the first three
sources substitute `e=1−phase`, alias f to phase, and delete the now-zero
`phase−f` residual. The retained Boolean square validates phase∈{0,1}; its
binary value is not assumed at the interface. Thus restored e is natural at
all child natural zeros, and full zero tuples correspond bijectively.

The child complete polynomial is exactly the parent's graph substitution, over
all values. Replacing the old `1−e` gate by `1−phase` costs the same one
subtraction. Removing the comparison producer, its square, and its joining
addition saves 1M+2A and one witness in each case. All other residuals are kept.

## 6. Unified-domain direct clock with three witnesses

Write p=phase, e=1−p, and `n0=Rx−3−p`. Keep only natural witnesses j,r,t and
use these eight residuals:

```
p*(1−p);
Hx−1−j;
Rx−Hx−1−p−r;
Lx;
Hy−Ly;
Ly−t−n0;
Ry−Ly−p;
C=t−Rx*(Rx−3)−(1−2p)*Hx+(1−p).
```

At a natural zero p∈{0,1}. The two slacks give
`j+r=n0+1`, so n0≥−1. If n0=−1, naturalness forces j=r=0;
then Hx=1 and Rx=2+p. The clock forces t=−2 when p=0 and t=−1 when p=1,
contradicting natural t. Therefore **n0≥0** without a separate cycle-index slack.
This exclusion is particular to this clock and these domains.

For p=0, the old E parameters are n=n0 and within-phase index j; for p=1,
the old W parameters are n=n0 and within-phase index r. In either case the
other slack is n+1 minus that index. The old six branch slacks restore as

```
sEn=e*n0, sEj=e*j, sEk=e*r,
sWn=p*n0, sWj=p*r, sWk=p*j.
```

They are natural, and they restore every old membership and clock equation.
Conversely every original natural zero supplies these unique j and r. Thus
this further reduction preserves the complete external target relation and
its singleton natural fibers. It is a zero-set equivalence, not an assertion
that the unified polynomial equals the old one on arbitrary tuples.

The receipt includes two complete signed boundary zeros at n0=−1. They have
`(Hx,Rx,t)=(1,2,−2)` or `(1,3,−1)` and satisfy all eight rows, illustrating
exactly why the natural-time hypothesis is necessary. At natural t=0 with the
spatial equalities adjusted, the output is respectively 4 or 1.

## 7. Complete paid sources

The first three sources share a 28-gate membership prefix; their projected
versions share the corresponding 27-gate prefix. Nonunit constant
multiplication is paid. The signed-head coefficient uses e−f, reusing the
already available f rather than paying two additions to form 2e−1. The
unified source analogously uses e−p. Only exact constant, zero, and unit folds
occur. There is no automatic CSE or uncharged pruning. Every supplied port and
gate is live. Every residual is squared, and R squares require R−1 final
additions.

| Complete schedule | M | A | Total | Natural witnesses | Squared rows |
|---|---:|---:|---:|---:|---:|
| One generic square lift | 24 | 40 | 64 | 9 | 14 |
| One shared cycle | 24 | 42 | 66 | 9 | 14 |
| Direct common quadratic | 22 | 37 | 59 | 8 | 13 |
| Phase-projected generic lift | 23 | 38 | 61 | 8 | 13 |
| Phase-projected shared cycle | 23 | 40 | 63 | 8 | 13 |
| Phase-projected direct clock | 21 | 35 | 56 | 7 | 12 |
| Unified direct clock | 11 | 24 | **35** | **3** | **8** |

The unified source's 20 arithmetic gates precede its fully paid 15-operation
finalizer. The direct clock saves 2M+3A versus the declared sufficient
one-square generic clock. The shared-cycle clock costs two more additions
than the generic clock here; its dimension-independent witness advantage in
other settings does not force an improvement in this fixture.

All seven complete polynomials have degree **exactly four**. The original
three have coefficient `[e^4]=1`; the projected and unified sources have
`[phase^4]=1`. Their numbers of collected monomials are respectively
76,84,73,73,79,69,47. These degrees include all external and witness
coordinates; no zero-only substitutions are used.

## 8. Independent checks and limits

A separate sparse reference expands every residual from mathematical formulas;
it does not evaluate the source emitter's expression objects. The helper
compares all 87 residuals and all seven entire output polynomials. It also
checks both full clock corrections, the generic unconditional pullback, the
Boolean-qualified cycle pullback, and all three entire phase-coordinate
substitutions. All 404 paid gates are checked for closure and liveness, and
all seven complete finalizers are charged.

A separately written single-head transition stepper applies the four literal
rules and then the vertical shift. It agrees with the charts on all 88
consecutive times in the first eight cycles and on the next section. These
actual configurations yield 616 complete natural zeros, including phase ends,
both reflections, and cycle starts. The unified witness restoration is also
checked exactly against every original six-slack tuple. Another 84 off-zero
output checks include 28 rational assignments. These bounded tests supplement
the exact identities and the all-n,j induction; they do not replace those proofs.

The helper authenticates placed proof bytes only. It neither executes previous
scripts nor validates an arbitrary CA/profile input. Real SOS nonnegativity is
not a real-witness uniqueness theorem. No global coefficient-optimality,
universal-operation, fixed-arity-over-input, or asymptotic bit-complexity claim
is made. The domain reductions were supplied by root and checked against the
literal source and full equations here; they are not generic chart-compiler
optimizations.

Replay from `/`:

```sh
python3 /tmp/original_frame_first_hit30_fixture.py --repo /home/codex/.codex/worktrees/2a71/Proofs --expect /tmp/original_frame_first_hit30_fixture.json
python3 -O /tmp/original_frame_first_hit30_fixture.py --repo /home/codex/.codex/worktrees/2a71/Proofs --expect /tmp/original_frame_first_hit30_fixture.json
```

The exact typed receipt includes the helper's own SHA256. All checks use explicit
exceptions. Fresh normal and optimized exact-receipt replays from `/` both passed.
