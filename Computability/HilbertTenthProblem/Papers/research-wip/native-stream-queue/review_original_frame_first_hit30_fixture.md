# Independent review: a 35-operation first-hit quartic for one explicit orbit

The [author packet](original_frame_first_hit30_fixture.md) passes the scoped
mathematical and full-source review below. Its smallest saved polynomial has
**35=11M+24A operations, three natural witnesses and exact degree four**.
It represents complete positioned configurations of one specified expanding
mass-four cellular-automaton orbit, with a unique first-hit time. It supplies
no new universal bound; the established universal polynomial remains84.

The [independent checker](review_original_frame_first_hit30_fixture.py) reads
the frozen author trio and four placed proof files and the prior intake as authenticated data.
It imports or executes no author, archived or predecessor Python. The
[receipt](review_original_frame_first_hit30_fixture.json) records independent
expansion of all seven complete sources, all404 live gates, every one of the87
residuals, five whole-polynomial identities, and616 genuine zero checks at88
successive configurations. The seven arrays represent seven implementations
of the same fixed orbit, not seven independent physical examples.

## Proof and physical scope

The full timed dependency `19-mass-four-zd-timed-PROOF.md` was read. Its
half-open chart ownership, common clock, first-difference sorting, constant
term lifts, pooled denominators, inactive natural-coordinate uniqueness,
and original-frame padding are sound as conditional statements. The general
normal-form hypothesis remains inherited; finite arithmetic checks do not
prove that hypothesis or implement an arbitrary CA-to-chart compiler.

For the concrete example, the four printed local rewrites in the geometry
proof's Section6 give an independent direct argument. A mass-two E/W head
shuttles between two identical mass-one markers. Eligibility keeps writes of
different heads disjoint; on this one-head orbit eligibility is automatic.
The root read the complete Section6 and the drift formulas in Section8.
The checker separately implements this three-position dynamics and applies
one vertical shift at each time. All88 successive states and the owned start
of cycle8 match the saved complete targets, labels and time witnesses.

For cycle n≥0, each of its two phases has local index 0≤a≤n+1. Writing b=0
for E and b=1 for W, the original-frame configurations are

    E: t=n²+3n+a,       L=(0,n+t), H=(1+a,n+t), R=(n+3,n+t);
    W: t=n²+4n+2+a,     L=(0,n+t), H=(n+2−a,n+t), R=(n+4,n+t+1).

The fixed labels are u, E/W, u in strict x order. The intervals partition
all natural times. A complete target determines b, then n=Rx−3−b, then its
local index, and therefore t. Thus it occurs at most once and the witness
time is its first hit. This proof concerns complete targets, not site visits,
partial patterns, or configurations modulo translation.

## The smallest certificate and its natural-domain argument

The external integer fields are Lx,Ly,Hx,Hy,Rx,Ry,b. Its natural witnesses
are j,r,t. Define the paid quantities

    e=1−b, n=Rx−3−b,
    C=t−Rx(Rx−3)−(e−b)Hx+e.

The polynomial is the sum of the squares of these eight residuals:

    b(1−b), Hx−1−j, Rx−Hx−1−b−r, Lx,
    Hy−Ly, Ly−t−n, Ry−Ly−b, C.

At a natural zero, the Boolean residual forces b=0 or1. The two inequality
slacks give j+r=n+1, so integral n≥−1. If n=−1, then j=r=0 and Hx=1,
Rx=2+b. The clock residual would force t=−2 when b=0 and t=−1 when b=1,
contradicting t≥0. Hence n≥0. In phase E the local index is j; in phase W
it is r. The other slack proves its upper bound n+1. The geometric residuals
and clock then recover precisely the displayed physical state.

Conversely each actual state supplies the unique j=Hx−1, r=Rx−Hx−1−b
and actual t. Every witness is natural. Both maps preserve every external
coordinate, and all discarded branch slacks are restored uniquely as

    (sEn,sEj,sEk,sWn,sWj,sWk)=(en,ej,er,bn,br,bj).

The sign/domain step precedes this restoration. Without nonnegative time,
the two n=−1 points really are full signed zeros; both are checked explicitly.
No inequality, first-time minimization or label-validity test is assumed free.

## Complete arithmetic comparison

| Saved implementation | M | A | Total | Natural witnesses | Squared residuals |
|---|---:|---:|---:|---:|---:|
| One-square clock lift |24|40|64|9|14|
| Shared cycle witness |24|42|66|9|14|
| Common quadratic clock |22|37|59|8|13|
| One-square lift, external phase projection |23|38|61|8|13|
| Shared cycle, external phase projection |23|40|63|8|13|
| Common quadratic, external phase projection |21|35|56|7|12|
| Unified inequalities and natural time |11|24|35|3|8|

All columns are independently recounted from the full arrays, including
nonunit fixed-coefficient multiplications, every square, and all final joins.
Every supplied port and emitted gate reaches the output. The comparison
uses the one square actually needed here; it does not inflate the generic
baseline to a formal bound for arbitrary seven-dimensional outputs.

The first improvement uses the common quadratic part of both phase clocks.
The external phase projection computes e=1−b and deletes its now-zero label
residual; the retained Boolean equation validates the external label. The
last improvement replaces the six separately gated inequalities by the two
unified slacks, with the natural-time argument above recovering n≥0.

For the unprojected sources put B=e(e−1), n0=Rx−4+e and let C be the direct
clock residual. If J=U−Rx², the full lifted polynomial minus the direct one
is exactly 2J²−2CJ. For L=N−n0 and D=B+L(N+n0+3), the cycle polynomial
minus the direct one is L²+D²−2CD. These two identities include their full
SOS finalizers. Each of the three external-phase substitutions is also a
whole-polynomial identity. The unified polynomial instead has the proved
natural-zero bijection; equality off zeros is not claimed.

The review uses an exponent-vector polynomial ring, independently forms
all original residuals, and compares all collected coefficients. It proves
exact degree four in each source and checks the saved coefficient hashes.
The unified source has47 collected monomials; its b⁴ coefficient is1.
Its low degree and arity belong to this fixed, explicitly classified orbit.
They do not encode an arbitrary ordinary-input computation.

Fresh normal and optimized exact-receipt replays from `/` pass for author
and reviewer. The fixed-input semantic proof is mathematical; the88 physical
states supplement it and are not presented as an exhaustive dynamics proof.

    python3 review_original_frame_first_hit30_fixture.py --root /path/to/author-trio --repo /path/to/Proofs --expect review_original_frame_first_hit30_fixture.json
    python3 -O review_original_frame_first_hit30_fixture.py --root /path/to/author-trio --repo /path/to/Proofs --expect review_original_frame_first_hit30_fixture.json
