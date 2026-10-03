# A fixed binary five-particle counter-machine compiler

This is a mathematical construction with executable regression checks, not a
machine-checked proof. No priority or new-record claim is made. It is independent
of the reported 2016 five-numerical-particle construction: the latter's full paper
has not been located in this research.

## 1. Exact domain and finite data

The source is a finite deterministic machine on two natural counters. Its
nonhalting rows are ADD j q', SUB j q_pos q_zero, and optionally NOP q'. ADD
increments; SUB decrements and takes q_pos when positive, otherwise leaves zero
unchanged and takes q_zero. A distinguished halt state has no outgoing row.

Let m be the number of controls including halt, and p the number of ADD/SUB
controls. Number all controls in lexicographic order, placing halt last. Assign
distinct packet-gap codes in the order H_q (all m controls), O_q (p moving
controls), I_q (the same p controls). The gaps are precisely 1,...,D, where

    D=m+2p, C=D+1, E=2D+2, K=4D+5=2E+1, Z=4K,
    R=Z+3K+E=30D+37.

The target alphabet is exactly {0,1}; numerical state is mass. Every valid
configuration has exactly five occupied sites. In source configuration (q,a,b),
the occupied coordinates are

    {-(Z+a), 0, Z+b, C, C+d(H_q)}.

The first three positions are left endpoint, origin and right endpoint. Those
names describe the valid-encoding invariant, not extra labels in the CA.
All other sites are exactly zero. Translating this set translates its entire
future. The input conversion is computable on finite natural-counter inputs.
No promise about polynomial-time conversion from an arbitrary TM encoding is
needed or made.

## 2. Complete component rule, including malformed configurations

In any binary configuration, join consecutive occupied sites when their distance
is at most K. Freeze each component except for the listed rules below. In
particular, components of sizes 0, 1, or at least 4 never change. Infinite
components also remain unchanged. A finite three-particle component is eligible
only if exactly one of its two adjacent gaps is at most D and the other gap a
lies in [C,K]. Its close pair is the packet; its remaining singleton is the
marker. These are unique because C>D. All unlisted eligible cases also freeze.

For a moving control q operating on j, let s=-1 for the left counter and s=+1
for the right counter. O_q moves in direction s; I_q moves in direction -s.

1. A two-particle component with gap d(O_q) or d(I_q) translates one site in
   its direction. A two-particle H_q component freezes.
2. A three-particle travel component whose marker lies behind its direction
   translates its two packet particles one site in that direction and fixes
   the marker. This rule is used for every a in [C,K]. A marker ahead triggers
   an arrival only when a=K; all smaller forward gaps freeze.
3. A home component is exactly {o,o+C,o+C+d(H_q)}. For ADD, replace the pair
   by {o+sC,o+s(C+d(O_q))}. For SUB, read the single contextual bit at o+sZ.
   If it is one, replace the pair by the home pair for q_zero. If it is zero,
   launch O_q as for ADD. A NOP changes to the successor home pair. Halt fixes
   the component. These reads never modify the sensed particle.
4. On an O_q arrival, let o be the contacted marker, and let Delta be +1 for
   ADD and -1 for SUB. Move the marker to o'=o+s Delta and place the I_q pair
   at {o'-sC,o'-s(C+d(I_q))}. Thus the packet reverses on the inner side.
5. On an I_q arrival, retain its marker o and place the home pair for q_pos
   (the ADD successor or positive SUB successor) at
   {o+C,o+C+d(H_qpos)}. This may pass across the marker.

These rules have no priority conflict: pair and triple sizes differ, gap codes
separate H/O/I, marker-ahead and marker-behind are exclusive, and the two home
SUB alternatives have complementary read guards. Hence they specify a unique
successor on every binary configuration, without input promises.

## 3. Global conservation and locality

Every listed rewrite preserves the component cardinality. Each output is inside
its old component hull enlarged by E on both sides:

- translations enlarge by at most 1
- a changed endpoint enlarges by at most 1, and its new inner pair remains
  inside the old hull since K exceeds both C+D and C+2D+1
- a home dispatch or origin crossing enlarges by at most C+D=2D+1<E
- changing a home gap enlarges by at most D

Distinct components are separated by more than K>2E. Their enlarged hulls are
therefore disjoint, including frozen components. No two outputs collide and no
output overwrites another component's retained particles. Summing cardinalities
proves numerical conservation on EVERY finite-support binary configuration,
including dense, ambiguous, multiple-head, and false-zero-sensor inputs.
Complementary or inaccurate contextual sensor values only select one of two
equal-cardinality bounded-write outputs, so they cannot impair this argument.

The component rule is a finite-radius CA. For an output at coordinate i from
an active component, the distance from i to its old hull is at most E and
that hull has diameter at most 2K.
Thus all its particles lie within E+2K of i, and its K-neighbor boundary guards
lie within E+3K. Its possible contextual read lies within E+2K+Z. Both bounds
are at most R=E+3K+Z. Conversely, a component of at least four particles that
contains a relevant input site reveals four connected particles within 3K;
it cannot be mistaken for an eligible component by truncating at radius R.
Components near the truncation boundary cannot write at i. Therefore applying
the component procedure to the exact radius-R word and reading its center gives
the same output as on the full configuration. This is `BinaryCA.local`.
The rule is time-independent and translation-equivariant; the all-zero word
maps to zero. The binary truth table has 2^(2R+1) entries, specified by this
finite algorithm rather than expanded as an astronomical bit string.

For a stronger full-shift transport statement, match old and new particles
in sorted order within each rewritten component, and use the identity match
on every frozen component. The disjoint-hull argument makes this a global
particle bijection, translation-equivariant and of displacement at most
2K+E. On a periodic configuration this transport induces a bijection on
occupied-site orbits modulo the period, proving per-period conservation too.
The finite-support conservation claim used by the theorem needs no periodic
input assumption.

## 4. All-input simulation invariant

At every source boundary the encoding in Section 1 holds. The marker spacing
is at least Z. During travel the packet gap is at most D. A packet could join
two distinct markers only if their separation were at most 2K+D, but Z=4K
exceeds that bound. Consequently every active valid component has two or
three particles and every other component is an isolated marker.

At home the contextual sensor o+sZ equals one exactly when the selected
counter is zero: its outer marker is at o+s(Z+c), the other outer marker is
on the opposite side, and the packet is within C+D<Z of the origin.
The marker is therefore never decremented below the buffer. Every nonzero
excursion starts at packet-marker gap C. Unit translations increase this gap
until separation and then decrease the gap to the target marker. Integer motion
hits exactly K; it never crosses an unobserved encounter. The O/I direction
and unique gap code determine which marker's role is being processed, even
though the particles are unlabeled. Endpoint reversal preserves marker order,
sets the correct updated counter, and initiates the analogous return trip.
The return arrival commits the specified next home state.

The outer-marker separation after a positive SUB is still at least Z; ADD only
increases it. Zero SUB and NOP commit in one step. Induction proves exact source
simulation on every finite natural input and for every finite/infinite source
run. This argument is independent of any source universality attribution.

## 5. Exact clock and halt observation

For an excursion from source q with selected old counter c and signed counter
change Delta=+1 (ADD) or -1 (positive SUB), the exact home-to-home duration is

    tau_q(c) = 3+2(Z+c)+Delta-2K-2C-d(O_q)-d(I_q).

There is one dispatch step; Z+c-K-C-d(O_q) unit travel steps; one endpoint
rewrite; Z+c+Delta-K-C-d(I_q) return travel steps; and one home commit.
The buffer inequalities make both travel counts strictly positive. A zero SUB
or NOP takes one step. The halt configuration is fixed.

The finite anchored observation word at positions 0,...,C+D has ones exactly
at 0,C,C+d(H_halt), and zeros at EVERY other position. It has length 2D+2.
It holds on a valid orbit exactly at a committed halt configuration: a valid
configuration contains only one close pair, all travel and other home codes
have different gaps, and the endpoints lie outside this window. In particular
an intermediate arrival whose future source state is halt is not yet observed.
The observation persists thereafter. Its first physical time is the sum of
the displayed durations along the first-halt source trace. This is an anchored
finite-pattern result, not a claim about exact-target halting, reversibility,
intrinsic universality, or an efficient simulator.

## 6. Exact finite-description counts

Let z be the number of SUB controls and n the number of NOP controls. There are
m=p+n+1 home codes, p outbound codes and p inbound codes. Before identity or
unreachable-row simplifications the listed component rewrite rows are:

- 2p free-packet rows
- 2p(K-C+1) marker-behind departure rows
- 2p marker-ahead contact rows
- p+n+z home rows (each SUB split by its contextual bit)

The total is 4p+2p(K-C+1)+p+n+z. These are guarded component schema rows,
NOT binary radius-R truth-table entries. The schema has two alphabet symbols;
its true local truth table has exactly 2^(2R+1) binary input rows.

## 7. Literal universal instantiation and provenance limits

The already-delivered two-counter source `literal2.json` has SHA-256
85e16b44828f2f3d4ad6d0805dcc9e9922893a6d286874f2018d6a33af864b00.
It has 8408 literal rows: 6068 ADD and 2340 SUB, and 8409 controls including
HALT. It uses no aliases or unexpanded instruction macros. Its associated
all-input proof implements a 528-row three-counter program by prime coding
A=C0*2^L*3^R*5^T, B=0, with positive A and gcd(C0,30)=1. A prologue clears T.
The three-counter program is an exact finite-half-tape simulation of the
Neary-Woods 15-state two-symbol TM. The prior source verifier covered all 8408
rows by symbolic affine loop-body paths, supplemented by concrete regressions.
The current construction reads and pins that data; it does not infer its
universality merely from its row count.

Primary source: T. Neary and D. Woods, Four Small Universal Turing Machines,
Fundamenta Informaticae 91 (2009), 105-126, DOI 10.3233/FI-2009-0008,
https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf . Section 3's Eq. (3),
Definition 3.1 and Table 1 give effective finite program/data encodings, start
state u1 and blank c. Section 3.5 and Table 16 (printed page 121, PDF page 17)
give U15,2, whose alphabet mapping
is c=0,b=1 and u1,...,u15=A,...,O. This is standard finite-input universality,
not a periodic-background weak-universality assumption. Both finite half tapes
are allowed to vary. The literal source begins in A scanning 0, representing
them as natural binary stacks L,R. Its physical input is (A,B)=(2^L*3^R,0).
Thus composing the primary finite encoding, the proved literal counter
simulation, and Sections 1-5 gives one fixed binary mass-five CA whose anchored
halt-pattern occurrence is undecidable on a computable finite-input family.

There is a visible primary-text discrepancy to preserve: Table 16 leaves the
u10,b entry undefined, matching the delivered literal J1 halt. The displayed
halting configuration on printed page 123 (PDF page 19) underlines b, also
agreeing with the table, while its final prose sentence says u10,c instead.
The table and displayed configuration define the checked interpretation.
All 30 table entries were independently matched to the pinned serialization.
No author-issued erratum is claimed, and no delivered source table is changed.
The copied serialization's bibliography comment retains the old incorrect
pages 123-144 because its exact bytes are pinned by the source verifier;
the corrected citation is supplied above and in SOURCE_PROVENANCE.md.

For this literal instantiation: D=25225, C=25226, E=50452, K=100905,
Z=403620, R=756787, and the observer length is 50452. The local truth table
has 2^1513575 entries. The schema-row count is emitted in `checks.json`.

Targeted read-only searches in VladimirReshetnikov/ProveIt at commit
c8e503d8ab4b4d7e237f65e88155ceda17800a52 found the prior five-particle abstract
provenance, but no reusable five-particle CA table in the inspected results.
That limited search does not establish novelty or the absence of other work.
Relevant inspected provenance file:
https://github.com/VladimirReshetnikov/ProveIt/blob/c8e503d8ab4b4d7e237f65e88155ceda17800a52/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/13-sparse-lattice-SOURCE-PROVENANCE.md

## 8. Explicit source-horizon Diophantine frontend

Fix a source table and a source-step horizon h>=1 in the compiler syntax. Expand
each ADD or NOP into one branch and each SUB into positive and zero branches.
Let B be the number of branches, z the zero branches, and s_j,t_j their
source/target codes under an injective coding of controls. A self-loop may
have s_j=t_j. Let delta_jk be the -1,0,+1 change to
counter k. Every branch source is nonhalting.

For each t=0,...,h-1 introduce natural selectors e_tj (j=1,...,B) and two
natural postcounter coordinates a_(t+1),b_(t+1). Initial a_0,b_0 and q_0 are
inputs or supplied constants. Use these residuals:

    sum_j e_tj - 1
    sum_j s_j e_tj - q_0                          (t=0)
    sum_j s_j e_tj - sum_j t_j e_(t-1,j)          (t>0)
    a_(t+1)-a_t-sum_j delta_j0 e_tj
    b_(t+1)-b_t-sum_j delta_j1 e_tj
    e_tj * selected_old_counter                  (each zero branch j)
    sum_j t_j e_(h-1,j) - q_halt                 (terminal)

The polynomial P_h is the sum of the squares of ALL these residuals. The
selectors are natural and sum to one, so are genuinely one-hot without extra
Boolean wires. A zero branch forces the tested old counter to zero. Choosing
a positive decrement at old zero would force its postcounter to -1 and hence
has no natural witness. Thus no positive-test slack is omitted. State and
counter balance enforce the unique deterministic trace. Since halt has no
outgoing branch, the terminal condition means first source halt exactly at h.
There is exactly one complete natural witness iff that first-halt trace exists.

Exact emitted ledger:

    witness variables = h(B+2)
    squared residuals = h(4+z)+1
    polynomial degree <=4
    raw residual monomial slots <=h(4B+5)+2

The last bound treats a_0,b_0 as atomic input coordinates or constants, and
counts written monomial occurrences before collecting constants,
zero coefficients or coincident terms; it does not charge an expanded SOS as
though squaring were free. Expanding every square has the explicit term-occurrence
bound given by the sum of the squared residual lengths. The implementation
emits each actual residual, its actual length, and that expansion bound.

For exact physical time, add a natural Theta coordinate and the residual

    Theta - sum_(t,j) e_tj tau_j(a_t,b_t).

Here tau_j=1 for zero/NOP branches and the proved affine excursion duration
for arithmetic branches. It adds exactly one variable, one squared residual,
and at most h(2B-z)+1 raw residual monomial slots when there are no NOPs.
The degree remains at most four and the complete witness remains unique.
Alternatively Theta is a specified input coordinate, adding no witness.

The numerical witness-height cost is explicit too. Put M=max(a_0,b_0) and
kappa_max=max(1, all excursion constant terms). In a valid h-step trace,
every postcounter is at most M+h, all selectors are zero or one, and

    Theta <= h(kappa_max+2M)+h(h-1).

Indeed the old counter used in layer t is at most M+t. The complete CA trace
through these h source steps has spatial diameter at most
2Z+a_0+b_0+h, since each instruction increases the counter sum by at most one
and the packet always remains between the outer markers. These bounds charge
the numerical counter sizes; they do not replace the external TM input loader
by a polynomial-time map in the TM input length.

For the literal table B=10748 and z=2340: the core has 10750h witness
variables and 2344h+1 squared residuals. The optional physical-time wire adds
one each. At h=0 no witnesses are needed: use (q_0-q_halt)^2, and physical
first-halt time zero if present. The emitter retains an optional unsimplified
Theta wire at h=0 when clock=True, so then its actual ledger is one witness
and two squared residual slots, namely (q_0-q_halt)^2+Theta^2. Substituting
Theta=0 gives the witness-free statement.

The implementation fixes q_0,a_0,b_0 to supplied natural constants. Allowing
atomic natural input coordinates in those positions is the same theorem-level
formula, but is not a claim that this emitter exports symbolic input wires.

### Paid nonnegative-real variant

For EACH source layer add the selector-norm residual

    sum_j e_tj^2 - 1.

Together with sum_j e_tj=1 and e_tj>=0, its vanishing forces one-hot selectors:
subtracting the two identities gives sum_(j<k) e_tj e_tk=0. Every summand is
nonnegative, so at most one selector is positive, and that one is exactly one.
If the external initial counters remain natural, the counter updates then
inductively force every counter witness to be a natural integer. The exact
clock is integral too. Consequently this paid variant has the same empty or
singleton complete witness fiber over the NONNEGATIVE REAL orthant as the
baseline has over naturals.

It uses the same h(B+2) core witness variables, h(5+z)+1 squared residual
slots, and degree at most four, plus the optional clock as counted above.
The added norm rows have h(B+1) written monomial slots before simplification.
The actual emitter exports them when nonnegative_real=True and counts their
actual lengths and expansion cost. This is not an unrestricted-real witness
claim, and it does not relax the natural external-input requirement.

This is a separate ordinary polynomial for EACH syntactically fixed h; h is
not silently promoted to an input of a single finite polynomial. It is not
an unbounded single-fold representation theorem, a small universal polynomial
record, or a claim that the numerical value of a huge geometric input is free.
The external universal input loader A=2^L*3^R is computable. An optional free
raw input x can instead set a_0=x+1,b_0=0; x is an input, not a trace witness.
That optional substitution is not implemented by the current constant-input
emitter. Expanding it can add first-layer monomials (in particular one for each
zero guard on the first counter); the displayed atomic-input monomial bound
must be updated if that substitution is emitted. Variable, degree and
unique-witness statements remain as above.
