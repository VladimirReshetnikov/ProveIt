# Fixed-horizon natural-witness polynomial for the new parallel rule

## Exact claim and scope

Fix a schema-valid finite reversible source `s`, particle mass `n >= 0`, whole-step
horizon `T >= 0`, and direction. `Certificate(s,n,T,inverse)` emits an explicitly
indexed finite list of integer residual polynomials R_1,...,R_M of degree at most
two. Set P = sum_j R_j^2. The external variables are the 4n natural numbers
(x_i^+,x_i^-,y_i^+,y_i^-). All other W natural variables are witnesses.

There is exactly one complete natural witness with P=0 if and only if:

1. both external lists are canonical signed pairs (p*m=0);
2. their represented coordinates are strictly increasing; and
3. the new parallel CA, iterated T times in the fixed direction on X, equals Y.

Otherwise there is no natural witness. This is an exact-endpoint relation.
Acceptance of some other endpoint predicate is not implemented implicitly.
The source, n, T, and direction are compiler syntax, not existential values.
The theorem is not a fixed-arity unbounded-time Diophantine representation and
makes no uniqueness claim over real witnesses or infinite supports.

The construction binds the NEW rule P(E(X)); its inverse is E(P(X)). It does not
reuse the old ordered factor scheduler. Universal-source instantiation is a
symbolic consequence for every fixed finite source; no universal-size polynomial
was emitted and no practical universal resource claim is made.

## Trusted mathematical interface

The four adjacent frozen files are byte-pinned copies of the previously checked
local research evaluators. The emitter calls only `compile_lazy_source` for
schema/source validation and immutable source metadata; it never calls a frozen
transition, candidate enumerator, template lookup, or ordered factor evaluator.
The finite family geometry and parallel-block involution theorem are the ones
in the frozen parallel proof packet, with the all-input raw completeness and
reverse-anchor analysis in `audit-design.md`. The independent implementation
review is `audit-emitter.md`. Finite tests corroborate the binding; they do not
replace the all-input arguments below.

## 1. Direct fixed slots, with no F-template array

For each occupied pair i<j, each distinct marker index k where needed, each
source record/moving mode/control, and each endpoint orientation, the emitter
creates precisely the families in section 2 of `audit-design.md`. Travel t is
computed from a coordinate difference and range-tested, never enumerated over
S,...,L. Its type-ID use is masked to an in-range dummy when out of range.

The raw slot counts are exactly

K_E = binom(n,2)[4p + (14p+2a) max(n-2,0)]
K_P = binom(n,2)[4p + (8p+2m) max(n-2,0)].

The actual IDs are the frozen arithmetic IDs. Endpoint-interaction reverse uses
u=z-v*delta; free-E reverse uses u=h-w. Dispatch, commit, and direct guards are
fixed by type in both orientations: respectively domain, image, and domain.
Every closed exactness test uses 3B+1, not B or a universal triple radius.

A descriptor's old sites are the chosen pair and optional marker. Gap, incidence,
and travel predicates identify the literal endpoint. Exactness counts all n
coordinates in the closed 3B+1 interval; there must be exactly 2 or 3. Guards scan
all n particles in each of the two closed detector intervals. Zero hits gives
class J+1; one hit gives its offset; two or more hits gives a false guard.
The entire (J+2)^2 truth table is scanned by equality/Boolean gates, including
false cells. Rejected classes still have a fully computed integer value and
execute the whole scan: no nonexistent table row is ever dynamically indexed.

Every true endpoint has exactly one close pair with gap <=D; any triple's third
particle is farther than D from both pair particles. The pair and marker indices,
orientation, invariant anchor, mode, and travel therefore determine exactly one
true slot. The two orientations cannot both be raw at one key. Conversely each
true slot meets the literal endpoint, exactness, and guard definition. Hence the
live slots are precisely the raw key map, without duplicate (type,anchor) keys,
including on arbitrary malformed supports. Families are emitted only once.

## 2. Isolation by a fixed sorting network

The emitter pads K records to N=2^ceil(log2 K) and runs the standard bitonic
compare-exchange network. Its comparison order is live records first, then
increasing signed anchor. Original slot index is payload. Equal comparison keys
never swap at that comparator. All padding records have live=0, anchor=0,
slot=-1. Every comparator and both selected output payloads are fully evaluated.
No arbitrary permutation or sorting witness is introduced.

The comparator is a total preorder on all live/inactive records. Bitonic sorting
therefore puts all live records first in nondecreasing anchor order; inactive
records never interrupt that prefix. A live key is isolated precisely when
neither adjacent live key is at distance <=H. This is equivalent to absence of
ANY other raw key within H. Distinct types at an equal anchor have distance zero
and conflict. Orientation is irrelevant to isolation. Duplicate slots would
invalidate this argument, which is why the preceding uniqueness proof is needed.

Use deterministic prefix sums of isolated bits. The rank-r isolated record routes
to lane r, for r<floor(n/2). Each lane's descriptor is then selected by its original
slot index from the fixed raw list. Missing lanes have present=0, index=-1, and
all-zero descriptor fields, including arity=0 and both endpoint lists. Every
unselected routing select is nevertheless evaluated and constrained.

Each raw endpoint contains at least two particles. Isolated anchors differ by
more than H>=2b, so their endpoint supports are disjoint. Thus there are at most
floor(n/2) isolated keys: the fixed lane capacity cannot discard an isolated key.

## 3. Full prospective rediscovery and simultaneous output

For each lane, a deterministic transport replaces its old endpoint with its new
endpoint when present=1, and leaves X unchanged when present=0. All resulting
coordinates are sorted by n fixed odd-even transposition phases. Unoccupied
lanes run the SAME complete downstream raw circuit on X; none of their scratch
variables is unconstrained.

Let q=b+r and H=2q. For an isolated key k, the raw before-key set in its closed
q-neighborhood is exactly {k}. On the hypothetical single-swap support, the
emitter recomputes ALL direct raw slots, including initially absent type IDs.
It requires at least one after key equal to k and no distinct after key within q.
Equality uses BOTH type ID and invariant anchor and excludes orientation. Thus
it is exactly the prescribed equality of before/after key sets. Endpoint
symmetry implies the own key is present with reversed orientation; testing its
presence explicitly strengthens the implementation binding without changing
the rule. Lanes are selected only if present and this prospective test passes.

For each original particle x, the final displacement is the sum over selected
lanes and their 2 or 3 old sites of the corresponding old-to-new displacement
when x matches that old site. Every decision was computed on immutable X.
Selected old supports are disjoint. Exactness excludes collisions with unchanged
particles, and anchor separation excludes collisions between selected endpoints.
The output is therefore precisely the simultaneous endpoint-set replacement,
with n distinct particles. Its fixed coordinate network returns canonical order.

This reasoning applies to every finite support, not just source encodings or
single-head configurations. Repeating E then P, or P then E, T times gives the
correct whole-step endpoint. The output can be fed to the next block because
canonical order and mass are preserved.

## 4. Quadratic gates and unique complete natural witnesses

All signed registers v are represented by natural p,m with residuals
p-m-f=0 and p*m=0, where f is the fully specified previous-wire expression.
They uniquely give (p,m)=(max(f,0),max(-f,0)). f has degree at most two.

For comparator d=x-y, natural b,s satisfy
b(b-1)=0 and d-(2b-1)s+1-b=0.
If d>=0, only b=1,s=d is possible; if d<0, only b=0,s=-d-1 is possible.
Equality is ge(x,y)-ge(x,y+1). Boolean AND/OR and selected integer assignments
have degree at most two. Boolean assignment z=f uses the single residual z-f:
its predecessors already force f to be 0 or 1, so an extra bit residual is
unnecessary. Complement is the affine expression 1-b.

Every operation exists in one fixed topological order. Constants, including all
padding and invalid-branch dummies, are fixed. For ANY external natural input,
even one that later fails domain checks, every pre-check gate has exactly one
complete natural assignment. There are no implication-only masked equations,
free slack variables, free permutations, or free inactive branches.

Input signed-pair equations, strict-sortedness comparator checks for both lists,
and final coordinate equality equations either retain that one assignment or
reject it. Over naturals, sum of integer squares is zero exactly when every
residual is zero. Hence P has the stated zero/one witness fibers and degree <=4.
This proof is algebraic; trusting `evaluate` is not needed to verify a supplied
assignment against the emitted residuals or expanded polynomial.

## 5. Paid size and coefficient accounting

Let c=(J+2)^2 and K=K_E or K_P. A raw pass costs
O(K(n+c+1)) scalar operations and residual monomial occurrences. The bitonic
network costs O(K log^2(K+1)); isolated-rank routing costs O(nK).
There are floor(n/2) hypothetical raw passes. Each transport and deterministic
coordinate sort costs O(n^2), and final simultaneous transport costs O(n^2).
A conservative complete block bound is therefore

O(K log^2(K+1) + nK(n+c+1) + n^3),

This bound measures circuit construction and sparse residual syntax, not the
post-expansion monomial count of the ordinary quartic. Its literal expansion
has at most sum_j |supp(R_j)|^2 ordered terms, charged explicitly in each ledger.
The widest row here has O(n+1) monomials, giving the additional conservative
factor O(n+1) when converting the residual-syntax bound to an expansion bound.

With zero-slot blocks handled separately, multiply by the 2T blocks, and add
O(n) external-domain/endpoint work. This supersedes the quadratic-isolation
macro estimate in the earlier design audit. It is source-sized: the construction
never enumerates the F templates, never enumerates a coordinate travel interval,
and never packs the template array into an uncharged integer constant. Source
validation still explicitly pays the finite guard tables; there is no poly(log J)
claim. A huge universal source is not practical just because a bound is finite.

A counts signed assignment registers, I counts comparator pairs, G counts
Boolean output registers, and Q counts pure check rows. Exactly

W = 2A+2I+G,   M = 2A+2I+G+Q.

Exactly Q=5n-2 for n>=1 and Q=0 for n=0: 2n external signed-pair
checks, 2(n-1) strict-order checks, and n endpoint checks. Domain comparator
auxiliaries number 4 max(n-1,0). If w_E,w_P are the emitted witness counts
for one block (excluding external checks), then
W(T)=4 max(n-1,0)+T(w_E+w_P). The same formula holds in either direction.
This is affine growth in the fixed horizon; it is not fixed arity.
Monomial/coefficient counts can involve cancellation and are reported separately.

A is NOT by itself a uniformly bounded-fan-in elementary-operation count:
some count/offset/displacement sums are multi-input affine assignment residuals.
Their widths are charged by residual_monomials and coefficient-bit totals.
Each numeric ledger reports every residual monomial/coefficient occurrence,
maximum residual degree, maximum coefficient bit length, total coefficient
magnitude bits, coefficient L1 mass, and sum_j (number of terms in R_j)^2,
an exact ordered-SOS expansion term bound before like-term cancellation.
The pair example is also expanded into one ordinary sparse quartic; its exact
post-cancellation monomial and coefficient totals and serialized byte lengths
are reported. Larger examples are delivered as explicit finite SOS residual
syntax, not with an unmeasured claim that their expanded polynomial was stored.

No coordinate bound is assumed. On true snapshots, movement is at most 2b per
block, so support coordinates after T steps have magnitude at most A+4bT.
Comparator slacks and rejected-slot scratch integers are still fully paid
witness variables; their integer bit lengths may depend on input coordinates,
n, source constants, and T. Fixed-source polynomial coefficients do not depend
on the coordinate magnitudes. Large signed translation tests check this useful
separation without proving it.

## 6. Edge cases and computational evidence

At n<2 no raw slots or lanes exist; each block is identity. At T=0 the compiler
still emits canonical signed-pair, sortedness, and endpoint checks. At n=T=0
the zero polynomial has the unique empty witness. With p=0 there are no moving
slots; direct E and home-phase P families remain as required.

`test_certificate.py` compares all raw maps from the finite fixture corpus,
full endpoint/selection traces on the four nonvacuous exhaustive domains and
targeted small instances, forward and reverse directions, and the five-particle
malformed cascade. It evaluates every emitted residual at each accepted witness,
rejects wrong endpoints and noncanonical/unsorted/duplicate coordinate inputs,
and mutates witness coordinates including inactive scratch. Normal and optimized
receipts state exact counts. The supplemental tests exercise two simultaneously
selected lanes, guard-fixed orientations, and large translations.

The cascade X={-118,-112,0,18,23} is fixed under the new rule. Its E hypothetical
swap births (type 1,anchor 0); its P hypothetical swap births (type 59,anchor 0).
The old ordered image {-119,-113,0,19,24} is rejected by the new certificate.
This is a nontrivial prospective-rejection test, not a vacuous no-raw-key input.

One-coordinate mutation tests are binding checks, not a proof of global witness
uniqueness. Likewise exhaustive tests are exhaustive only on the stated finite
domains, not over all integer supports. The general proof above is essential.
