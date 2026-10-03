# Source-sized sparse evaluation of the new parallel CA

## Result and scope

For every source accepted by the frozen reversible-two-counter-v1 schema and
every finite binary support X contained in the integers, the new
`SparseParallelCompiler(source).step(X)` equals the new eager
`ParallelCompiler(source).step(X)`. The inverse flag reverses the **two blocks**.
Each block makes one simultaneous decision on an immutable snapshot. There is
no ordered template cascade. This implementation evaluates malformed supports
as well as encoded computations; it does not assume a unique global head.

The production evaluator constructs no array, loop, or truth table of all F
template types. Small-source test oracles intentionally enumerate them. Runtime
depends on finite input mass, occupied-coordinate bit lengths, source metadata,
and explicit finite guard-class descriptors. The dense class descriptors still
cost quadratic space in the numeric class cutoff J; no polynomial-in-log(J)
claim is made. This is a mathematical proof, supported by independent audits
and finite tests, not a proof-assistant formalization.

The prior ordered evaluator is preserved under its original semantics. Its
byte-identical source is copied as `frozen_lazy_source.py`, SHA-256
42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61.
The new runtime checks those bytes before executing them. That module in turn
checks the exact frozen compiler bytes, SHA-256
f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f.
Only source validation, immutable metadata, arithmetic gate lookup,
candidate-index discovery, and sparse guard reading are reused. No old
`step`, old `apply_gate`, old gate `apply`, or eager source compilation is used.

The eager new-rule reference is `parallel_particles.py`, SHA-256
2c8b639646a587a51bddeaac16e46d2dbd8c4e8138ac67a2601025334d4a64cd.
Its theorem is copied without changes as `PARALLEL_RULE_PROOF.md`, SHA-256
fe809adaa74418bcddafc61cc5ff70102724256c310ae53fd396c2fe34ef65c9.
The inherited full-shift lemma and admissible-state preservation audits are
also copied unchanged. This packet supplies finite-support implementation
equality and resource bounds; it does not rebrand the old implementation.

## 1. Metadata, shapes, and identities

Let m be the number of controls, p the moving branches, a the zero-update
branches, t=p+a, and J the guard cutoff. Preserve source ordering, including
the order-preserving moving/direct partitions. Set

- D=2m+4p, S=2D+2, B2=D+1, Ltravel=3D+4, b=B3=4D+5
- Z=10B3+10+2J
- Etypes=p(4D+15)+a; Ptypes=p(4D+14)+m
- F=Etypes+Ptypes=8pD+29p+m+a

All source controls and branches, the control incidence lists, guards, and
source snapshot are immutable. `gate_at(i)` inverts the original arithmetic
partition of [0,F), materializing a single two- or three-particle pair of
endpoint shapes. It does not enumerate a travel interval or any preceding
types. The construction and exact indexing are inherited from the independently
audited frozen metadata implementation, and checked against eager gate shapes
on small sources.

An E identity is its zero-based original E index i. A P identity is its original
P index plus Etypes. These global integers are names, not an execution order.
For each identity, a raw key is (i,u), with u any integer, and its value is
orientation 0 or 1. The eager P keys are converted by adding Etypes only when
performing differential tests. Keys of distinct types at the same anchor remain
distinct, and compete with one another. Selection is all-type within the
current E or P family, never across the two blocks.

Each endpoint shape lies in [-b,b], has two or three particles, and is distinct
from the other endpoint and all its translates. Its exactness radius is
`gate.L=3*gate.B+1`: Ltravel for pair templates and 12D+16 for triple templates.
Using either the old raw radius `gate.B` or a uniform triple exactness radius
would implement a different rule.

The E block has read radius rE=Z+J; P has rP=3b+1. Both use exclusion
H=2(b+r) and block output radius 3(b+r). Thus the composed radius is

R=180D+258+9J.

## 2. Complete sparse discovery, including malformed supports

First generate a superset of potentially present template identities. Inspect
each occupied close pair (h,h+d), 1<=d<=D. Its gap uniquely determines a signed
mode: home q has gaps 2q+1 and 2q+2; outbound moving branch e has
2m+4e+1 and 2m+4e+2; inbound has 2m+4e+3 and 2m+4e+4. Odd is plus.

Every endpoint contains such a close pair. Every triple endpoint has exactly
one: the marker z is separated from the head by at least S, and from its other
particle by at least S-D=D+2>D. This also holds at a reverse interaction
endpoint where the marker itself has moved. X can have any number of close
pairs; enumerating all of them, and all distinct third particles z, finds the
distinguished pair/marker of every contained endpoint.

Write dsign=0 for plus and 1 for minus, Hrel=h-z, and w for the mode's travel
direction (branch side v for outbound, -v for inbound). Candidate formulas are:

- Every moving pair emits free and phase-free of its mode
- Behind: t=w*Hrel-dsign, requiring S<=t<=Ltravel
- Ahead: t=-w*Hrel+dsign, requiring S+1<=t<=Ltravel
- Phase-near: t=abs(Hrel), side=sign(Hrel), requiring S<=t<=Ltravel
- O plus, Hrel=-vS emits endpoint
- O minus, Hrel=vS emits dispatch
- I plus, Hrel=vS emits commit
- I minus, Hrel=-vS emits endpoint
- Hq plus with Hrel=S emits all q-outgoing moving dispatch/direct identities
- Hq minus with Hrel=S emits all q-incoming moving commit/direct identities
- Either such home sign emits its home-phase identity

The free reverse endpoint changes the predecessor anchor; this is handled by
the exact shape when anchors are recovered below. The endpoint reverse shape
uses the shifted marker, but its relative distance to the inbound pair is
still -vS. Consequently neither case needs a guessed current head anchor.

**Discovery lemma.** Whenever an endpoint of type i is contained in X,
`_candidate_indices(X)` contains i. The exhaustive endpoint classification
above proves this directly. No exactness, context, exclusion, or admissibility
assumption is needed. Filtering the returned IDs to one block therefore cannot
lose any of that block's raw keys.

For each emitted ID, each of its two sorted shapes Qlabel, and each occupied
first site z, set u=z-min(Qlabel). Retain (i,u,label) precisely when:

1. Every u+d for d in Qlabel belongs to X
2. The closed interval [u-gate.L,u+gate.L] has exactly |Qlabel| particles
3. The immutable class guard, if any, allows (X,u)

The discovery lemma guarantees the ID is visited; the least endpoint particle
guarantees the correct anchor is visited. These are exactly the eager new-rule
raw conditions. Conversely every emitted key passes those conditions. The
shapes' nontranslation property forbids ambiguous orientation at one key.

The interval count is computed by two binary searches in sorted X. For each
class-guard detector interval [u-Z-J,u-Z] and [u+Z,u+Z+J], zero particles means
class J+1, one particle means its exact offset, and multiple particles reject.
This equals the original guard's finite-site definition without scanning J+1
integer sites. Guard table access is constant-time after metadata compilation.

Optional (center,radius) arguments filter returned anchors inclusively. They
do not truncate the support used to establish candidates. Returned maps are
immutable snapshots. All integer positions and anchor arithmetic are exact;
negative coordinates and arbitrarily large integer shifts are included.

## 3. Selection and simultaneous evaluation

Obtain the complete raw map A(X) for the block. Sort all its keys by anchor,
with type as tie breaker. A key is isolated iff neither adjacent key in that
ordering has anchor distance <=H. This is equivalent to comparison against
every other key, including distinct types at exactly the same anchor.

For each isolated key k=(i,u), with orientation label, make the hypothetical
single swap Yk of its two endpoints. **Rediscover all candidate identities on
Yk**; do not reuse the old ID set. Compare the complete key sets of A(X) and
A(Yk) restricted to |anchor-u|<=b+r, ignoring orientation. The key is selected
iff those sets are equal. The selected key must occur with reversed orientation;
the implementation checks that consequence explicitly. Candidates that fail
their own selection still remain competitors in A(X).

Only after every selection decision has been made from X, remove/add all
selected endpoint particles simultaneously. There is no refresh-and-continue
cursor, no old same-type M isolation, and no iteration in template order.

**Block equality theorem.** The sparse block equals its eager new-rule block
on every finite support. Raw-map equality was proved above. The same all-type
H test is used, the hypothetical swap uses the same shapes and invariant
anchor, and before/after prospective key equality uses the same complete maps
and closed interval. Thus the selected key+orientation maps agree. The eager
theorem makes selected write neighborhoods disjoint, so both simultaneous
rewrites yield exactly the same support. QED.

**Step equality theorem.** Applying block equality first to E and then to P
proves forward equality. Applying it first to P and then to E proves inverse
equality, since each whole block is an involution. The inherited new-rule
theorem supplies full-shift reversibility, number conservation, locality, and
agreement with old trajectories on every admissible five-particle encoding.
The sparse evaluator handles finite supports of every mass, including zero.

The local-output API uses only X intersected with [i-3(b+r),i+3(b+r)]. It
enumerates writing anchors within b of i, competitor anchors within H of those,
and prospective anchors within b+r. These predicates have read radius r, so
the outermost required coordinate is b+H+r=3(b+r). The algorithm is the same
finite-neighborhood construction as the eager oracle; tests compare both to
global outputs.

## 4. A no-cascade work bound

Let n=|X|. A key admitted to the hypothetical-swap stage has no other raw key
within H. Two such keys therefore have anchor distance >H>=2b. Their original
endpoints lie in disjoint [-b,b] neighborhoods, each using at least two particles
of the same unchanged X. Hence there are at most floor(n/2) such keys. This
bound is for **all isolated keys before prospective rejection**, not merely
keys ultimately selected. It remains valid when different types share anchors:
such keys are not isolated.

Each isolated hypothetical swap is mass preserving: exactness at gate.L
ensures the other endpoint contains no outside particles, and the endpoint
masses are equal. The final simultaneous block also preserves mass. Thus both
blocks of a step have input mass n, and every discovery snapshot has mass n.

With verify=False, each block calls raw discovery once initially and once per
isolated key. A complete forward or inverse step therefore makes at most

2+2 floor(n/2) <= n+2 raw-discovery calls.

This includes trace=True; collecting trace does not re-evaluate selection.
With verify=True, each block additionally discovers the final support's raw
map and redoes selection once. The bound becomes

4+4 floor(n/2) <= 2n+4 raw-discovery calls.

The reverse write check uses that computed active map, without further
discovery. The counts hold for n=0 and n=1 as well. There is no F-sized or
changing-factor-budget term in these call bounds. The local-output API is a
separate literal neighborhood oracle, not covered by these step-call counts.

## 5. Space and arithmetic costs

Let Delta bound the length of either signed home-incidence list, G the total
guard-program/snapshot size, c=(J+2)^2, and M the immutable metadata size,
including string/number payloads. Metadata storage is O(m+t+G+tc) words plus
those payloads. Expected class validation costs O(cG+tc) arithmetic operations;
the dense growing masks add a deliberately loose O(tc^2) bit-work bound.
Adversarial metadata hash collisions can degrade parsing; they affect speed,
not source acceptance. Large binary-encoded J remains expensive because its
explicit class descriptors are expanded. The input file alone is not the
appropriate size parameter if it compresses those descriptors.

Let C bound the number of discovered type IDs over every initial or
hypothetical support in this step, counting both families before filtering.
Close-pair/third-particle enumeration gives

C=O(n^3+n^2 Delta),

independently of F. Put Q=1+n^3+n^2 Delta, so C=O(Q), and let K bound the raw
keys in one family. Each type tries at most 2n anchors, so K<=2nC. One raw-map
call costs, under expected constant-time hash operations and unit-cost exact
integer arithmetic,

Traw=O(n log(n+1)+Q+C log(C+1)+Cn log(n+1)).

The actual name-string construction cost must also be charged; each visited
template copies only the source names it uses plus logarithmically many digits.
Selection sorts K keys once and scans at most K keys per isolated candidate
when forming the before-set. A safe expected per-step bound is

O((n+2)Traw + K log(K+1)+nK+n^2),

with a constant-factor increase for verification. Taking C=O(Q), K=O(nQ)
removes any dependency on F except integer ID bit lengths. Work storage is
O(n+Q+nC) words beyond M. The original raw map, one hypothetical map, their
restricted key sets, and output support coexist; no maps from previous
hypotheticals or steps are retained. Trace stores at most n selected triples
per step. No persistent materialized-template cache exists.

For a concrete bit bound, let A be the maximum absolute initial coordinate
(zero for empty X). A block moves a particle by at most 2b under an arbitrary
bijection between equal-sized endpoints. Two blocks move it by at most 4b.
Hypothetical swaps and verification do not increase this order of bound. All
coordinate arithmetic is bounded in magnitude by A+O(b+Z+J), independent of F.
Include in W the bit lengths of that quantity, F, J, source numeric values,
and array/dictionary indices; include source name lengths in Lname. Then
coordinate addition/comparison/hashing costs O(W), and a safe generic bound
for multiplication/division is O(W^2).

The expected bound is not advertised as worst-case Python hashing. A loose
deterministic bound follows by taking U=1+M+n+Q+nC, replacing each set/dict
operation by at most U key comparisons, and charging
O((W+Lname+1)^2) per scalar operation. Multiplying the displayed operation
bound by U*(W+Lname+1)^2 is an intentionally loose polynomial worst-case bit
bound. This suffices to establish a uniform finite algorithm independent of
the geometric coordinate span and of an F-long execution sequence. It is not
a practical estimate and is not claimed tight.

## 6. API and executable evidence

The supported entry point is SparseParallelCompiler(source), not arbitrary
user predicate objects. Position collections are exact set/frozenset objects
whose elements are exact Python ints; bools and int-like aliases are rejected.
Flags are exact bools. Numeric IDs, coordinates, counters, and interval bounds
are validated without assert statements. Compiler and block objects, source
snapshots, maps returned by discovery/selection, and trace records are
immutable. Input-source mutation after compilation cannot change semantics.
The scalar `ledger()` returns a fresh ordinary dictionary for convenient JSON
serialization; mutating it cannot affect the compiled object.

The suites compare every endpoint family and orientation on varied sources,
all raw maps and selected maps, forward/inverse execution, exhaustive malformed
subsets, empty supports, guard detector multiplicities, competing types,
simultaneous far-separated swaps, huge translations, local outputs, strict
input rejection, and snapshot immutability. They use explicit exceptions and
run normally and under python -O. The malformed old-rule cascade fixture
{-118,-112,0,18,23} stays fixed under the new rule, distinguishing it from the
old ordered evaluator.

The universal benchmark loads the pinned 32,034,272-byte source with
(m,p,a,J)=(122622,66066,75495,0), F=269291358255, and R=91711698. It disables
old execution and eager compilation entry points before compiling metadata.
It executes 128 literal new-rule startup steps with inverse checks and exact
comparison to the pinned old admissible-state trace; then 128 arbitrary
endpoint/noise configurations from across the type-ID range, with mass and
roundtrip verification. All runtime choices are made from finite particle
supports, never from a promised source state or source-boundary shortcut.

These bounded checks do not complete the long universal startup, simulate a
whole Turing step, establish halting, or provide an eager universal oracle.
They demonstrate source-sized initialization and genuine finite-support
execution. Small-source eager comparisons plus the equality theorem establish
the implementation claim; roundtrips alone would not establish it.
