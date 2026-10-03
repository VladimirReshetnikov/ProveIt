# Independent audit: sparse candidate completeness

## Verdict

The inspected `sparse_parallel.py` implements the new parallel rule correctly
on arbitrary finite supports. `_raw` uses each gate's L-exactness, sparse class
guards, stable global type-anchor keys, and full-support rediscovery before
anchor filtering. `_select` considers every raw type in the current family,
tests swaps of the same original support, and compares keys without orientation.
`_write` applies selections synchronously. No ordered evaluator is called; no
factor-indexed array or persistent gate cache is constructed.

This is a mathematical/code audit, not proof-assistant verification. Old packets
were read only. Its executable audit enumerates all types only as a small-source
test oracle. The verdict applies to the implementation inspected 2026-10-03.

## 1. Discovery covers every endpoint and orientation

Put D=2m+4p, S=2D+2, L_pair=3D+4, B2=D+1, B3=4D+5. Every endpoint contains
exactly one pair with gap d in [1,D]. A triple's singleton is at distance at least
S from the head-pair anchor and at least S-D=D+2>D from either pair particle.
This also holds for the reverse endpoint interaction: the singleton and pair
both move by v*delta, preserving their relative anchor distance S.

Enumerating every occupied close pair therefore finds the pair of every
contained endpoint, even when X itself has many close pairs or heads. No global
uniqueness or admissibility assumption is used. The signed gaps partition [1,D]:

- Home i: 2i+1, 2i+2
- Outbound branch e: 2m+4e+1, 2m+4e+2
- Inbound branch e: 2m+4e+3, 2m+4e+4

Odd gaps are plus. Coordinates may have either sign. For d>2m,
divmod(d-2m-1,4) produces a valid branch/kind because d<=D.

For a moving pair (h,h+d), free and phase-free types are always proposed. For
every distinct third particle z put H0=h-z, epsilon=0 for plus and 1 for minus,
and w=v for outbound or -v for inbound. The exact equations are:

    behind: t=w*H0-epsilon, S<=t<=L_pair
    ahead: t=-w*H0+epsilon, S+1<=t<=L_pair
    phase: t=abs(H0), S<=t<=L_pair, side=sign(H0)

Behind minus indeed has H0=w(t+1); ahead minus has H0=-w(t-1). All equality
boundaries are retained. The remaining moving interactions are precisely:

- O plus, H0=-v*S: endpoint
- O minus, H0=v*S: dispatch
- I plus, H0=v*S: commit
- I minus, H0=-v*S: endpoint

The last case keeps the old-marker gate anchor even though the current marker
has moved. Discovery only identifies the type; subsequent literal shape
matching recovers that invariant anchor.

A home endpoint requires h-S occupied. Plus gaps add all outgoing
dispatch/direct incidences; minus gaps add all incoming commit/direct
incidences. Both add home-phase. Direct edges are covered at both endpoints.
Stored incidence has O(p+a) entries.

Thus containment of any translated endpoint of type i implies that
`_candidate_indices(X)` emits i. New-rule exactness and guards only discard
proposals, so this stronger containment result proves candidate completeness
for arbitrary finite X, including malformed and negatively translated inputs.

## 2. Recovering complete raw keys

After filtering discovered global indices to the current E or P family,
materialize `gate_at(i)`. For each sorted shape A and occupied z, test anchor
u=z-min(A). Check every endpoint particle, exactly |A| particles in the closed
interval [u-gate.L,u+gate.L], and the literal guard. Every real occurrence's
least particle is enumerated, including negative min(A), free-minus predecessor
anchors, and shifted endpoint anchors.

The metadata's L equals L_pair, whereas gate.L=3*gate.B+1. Triple exactness is
12D+16, not L_pair. Uniform metadata.L, uniform B3 exactness, old B-exact raw
matching, and old M exclusion would all be incorrect substitutions. Inclusive
counts use bisect_right(high)-bisect_left(low).

Keys are (global factor index, integer anchor); orientation is a separate value.
Distinct types at one anchor remain distinct. Exactness cannot equal two
distinct endpoint sets simultaneously, so orientations are unambiguous. The
reference P block's local indices need offset E_count for comparisons.

Class windows are [u-Z-J,u-Z] and [u+Z,u+Z+J]. Zero particles mean class J+1;
one gives its exact signed offset; multiple particles reject. Sparse interval
counts exactly reproduce the literal guard without scanning J sites. Commit
uses the image table supplied by gate_at, never the domain table.

## 3. Exclusion, prospectivity, synchronous updates

Each block uses b=B3, its own r, and H=2(b+r). All-type means all types within
this block family; E and P do not compete across separate blocks. Sorting keys
by (anchor,type) makes predecessor/successor checks equivalent to exclusion by
any other key within H. Distinct types at the same anchor have distance zero.

For each isolated key, hypothetically swap its endpoint on original X. Discover
types afresh on the entire resulting Y, match every family raw key anchored in
the closed b+r interval around the key, and compare this key set with original
raw keys in that interval. Ignore orientation in equality; the retained key's
own orientation reverses, as the implementation additionally checks.

Keeping only previously discovered types would miss births. Testing only the
swapped type, selected types, or eligible keys would also be wrong. Cropping
support to the anchor interval would lose reads extending a further r; the
implementation keeps full support and filters only output anchors.

All hypothetical decisions use the same immutable X, then retained endpoints
are rewritten together. Their anchors are pairwise >H apart and writes are
disjoint. This is exactly the proved prospective-isolation rule, inheriting
all-input block involutivity and mass conservation. Forward order is E then P;
inverse is P then E.

The local-output crop is also sufficient: output-to-writing-anchor distance b,
then exclusion distance H, then candidate read radius r total b+H+r=3(b+r).
Prospective reads fit within 2b+2r. All queried endpoint/read sites remain in
the crop, so arithmetic discovery remains complete for queried candidates.

## 4. Work and storage, with source and class parameters exposed

Let q=p+a, c=(J+2)^2, G be total guard-program size, Delta the longest stored
home-out/home-in incidence list, and n=|X|. Delta<=q. There are symbolically
F=8pD+29p+m+a types. Define Q(n)=O(n^3+n^2*(Delta+1)).

Expected-hash discovery costs O(n log(n+1)+Q(n)), with C<=min(F,Q(n)) discovered
types. Sorting indices adds O(C log(C+1)). A raw scan costs
O(C*n*log(n+1)) plus actual gate-name copying. Raw-key count R<=2nC; more sharply,
R=O(Q(n)), since each close pair gives constantly many pair types, each
pair/singleton constantly many moving triples, and each home witness at most
Delta incidences.

Let C,R bound all original/hypothetical snapshots in a block and put

    Traw=O(n log(n+1)+Q(n)+C log(C+1)+C*n*log(n+1)).

Isolated keys have pairwise anchor distance >H>=2b, disjoint endpoint supports,
and at least two particles each. Their number s is at most floor(n/2) before
prospectivity. A conservative cost for the actual block implementation is

    O((s+1)*Traw + R log(R+1) + s*(R+n)).

This includes sorting raw keys, hypothetical copies, and full scans of original
raw keys to restrict each interval. Each actual block preserves n. Without
optional verification a full step makes at most 2+2*floor(n/2)<=n+2 discovery
calls. There is no old ordered cascade parameter. Verification adds additional
evaluations with the same polynomial form.

Substituting C,R<=O(Q(n)) gives polynomial work in n and explicit source
parameters without unconditional F loops, travel-distance loops, or coordinate
span scans. Dense supports can still discover all F types; no sublinear-in-F
worst-case claim follows. Computing F as an integer is not enumeration.

Transient storage is O(n+C+R) beyond metadata, discarding hypothetical maps one
at a time. The actual code has no gate cache. An unbounded cache retained over
many steps could eventually store every type and would invalidate that storage
claim. Current traces retain selected keys and counts only, adding O(n) words.

### Compilation and the J-squared limitation

The reused compiler explicitly constructs two c-entry Boolean tables per
branch. Metadata is O(m+q+G+q*c) words plus actual string/integer payloads.
Unit-operation compilation costs O(c*G+q*c+m+q), plus parsing/name/dictionary
costs. No pD-sized factor array is built.

Dense c-bit conflict masks have a conservative O(q*c^2) bit-work construction
bound beyond guard evaluation/comparisons. Per-incident-control masks remain
within this broad metadata budget. Large binary-encoded J therefore remains
expensive: explicit quadratic-in-J table allocation is not polynomial in log J.
Source-sized claims must expose expanded class metadata, even though runtime
guards do not scan J sites.

### Bit lengths and hashing

Let A bound initial absolute coordinates. Endpoint sets inside [-b,b] allow
particles to be matched with displacement at most 2b per block. Two actual
blocks, or a second-block hypothetical swap, reach at most A+4b. Anchors/reads
extend this by b+max(r_E,r_P). A sufficient coordinate bit bound is

    Wcoord=O(1+log(1+A+b+Z+J)).

This has no ordered F-dependent displacement term. Index arithmetic still
uses O(log(F+1)) bits; source/table indices have their own parameter bit lengths.
Coordinate addition/comparison/hashing costs O(Wcoord) in a simple bit model;
gate decoding multiplication/division can conservatively be charged quadratic
in its bounded integer bit length. Masks and actual string lengths have the
separate costs stated above.

Python hash bounds are expected, not adversarial worst-case constant time.
Replacing hash accesses by linear container scans gives a loose deterministic
polynomial bound in n and explicit source/class metadata, with integer bit
costs included; sorted containers can give comparison-based bounds instead.
Neither removes the non-polynomial-in-log-J expansion. No empty coordinate
interval or full factor range is required in either implementation approach.

## 5. Executable evidence

Self-contained `audit_candidate_completeness.py` imports adjacent pinned
metadata and the actual sparse implementation. Both normal and optimized
Python runs pass explicit exception checks:

- 14 source cases: both sides; decrement/zero/increment; J=0 and J=2; empty E;
  guarded branching and disjoint incoming images at a shared target
- 17,504 discovery checks across every small-source endpoint/type, both
  orientations, zero/negative/positive and 130-bit translations, with and
  without additional particles
- 1,120 complete key/orientation maps versus an all-index literal inclusive-L
  and literal-guard oracle
- 2,240 actual block comparisons of candidate maps, eligibility using a
  quadratic all-type oracle, and synchronous output
- 2,560 sparse versus literal domain/image guard comparisons, including
  absent and multiple markers

Receipts are `audit-candidate-receipt.json` and its optimized counterpart.
Finite tests supplement the symbolic arbitrary-support argument; they do not
exhaust the universal local neighborhood or materialize its factor family.
