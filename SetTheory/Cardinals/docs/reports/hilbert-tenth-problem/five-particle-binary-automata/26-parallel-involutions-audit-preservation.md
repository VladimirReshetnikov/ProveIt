# Audit: preservation of the entire admissible five-particle micrograph

## Result and scope

**PASS.** For every finite source accepted by the frozen `compile_source`, every
configuration in its admissible doubled micrograph, and every integer translate
of such a configuration:

1. The new edge block has zero or one candidate key. It has one exactly when
   the signed node is incident to the intended doubled microedge.
2. Swapping that candidate produces another admissible signed node and preserves
   the **same type and the same integer anchor**, with opposite orientation.
3. The new phase block has exactly one candidate key. Its swap is precisely the
   sign flip and preserves that same candidate key.
4. Therefore the all-type isolation and prospective candidate-set tests reject
   no intended edge or phase move, for either sign, at any corridor boundary,
   on any admissible intermediate state, or at either kind of reflection.
5. Consequently the new map and its inverse agree with the original compiler
   on the entire admissible doubled set, not merely on one encoded forward run.

This is a symbolic audit for arbitrary finite accepted sources and arbitrary
natural counter values. It is not an inference from sampled executions. It
does not assert equality of the old and new maps on malformed configurations,
nor that either old ordered gate block is globally an involution.

Sources inspected:

- Original `reversible_binary.py`, SHA-256
  `f95a6028c9d3cc6f8b0b497cfc0cad68104da6d70e55205df04ad234e5d0c76f`
- The local `frozen_reversible_binary.py`, independently checked to have that
  same SHA-256
- Original `COMPILER_PROOF.md`, especially Sections 3--7
- Final hardened `parallel_particles.py`, re-read on 2026-10-03, SHA-256
  `2c8b639646a587a51bddeaac16e46d2dbd8c4e8138ac67a2601025334d4a64cd`

## 1. Constants and the exact admissible set

Write

    D = 2m+4p,  S = 2D+2,
    B2 = D+1,  L = 3D+4,
    b = B3 = 4D+5 = L+D+1,
    K = 3b+1 = 12D+16,
    Z = 10b+10+2J.

Here `L` is the pair gate's exactness radius; `K` is the triple gate's
exactness radius. In particular,

    S-D = D+2 > D,
    Z-1 > K,
    Z > 2(L+1).

All signed head modes have distinct gaps in `1,...,D`. A head at anchor `x`
has sites `x,x+d`; the anchor is always its leftmost site, also for leftward
motion.

An admissible unsigned node is either an arbitrary natural-counter home ID,
or a strict intermediate node in the prescribed finite subdivision of an
**enabled** source edge. Both signs of every such node are admissible. In
particular, arbitrary geometric O/I packets whose source branch is disabled
are not included in this claim.

The three marker sites at every admissible node are the origin and the two
counter endpoints. Their mutual separations are at least `Z`. A moving head
is in the corridor between the origin and the selected endpoint, at anchor
distance at least `S` from both corridor endpoints. The third marker is farther
away. These statements remain true after a decrement because compilation
requires every enabled update to leave natural counters. A home head has
anchor `origin+S` and the same minimum-separation properties.

## 2. Recognition cannot substitute the wrong particles

Every admissible state has exactly one pair of occupied sites at separation
at most `D`: the two head particles. Head-to-marker distances are at least
`S-D=D+2`, and marker-to-marker distances are at least `Z`.

Every pair template is exactly a head pair. Every triple template has exactly
one close pair, which is its head pair; every distance from its singleton to
either head particle is greater than `D`. This also holds for the extreme
travel endpoints at anchor distance `L+1`, and for the translated endpoint
template after a counter update.

It follows that any match of any template on an admissible state:

- must use the actual head pair as its displayed close pair;
- must have the signed mode determined by that pair's globally unique gap;
- if it is a triple, must use one of the actual three markers as its singleton.

No marker pair, head-marker pair, or alternative division of the particles can
match. A fixed template orientation determines its anchor once the head pair
is known. A match involving a nearby singleton cannot also involve a second
nearby singleton: the entire template diameter is at most `2b<Z`.

These facts also show that, for each individual old gate, there is at most one
old raw key on an admissible state. Its old same-type raw-key exclusion is
therefore vacuous there. This establishes why deleting that particular test
does not expose hidden valid-state matches; it does not use any assertion
about old whole-block involutivity.

Whenever an intended triple is matched, its other two markers are outside its
`K` exactness window. For the ordinary triple types their anchor is a marker
and those other markers are at least `Z` away. For the reverse endpoint type,
the anchor is the old marker coordinate, at distance at most one from the new
marker; the other markers are at least `Z-1>K` away. Its exactness predicate
therefore holds. Pair exactness is the nontrivial free/contact distinction
treated below.

## 3. All moving nodes reduce to one oriented corridor

For a moving mode let `w` be its forward direction. Let `A` be the marker
behind the head and `C` the marker ahead, ordered in direction `w`. Define

    N = w(C-A) >= Z,
    t = w(x-A),
    S <= t <= N-S.

For outbound `O_e`, `w=v`, `A=origin`, `C=old selected endpoint`, and
`N=Z+c`. For inbound `I_e`, `w=-v`, `A=new selected endpoint`, `C=origin`,
and `N=Z+c+Delta`. Thus this coordinate system covers both sides, both update
signs, and every intermediate anchor without a reflection convention for the
two head particles.

The third marker is never within `L+1` of the head or a free predecessor
anchor. It cannot match any travel template with this head. The only possible
contacted markers are `A` and `C`, and they cannot both be in the relevant
near-contact range because `N>2(L+1)`.

### 3.1 Plus travel candidates

At a plus node the free gate's invariant predecessor anchor is `u=x`.
Pair exactness holds precisely when neither `A` nor `C` is in
`[x-L,x+L]`, equivalently

    L < t < N-L.

The matching triple orientations and free range are therefore exactly:

    behind-plus:  S <= t <= L,
    free-plus:    L+1 <= t <= N-L-1,
    ahead-plus:   N-L <= t <= N-S-1.

The behind key is `A`; the ahead key is `C`. These disjoint intervals exhaust
all `S <= t <= N-S-1`. At the one remaining plus position, `t=N-S`, there is
no travel candidate. That position is handled by the forward interaction:
the endpoint gate for O, and the commit gate for I.

### 3.2 Minus travel candidates, with the correct free key

At a minus node the free template's invariant predecessor anchor is

    u = x-w,

not `x`. Its oriented coordinate relative to `A` is `t-1`. Its pair exactness
therefore holds precisely when

    t-1 > L  and  N-(t-1) > L.

The matching reverse orientations are exactly:

    behind-minus: S+1 <= t <= L+1,
    free-minus:   L+2 <= t <= N-L,
    ahead-minus:  N-L+1 <= t <= N-S.

These disjoint intervals exhaust `S+1 <= t <= N-S`. At `t=S` no travel
candidate exists. The reverse interaction is the dispatch gate for O and the
endpoint gate for I.

This proves the full free/contact complement, including the cases most likely
to be mishandled:

- A behind triple moves plus distance `L` to minus distance `L+1`. At that
  minus endpoint the free key is still at predecessor distance `L`, whose
  exactness window contains the marker, so a second free candidate does not
  appear.
- An ahead free move takes plus distance `L+1` from the ahead marker to minus
  distance `L`. Its invariant predecessor still sees that marker at `L+1`.
  The reverse ahead triple range ends at minus distance `L-1`, so a second
  triple candidate does not appear.
- At the ahead wall, plus distance `S` has no forward travel template. At the
  behind wall, minus distance `S` has no incoming travel template. Those are
  precisely the interaction endpoints, for both physical directions.

## 4. Interaction candidates and guards

The signed-gap recognition argument excludes interaction gates of other
branches and modes, except the intended shared-home alternatives. The full
interaction list is as follows.

### Home plus

Only the forward orientation of a dispatch or direct gate with this source
control can match. Its anchor is the origin. The exactness window contains
the origin and home pair and excludes the endpoints.

At origin-relative locations `-(Z+k)` and `Z+k`, `0<=k<=J`, the guard reads
exactly the corresponding counter class: one bit for a counter at most `J`,
and no bit for a counter greater than `J`. The head cannot contaminate those
reads because all home-interaction head sites are within `b<Z` of the origin.
Thus the code's class table returns exactly `G_e(c)`. Disjoint source domains
give at most one candidate. There is one iff the source ID has an outgoing
edge.

### Home minus

Only the reverse orientation of a commit or direct gate with this target
control can match. Its anchor is the origin. The commit guard is the exact
image predicate `I_e`, including existence of natural pre-counters. For a
direct zero-update gate, `G_e=I_e`. Disjoint actual branch images give at most
one candidate, and one exists iff this source ID has a predecessor.

An enabled reverse commit reaches the inbound subdivision associated with
that genuine predecessor. No geometrically plausible but source-invalid
intermediate is added.

### Outbound plus at the ahead wall

Only the forward endpoint template matches. It is anchored at the old
selected marker `m`, with head anchor `m-v*S`. The swap produces marker
`m'=m+v*Delta` and inbound-minus anchor `m'-v*S`. It is an admissible endpoint
transition of this enabled branch. No contextual guard is needed.

### Outbound minus at the behind wall

Only the reverse dispatch template matches, anchored at the origin. The old
counters still satisfy `G_e`, because this entire outbound corridor belongs
to an enabled source edge. It returns to that edge's home-plus predecessor.

### Inbound plus at the ahead wall

Only the forward commit template matches, anchored at the origin. The post
counters satisfy the exact image predicate `I_e`, by their construction from
the enabled source edge. The target is its home-minus state.

### Inbound minus at the behind wall

Only the reverse endpoint template matches. Its key is

    u = m'-v*Delta = m,

the **old** marker coordinate, rather than `m'`. In fact the template's
singleton offset is `v*Delta` and its head-anchor offset is
`v*Delta-v*S`, so this key is forced by either component of the match.
The swap restores the old marker and outbound-plus head. Its successor has
the forward endpoint at exactly this same key.

The only shared signed-mode endpoints requiring guard disambiguation are the
homes. All other interactions have their own branch-specific O/I signed gaps.
The corridor interval calculation excludes travel competition at their walls.
Together these facts prove that every admissible signed state has precisely
its desired edge candidate, or has none at a missing source edge.

## 5. Exactly one phase candidate everywhere

At a home state, the unique matching phase type is `phase-home:q`, anchored
at the origin. It matches both signs; its exactness condition holds as above.
There is no free-home phase type.

At a moving state, the pair phase type for that mode has invariant anchor
`x` in both orientations. It matches exactly when no marker is within `L`
of `x`, or equivalently

    L < t < N-L.

Otherwise there is exactly one marker at head-anchor distance in `[S,L]`.
Its side and distance select exactly one `phase-near` type, anchored at that
actual marker. Distinct marker neighborhoods cannot overlap. There are no
other possible phase matches by signed-gap recognition.

A phase swap fixes all markers, the head anchor, and the unsigned mode. It
changes only the signed gap. Thus the same free/near/home case, type, and
anchor hold afterward. The whole phase candidate-key set is the same
singleton, with opposite orientation.

## 6. New eligibility tests always pass on intended moves

Let `C_E(X)` and `C_P(X)` denote the new all-type candidate-key sets, retaining
the type index and integer anchor but ignoring orientation.

For the edge block, Sections 2--4 give either `C_E(X)=empty` or
`C_E(X)={k}`. In the singleton case its swap `Y` is admissible. Its intended
reverse incidence is represented by the same key `k`:

- free travel: the shared predecessor anchor;
- behind/ahead travel: the unchanged contacted marker;
- dispatch, commit, direct: the unchanged origin;
- endpoint: the old endpoint coordinate in both orientations.

The uniqueness proof applied to `Y` therefore gives `C_E(Y)={k}`. This is
equality of the complete global candidate-key sets, stronger than equality
inside the new prospective test's finite interval.

For the phase block, Section 5 gives `C_P(X)={k}=C_P(Y)` with its same type
and anchor. Consequently, for either block:

- there is no other candidate within `H=2(b+r)`, or anywhere else;
- the prospective candidate sets agree within radius `b+r`;
- the retained candidate has opposite endpoint orientation.

Thus every intended swap is eligible, independently of how large `H` is.
At a missing edge the empty candidate set correctly makes the edge block
the identity. The subsequent phase flip implements reflection there.

## 7. Agreement with the original execution and its inverse

For each intended candidate, the old gate's raw recognition, exactness, and
guard hold, and its same-type raw-key exclusion is vacuous by Section 2. Every
other old gate is inactive on that admissible state. After the intended gate
fires, only that same gate can match the new state, and the ordered block
does not apply that gate again. Hence the old ordered E product equals the
same edge matching on the admissible set. The identical argument for the
unique phase type makes the old ordered P product the same sign flip.

Both these restricted actions preserve the admissible doubled set and are
involutions there. Therefore

    F_new = P_new after E_new = P_old after E_old = F_old

on the entire admissible set. Their inverse actions agree there as well:
first flip phase and then apply the edge matching. This includes all homes,
all strict intermediates on every enabled source edge, both signs, both
reflection endpoints, arbitrary counter sizes, and integer translates.

This argument is restricted to the admissible set where it is proved. Global
involutivity of the **new** blocks comes from the separate prospective-isolation
lemma. No global claim about the old whole blocks is used.

## 8. Code correspondence and the common-window caveat

The new code constructs one type for each old gate using exactly `g.P`, `g.Q`,
`g.L`, and `g.guard`. `candidates` includes type and anchor in its dictionary
key and records orientation only as the value. Its window particle count,
together with inclusion of every displayed endpoint particle, is the exact
endpoint predicate used above. Its optional center/radius filter restricts
candidate anchors only. `eligible` tests all-type isolation and compares
unoriented keyed sets as required. `swap` retains all particles outside the
displayed endpoint change.

There is one important formulation detail for applying a general swap lemma:
pair templates use exactness radius `L<b`. A valid free head may have a marker
at distance `L+1`, inside the common interval `[-b,b]`. Thus it would be
incorrect to describe every candidate as one fixed two-one word on the whole
common `[-b,b]` interval with zeros everywhere else in that interval.

The correct formulation permits type-dependent local swap windows bounded
by `b`, or equivalently preserves arbitrary untouched bits in that common
interval. For a pair type, exchange its two complete endpoint words on the
old `[-B2,B2]` window and leave all other bits unchanged; for a triple, use
`[-b,b]`. Exactness on `L` or `K` implies the required endpoint word on the
corresponding smaller swap window. Each such partial word-exchange extends
to a genuine involution by fixing all non-endpoint words. Its changed support
is bounded by the common `b`, and the candidate read radius is bounded by
the chosen `r`. The prospective-isolation lemma's locality proof then applies
unchanged. This is a necessary wording adaptation, not a code or preservation
failure.

Finally, all E predicates read at most `r_E=Z+J`; all P predicates read at
most `r_P=3b+1`. The original guards read outside the swapped supports, so
their truth is symmetric on the two endpoints. The code's global bounds are
therefore consistent with the general lemma:

    R_E = 3(b+Z+J),
    R_P = 3(b+3b+1),
    R_F <= R_E+R_P
         = 45b+33+9J
         = 180D+258+9J.

The radius result requires that general lemma, with the type-dependent-window
formulation just stated. The simulation-preservation result above does not
depend on any unproved radius optimization, universal-source instantiation,
or empirical test coverage.

## 9. Final hardened implementation recheck

The complete final implementation at the hash above was re-read after API
hardening. The candidate loop, sparse swap, all-type isolation, prospective
key comparison, local-output selection logic, source-template construction,
block order, and radius arithmetic are unchanged from the implementation
analyzed in Sections 1--8.

The changes add exact built-in integer set/frozenset checks, exact Boolean
flag checks, integer radius/output-coordinate checks, immutable slotted
pattern/block/compiler records, and immutable snapshots of pattern endpoints.
All mathematical admissible inputs are finite frozensets of integers and use
Boolean direction/verification flags, so these checks do not remove or alter
any state or operation covered by this preservation theorem. Freezing the
records retains the source-template data used by the proof. The frozen old
compiler's hash was also rechecked and remains unchanged.

The completed `PROOF.md` now explicitly uses type-dependent write sets, so
its lemma formulation incorporates the common-window correction in Section
8. Its certificate-transport distinction is consistent with this audit:
step-for-step equality transfers semantic admissible computations and their
observations, but does not identify the two full-shift rules or automatically
repurpose an arbitrary old arithmetic verifier. This audit certifies the
final implementation's mathematical preservation correspondence; it does
not claim that the finite regression suite alone establishes the theorem or
provide a separate comprehensive API-security audit.
