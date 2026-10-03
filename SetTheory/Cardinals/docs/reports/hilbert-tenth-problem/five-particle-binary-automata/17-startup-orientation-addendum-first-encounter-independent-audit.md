# Independent audit: first-encounter orientation is prefix-optimal

Audited 3 October 2026. This is a proof note only. No existing source,
generator, checker, receipt, or generated artifact was edited or regenerated.
The theorem and `2^227` optimal-assignment corollary in
`FIRST_ENCOUNTER_OPTIMALITY.md` were independently checked and pass. The
recorder and prime-template facts below were checked against
`OPTIMIZATION.md`, `independent-relabel-audit.md`, and the literal construction
in `build_source.py`. This note does not add a different recorder or machine.

## Verdict and exact quantifiers

**PASS.** For a fixed finite valid normalized-source trace, assigning zero to
the first encountered incoming edge of each collision pair simultaneously
minimizes boundary history and cumulative literal two-counter arrival time
at every boundary. This includes repeated encounters of either member of a
pair. The precise strictness qualification is:

- If an alternative differs only on pairs absent from a prefix, its histories
  and arrival times agree through that prefix.
- At the boundary immediately after the first edge belonging to a pair on
  which the orientations differ, both inequalities become strict. They stay
  strict at every subsequent normalized boundary of the fixed trace.

The theorem compares static bijections on collision pairs, using the same
recorder and prime templates, common initial data, common initial history
`h0 >= 0`, `W=0`, and common positive cofactor `C` coprime to `2310`.
Physical expansion starts with auxiliary counter zero and encoded integer

    C * 2^a0 * 3^a1 * 5^a2 * 7^h0.

The trace can start at any appropriate normalized boundary. It consists of
specified enabled source edges, not merely a sequence of control names. The
source's data trajectory does not depend on the history-label orientation.
Arrival time means the number of literal two-counter primitive steps since
this common starting boundary. It does not mean wall-clock time, CA time,
or comparison at equal physical-clock instants.

Write `G` for the first-encounter orientation. For each collision pair visited
by the trace, its first used incoming edge receives `G`-bit zero and its
companion receives one. Choose either bijection for each unvisited pair.
These choices define one static orientation; no pair is relabeled on a later
visit. The claimed inequalities hold against every other static orientation
`A`, for every boundary of this one trace. Equivalently, for each prefix the
minimizers are exactly the orientations agreeing with `G` on every pair
encountered in that prefix. Unvisited pairs cause genuine ties.

## 1. History dominance, including repeated pairs

Index all normalized boundaries by `k=0,...,m`. Let `H_G(k)` and `H_A(k)` be
the histories there. A nonrecording edge leaves history unchanged. A recording
edge with label `b` changes it by

    h -> 2h+b.

If no encountered pair differs between `G` and `A`, every used label agrees,
so their histories agree. Otherwise let edge `r` be the earliest encountered
edge whose pair has a different orientation. That edge must also be the
first encounter of its own pair: an earlier encounter of the same pair would
already have used different bits, because the only alternative bijection of
a two-element pair swaps both bits. Consequently this edge has

    b_G = 0, b_A = 1.

Histories agree before edge `r`, and its completion creates gap
`d = H_A-H_G = 1`. On every later nonrecording edge the gap is unchanged.
On every later recording edge,

    d' = 2d + b_A-b_G >= 2d-1 >= 1.

Thus it never closes. In fact `d' >= d` whenever `d >= 1`. This includes the
apparently unfavorable repeated-pair case `b_G=1,b_A=0`: it gives the lower
bound `2d-1`, which is still positive even when `d=1`.

Another formulation is that `G` makes the recording-bit string
lexicographically least among the strings compatible with static pair
bijections. The usual binary recurrence makes that first disagreement
outweigh every possible later reversal at every finite endpoint. The gap
argument also covers the intervening nonrecording boundaries directly.

## 2. Literal-clock comparison lemma

History dominance alone would not prove a clock theorem for arbitrary
recorders. The fixed literal templates here supply the missing lemma.

At encoded positive integer `N`, the physical costs of enabled five-counter
operations affecting prime `p` are

    identity:  1
    increment: (p+7)N+3
    decrement: 4N+(p+3)(N/p)+3, on enabled divisible inputs
    test:      4N+4 floor(N/p)+3.

Each cost is nondecreasing in its encoded input on its enabled domain.
Matching operations below means the same counter and primitive symbol;
private control names need not agree. In particular, equality of used labels
does not assert byte-identical literal paths under different generator
allocations.

For one recorded normalized edge, the five-counter operation word is

    source operation;
    W=0;
    (H>0, H-, W+, W>0)^h;
    H=0;
    (H+, H>0)^b;
    (W>0, W-, H+, H>0, H+, H>0)^h;
    W=0.

All its suffix operations preserve the post-source data factor
`K=C*2^a0*3^a1*5^a2`. It ends at `H=2h+b,W=0` and has `10h+4+2b`
five-counter operations.

### Positive history gap, arbitrary bit pair

Compare a higher-history execution with input `h+d`, bit `a`, against a
lower-history execution with input `h`, bit `b`, where `d>=1`. Their source
edge and data are the same. Embed every lower execution operation, in order,
into the higher execution, as follows.

1. Match the source operation, entry `W=0`, and first `h` transfer iterations.
   Encoded inputs in every matched pair have higher/lower ratio `7^d`.
2. Skip the higher execution's `d` remaining transfer iterations, then match
   `H=0`. The ratio is now `11^d`.
3. Handle preparation and surplus doubling according to the bits:
   - `a=b=0`: perform `d` unmatched higher doubling iterations
   - `a=b=1`: match the two preparation operations at ratio `11^d`, then
     perform `d` unmatched higher doubling iterations
   - `a=1,b=0`: skip the higher preparation, then perform `d` higher doubling
     iterations
   - `a=0,b=1`: in the first higher doubling iteration, skip `W>0,W-`,
     and match the lower preparation `H+,H>0` to that iteration's first
     `H+,H>0` pair. Its ratio is `11^(d-1)>=1`. Complete that higher iteration
     and its next `d-1` iterations
4. In every case the work counters now both equal `h`, and the higher history
   exceeds the lower by `2d+a-b>=1`. Match the lower execution's `h` doubling
   iterations and final `W=0` against the higher remainder. The ratio is
   `7^(2d+a-b)>=7` throughout these matched operations.

This is order-preserving and never uses a higher operation twice, including
when `h=0` or `d=1`. Each matched higher operation costs at least its lower
counterpart by prime-clock monotonicity. There are also unmatched
positive-cost higher operations, including the surplus transfer operations.
Therefore the higher-history recorded macro costs **strictly more**, for
all four bit pairs.

### Equal history

Equal history and equal bit give equal costs. At equal history, bit one costs
strictly more than bit zero: match the common source and transfer parts,
skip the bit-one preparation, and match the remaining doubling iterations
and final test with encoded ratio `7`. The skipped preparation already has
positive cost. This also applies at `h=0`.

For a nonrecording edge, ordered histories and equal data give ordered
encoded inputs. The same primitive therefore costs no less at higher
history. An identity can have equal cost; no strict per-edge statement is
needed for such an edge.

## 3. Prefix-optimal arrival times

Before the first differing encountered pair, the runs have equal data,
history, used labels, operation types, and costs. The first differing edge
has equal input history and bits `b_A=1,b_G=0`, so the equal-history part of
the lemma gives strictly greater alternative macro cost. After that edge,
the history-gap proof gives `H_A>H_G` permanently. Every subsequent recording
macro is strictly more expensive in `A`; every nonrecording edge is at least
as expensive. Adding these costs proves

    H_G(k) <= H_A(k),     time_G(k) <= time_A(k)

at every boundary, with the strictness qualification stated at the start.
Even if later edges are all identities, the already positive cumulative
time difference cannot disappear.

This proves simultaneous optimization, rather than merely optimization of
the final endpoint or a weighted objective. In particular, no static
orientation can trade a later improvement for the initial loss on this
fixed trace under these templates.

## 4. All-input clean-prologue corollary

The literal normalized prologue is

    entry;
    (v0000p, v0000d)^T;
    v0000z;
    n0001e0; n0001e1; n0001e2; n0001e3.

The `v0000p` edges are nonrecording positive tests. `entry` and `v0000d`
are the two members of the `init_clear_T` collision pair. Crucially, entry
is its first encounter for every `T>=0`; the decrement companion only
occurs later. The other five encountered pairs are first used through
`v0000z,n0001e0,n0001e1,n0001e2,n0001e3`. These are six distinct pairs,
and their first-used members are independent of `L,R,T,C`.

The existing six zero choices are therefore simultaneously prefix-optimal
for every promised prologue input

    L,R,T >= 0, C >= 1, gcd(C,2310)=1, H=W=0.

The remaining 227 pair choices do not affect any of these prologue clocks.
Thus exactly `2^227` of the `2^233` static label assignments attain the
complete-startup optimum. This counts assignments, not isomorphism classes.
Any alternative differing on at least one of the six startup pairs is
strictly worse from its first affected completed recording edge onward,
including the first TM boundary. Thus the minimizers of the complete
prologue are exactly the orientations fixing these six zero choices.
The argument also works for common initial history `h0>0`, though the
quoted clean-loader formulas below assume `h0=0`.

A useful repeated-pair check is to flip only the `init_clear_T` pair. The
alternative begins with bit one instead of zero, creating gap one. Each
clearing decrement then has alternative bit zero versus optimized bit one,
so the gap obeys `d'=2d-1=1` throughout all `T` decrements. The five exit/merge
zeros multiply it by 32. Many later zero tags therefore cannot compensate
for that initial one tag, however large `T` is.

The existing clean formulas consequently describe the minimum obtainable
by static pair orientation within this template family:

    final H = 32*(2^T-1)
    five-counter prologue steps = 320*2^T-296-3T.

For `T=0`, put `A=C*2^L*3^R`. The minimal literal two-counter prologue clock is

    76A + 4 floor(A/5) + 24 floor(A/7) + 48 floor(A/11) + 62.

The five-counter minimum follows directly too: with gap `d>=1`, its
recorded-macro cost difference is `10d+2(a-b)>=8`, while the first differing
bit at equal history costs two more steps. These formulas do not assert a
small clock at nonzero `T`, and they do not modify or reprove the separate
all-input simulation and injection certificates.

## 5. Computability and scope

For an explicitly supplied finite trace, scan its edges once, remember the
first used member of each encountered pair, and label that member zero.
Complete the unseen pairs arbitrarily. This is an effective finite algorithm
with linear scan time and at most one stored choice per collision pair.
A finite trace specified as the first `m` source steps can also be obtained
by finite simulation. A purported entire finite run given only by a program
and input is different: one must first obtain that run, and the theorem does
not decide whether it halts.

For an unbounded run, first encounters can still be assigned online when
they occur. No theorem here supplies an effective, uniform procedure that
recognizes when all choices for a fully precompiled infinite-run optimum
have been determined. Knowing which pairs will never occur is not supplied
by the finite-trace proof. No uniform extraction or impossibility theorem
for unbounded runs is claimed here.

This last point must not be phrased as saying that a particular assignment
is an uncomputable object. This machine has only 233 pairs: every complete
orientation is a finite bitstring and is therefore nonuniformly computable.
For each fixed infinite trace some finite point contains all of its
first encounters; the proof does not give a uniform procedure to locate
such a point from an arbitrary machine/input description. No special
noncomputability result for this particular 233-pair source is claimed.

The theorem has no claim of one orientation optimizing every possible
source trace: two traces may first enter the same pair through opposite
members. Nor does it optimize over different recorders, encodings,
instruction templates, numbers of counters, dynamically changing labels,
or universal-machine architectures. It does not assert equal-clock state
ordering or a cellular-automaton-clock bound. The prologue family is special
because its first-used members agree across all promised inputs.

## 6. Read-only finite cross-checks

An independent in-memory arithmetic check read the serialized normalized
rows, derived collision pairs from their incoming operations, and simulated
the prologue's data operations. It did not import or execute a builder or
write receipts. For each of 64 combinations

    L,R in {0,1}, T in {0,1,2,3}, C in {1,13}, H0 in {0,1},

it compared all 64 static orientations of the six encountered pairs,
checking both strictness and ties at each normalized boundary. This gave
**4,096 orientation/input comparisons and 36,864 boundary checks**, all
passing. A further **975** direct exact-arithmetic comparisons checked the
recorded suffix's positive-gap and equal-history inequalities.

Those suffix checks used `K in {1,13,30}`, `h=0,...,12`, gaps `d=1,...,6`,
and all four bit pairs, plus equal-history bit-one/bit-zero comparisons.
For reproducibility, with `F_p(N)=4N+4 floor(N/p)+3`, the exact suffix cost
excluding the original source operation used in the check was

    F_11(K*7^h)
    + 34K*(11^h-7^h) + 12h
    + F_7(K*11^h)
    + b*(46K*11^h+6)
    + 474K*7^b*(49^h-11^h)/38 + 18h
    + F_11(K*7^(2h+b)).

The geometric-series quotient is integral. These finite arithmetic checks
corroborate the proof; they are neither new full literal-source executions
nor a proof by bounded testing. The unbounded conclusion rests on the
history-gap argument and the operation-level embedding above.

Audited source SHA-256:
`fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`.
Normalized-source SHA-256:
`7072d5c2806f43d01435aa35418b2cf918ef4d45eb6c173d96d0c7323fc12e06`.
