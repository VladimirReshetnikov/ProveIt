# Four history-label swaps remove the clean startup explosion

Portable edition note: mathematical content below is inherited from the frozen
producer proof/audit. Statements about original visual inspections and external
release preservation describe historical work, not this offline replay. The
portable checker regenerates a pinned baseline from bundled inputs; no sibling
release is read. See README.md and PROVENANCE.json for exact replay scope.


Date: 3 October 2026. This is a separate new release; the original literal
source and all Report 16 bytes are unchanged. It is a targeted coding choice
inside the history recorder, not a smaller machine or a speedup on arbitrary machine states.

## Exact delta

The three-counter primitive and normalized source files are byte-identical
to the frozen predecessor. The prime encoding and macro graphs have the same
rules and sizes. For each colliding incoming pair, the history construction
may choose either bijection from that pair to {0,1}. We choose bit 0 for each
edge of the clean T=0 startup path:

| Target | Startup edge | Old bit | New bit | Companion |
|---|---|---:|---:|---|
| init_clear_T | entry | 0 | 0 | v0000d |
| n0001_0 | v0000z | 0 | 0 | v0003 |
| n0001_1 | n0001e0 | 1 | 0 | v0028 |
| n0001_2 | n0001e1 | 1 | 0 | v0066 |
| n0001_3 | n0001e2 | 1 | 0 | v0155 |
| tm_A0_pop0 | n0001e3 | 1 | 0 | v0303z |

These are six distinct targets: no pair is asked to give both edges bit 0.
Exactly the last four pairs are permuted. The unchanged first two choices
are included in the generator's explicit policy to make the intent auditable.
All remaining 227 collision pairs retain their original order. There are 233
pairs total; six are touched by the policy and four change.

## All-input theorem and comparison with the old proof

For **every** natural L,R,T and positive C coprime to 2310, the new literal
machine starting at(START,C·2^L·3^R·5^T,0) simulates the same universal
three-counter source and reaches HALT iff that source does. The initial
history/work exponents remain 0. No input is pruned, and T-clearing is retained.

The old history boundary invariant was (data,H=h,W=0). A recorded source
edge e labelled b first performs e, then sends (h,0) to (2h+b,0) in 10h+4+2b
steps. Transfer and doubling ranks are H and W respectively. The proof
uses only b∈{0,1} and different labels for the two incoming edges. It never
uses a prescribed semantic meaning for either bit. The same invariant and
strictly decreasing ranks therefore prove every new macro, for arbitrary
natural h and every enabled source-operation input. All source operations
and their domains remain present. Composing with the unchanged normalization
and prime-encoding invariants yields full simulation, nonblocking finite
macro completion, and halting equivalence on the entire old loader domain.

This promised-input theorem is separate from global injection. The new
five-counter and two-counter literal tables are each checked anew: every
primitive is a partial injection, outgoing multiple edges have disjoint
zero/positive domains, and incoming multiple edges have disjoint zero/positive
images of the same counter. Each configuration in Q×N^k therefore has at most
one successor and at most one predecessor, including malformed encodings and
all intermediate controls. The strict serialized-source checker separately
derives image guards and exhaustively tests the four J=0 product classes.
This is an all-natural partial-injection proof, not an assertion restricted
to reachable configurations. START still has no incoming row, HALT no outgoing.

The generic independent reconstruction checker was changed only to verify a
bijection on each history pair before building its expected graph. It does
not trust the generator's order or import the generator. All affine paths
and global source/image checks are rerun against the new hashes. A separate
checker derives the exact four permutations and startup formula independently.

## Exact startup formula and executed prefix

When T=H=W=0, all six recording edges are labelled 0. Each history macro
therefore costs 4 five-counter steps and keeps H=W=0. The whole prologue
contains 5 identities, one zero test of T, six zero tests of H, and twelve zero
tests of W:24 steps total. Neither L nor R changes, so for
A=C·2^L·3^R every prime boundary has the same A and physical auxiliary B=0.
A test for prime p costs 4A+4⌊A/p⌋+3. Summing gives the exact formula

    5 + (4A+4⌊A/5⌋+3)
      + 6(4A+4⌊A/7⌋+3) + 12(4A+4⌊A/11⌋+3)
    = 76A + 4⌊A/5⌋ + 24⌊A/7⌋ + 48⌊A/11⌋ + 62.

`verify_initialization.py` traversed each serialized branch without macro
acceleration. At A=1 it executed 138 source steps and arrived at
(tm_A0_pop0,1,0):100 zero updates,19 decrements,19 increments. It saves the
entire trace. Five other T=0 cases A=2,3,13,72,78 were also fully traversed,
matching the formula. Finite examples are corroboration; the displayed
macro decomposition proves the formula for all promised A.

Exactly the first empty-input TM transition was then executed:210 further
literal steps, reaching (tm_B0_pop0,7,0), corresponding to five-counter data
(L,R,T,H,W)=(0,0,0,1,0). Its independent three-counter run uses 4 instructions,
and its reversible five-counter run 22 steps. Total literal execution through
this boundary is 348 steps. This is not a completed universal program.

## Nonzero scratch and the honest tradeoff

The entire T>0 domain is retained. Let h_T=2^T−1. Starting with H=0, the
initial edge records 0; each of the T decrement-loop iterations records 1;
the exit and four merge edges then record 0. Thus final history is 32h_T,
whereas the old prologue had 32h_T+15. The exact new five-counter prologue
clock is

    4 + Σ(i=0..T−1)(10·2^i−3) + 20 + 310(2^T−1)
    = 320·2^T−296−3T.

The old prologue costs 118 more five-counter steps for every T. For T=1,
the new five-counter startup has 341 steps and H=32. The composed literal
clock is 18,595,602,803,420,561,611,627,873,065, predicted but not traversed.
The T=0 formula must not be used for this case.

The four companion edges v0028,v0066,v0155,v0303z now receive 1 instead of 0.
At equal starting h their history macro costs two extra five-counter steps,
and final history is one larger; the prime encoding can magnify that change.
For example, the v0303z companion at data (0,0,0),H=W=0,C=1 costs 104 literal
steps now, versus 28 before. Its output H changes 0→1. Across a fixed normalized
path containing k collision events, the history difference is exactly
Σ(j=1..k)(b_new,j−b_old,j)·2^(k−j). This may have either sign. No pointwise
comparison or uniform speedup follows for arbitrary later paths or histories.

## Stronger comparison for paired clean-loader runs

Although arbitrary equal-history states can slow down, **every paired run
from the same clean loader input reaches each corresponding normalized
boundary no later in literal two-counter steps with the new table**. At every
TM cut, including the first one, the new arrival is strictly earlier.
This is a theorem comparing the two exact literal source clocks; it makes
no claim about raw CA evaluation speed or a uniform speedup ratio.

Here is the operation-level embedding proof. Compare the same recording
edge e with old history n+d and new history n, both with W=0 and equal data.
Assume d≥1, and let b_o,b_n be the possibly different recording bits. Match
the source operation, W=0 entry test, and the first n transfer iterations
in chronological order. Every matched old encoded integer is 7^d times the
new one. Let the old macro finish its d extra transfer iterations before
matching the H=0 exit: its encoded integer is 11^d times the new one.

If both bits are 1, match their two preparation rows (encoded ratio 11^d).
If old bit1/new bit0, skip the old preparation. If both bits are 0, neither has
preparation. Then let the old macro complete d surplus doubling iterations.
Both have W=n and their H difference is 2d+b_o−b_n≥1, so match the n remaining
doubling iterations and the final W=0 test with encoded ratio
7^(2d+b_o−b_n)≥7.

For old bit0/new bit1 the preparation needs a different placement. In the
old macro's first doubling iteration, skip W>0 and W−, then match the new
H+ and H>0 preparation rows to that iteration's first H+/H>0 pair. Before
these paired operations the old encoded integer is 11^(d−1) times the new
one. Finish that old iteration and its next d−1 surplus iterations. Both
now have W=n; old H=2d and new H=1, so match the new doubling iterations and
final W=0 at encoded ratio 7^(2d−1)≥7. The pairing preserves chronological
order and never uses an old row twice.

Each paired row has the same counter and primitive symbol. Its exact prime
macro cost is a nondecreasing function of its positive encoded integer
(also for division, on enabled divisible integers). Thus every paired old
row costs at least its new counterpart, and unmatched old rows cost positive
time. This proves strict recorded-macro cost dominance for d≥1, regardless
of the two bits. If d=0 and b_o=b_n, costs are equal; if d=0,b_o=1,b_n=0,
skipping the old preparation and matching its doubling part at H difference 1
proves strict dominance as well. Nonrecording edges have the same data
operation and monotonically ordered encoded inputs, so their costs cannot
reverse the comparison.

In the common clean prologue, histories agree until the first changed bit;
all changed startup bits have b_o=1,b_n=0. At its end old H−new H=15 for
every natural T. Thereafter a nonrecorded edge leaves the gap unchanged,
while a recorded edge sends d to 2d+b_o−b_n≥2d−1≥d≥15. Induction on
normalized edges proves the claimed paired-boundary and TM-prefix result
on the entire original L,R,T,C loader domain. This hypothesis distinguishes
it from the valid 28→104 counterexample at unrelated equal-history states.

For a direct arithmetic cross-check, with post-operation data factor
K=C·2^L·3^R·5^T, the exact prime-expanded costs are:

- One transfer iteration at (H,W)=(h−j,j):
  136K·7^(h−j−1)·11^j+12
- One doubling iteration at (H,W)=(b+2j,h−j):
  474K·7^(b+2j)·11^(h−j−1)+18
- Bit 1 preparation after transfer: 46K·11^h+6

These are obtained by summing the same four, six, and two primitive costs,
respectively; they are not accelerated operations supplied to the source.

## Counts, hashes, and CA constants

| Layer | Controls | Rows |
|---|---:|---:|
| primitive3 | 763 | 995 |
| normalized3 | 792 | 1024 |
| reversible5 | 4520 | 5451 |
| reversible2 | 122622 | 141561 |

All counts equal the predecessor. This is a new fixed literal machine and
therefore a new indexed CA rule, with unchanged numerical geometry only.
No equality or conjugacy of the old and new global CA maps is asserted.
Source SHA-256:
`fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`.
Reversible-five SHA-256:
`2f426dda9743a80d1677bf367f4c75b1522efbd31cd6f07ab59ff7643b4ed31f`.
The rebuild receipt pins every generated file and checks byte-exact fresh
regeneration. The new manifest pins this package, and a historical receipt
records original predecessor preservation. Portable checks require exact
regenerated predecessor output hashes, without reading its external directory.

The unchanged strict-compiler parameters are m=122622,p=66066,a=75495,J=0,
D=509508,S=1019018,Z=20380380. Its indexed construction still has
269,291,358,255 local involution factors and radius upper bound
3,292,955,588,459,274,804. This work never allocated that factor array.

Each source zero update takes one CA microedge; a source move at selected
counter c takes 3+2(Z+c)+delta−4S microedges. Summing over the actually executed
empty startup gives 1,394,018,396 predicted CA microedges. The first TM
transition adds 2,788,036,936, giving 4,182,055,332 through that cut. These are
exact theorem-derived clocks, **not CA executions**. There is no raw CA
throughput claim, smaller-radius claim, or universal-program completion claim.
