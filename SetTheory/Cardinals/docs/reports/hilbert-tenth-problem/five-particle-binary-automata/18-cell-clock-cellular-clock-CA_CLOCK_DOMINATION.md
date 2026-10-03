# Cellular-clock domination for the fixed history-orientation templates

3 October 2026. Proof addendum in a new directory. The Report 16/17 source,
proof, trace, and manifest files are not modified. All times below count
**CA microedges**, equivalently iterations of the compiled CA on its forward
admissible plus orbit. They do not count host-language execution time or
applications of individual local involution factors. No gate array is built.

## 1. Result and exact scope

The remaining CA-clock comparison closes positively for the exact templates
in `reversible-initialization-optimization-20261003` and their frozen predecessor
`literal-reversible-source-20261003`:

1. On every common clean loader input
   `(START, C·2^L·3^R·5^T, 0)`, where `L,R,T` are natural,
   `C≥1`, `gcd(C,2310)=1`, and the history/work exponents start at zero,
   the optimized rule reaches every corresponding normalized-source boundary
   no later in CA microedges than the predecessor. Arrival is strictly earlier
   by the first TM cut and at every subsequent corresponding boundary.
2. Fix any finite enabled normalized-source trace, common initial data,
   history `h0≥0`, work `W=0`, and such a common cofactor `C`. Within the
   **static orientation class of the fixed normalized source, fixed recorder,
   fixed prime macros, and fixed strict binary-five compiler**, orienting each
   pair so that its first encountered incoming edge has bit zero minimizes
   cumulative CA arrival time at every normalized boundary simultaneously.
   A competing orientation ties through exactly the prefixes in which no
   encountered pair differs; it becomes strictly slower at its first
   encountered disagreement and remains strictly slower thereafter.
3. All `2^233` orientations have the same compiler size parameters, hence
   the same per-move constant `λ=36,684,691`. Exactly `2^227` orientations
   attain the complete clean-startup minimum for every promised loader input:
   the six startup first-encounter choices are fixed, and the other 227 are free.

These claims compare corresponding boundaries of different fixed CA rules.
They neither order arbitrary intermediate configurations nor assert equal-time
state alignment, conjugacy of the global CA maps, a uniform speedup ratio,
or global resource optimality outside the precisely stated template class.
The finite trace is given; the result supplies no procedure deciding whether
an arbitrary computation halts or discovering all first encounters uniformly
on an arbitrary unbounded run. All arithmetic and tests performed by the
simulated machines are charged. Constructing the initial encoded integer,
writing its spatial representation, and the host arithmetic used to calculate
a time formula are external input preparation, not additional claimed CA work.

## 2. Literal-row potential identity

For a literal row moving selected natural counter `c` by `δ∈{-1,+1}`,
the existing compiler's travel-time theorem gives

    τ(c,δ) = 3 + 2(Z+c) + δ − 4S.

An enabled decrement has `c≥1`. Set `λ=3+2Z−4S`. Then

    τ(c,δ) = λ + |(c+δ)²−c²|.

Indeed the last term is `2c+1` for increment and `2c−1` for enabled
decrement. Every zero-update row, including every identity and successful
guard test, costs exactly one microedge. Therefore for any finite enabled
literal two-counter path, writing `M` for its number of moving rows and `U`
for its number of zero-update rows,

    Θ = λM + TV(A²) + TV(B²) + U,

where total variation is the sum of absolute successive differences along
the actual path. It is **not** merely an endpoint potential difference:
turnarounds contribute in both directions. This identity charges every row.

The strict compiler has `D=2(m+2p_move)`, `S=2D+2`,
`Z=40D+60+2J`, so

    λ = 72D+115+4J > 0.

For these sources, `m=122622`, `p_move=66066`, `a=75495`, `J=0`,
`D=509508`, `S=1019018`, `Z=20380380`, giving the stated λ.
The lemmas below also hold as abstract weighted-clock statements for every
real `λ>0`; actual CA microedge counts use the integer compiler value.

## 3. Whole prime-macro clocks, derived from actual rows

Start a five-counter primitive's prime macro with physical counters `(N,0)`,
`N>0`, and a selected prime `p∈{2,3,5,7,11}`. The cofactor is held fixed and
the encoded other registers may be arbitrary naturals. A decrement requires
`p|N`; a positive test requires `p|N`, and a zero test requires `p∤N`.
These are the actual prime encoding domains, not assumptions silently dropped
from the time formulas. A disabled branch is not assigned a successful clock.

### Increment

The row graph first transfers all `N` units from `A` to `B`, then removes
each `B` unit and increments `A` exactly `p` times. Thus `A` travels
`N→0→pN`, while `B` travels `0→N→0`:

    M=(p+3)N,   TV(A²)+TV(B²)=(p²+3)N²,   U=4N+3.

The three isolated tests are the entry `B=0`, transfer-exit `A=0`, and
final `B=0`; each transfer iteration has two positive tests, and each
return iteration has two positive tests. Hence

    I_p(N)=(p²+3)N² + λ(p+3)N + 4N + 3.

### Enabled decrement

Write `N=pQ`. Transfer again gives `(0,N)`. The return loop removes
`p` units of `B` per iteration, adding one unit of `A`, and ends at `(Q,0)`.
Thus `A` travels `N→0→Q`, while `B` travels `0→N→0`:

    M=3N+Q,   TV(A²)+TV(B²)=3N²+Q²,   U=2N+2Q+3,

and

    D_p(N)=3N²+Q² + λ(3N+Q) + 2N+2Q+3.

The decrement loop's `p` separate decrement rows are all counted.
The divisibility promise ensures it never encounters an incomplete block.

### Successful test, either branch

Write `N=pQ+r`, `0≤r<p`. The scanner decrements `A` one unit at a time,
tracks the residue in finite control, and increments `B` once per completed
block of `p`. Its chosen successful exit has `(A,B)=(0,Q)` and residue `r`.
The destination-restoration graph first adds back the residual `r` units,
then restores `p` units for each removed unit of `B`. It ends at `(N,0)`.
Including that shared destination restoration, the monotone phases are
`A:N→0→N`, `B:0→Q→0`. The test's clock includes the restoration exactly once:

    M=2(N+Q),   TV(A²)+TV(B²)=2(N²+Q²),   U=2(N+Q)+3,

    T_p(N)=2(N²+Q²)+2(λ+1)(N+Q)+3.

The zero-update count is entry test 1, scanner positive tests `N+Q`,
scanner exit test 1, restoration positive tests `N+Q`, final test 1.
This remains correct when `Q=0` and for either enabled residue branch.
An identity costs 1 and preserves `(N,0)`.

These derivations use precisely the graphs serialized by `build_source.py`,
including tests, restore blocks, and arithmetic repetitions. They do not
replace those repetitions by unit-cost integer multiplication or division.

### Monotonicity

For fixed `p` and `λ>0`, the increment polynomial is strictly increasing
on positive integers. The decrement polynomial, written in positive `Q`,
is `(3p²+1)Q²+[λ(3p+1)+2p+2]Q+3`, strictly increasing on its enabled domain.
For tests, both `N` and `floor(N/p)` are nondecreasing as `N` grows, and
the positive `N²` term is strictly increasing; restricting to either enabled
test domain preserves this property. Identity is constant. All successful
macro clocks are positive.

## 4. Why λ is identical throughout the static orientation class

Fix the normalized three-counter graph and its 233 collision pairs.
Changing one orientation swaps the two source-operation payloads feeding
the pair's private `B0T1` and `B1T1` controls. The two transfer graphs and
the shared doubling graph are unchanged. Source operations are copied once
each, with their original source, selected counter, and symbol. The incoming
source operation assigned to each branch entry can change, but the pair's
multiset of operations cannot.

Consequently all of the following signatures are invariant:

- The five-counter control count, `4520`, and complete `(counter,symbol)`
  row multiset, of size `5451`
- The outgoing-source group multiset, classified by selected prime and
  either identity, increment, decrement, or available test set `{Z}`, `{P}`,
  `{Z,P}`. At original normalized sources the outgoing operations do not
  change; at private recorder controls the operation patterns are fixed
- The multiset of **destination restore blocks**, classified by prime.
  Internal recorder test destinations do not change. A swapped source
  operation can move the need for a restore block from `B0T1` to `B1T1`,
  or conversely, but it simply permutes this pair's incoming-operation
  multiset. A branch entry has one such incoming source row. Thus the
  number of restored destinations of each prime is unchanged

The last point is necessary: row counts alone would not establish the
number of shared destination restorers.

For each outgoing source group the exact additions to the literal graph are:

| Group | New private controls | Literal rows | Moving rows |
|---|---:|---:|---:|
| Identity | 0 | 1 | 0 |
| Increment or decrement at p | p+7 | p+10 | p+3 |
| Test set E at p | 2p+2 | 2p+3+(p−1)·1[Z∈E]+1[P∈E] | p+1 |
| Each destination restore block at p | 2p+2 | 2p+3 | p+1 |

Prefix naming keeps these private controls distinct, and the original 4520
controls are included once. Summing the invariant signatures gives
`122622` controls, `141561` rows, `66066` moving rows and `75495` zero-update
rows for **every** orientation. All guards have the same class cut `J=0`.
Hence `D,S,Z,λ`, local-factor counts and numerical radius bound are identical
throughout the class. Row/control order and the indexed rule itself can change;
no equality of rules follows. The recorder injection proof uses only that
incoming labels are distinct, so every class member retains the same validity
and promised-input completion arguments.

The included checker derives these signatures from actual rows, verifies
that they predict the serialized literal counts, and checks all 233 single
pair flips. The independent audit additionally reconstructs every row and
checks the all-flipped orientation. The universal invariance conclusion is
the local multiset proof above, not an inference from random samples.

## 5. Clock-preserving use of the recorder embedding

Consider the same recording source edge in two executions with equal data,
clean `W=0`, incoming histories `h+d` and `h`, and bits `a,b` respectively.
Its five-counter operation word is

    source operation; W=0;
    (H>0,H−,W+,W>0)^h; H=0;
    (H+,H>0)^b;
    (W>0,W−,H+,H>0,H+,H>0)^h; W=0.

This word counts a test as its own primitive. For `d≥1`, inject the smaller
word into the larger word in chronological order:

1. Match the source operation, `W=0`, and its first `h` transfer iterations.
   The larger encoded input is `7^d` times the smaller one
2. Let the larger run execute its `d` surplus transfer iterations, then
   match `H=0`. The ratio is `11^d`
3. If `a=b=1`, match preparation at ratio `11^d`. If `a=1,b=0`, skip the
   larger preparation. For `a=b=0`, neither has preparation. In these three
   cases let the larger run finish `d` surplus doubling iterations
4. If `a=0,b=1`, skip `W>0,W−` in the larger run's first doubling iteration,
   then match the smaller preparation `H+,H>0` to its first `H+,H>0` pair.
   The ratio here is `11^(d−1)≥1`. Complete this iteration and the next
   `d−1` surplus iterations
5. Both runs now have `W=h`; their history gap is `2d+a−b≥1`. Match all
   remaining `h` doubling iterations and the final `W=0`. Throughout these
   matched operations the encoded ratio is `7^(2d+a−b)≥7`

Every smaller operation is matched once; every matched pair has the same
symbol and selected prime, both are enabled, and the larger encoded input
is no smaller. Section 3 therefore compares their **whole CA macro clocks**,
not merely their literal row counts. Common λ is guaranteed by Section 4.
All unmatched larger operations have positive CA clock, including the
surplus transfer iterations. Thus the larger-history recording macro costs
strictly more for all four bit pairs.

At equal history and equal bit the costs agree. At equal history with
`a=1,b=0`, match the common prefix, skip the larger preparation, and match
the doubling suffix and final test with encoded ratio 7. This gives strict
increase. For a nonrecording edge, the identical data operation at encoded
inputs ordered by history has nondecreasing cost; identity may tie.

This is precisely why missing intermediate-state alignment is no obstacle:
the injection is between complete five-counter primitives, each of which
has its own proven literal expansion and CA clock. It is not an injection
between arbitrary instantaneous physical configurations.

## 6. Paired predecessor/optimized runs and first encounters

For clean-loader paired runs the normalized data/control path is identical.
Histories agree until the first of the four changed startup assignments;
each changed startup assignment has predecessor bit 1 and optimized bit 0.
The preexisting prologue recurrence gives end histories

    H_old=32(2^T−1)+15,    H_new=32(2^T−1).

The changed edge at equal history costs strictly more in the predecessor.
Every subsequent recording edge preserves a positive gap because
`d'=2d+b_old−b_new≥2d−1≥d≥1`; nonrecording edges preserve it. After startup,
the gap is at least 15 forever. Section 5 compares all subsequent macro
costs, so cumulative old-minus-new CA time can never shrink. Induction
proves the boundary statement of Section 1 for every finite prefix of
any promised run. No assumption that the run eventually halts is needed.

For first-encounter orientation G on a fixed finite trace, any competitor A's
first encountered disagreeing pair must be on that pair's first encounter:
swapping a pair changes both member labels. Thus at the first disagreement
`b_A=1,b_G=0`, creating history gap 1 and a strict CA clock difference.
Thereafter `d'=2d+b_A−b_G≥1`, so Section 5 propagates the cumulative strictness.
Before that edge every clock agrees. This proves all prefix inequalities
and their exact equality characterization. Repeated visits are included.

For all clean prologues the same six pair members are first encountered:
`entry,v0000z,n0001e0,n0001e1,n0001e2,n0001e3`. Hence one choice serves the
whole loader family, and the other 227 choices cause genuine startup ties.
This is an assignment count, not a count of nonisomorphic machines.

## 7. Exact clean T=0 minimum and replay

For `T=0`, let `A=C·2^L·3^R`. The optimized startup has five identities,
one successful test at prime 5, six at prime 7 and twelve at prime 11,
all at the same encoded integer A. Write `q_p=floor(A/p)`. Its exact minimum
CA startup clock within this static class is

    38A² + 2q_5² + 12q_7² + 24q_11²
    + 2(λ+1)(19A+q_5+6q_7+12q_11) + 62.

The loader promise makes all these zero tests enabled. At `A=1`, this is
`38λ+138=1,394,018,396`. It must not be used for nonzero T.

The checker re-traverses the actual serialized literal rows and compares
every control, counter pair, branch name, and per-row clock to the saved traces:

| Segment | Actual literal rows replayed | Theorem-derived CA microedges |
|---|---:|---:|
| Empty startup | 138 | 1,394,018,396 |
| First TM transition after startup | 210 | 2,788,036,936 |
| Continuous run through that first TM cut | 348 | 4,182,055,332 |

It independently sums the closed prime-macro clocks over the 24-step and
22-step saved five-counter traces, obtaining the same totals. Billions of
CA iterations have **not** been executed. This is exactly one TM transition,
not a completed universal computation.

## 8. Additional exact recorder formula and verification

For reproducible arithmetic tests, let `K=C·2^L·3^R·5^T`, `gcd(K,77)=1`.
Exclude the original normalized data operation from the recorded suffix.
One transfer iteration whose after-decrement encoded integer is X costs

    616X² + (76λ+60)X + 12.

One doubling iteration whose after-decrement encoded integer is Y costs

    8208Y² + (266λ+208)Y + 18.

Bit-one preparation at encoded integer V costs

    152V² + (26λ+20)V + 6.

For `h≥0`, define integral geometric sums

    U1=(11^h−7^h)/4,       U2=(121^h−49^h)/72,
    V1=(49^h−11^h)/38,    V2=(2401^h−121^h)/2280.

The full suffix clock for incoming history h and bit b is

    T_11(K·7^h)
    + 616K²U2 + (76λ+60)KU1 + 12h
    + T_7(K·11^h)
    + b[152K²·121^h + (26λ+20)K·11^h + 6]
    + 8208K²·49^b V2 + (266λ+208)K·7^b V1 + 18h
    + T_11(K·7^(2h+b)).

Each sum telescopes directly from actual operation clocks; the formulas
also give zero at h=0 for the empty iteration blocks. The code checks this
against explicit five-counter primitive words, and checks prefix inequalities
for all 64 startup assignments on 64 parameter choices. These finite checks
corroborate, rather than replace, the unbounded mathematical proof.

Run `python clock_verify.py`, then `python -O clock_verify.py --output
clock-receipt.optimized.json`. The independent audit has separate code and
receipts. Every verification uses explicit exceptions, so optimization does
not remove its checks. Receipts state exact test counts and distinguish
source-row replay from theorem-derived CA time.

## 9. What this settles, and useful next questions

The explicit CA-clock gap in the Report 17 first-encounter addendum is
settled within its existing static template class. The prior correct caveats
about arbitrary equal-history states, intermediate alignment, wall-clock
throughput, and architecture-wide resource optimality still apply.

Useful separate questions, not claims of this addendum:

- Can one derive a compact exact CA clock for the full nonzero-T startup,
  using the suffix formula without enumerating its enormous physical path?
- What tradeoffs change if the recorder, prime ordering, or compiler geometry
  itself may vary? The orientation proof does not compare those families
- For a supplied finite trace, how can a user-facing certificate record its
  first encounters and predicted arrival clocks without storing huge numbers
  in decimal? A verified symbolic or hexadecimal representation could help

No literature novelty, priority, lower bound, or unrestricted optimality is
claimed. The mathematical conclusion is deliberately tied to the fixed,
fully charged, validated construction above.
