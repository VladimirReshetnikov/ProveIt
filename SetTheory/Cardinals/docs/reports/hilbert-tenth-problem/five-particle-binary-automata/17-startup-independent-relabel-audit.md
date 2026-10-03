# Independent audit of the startup history relabeling

Portable edition note: mathematical content below is inherited from the frozen
producer proof/audit. Statements about original visual inspections and external
release preservation describe historical work, not this offline replay. The
portable checker regenerates a pinned baseline from bundled inputs; no sibling
release is read. See README.md and PROVENANCE.json for exact replay scope.


Audited 3 October 2026. This note audits the new literal artifacts against the
pinned regenerated baseline for `literal-reversible-source-20261003`. No frozen file,
generator, inherited checker, or inherited proof was edited by this audit.
No cellular-automaton rule table was allocated, and nothing was published.

## Result

**PASS, with a quantified tradeoff and a stronger paired-clean-run result.**
The change is exactly four local permutations of two incoming history labels.
The three-counter dependency, primitive source, and normalized source are
byte-for-byte unchanged. All six distinct clean `T=0` startup collision edges
receive zero. The all-natural global partial-injection property and the
simulation for every promised loader input survive the change.

For every `L,R >= 0` and positive `C` coprime to `2310`, put
`A = C * 2^L * 3^R`. The exact new `T=0` prologue, from `START` through first
arrival at `tm_A0_pop0`, is

    five-counter steps = 24
    physical two-counter steps
      = 76*A + 4*floor(A/5) + 24*floor(A/7) + 48*floor(A/11) + 62.

It ends with five-counter state `(L,R,0,0,0)` and physical state `(A,0)`.
In particular `A=1` takes **138 actual literal two-counter steps**.

The optimization is not faster at every arbitrary equal-history macro input.
A fully traversed counterexample below costs 104 new versus 28 old steps.
Nevertheless, **paired runs from the same clean loader input are never slower
at corresponding normalized-source boundaries**. After the prologue, each
history-recording macro is strictly faster in the new run. This stronger
claim follows from the history gap and an order-preserving embedding of
literal five-counter operations, not from a benchmark or the assertion that
smaller final history alone implies less work.

## Evidence and reproducibility

Run `python independent_relabel_check.py` or `python -O
independent_relabel_check.py` in this directory. The checker:

- derives collision pairs from actual `normalized3.json` rows;
- derives the prescribed label ordering from their serialized order and the
  six-edge zero policy, before comparing it with certificate claims;
- verifies exactly the four stated pair permutations and all unchanged pairs;
- reconstructs the full five-counter graph from those checked bijections;
- independently reconstructs every two-counter arithmetic, test, and shared
  restoration graph from the preceding literal rows;
- checks complete edge-multiset equalities and private-state separation;
- checks outgoing-domain and incoming-range separation on all configurations;
- checks all signed `source.json` branches against the physical primitives;
- executes 1,398 history-macro traces, 13 complete physical `T=0` prologues,
  and eight five-counter prologues with `T=0,...,7`;
- tests 336 monotone embeddings using actual five-counter suffix traces,
  covering all four bit pairs and multiple history gaps and cofactors;
- executes both sides of the equal-history companion counterexample;
- checks that the loader's `natural` and `from_counters` function ASTs are
  unchanged, and that audited files did not change during the run.

The deterministic receipt `independent-relabel-receipt.json` records all
input hashes, counts, and replay results. It does not contain wall-clock
measurements. The checker uses explicit verification exceptions, so optimized
Python cannot turn checks off. The finite runs corroborate the formulas;
they are not the proof of unbounded simulation.

New `source.json` SHA-256:
`fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`.
Frozen `source.json` SHA-256:
`38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a`.

The dimensions are unchanged: 4,520 five-counter controls and 5,451 rows;
122,622 two-counter controls and 141,561 rows; 233 collision pairs. This is
a labeling/runtime optimization, not a reduction in the machine's dimensions.

## Exact policy and collision audit

The prescribed zero edges are `entry`, `v0000z`, `n0001e0`, `n0001e1`,
`n0001e2`, and `n0001e3`. They enter six different collision targets. The
first two were already zero-labeled. The only changes are:

| Collision target | Old bit 0 / bit 1 | New bit 0 / bit 1 |
|---|---|---|
| `n0001_1` | `v0028` / `n0001e0` | `n0001e0` / `v0028` |
| `n0001_2` | `v0066` / `n0001e1` | `n0001e1` / `v0066` |
| `n0001_3` | `v0155` / `n0001e2` | `n0001e2` / `v0155` |
| `tm_A0_pop0` | `v0303z` / `n0001e3` | `n0001e3` / `v0303z` |

The first three companions are data-counter-0 increment edges from
`tm_A1_0_write`, `tm_B1_0_write`, and `tm_E0_0_write`. The fourth is the
data-counter-2 zero test from `tm_I0_0_restore`. Each pair remains a
bijection onto `{0,1}`. No target receives two zero-tag requests.

Certificates are not accepted as an authority for which incoming edge should
get which bit: the independent checker pins the policy above against the
literal normalized rows. It then checks every generated edge, including
all joins, transfer loops, doubling loops, and shared prime restorers.

## Why global partial injection survives

Each literal primitive is an injective partial map on natural counters.
An increment and an identity are always enabled; a decrement requires a
positive affected counter; a zero or positive test preserves all counters
and has its declared domain. For every source control, the actual outgoing
rows are either a singleton or complementary `Z/P` tests on the same counter.
For every destination control, the actual incoming rows satisfy the same
condition. Thus source domains do not overlap, and destination ranges do not
overlap. This establishes a partial injective step function on **all natural
counter configurations**, even unencoded or unclean ones.

This whole-graph condition is checked independently for both reversible
layers. Signed serialization is checked row by row, so the conclusion also
holds for `source.json` with its declared natural-counter interpretation.
`START` still has no incoming edge and `HALT` has no outgoing edge.

A zero tag at zero history need not change the history integer. This creates
no collision: at the same destination, the other incoming edge produces odd
history instead of even history, and all internal joins retain their
disjoint tests. The history integer alone need not encode the length of an
arbitrary bit string; reversibility concerns the complete machine state.

## All promised inputs, not only the empty tape

The input domain remains

    L,R,T in N,
    C >= 1, gcd(C, 2*3*5*7*11)=1,
    physical START input (C*2^L*3^R*5^T, 0).

At a normalized-source boundary the history invariant is `(H,W)=(h,0)`
for arbitrary `h>=0`. For either newly chosen bit `b`, a recording macro
performs the original source operation first, transfers `H` to `W`, and
then doubles back. During transfer after `j` iterations, `(H,W)=(h-j,j)`;
during doubling after `l` iterations, `(H,W)=(b+2l,h-l)`. Ranks `H` and
then `W` decrease. The macro therefore finishes on every enabled source
input, with the exact post-source data and

    H' = 2*h+b, W' = 0,
    five-counter clock = 10*h+4+2*b.

Changing the bijection changes neither the invariant nor either termination
argument. A noncolliding edge still preserves `H,W` in one step.

At five-counter boundaries, the prime invariant is

    N = C*2^a0*3^a1*5^a2*7^H*11^W, auxiliary physical counter = 0.

Unique factorization gives the correct data tests and preserves the same
cofactor `C`. The actual prime graphs are the checked templates in
`independent-macro-audit.md`: transfer ranks decrease the consumed integer;
multiplication and restoration decrease the remaining work counter;
division of an enabled decrement consumes a whole number of prime-sized
groups. Tests restore the original integer and select the right outcome.
Private states are disjoint from macro boundaries and from other private
allocations, except explicitly shared destination restorers.

The exact physical costs for an enabled five-counter primitive, at encoded
integer `N` and affected prime `p`, remain:

    identity:   1
    increment:  (p+7)*N+3
    decrement:  4*N+(p+3)*(N/p)+3
    test:       4*N+4*floor(N/p)+3.

These facts prove, by induction on every finite normalized-source prefix,
the correct data projection and successful finite expansion for every
promised `L,R,T,C`. Infinite source runs expand to infinite physical runs;
finite halting runs reach `HALT` exactly when their source does. The
unchanged splitting and normalization connect these runs to the original
three-counter program. The optimization does not introduce a new
universality premise or attempt to re-prove the cited source TM's theorem.

Global injection should not be confused with successful simulation from
all arbitrary physical pairs. In particular, the loader still excludes a
factor 11 representing dirty `W`. No new claim is made for such inputs.
Nor does this construction erase history or make `HALT` absorbing.

## Exact startup clocks

For `T=0`, the six normalized edges are precisely the selected zero edges.
Their old bits were `0,0,1,1,1,1`; their new bits are `0,0,0,0,0,0`.
Starting at `H=W=0`, each new history macro has four steps. The actual
24-row path consists of five identity operations, one `T=0` test, six
`H=0` tests, and twelve `W=0` tests. All preserve encoded `A`.

Let `F_p(A)=4*A+4*floor(A/p)+3`. The full cost is therefore

    5 + F_5(A) + 6*F_7(A) + 12*F_11(A)
      = 76*A + 4*floor(A/5) + 24*floor(A/7) + 48*floor(A/11) + 62.

This exact formula holds for all promised `L,R,C`, regardless of magnitude.
The physical replay examples include `A=1,2,3,4,6,9,13,17,26,27,81,243,351`.
For example, the clocks at `A=1,13,351` are `138,1130,29706`.

For every clean initial `T>=0`, each successful clearing decrement records
a one and follows one nonrecording positive test. Thus after the `T`
clears the history is `h=2^T-1`. The zero exit and four chain edges append
five zeros in the optimized graph. Hence

    new final H = 32*(2^T-1)
    old final H = 32*(2^T-1)+15.

The entry costs four. The clearing iterations cost
`sum(i=0..T-1, 10*(2^i-1)+7)`. The five final zero macros cost
`sum(j=0..4, 10*2^j*(2^T-1)+4)`. Consequently

    new five-counter prologue = 320*2^T - 296 - 3*T,
    old five-counter prologue = new five-counter prologue + 118.

These formulas do not assert a small physical clock for `T>0`: nonzero
history still enters the exponent of 7. The physical all-input proof is
valid even when traversing a run would be impractical.

## Equal-history tradeoff

The four companion edges gain the one tag that the startup path loses.
At equal incoming history `h`, their new final history is `2*h+1` instead
of `2*h`, and their five-counter macro clock increases by two.

A literal counterexample is the `v0303z` macro, started at
`tm_I0_0_restore` with five-counter values `(0,0,0,0,0)` and `C=1`.
Its physical starting pair is `(1,0)` in either machine. The frozen graph
reaches `tm_A0_pop0` with `(1,0)` after **28** steps. The optimized graph
reaches it with `(7,0)` after **104** steps. Both paths were fully traversed.
This rules out a universal pointwise speedup at arbitrary equal-history
states. It is not a counterexample to paired clean-input domination,
because those corresponding runs have different histories at this stage.

## Stronger theorem: paired clean runs are never slower

Compare the old and new runs from the **same** promised loader input at
corresponding normalized-source boundaries. Their data agree. After the
prologue, let `d=H_old-H_new`; the formulas above give `d=15`. Nonrecording
edges leave `d` unchanged, and every recording edge updates it by

    d' = 2*d + b_old - b_new >= 2*d-1 > 0.

Thus `d` stays positive indefinitely. To obtain a time result from this
value inequality, the following independent operation-embedding argument
is necessary.

For any `h>=0,d>=1`, compare one history macro at old input `h+d` and new
input `h`, allowing any old/new bit pair. The source data operation is the
same. Match it, the first `W=0` test, and the first `h` transfer iterations.
At each of these matched positions the old encoded integer is at least
the new one (ratio `7^d` in the transfer). Skip the old run's extra `d`
transfer iterations, then match the `H=0` exit tests. Here both histories
are zero and the old work counter is larger by `d`, giving ratio `11^d`.

Handle preparation and surplus doubling as follows:

- Both bits zero: let the old run finish `d` extra doubling iterations;
  its `W` then agrees with the new run's and its `H` exceeds it by `2d`
- Both bits one: match their two one-preparation steps, then do the same
- Old bit one, new bit zero: skip the old preparation, then `d` old
  doubling iterations; the remaining history gap is `2d+1`
- Old bit zero, new bit one: in the old first doubling iteration, skip
  `W>0` and `W-`, then match the new `H+` and `H>0` preparation steps to
  the old first `H+`,`H>0` pair. Their encoding ratio is `11^(d-1)>=1`.
  Finish that old iteration and `d-1` additional old iterations. Work
  counters now agree and the history gap is `2d-1>=1`

Now match all the new run's doubling iterations and its final `W=0` test
to the old remainder. The order of the matched operations is preserved,
no old operation is used twice, and each matched pair uses the same prime
and operation. The old encoded integer is always at least the new one.
Every physical cost function displayed above is nondecreasing in its
encoded integer on its enabled domain. The old macro also has unmatched
positive-cost operations. Therefore its total physical clock is strictly
larger, independent of the bit pair.

For a nonrecording normalized edge, the same prime-clock monotonicity gives
new cost no larger than old cost; identities can have equal cost. During
the prologue the runs initially agree, and the first changed bit is old
one/new zero at equal history. Skipping the old two preparation operations
embeds the new suffix, while all later matched old doubling encodings are
larger. Thus that first change already strictly improves time; thereafter
the positive-gap argument applies. This proves the claimed cumulative
and per-macro domination from clean inputs.

The 336 actual-row suffix-embedding checks are a finite supplement to this
all-`h,d` construction. This theorem concerns the literal two-counter clock
at corresponding simulated boundaries. It does not, by itself, assert
pointwise physical-state ordering, arbitrary-state domination, or a new
cellular-automaton-clock theorem.

## Remaining limitations

This audit found no label conflict, graph mismatch, injection defect, or
loss of promised-input simulation. The exact small clock is specific to
the `T=0` prologue. Later computation can still make history and encoded
integers extremely large. The optimization changes no row counts or target
construction size. Claimed CA clocks require their own saved-row/compiler
clock analysis; this audit did not instantiate a CA or simulate its rule
list. Existing primary-paper provenance and source-universality limitations
remain as stated in the original independent macro audit.
