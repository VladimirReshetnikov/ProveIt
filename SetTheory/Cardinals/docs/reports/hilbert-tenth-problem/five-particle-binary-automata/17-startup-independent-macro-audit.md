# Independent audit of the literal reversible source

Portable edition note: mathematical content below is inherited from the frozen
producer proof/audit. Statements about original visual inspections and external
release preservation describe historical work, not this offline replay. The
portable checker regenerates a pinned baseline from bundled inputs; no sibling
release is read. See README.md and PROVENANCE.json for exact replay scope.


Audited on 3 October 2026. This audit concerns the explicit machine in this
directory, not a claim that an unexpanded theorem reference is a machine.

## Result and evidence

**PASS.** `independent_audit.py` reconstructs every layer from the preceding
literal layer, checks equality of the complete edge multisets, checks global
determinism and reversibility of both reversible layers, and checks the final
signed-branch serialization. It does not import or call `build_source.py`.
Certificates supply private-state names; their claims about source edges,
targets, primes, macro kinds, and coverage are independently checked.

| Layer | Controls | Literal quadruples |
|---|---:|---:|
| Split three-counter source, fresh start | 763 | 995 |
| Indegree-at-most-two source | 792 | 1,024 |
| Reversible five-counter source | 4,520 | 5,451 |
| Reversible two-counter source | 122,622 | 141,561 |

The history layer has 233 collision pairs. The prime layer has 4,519 source
macros and 2,330 shared destination restorers. The supplementary interpreter
checks cover 2,330 history runs and 27,743 prime runs. They validate the stated
clocks and disabled singleton-test behavior but are not the unbounded-input
proof. That proof is the combination of complete graph reconstruction and the
invariants/ranks below.

The audited `source.json` SHA-256 is
`fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`.
`independent-audit-receipt.json` binds all audited source layers and certificates
to their hashes. Re-run `python independent_audit.py` after changing them.

## Provenance and limitation of the primary-source check

The construction origin is Kenichi Morita, *Universality of a reversible
two-counter machine*, Theoretical Computer Science 168 (1996), 303–320,
[DOI 10.1016/S0304-3975(96)00081-3](https://doi.org/10.1016/S0304-3975(96)00081-3).
The accessible primary-text extraction came from
[the paper PDF](https://www.mobt3ath.com/uplode/book/book-94727.pdf), particularly
printed pp. 308–309 and 314–316. Its constructions use separate tests and moves.

Visual verification of the scan was **not available**: web PDF screenshot
requests failed, and the live download endpoint returned HTML rather than PDF.
No assertion in this audit depends on accepting an ambiguous OCR symbol. The
explicit local graphs were reconstructed and proved directly. This establishes
their mathematical properties even without a visual-transcription certificate.

## Model and global reversibility

A quadruple `(q,i,x,t)` has `x` in `{Z,P,+,-,0}`. Tests preserve all counters;
`Z` is enabled at zero and `P` at positive values. Moves `+` and `-` change
counter `i` by one; `-` is disabled at zero. A `0` move is an identity move.
Every executed quadruple counts as one step, including successful tests.
Counters are always natural numbers.

The checker groups edges by source and, separately, target. Within either
group any pair must consist of complementary `Z` and `P` tests of the same
counter. Thus any group has at most two edges. This is stronger than merely
checking a finite collection of reachable configurations. For every natural
counter vector, at most one outgoing edge is enabled. Every individual edge
is an injective partial map, and the only permitted multiple incoming edges
have disjoint zero/positive ranges. Therefore the global step relation is an
injective partial function on **all configurations**, including configurations
outside the intended simulation encoding.

The final signed serialization is checked row by row: counter 0 maps to side
−1 and counter 1 to side +1; the delta is +1, −1, or 0; a `Z` guard is equality
to zero; `P` and `-` use positivity; the other guards are true. Hence the
primitive and serialized relations coincide, provided the downstream consumer
uses the declared two-natural-counter semantics.

`START` has no incoming edge in all four layers. `HALT` has no outgoing edge.
The final graph is not made absorbing by adding a self-loop at `HALT`.

## Source splitting and indegree normalization

The dependency has 528 instructions: 295 `ADD` and 233 combined `SUB`.
For each combined `SUB i positive zero`, replace its zero behavior by a
`Z` edge to `zero`, and its positive behavior by a `P` edge to a private
state followed by a `-` edge to `positive`. Thus the zero branch costs one
primitive step, and the positive branch costs two. Each `ADD` costs one.

The dependency's initial `init_clear_T` has a self-loop. It cannot serve as
the no-incoming start. A fresh `START` with a single identity edge to it fixes
this, adding exactly one primitive step and preserving every data input.

For a target with ordered incoming edges `e1,...,em`, `m>2`, introduce
`u1,...,u(m−2)`. Redirect `e1,e2` to `u1`, `ej` to `u(j−1)` for
`3≤j≤m−1`, and keep `em` pointed at the target. Chain the new states to
the original target with identity edges. Every new state has indegree two.
Every original operation is followed by a uniquely determined finite chain
of identities. The additional clock for edge `ej` is

    m − max(2,j).

The number of remaining chain states is a strictly decreasing termination
rank. The original target is reached with exactly the original data values.
The checked source needs 29 new chain states and 29 new identity edges.
All normalization edges, including edges into `HALT`, are included in the
next history pass.

## History macro: invariant, termination, and exact clock

Call the additional counters `H` (index 3) and `W` (index 4). At each
normalized-source boundary the intended invariant is `H=h≥0,W=0`, with
the first three counters equal to the simulated data.

A normalized edge that has no conflicting incoming companion remains one
literal edge. It changes only its specified data counter, costs exactly one,
and leaves `H,W` unchanged.

At a colliding pair, designate the incoming edges by `b=0` and `b=1` through
any bijection. The checker verifies exactly that bijection, with no assumed
order of input rows. In this startup-optimized table four assignments are
permuted; `independent-relabel-audit.md` checks those choices independently.
Nothing in the following all-input invariant depends on which edge has which
bit. Each
edge first performs its actual source operation. Then a `W=0` test enters
the transfer loop. This arrangement preserves the source operation's domain.
In particular, an invalid decrement is blocked before the history work.

At the transfer test after `j` completed iterations:

    H = h−j, W = j, 0≤j≤h.

The data counters remain equal to their post-source-operation values.
An iteration tests `H>0`, decrements `H`, increments `W`, and tests `W>0`:
four literal steps. The rank `H` decreases. At `j=h`, the zero test exits
with `H=0,W=h`.

Branch 0 enters the doubling-loop test immediately. Branch 1 performs one
increment of `H` and one positivity test first, so both cases enter that
test with `H=b,W=h`.

At the doubling-loop test after `l` completed iterations:

    H = b+2l, W = h−l, 0≤l≤h.

One iteration tests `W>0`, decrements `W`, increments `H`, tests `H>0`,
increments `H` again, and tests `H>0` again: six literal steps. The rank
`W` decreases. The terminating zero test reaches the original target with

    H = 2h+b, W = 0.

Every decrement in either loop is preceded by an appropriate positive
test; every positivity test after an increment is valid. These observations
and the two decreasing ranks prove that no promised macro input can get
stuck or loop internally.

The full clock, including the simulated source edge, is

    1 + 1 + 4h + 1 + 2b + 6h + 1 = 10h+4+2b.

The formula includes `h=0`: branch 0 costs four and branch 1 costs six.
The guards that make incoming paths disjoint are essential. Transfer-loop
entries distinguish `W=0` from `W>0`. The two joins in the doubling part
distinguish `H=0` from `H>0`. Replacing those tests by identity moves would
invalidate global reversibility.

## Prime encoding and its actual input promise

Use primes `(2,3,5,7,11)` for the five source counters. At a five-counter
boundary encode vector `(a0,...,a4)` by

    A = C·2^a0·3^a1·5^a2·7^a3·11^a4, B = 0,
    C≥1, gcd(C,2·3·5·7·11)=1.

The arithmetic and test macros below preserve the cofactor `C`. Unique
factorization identifies `ai=0` with nondivisibility by its prime, and
`ai>0` with divisibility. Encoded `A` is positive at every boundary,
although intermediate `A` may be zero.

The standard history simulation starts with `H=W=0`, so the clean initial
integer is `C·2^L·3^R·5^T` and the auxiliary physical counter is zero.
The earlier irreversible source's promise for every raw positive integer
does **not** automatically survive this conversion: an initial factor 11
means nonzero `W`, violating the history transfer's clean-work promise.
An arbitrary initial `H` happens to remain harmless to the simulated data
because the history proof holds for every `h≥0`, but this is an explicitly
broader interface, not a reason to ignore the work-counter condition.

## Common transfer phase of prime arithmetic

For multiplication or division at prime `p`, assume `A=N≥1,B=0`.
An initial zero test on `B` enters the transfer loop. At its loop test after
`j` completed iterations:

    A = N−j, B = j, 0≤j≤N.

Each iteration is a positive test on `A`, decrement of `A`, increment of
`B`, and positive test on `B`: four steps. The rank `A` decreases. The
final zero test yields `A=0,B=N`. Including the initial `B` guard, this
phase takes `4N+2` steps.

### Increment of one encoded counter

At the multiplication-loop test after `l` iterations:

    A = pl, B = N−l, 0≤l≤N.

An iteration consists of a positive test and decrement on `B`, `p`
increments of `A`, and one positive test on `A`. It costs `p+3` and
decreases rank `B`. The terminating zero test on `B` exits with `A=pN,B=0`.
The exact complete clock is

    4N+2 + (p+3)N + 1 = (p+7)N+3.

### Decrement of one encoded counter

For an enabled source decrement, write `N=pQ`, `Q≥1`. At the division-loop
test after `l` iterations:

    A = l, B = N−pl = p(Q−l), 0≤l≤Q.

An iteration tests `B>0`, performs exactly `p` decrements on `B`, increments
`A`, and tests `A>0`. It costs `p+3`. The invariant implies that all `p`
decrements are enabled. Rank `Q−l` decreases. The final zero test exits
with `A=Q,B=0` and complete clock

    4N + (p+3)Q + 3 = (5p+3)Q+3.

If `N=pQ+r`, `0<r<p`, the purported source decrement is disabled. The
literal division performs `Q` complete groups, then consumes the remaining
`r` from `B` and blocks at a forced decrement before reaching any source
boundary. This does not spuriously reach `HALT`. A claim that the division
macro terminates successfully for all positive `N` would therefore be false;
its success promise is exactly divisibility.

## Prime zero/positive test and shared restoration

For `A=N≥1,B=0`, write `N=pQ+r`, `0≤r<p`. Division tracks a bounded
remainder in control. At division state `j`, after `k` full groups:

    A = N−pk−j, B = k, 0≤j<p,

whenever the right-hand side is nonnegative. Every consumed `A` unit
requires a positive test and decrement: two steps. Every completed group
requires an increment of `B` and positive test on `B`: two more steps.
The rank is the unconsumed `A`, with at most two group-close steps between
strict decreases. No unbounded auxiliary register is used for the remainder.

The first zero test on `A` occurs at `A=0,B=Q`, remainder state `r`.
The total division clock, including the initial `B=0` guard and final
zero test, is

    2N+2Q+2.

Remainder zero selects the source positive test; remainders 1 through `p−1`
select the source zero test. For a singleton source test, the other exit is
absent. A false singleton test therefore blocks in the division part instead
of reaching an incorrect source boundary.

For the selected destination, restoration enters its shared remainder state
`r`. First it adds `r` to `A`, using one increment and one positive test per
unit, and reaches remainder state zero with `A=r,B=Q`. After `l` full
restoration groups:

    A = r+pl, B = Q−l, 0≤l≤Q.

One group is a positive test and decrement on `B`, followed by `p` pairs
of increment/positive-test on `A`. This costs `2p+2`; rank `B` decreases.
The final zero test on `B` returns to the selected source destination with
`A=N,B=0`. Restoration costs

    2r + (2p+2)Q + 1.

Combining both phases gives the exact test clock

    2N+2Q+2 + 2r+(2p+2)Q+1 = 4N+4Q+3.

Restoration must be shared **per destination**, rather than independently
copied for every incoming test edge. Two private restorers ending with
`B=0` tests at the same destination would have overlapping ranges.
The source's global reversibility guarantees that all tests entering one
destination use the same counter, and at most one incoming zero test and
one incoming positive test exist. Their distinct remainder entries meet
the shared restorer through complementary zero/positive guards. The checker
verifies exactly this structure and all its joins.

## Composition and exact forward time

For a normalized-source run of `m` steps with counter values `v_j` and
history `h_j` at step `j`, let `b_j` be defined only when that step uses a
colliding incoming edge. Define

    h_(j+1) = h_j                    for an unchanged edge,
    h_(j+1) = 2h_j+b_j               for a history-recording edge.

The corresponding five-counter time is exactly the sum of `1` for each
unchanged edge and `10h_j+4+2b_j` for each recording edge.

For the expanded five-counter run, let `N_t` be the encoded integer before
its `t`th edge and `p_t` the affected counter's prime. Its two-counter
clock is the sum of the following exact costs:

| Five-counter operation | Physical forward cost |
|---|---:|
| identity | `1` |
| increment | `(p_t+7)N_t+3` |
| enabled decrement | `4N_t+(p_t+3)(N_t/p_t)+3` |
| enabled zero/positive test | `4N_t+4 floor(N_t/p_t)+3` |

An identity edge preserves the physical pair directly. The other macros
terminate on precisely the promised source inputs and return to a source
boundary with the correct encoding. Private macro states do not coincide
with boundary controls. Thus induction yields equality of every finite
simulated prefix, with the above exact time sums. Infinite source runs give
infinite physical runs because every enabled macro has finite positive
duration. Finite source runs reach `HALT` exactly when the physical run does.
There is no need to posit a uniform constant slowdown, and no such slowdown
is claimed.

For the original 528-instruction program, prepend the one-step fresh entry,
charge one/two steps for each zero/positive combined-`SUB` branch, include
the exact normalization-chain lengths, then apply the history and prime
costs at each actual intermediate state. This is a state-dependent exact
clock, not a runtime claim obtained by extrapolating finite tests.

## Scope of the conclusion

There is no obstruction to this particular literal construction as an
injective partial two-natural-counter machine with separate tests and moves.
The audit does not assert that a different combined-`SUB` instruction set
inherits reversibility. It does not assert successful simulation for arbitrary
unclean auxiliary inputs, an absorbing final state, garbage erasure, or a
new proof that the chosen source TM is universal. Those are separate claims.
The work establishes the explicit source conversion, its global partial
injection, its promised all-input simulation, and its exact forward clocks.
