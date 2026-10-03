# First-encounter optimality for static history orientations

Date: 3 October 2026. This is a proof-only addendum to the frozen startup
optimization package. No source, checker, recorded trace, or generated table
is changed. The comparison is confined to per-pair history-bit assignments
inside the existing normalized source, recorder, and prime-expansion templates.

## 1. Setting and theorem

Fix a finite enabled normalized-source trace

    q_0 --e_1--> q_1 --e_2--> ... --e_n--> q_n,

including its natural three-counter data values. Start every compared
simulation with the same history h_0 >= 0, clean work counter W=0, and
positive cofactor C coprime to 2310. At a physical boundary the counters are
(C*2^L*3^R*5^T*7^H, 0), since W=0. Each static orientation assigns the
two incoming edges of every recording collision pair bijectively to {0,1}.
Nonrecording edges, data operations, normalization, and all macro templates
are fixed. A recording edge labelled b updates H to 2H+b and restores W=0.

Define the first-encounter orientation G by scanning the finite trace. When
an edge first enters a previously unencountered recording pair, assign that
edge bit 0 and its companion bit 1. Assign unseen pairs arbitrarily. Here
“encounter” means traversing an incoming edge; merely starting at a pair's
target control does not count as an encounter.

**Theorem.** Among all static orientations in this class, G simultaneously
minimizes, at every normalized boundary q_i:

1. the history value H_i;
2. the cumulative literal two-counter arrival clock from q_0.

If an alternative orientation A first differs on a pair encountered by e_j,
then histories and corresponding macro clocks agree before that edge, and
at q_j and every later boundary the alternative has strictly greater history
and strictly later cumulative arrival. An orientation differing only on
unseen pairs remains tied throughout this trace. Equality of the clocks
and counter operations does not assert byte-identical private control names
in separately generated tables.

## 2. History proof, including repeated pair visits

If two static orientations differ on a pair, they disagree on both of its
incoming edge labels. Therefore the first disagreement encountered along
the trace occurs on that pair's first encounter. At this edge G uses 0 and
A uses 1. Their incoming histories agree, so the outgoing gap is

    d = H_A - H_G = 1.

A subsequent nonrecording edge preserves d. At a recording edge, even when
it revisits either member of a previously encountered pair,

    d' = 2d + b_A - b_G >= 2d - 1 >= 1.

The gap can never close. Before the first disagreement the histories agree.
This proves every-prefix history optimality, without assuming that each
collision pair is used only once. It also proves that equality through the
whole trace occurs exactly when all encountered pair orientations agree.

Equivalently, after k recording events,

    H_k = 2^k h_0 + sum(j=1..k, b_j 2^(k-j)).

The first-encounter policy gives the lexicographically smallest feasible
recording-bit sequence among static orientations. The leading differing
bit outweighs all subsequent opposite bit differences, including those
forced by repeated visits.

## 3. Literal-clock lemma

The history inequality alone is not sufficient for a runtime conclusion.
The required clock comparison follows from the exact recorder and prime
macros already independently reconstructed in this package.

For encoded positive integer N, a five-counter primitive expands to:

- identity: 1 literal step;
- increment at prime p: (p+7)N+3;
- enabled decrement: 4N+(p+3)(N/p)+3;
- either successful test: 4N+4 floor(N/p)+3.

Each cost is nondecreasing in N on its enabled domain. The two histories
being compared accompany equal data, and W=0 at each normalized boundary.
Thus a nonrecording edge cannot cost less with a larger history. For a
recording edge the following stronger facts hold:

- At equal incoming history, bit 1 costs strictly more than bit 0;
- If the alternative incoming history exceeds the first-encounter history
  by d>=1, its recording macro costs strictly more, regardless of its bit
  and the first-encounter bit.

For completeness, here is the operation-level proof. Write the smaller
history as h. Match the source data operation, the W=0 test, and the first
h transfer iterations in chronological order. In the larger-history macro
the encoded integer at these matched positions is 7^d times as large.
Allow its d surplus transfer iterations, then match the H=0 exit test;
its encoded integer is now 11^d times as large.

For bits (b_A,b_G)=(0,0), let A execute d surplus doubling iterations,
then match the remaining h iterations and the final W=0 test. Their W
values agree, and A's H exceeds G's by 2d. For (1,1), first match the two
preparation rows, then do the same. For (1,0), skip A's preparation and d
surplus doubling iterations; the remaining H gap is 2d+1.

For the difficult case (0,1), use A's first doubling iteration to host G's
preparation: skip its W>0 and W- rows, then match G's H+ and H>0 rows to
A's first H+/H>0 pair. The encoded ratio is 11^(d-1)>=1. Finish that old
iteration and d-1 further surplus iterations. W now agrees, while the H
gap is 2d-1>=1. Match G's remaining doubling iterations and final W=0.

In every case this is an order-preserving injection from the smaller
macro's primitive operations into the larger macro's operations. Matched
operations use the same counter and symbol, with no smaller encoded input
in A. All their literal costs are therefore ordered correctly; unmatched
operations in A have positive cost, proving strictness. For equal incoming
histories and bits (1,0), common transfer operations agree; skip the two
bit-1 preparation rows and match the doubling suffix with H gap 1. This
proves the equal-history strict comparison too.

The full recorder invariants, including the actual row patterns and all
natural input scope, appear in `independent-macro-audit.md` and
`independent-relabel-audit.md`. This argument is an unbounded mathematical
comparison, not an extrapolation from executed sample traces.

## 4. Cumulative clock proof

Before the first encountered orientation disagreement, all corresponding
macro clocks agree. At the first disagreement, incoming histories agree
and the alternative uses bit 1 rather than 0, so its macro takes strictly
longer. At every later normalized boundary the history gap is positive by
Section 2. The clock lemma shows that each subsequent alternative macro
costs at least as much; each recording macro costs strictly more.

Adding these per-edge clocks proves the theorem simultaneously at every
prefix. All macros terminate on their promised inputs by the existing
rank proofs, so every finite arrival clock used here is well-defined.

This theorem compares arrival times at corresponding normalized boundaries.
It does not claim pointwise ordering of all intermediate physical states,
raw CA evaluation time, or a fixed multiplicative speedup ratio.

## 5. Simultaneous optimality of every clean startup

For every natural L,R,T and positive C coprime to 2310, the normalized
startup trace is exactly

    entry;
    (v0000p, v0000d) repeated T times;
    v0000z;
    n0001e0; n0001e1; n0001e2; n0001e3.

The data counters L and R and cofactor C do not change this control trace.
The pair entering init_clear_T is first encountered through entry. Each
v0000d later revisits its companion in that same pair. The v0000p edges
are nonrecording. The five subsequent first encounters are through v0000z
and the four merge-chain edges. Consequently the first-encounter zero
choices are, for every T,

    entry, v0000z, n0001e0, n0001e1, n0001e2, n0001e3.

These are exactly the six choices in the frozen optimized source. Thus
its prologue is history-minimal and literal-clock-minimal at every
normalized prefix, simultaneously for the entire original L,R,T,C loader
domain, among all static orientations of these fixed templates.

All six pairs are encountered even when T=0. Any assignment that differs
on any of them is strictly slower at the final startup boundary; choices
at the other 227 of the 233 recording pairs are irrelevant to startup.
Thus exactly 2^227 static assignments attain the startup optimum. This
counts label assignments, not machines modulo isomorphism.

In particular, when T=0 and A=C*2^L*3^R, the already proved exact minimum
literal startup clock within this class is

    76A + 4 floor(A/5) + 24 floor(A/7) + 48 floor(A/11) + 62.

For A=1 the attained minimum is 138 literal steps. The optimal history and
clock statement also covers T>0; it does not make those clocks small.
Nor does startup optimality claim that the remaining canonical pair choices
are first-encounter-optimal for every later computation or every input. Different traces can require
opposite first-edge choices at a pair; the general theorem supplies an
optimum for its specified trace, not one common optimum for all traces.

## 6. Effective scope and limitations

Given the finite trace as a sequence of normalized edge identities, its
optimal static orientation is computed by one scan, using a dictionary of
visited collision pairs. No halting oracle or simulation callback is used
by the resulting literal machine. A finite requested number of normalized
steps can also be simulated to supply such a trace.

An infinite trace still determines a mathematical first-encounter choice
for each pair that ever occurs. Because there are finitely many pairs,
every completed assignment is a finite object and is nonuniformly
computable. What is not supplied here is a uniform terminating procedure
that extracts the completed optimal assignment from an arbitrary unbounded
machine/input description: an online scan can fix encountered choices but
need not certify which unencountered pairs will never occur. The finite-
trace theorem needs no such certification.

This is an optimum only within the specified static orientation class.
It does not optimize the data program, indegree normalization, recorder
algorithm, number or encoding of registers, prime choices, literal-source
size, compiler geometry, CA local rule, or arbitrary universal machines.
It makes no universal-program completion claim and changes none of the
previously frozen source or execution evidence.

## 7. Artifact identity

The frozen source SHA-256 remains
`fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`.
The frozen 86-file base-manifest SHA-256 remains
`bc7ef047e14499de6048789f93ae7ec082d679f4787c96b6c1bf7fbff0343d89`.
Only this theorem note and its separate independent audit are new;
`first-encounter-manifest.json` records their hashes separately.
