# Independent review: constant-bias stack credit over unsafe tail2

Verdict: PASS as an all-natural theorem about the stated constant-bias abstract scheduler. Application to a binary table is conditional on exact source binding, full runtime and the startup bridge. No state-count claim is made by this review.

Reviewed `research215_round4_scheduler/CONSTANT_BIAS_CREDIT_THEOREM.md` and both finite base certificates.

## The changed recurrence is essential

At constant bias1, every internal first-field read acts on the current residual itself. Consequently

    W(P(0,y)) = S followed by W(y) when y>0,

not W(y−1). MP and AX suffixes remain W(f(y)) and W(f²(y)), respectively, unless those residuals are zero. The document and finite checker use this corrected recurrence.

As before, s(0)=1 but g(0)=0; this distinguishes executing candidate zero from ending a candidate at zero residual.

## Infinite counting bound

For the strong induction A(N)=sum_{n<N}s(n)≤N, the corrected triangular-boundary identity is

    A(T_q) = q + G(q) + H(q−1) + sum_{l=1}^{q−2}H2(l),
    G(q)=A(q)−1.

The q root S commands have suffix arguments0,...,q−1, so G(q) is exactly the required contribution. For q≥2, q<T_q, making the induction use A(q)≤q legitimate. Thus q+G(q)≤2q−1, the same numerical upper bound as in the earlier feedback-bias proof. The q=1 boundary and N=2 partial diagonal are correctly handled directly; there is no circular invocation of A(1).

The Cantor pullback estimate H(L),H2(L)≤L−r(L) remains valid because g vanishes at zero and each positive prefix has sum at most its length minus one. The partial-diagonal decomposition is unchanged. Its final MP contribution is bounded by g(f(q−1))≤f(q−1)≤r(q−1), using strictly smaller induction indices. Hence A(N)≤N is established for every natural N, not extrapolated from finite enumeration.

## Prefix resource bound

The earlier density argument applies to the corrected candidate grammar because the number of root AX commands depends only on the first selector, and the total S count is still bounded by A(n+1)≤n+1.

For any sequence starting at1 with gaps1 or2, at least floor((n−1)/2) earlier candidates have completed before current candidate n. Subtracting the overestimate2q+1 of all non-AX root indices through n gives a valid lower bound on earlier completed root AX commands. No credit from the current candidate is used before it executes. The resulting lower bound

    4n−20sqrt(2n)−21

is strictly positive for n≥64. The exact finite domain1,...,63 is therefore sufficient.

## Independently reproduced finite bases

An independent implementation used the recursive command grammar above and elementary triangular-search unpairing, rather than the worker's iterative parser and integer-square-root routine. It reproduced every word and entry/internal/exit minimum in the63-case gap1/2 dynamic program, obtaining minimum−3.

A separate fixed odd schedule1,3,...,63 reproduced minimum0 and exit balance254. The analytic bound handles every later odd candidate. Therefore every command prefix of the entire odd schedule has nonnegative conservative balance.

Owned checker: `check_credit_independently.py`.
Receipt: `CREDIT_BASE_REVIEW.json`.
Reviewed finite certificate hashes:

- DENSITY_CREDIT_BASE.json: `c86001d2cdc2dfe46639ca9866d8d2528528cd70fc21fb6ae2a78344eea0ded8`.
- ODD_SCHEDULE_BASE.json: `ee4e739b583652824b154ae6d7ba8b0079f7fbb8b0fb97d62f331ac6eb220006`.

## Application to the proposed seed

The proposed startup seed is (N,T,W,A,D,H,X,Y,L)=(1,0,2,0,0,0,0,0,0). The stack2 must not be called entirely safe:2=P(0,1), and1=P(1,0), exposing refutation1 on its second decoded head if it were reached.

The initial AX nevertheless places ten theorem heads above this opaque tail, with theorem-valued incoming top/cache and the ordinary numerical parameter restrictions. The constant-bias odd schedule's nonnegative prefix balance ensures the wrapper length never drops below ten. Thus no head of tail2 is exposed. Under an arbitrary gap1/2 sequence from1, the weaker minimum−3 would still leave at least seven safe heads.

For composite transfer S=DROP;NIP;NIP, its internal stack behavior first pushes a theorem top and then pops twice. Its lowest wrapper depth is the final depth, one below entry, so the atomic balance−1 correctly bounds its entire execution. Both the top and cache guards inspect theorem codes. MP's successful extra zero push only improves the conservative bound; AX appends ten safe heads without consuming the opaque tail.

The wrapper is an explicit proof invariant, not a uniquely recoverable numerical list length; the alias P(0,0)=0 does not invalidate the argument.

## Scope

The theorem assumes the first enumerated candidate is1 and the constant-bias source has the specified work-tuple command equations. An arbitrary later initial counter, different step size, or misplaced footer is not covered without another argument. Exact physical/runtime and literal startup obligations remain separate.
