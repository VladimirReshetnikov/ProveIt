# Independent mathematical review of the pooled Pell frame

This review is by a separate research agent within the AI collaboration. It is
not external human peer review or a proof-assistant certificate. It reviews the
ordinary finite-batch theorem in `../report/batched_powers.tex`, including the later
output-inclusive dominating sum. The existing Pell-index and positive-power
characterizations remain named inherited mathematical interfaces.

## Result

The proposed common-frame reduction is valid on nonnegative integer coordinates,
provided every represented power has strictly positive base and exponent, the
common sum excludes all newly introduced certificate coordinates, and grouping
uses exact equality of exponent expressions. The graph implementation must still
be independently checked against these formulas.

## Simultaneous completeness

First fix all finitely many semantic triples `(n_i,k_i,m_i)` with
`m_i=n_i^k_i`, as determined by the acyclic source graph. Set
`W=1+sum_i(n_i+k_i+m_i)` (repeated expressions may be counted only once if every
individual domination inequality is preserved). For `a=chi_(W+1)(W)` and
`Z=psi_(W+1)(W)/W`, the recurrence modulo W proves Z integral and the global
Pell norm holds. W is positive, hence a is at least two.

At this now fixed a, let `(X_j,Y_j)` be its Pell pair at every distinct exponent.
All Y_j are positive. Put `P=product_j Y_j`. The matrix
`[[a,a^2-1],[1,a]]` has determinant one over Z/(4P^2); consequently its finite
group order is positive. A sufficiently large positive multiple L of that order
gives `U=chi_a(L)>a`, `V=psi_a(L)>0`, `U=1 mod 4P^2`, and `V=0 mod 4P^2`.
This proves the full pooled condition `P^2 | V`, even if distinct Y_j share
prime factors. The incorrect weaker inference from all `Y_j^2 | V` to
`P^2 | V` is not used.

Since gcd(U,4P)=1, CRT gives B congruent to a modulo U and to one modulo 4P.
Choose its nonnegative representative plus a sufficiently large multiple of
4PU, so B>=2. Then `(S_j,R_j)=(chi_B(k_j),psi_B(k_j))` simultaneously satisfies
all index congruences. The auxiliary scale witnesses d and q in
`V=P^2(d+1)`, `B=1+4Pq` are nonnegative integers. All choices occur after the
semantic triples, and none feeds back into those triples or W.

## Why every local output-bound slack can be deleted

At an arbitrary polynomial zero, the global norm is

    a^2 = 1 + W^2*((W+1)^2-1)*Z^2.

The explicit constraint a>=2 excludes Z=0. Because Z is natural, Z>=1. Since
W>=1, the right side is strictly larger than W^2, proving a>W without any
Pell classification. The common sum gives n_i,m_i<=W. For each positive n_i,
let the retained local modulus equation define `T_i=2an_i-n_i^2-1`.
Using a>=n_i+1 gives the exact estimate

    T_i-a = a(2n_i-1)-n_i^2-1
          >= (n_i+1)(2n_i-1)-n_i^2-1
          = (n_i+2)(n_i-1) >= 0.

Thus `m_i<=W<a<=T_i`. This establishes both T_i>0 and m_i<T_i from retained
rows. Removing all separate output-gap coordinates and their equations is sound.
Completeness sets T_i to the indicated positive value, so the same removal
loses no semantic triple.

## Soundness of pooling

For each group, the retained inequality Y_j>=k_j>0 proves P>0. Therefore
`V=P^2(d+1)>0`, every Y_j^2 divides V, and `B=1+4Pq` gives B=1 modulo 4Y_j.
All other group rows are exactly the existing index criterion. Applying that
criterion independently to every group recovers its exact Pell pair. The one
global `(W,a,Z)` norm and the now proved local bound m_i<T_i satisfy the old
positive-power criterion for every call. Hence no power output is altered.

## Deferred common binomial radix and common congruence offset

For the binomial calls, first choose their semantic integer outputs in the old
acyclic graph. Only then form N as the sum of all upper arguments and use
`R=2^N+1`. The actual calls have positive upper arguments and positive lower
arguments, as required by the positive-power graph. Since N>=n_i,
`R>2^(n_i)>=binomial(n_i,j)` for every j. The usual digit theorem in
`(R+1)^n_i` therefore applies at every call without carries. Sharing R does not
create a semantic cycle even when an earlier binomial output is a later upper
argument: all binomial values were fixed before choosing the certificate radix.

For congruences `left_i = right_i mod modulus_i`, write
`left_i+modulus_i*q_i=right_i+modulus_i*t` with one shared natural t. At every
assignment this implies the original congruence. Conversely finitely many
integer quotient differences have a common natural upper bound; choose t
large enough that every q_i is natural. If a modulus is zero, the old
congruence is simply left_i=right_i and imposes no condition on t. The common
t is chosen after the complete Pell/binomial semantic and certificate data,
and is excluded from W and the shared radix exponent.

## Remaining implementation obligations

The finite checker should verify: (1) all base/exponent positivity call sites;
(2) all exponent grouping keys; (3) every member of the common sum; (4) exclusion
of new frame and offset coordinates from that sum; (5) the common product P and
its declared factors; (6) exact retained Pell and modulus residuals; (7) exact
expanded-polynomial equality after any affine or terminal-gate elimination.
The ordinary proof, rather than bounded numerical examples, establishes the
universal existence equivalence.

## Final integration status

The final direct component independently checks all seven implementation obligations above. The one initially nonnegative factorial base is proved positive from its retained ceiling rows before its power criterion is invoked; the main report gives this dependency order explicitly. The release has 23 literal exponent-expression groups for 28 power requests. See the component audit receipts and top-level reproduction commands.
