# Independent review: calibrated two-block carry bridge

Let N=2^u, with integers 0<=S,T and S+T<N. Put

    X=N^2+(S+T)N+(N-1-S),
    Y=2^(u+popcount(T)+1).

The three displayed summands occupy disjoint binary blocks: the leading
block is the single bit at position 2u; the middle block is S+T<N; the
bottom block is the u-bit complement of S. Consequently

    popcount(X)=1+popcount(S+T)+u-popcount(S)
               =u+popcount(T)+1-c(S,T),

where c(S,T)=popcount(S)+popcount(T)-popcount(S+T) is the number of
binary carries, counted with propagation. It is nonnegative and equals
zero precisely when S&T=0. Legendre's factorial valuation formula gives
v_2(binomial(2X,X))=popcount(X). Thus Y divides that binomial exactly
when there is no binary carry. The stronger bound S+T<N is indispensable;
the old three-block construction did not require it. The accompanying
finite audit includes a counterexample if it is omitted.

## Applying an explicit sparse source mask

Suppose b=2^k, B=2^v, and n distinct positive positions a_i<=t are
chosen. Let m distinct nonnegative target positions e_j<=e be chosen.
Use the low and high masks

    N0=B^(t+1),
    Mlow=N0-1-(b-1) sum_i B^a_i,
    Thigh=(B-2) sum_j B^e_j,
    T=Mlow+N0 Thigh.

Assume B>b. Low digits are B-1 except at the n designated positions,
where they are B-b. Therefore

    popcount(T)=(t+1+m)v-nk-m.

This calculation does not depend on target spacing, only on their
being distinct. In particular overlapping reversed source blocks do not
alter the formula if the extraction certificate still separates targets.

Let K=e+2t, N1=4B^(K+1), N=N0N1. Then

    u=2+(t+K+2)v,
    u+popcount(T)+1=3-m+(2t+K+3+m)v-nk.

Write H=2t+K+3+m. If B=beta*b^2 and beta=2^kappa, the threshold is
the polynomial with fixed coefficient

    Y=2^(kappa*H+3-m) b^(2H-n).

This is not a variable exponent in the equation. The exponents H,n,m,
kappa are fixed finite integers. To avoid materializing the larger fixed
coefficient for n=31, an equivalent division-free circuit is

    Y=beta^15 * 2^(kappa+3-m) * B^(H-16) * b.

Here H>=16 and kappa+3-m>=0 hold for the supplied instance.

If the source padding satisfies J<3B^(K+1), with integer J>=0 and
0<=g<N0, then S=g+N0J<3N0B^(K+1). Since Thigh<B^(K+1),
T<N0B^(K+1). Hence S+T<N follows strictly. The low g term cannot
be dropped without explaining integrality: J<=3B^(K+1)-1 gives the
needed strict inequality.

## Modulo three and order of hypotheses

For the Sun route b=1+3f and beta is a power of four, so B=N0=1
modulo three and N=4B^(t+K+2)=1 modulo three. These statements hold
before any binary-base recovery. Then Mlow=0 modulo three,
Thigh=-m modulo three and

    X=1+T=1-m modulo three.

For m=22 this is zero. The requirement 3|X therefore does not rest on
an illicit assumption that an arbitrary square b is a power of two.
The popcount/divisibility equivalence, in contrast, is invoked only after
the inherited arithmetic bridge supplies a power-of-two b, or in the
forward construction where b is deliberately chosen to be a power of four.

This review proves only the replacement carry lemma and its explicit-mask
specialization. The delivered source proof must separately establish its
unconditional size bounds and output extraction; the Sun bridge is an
identified imported theorem, not a consequence of the finite tests.

## Sparse-padding specialization used in the final Sun circuit

The final sparse source uses J=2(1+g)^2D+A_targets, where
A_targets=sum_j B^e_j, instead of the geometric sum. Its stronger size
bound allows N=B^(t+K+2) without the leading factor four. Accordingly
u=(t+K+2)v and the threshold becomes

    1-m+(2t+K+3+m)v-nk.

Thus the Sun fixed multiplier is 2^(kappa+1-m), not the provisional
2^(kappa+3-m), when the factor-four block is removed. The general formula
for N=2^c B^(t+K+2) replaces the constant 3-m by c+1-m. The independent
implementation audits must check which block convention is actually used.

For the stronger bound let A bound each coefficient of D, beta>8192A,
B=beta*b^2, K=e+2t, t>=1. With 0<=g<2bB^t,

    2(1+g)^2D <36A b^2 B^K < B^(K+1)/128,
    A_targets <2B^e <=2B^(K-2) <B^(K+1)/256

for B>=16. Hence J<B^(K+1)/4. Integrality and g<N0 give
S<N0 B^(K+1)/4+N0; this is <N/2 for the actual B and K. The mask
satisfies T<N0 B^(e+1)<=N/B^2<N/4. Therefore S+T<N without circularly
assuming a decoded solution. An alternative exact integer argument may
use floor(B^(K+1)/4) when B is divisible by four.

Sparse signed-borrow induction: write h_i for the formal coefficients of
(1+g)^2D after low-digit decoding, with |2h_i|<B/2. The nominal coefficient
of J is 2h_i+1 at a target and 2h_i elsewhere. Starting at borrow zero,
every outgoing borrow is -1 or 0. At a target, the digit is
(2h_i+1+epsilon_i) mod B, epsilon_i in {-1,0}. It is 0 or 1 exactly
when h_i=0. These are exactly the digits disjoint from B-2. Thus the
sparse padding preserves all target tests, including negative residuals.
The actual integer J is positive by D(B)>0, so the high end represents
an ordinary nonnegative integer, not an infinite signed expansion.
