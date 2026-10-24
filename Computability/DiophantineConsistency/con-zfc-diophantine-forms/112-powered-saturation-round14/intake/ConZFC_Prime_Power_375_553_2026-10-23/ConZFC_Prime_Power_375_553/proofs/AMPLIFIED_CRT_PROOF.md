# Amplified CRT certificates with only the horizon factorial

The following argument is independent of the C222 calculus. It is an
ordinary theorem of elementary arithmetic, and all its finite arguments
can be formalized in ZFC. It replaces the requirement that every CRT
modulus have a prime factor above the complete polynomial evaluation bound.

## 1. A one-sided prime-power range lemma

Let p be a prime, let e,k be positive integers, and let a be a nonnegative
integer. With the ordinary convention
binom(a,k)=0 when a<k,

    p^e | binom(a,k)  ==>  a mod p^e < k.

If a<k this is immediate. Otherwise all integers a-k+1,...,a are
positive. The factorial valuation identity gives

    v_p(binom(a,k)) = sum_{j>=1} [ floor(a/p^j)
                       - floor((a-k)/p^j) - floor(k/p^j) ].

Every summand is 0 or 1. If none of a,a-1,...,a-k+1 is divisible by
p^e, no integer in that interval is divisible by p^j for j>=e. Thus the
displayed summands vanish for j>=e, and the valuation is at most e-1.
Contraposition proves that some a-r, 0<=r<k, is divisible by p^e.
Its residue representative r modulo p^e is at most r, hence less than k.

Equivalently, p^e|binom(a,k) implies existence of r in[0,k-1] such that
a=r mod p^e. This implication is deliberately one-sided: a=4,k=2,p=2,e=2
satisfies a=0 mod4 but 4 does not divide binom(4,2)=6.

## 2. Amplified CRT theorem

Fix integers t>=1, K>=1, bounds b_1,...,b_r>=0 satisfying

    K >= t,     K >= b_j+1 for every j.

Put

    T=t!,  d_i=1+(i+1)T (0<=i<t),
    B=product_{i<t} d_i,   N=B^K.

Let L(I,W_1,...,W_r) be an integer polynomial, with any additional fixed
integer parameters suppressed. Assume

    0 <= L(i,w) < 2^K

for every i<t and every tuple 0<=w_j<=b_j.
Then the following are equivalent:

1. For every i<t there is such a tuple w with L(i,w)=0.
2. There are positive C,A_1,...,A_r, each at most N^2, satisfying

       B | 1+(C+1)T,
       N | binom(C,t),
       N | binom(A_j,b_j+1) for every j,
       N | L(C,A_1,...,A_r).

The upper bounds in (2) are needed only to furnish economical radix
bounds; soundness holds without them.

### Soundness

Fix i<t and choose a prime p dividing d_i. Since p cannot divide T,
we have p>t. Write m=v_p(d_i)>=1 and e=Km. Subtracting d_i from the
index-congruence expression gives p|(C-i)T. Since p does not divide T,
cancellation gives C=i modp. The prime-power range lemma applied to binom(C,t) gives
C=s mod p^e for some s in[0,t-1]. Since p>t and s=i modp, s=i.
For each j the same lemma gives A_j=w_j mod p^e for some w_j in[0,b_j].
The local congruence therefore yields

    p^e | L(i,w).

But p^e>=2^K and 0<=L(i,w)<2^K, so L(i,w)=0.

### Completeness

The d_i are pairwise coprime. Indeed any common prime divisor of d_i,d_h
is coprime to T and divides i-h; it is therefore at most t and divides
T, a contradiction. Choose CRT representatives C,A_j in[1,B^(2K)] with

    C=i mod d_i^(2K),   A_j=w_{ij} mod d_i^(2K).

The index congruence and local congruence follow directly. To establish a
range condition, fix p|d_i, let m=v_p(d_i), and let k be its lower index
(t for C, or b_j+1 for A_j). The chosen residue lies in[0,k-1]. If the
upper argument a is below k, its binomial coefficient is zero. Otherwise
the falling factorial has a factor divisible by p^(2Km). Since

    v_p(k!) <= k-1 <= K-1 < Km,

the binomial coefficient has valuation at least Km. This holds for every
prime divisor of B, so N divides every required binomial coefficient.

## 3. Applying the theorem to the eight-column C222 path

Use the unchanged eight-column local polynomial of the incoming 407
construction, with bounds(t,t,t,t,y,y,x,x), and

    R=2+t+x+y+M0.

Its literal majorant certificate proves L<R^E with E=2^23. Define the
amplification exponent by the affine expression

    K=E R.

For R>=1, 2^R>R, hence 2^K>R^E>L. Also K exceeds t and all lower
range indices. The 23 squarings formerly used to construct H=R^E are
therefore unnecessary: H is used only in the mathematical upper bound.

## 4. A smaller CRT-product majorant

The inherited product identity computes B as the remainder of

    T^t t! binom(Q+t,t)

modulo TQ-1. The previous Q=(1+(t+1)T)^t+2 can be replaced by

    Q=T^t (t+1)^t+2.

For T>=1, 1+jT <=(j+1)T, so

    B=product_{j=1}^t(1+jT) <= T^t (t+1)! <= T^t(t+1)^t < Q.

Modulo TQ-1, each factor T(Q+j) is congruent to 1+jT. Therefore the
displayed numerator is congruent to B. Since Q>=B+2,
TQ-1>B, proving that its remainder is exactly B.

Both powers T^t and(t+1)^t were already required, so this modification
removes a separate power call and its base-specific Pell congruence.

## 5. Radix bootstrap without H!

The sole factorial t! already requests

    rho=(t+2)^(t+2),   V=(rho+1)^t,

and its exact binomial binom(rho+t,t). Use

    N=B^K,   q=N*(N+V+1)^K.

The delivered graph explicitly forces raw B>=2 with the natural slack
B=B_0+2. The shared positive-power theorem recovers the displayed powers
in the source's dependency order, before any factorial or binomial is
interpreted. In the signed interpretation, after the anchored t pair
and rho have been recovered, (rho+1)^t gives V>0. The raw factorial rows
c=r+s+1 and cT=V+s, with r,s>=0, therefore give c>0 and T>0 before the
exact binomial is interpreted. Thus T^t has a positive base and uses the
already oriented t pair, including when T=1. Independently, the raw guard
B>=2 and K>0 allow recovery of N=B^K and (N+V+1)^K. Hence N>=2 and q>V.
The full sign and orientation argument is in `SIGNED_COMPILATION_PROOF.md`.
The lower coefficients of (q+1)^(rho+t), through index t,
are at most binom(rho+t,t)<=V. Thus the first exact digit graph is valid,
and the inherited ceiling identity proves T=t!.

Now T<=t^t. Set U=T*(t+1). Since U<rho+1 and both are integers,

    V-U^t >= t U^(t-1).

For t>=2, U>=6 and the right side exceeds 2. For t=1, V=28 and U=2.
Thus in all cases Q=U^t+2<V. Consequently every lower coefficient through
t of the second exact binomial is at most

    binom(Q+t,t) <= (Q+1)^t <= V^t < q,

because K>=t. This validates the intended CRT product identity for B
before any coordinate range is decoded; the raw inequalities B>=2 and
N>=2 were already available above.

Choose the nine positive CRT representatives(C and the eight A_j) with
their sum plus a natural slack equal to 9N^2. This weaker aggregate bound
gives every upper argument n<=9N^2<=N^6. Its lower index k is at most R.
For 0<=j<=k,

    binom(n,j) <= n^k <= N^(6R) < q,

since E=2^23>=6 and q>N^(K+1). Also N|q. The inherited residue-only
digit graph therefore correctly represents every required divisibility.
There is no circular assumption about the factorial, product, or ranges.

## 6. Scope and attribution

The underlying C222 proof calculus, eight-column path, synchronized Pell
power theorem, nonnegative square-difference gates, contraction algorithm,
and residue-only binomial digit lemma are inherited. The new contribution
here is their replacement of the large-prime CRT step by the one-sided
prime-power range lemma, strengthened completeness precision, index
lifting, affine amplification budget, and the new radix bootstrap.
The product-majorant reuse is a separate elementary identity. No claim of
worldwide priority is established, and no formal proof object is supplied.
