# Inert-prime CRT closure: a different certificate architecture

## Status

This is a proved mathematical compiler lemma, with an explicit factorial/binomial/exponential certificate. It is not a claimed new small ordinary polynomial. Expanding its factorial, binomial and variable-exponent graphs through the repository's explicit representations remains to be done and counted. No Lean/Rocq kernel certificate is claimed. All bounds below are ordinary natural numbers, including zero. For natural A and k, use the total convention binom(A,k)=0 when A<k. Any later Diophantine graph substitution must implement this same total function, not silently restrict its domain to A>=k.

## Input

Fix n >= 1, external natural parameters x, and two polynomials e(i,w;x), f(i,w;x) with nonnegative integer coefficients, where w has m >= 1 coordinates. We represent

    for every i < n, there exist natural w with e(i,w;x)=f(i,w;x).

An arbitrary integer-coefficient polynomial can be split into its positive and negative coefficient parts. The input can remain a shared arithmetic DAG: flattening it into quadratic equations before this closure is unnecessary.

## Closed certificate

Existentially choose U, A_1,...,A_m, c. Define

    H = e(n,U,...,U;x) + f(n,U,...,U;x) + n + U + 1,
    T = H!,
    Q = (4Tn)^n + 1,
    M = 4TQ + 1,
    B = ((4T)^n n! binom(Q+n,n)) mod M.

For any nonempty fixed list define N recursively: N([z])=z, and N(L||R)=N(L)^2+N(R)^2, with L,R nonempty. A balanced tree minimizes maximal degree. Put

    z_j = binom(A_j,U+1),
    z_{m+1} = e(c,A;x)-f(c,A;x),
    z_{m+2} = 4T(c+1)-1.

The complete certificate is a single divisibility

    B | N(z_1,...,z_m,z_{m+1},z_{m+2}).

All displayed special functions have explicit constructive Diophantine graph representations in the pinned repository. These expressions are not themselves ordinary polynomials: one must retain this distinction when reporting variable counts.

## Product identity

Set m_i=4T(i+1)-1 for 0<=i<n. Then B=product_i m_i. Indeed,

    (4T)^n n! binom(Q+n,n) = product_{j=1}^n (4TQ+4Tj)
                          = product_{j=1}^n (4Tj-1) modulo M.

The positive product is less than (4Tn)^n, hence less than Q and M. Thus its least remainder is precisely B, with no parity branch. Each m_i is 3 modulo 4. Distinct m_i,m_j are coprime: any common divisor divides j-i, is coprime to 4T, and divides T because j-i<=n<=H and T=H!. It must be one.

## Soundness

Each positive m_i is 3 modulo 4, so it has a prime divisor p_i=3 modulo 4 (factor the integer and inspect parity of the exponents of primes 3 modulo 4). Every prime divisor of m_i exceeds H: a prime at most H divides H! and therefore cannot divide 4T(i+1)-1.

For a prime p=3 modulo 4, a^2+b^2=0 in F_p implies a=b=0. If b is nonzero, (a/b)^2=-1 contradicts Euler's criterion; the zero case is immediate. Induction on the fixed tree implies N(z)=0 modulo p iff every leaf z_j is zero modulo p. This is not true of an ordinary sum of three or more squares.

Choose p_i as above. The index leaf and m_i=0 modulo p_i imply c=i modulo p_i, because 4T is invertible. The norm condition implies every binom(A_j,U+1)=0 modulo p_i. Since p_i>H>=U+1, multiplying by the invertible factorial (U+1)! gives

    product_{r=0}^U (A_j-r)=0 modulo p_i.

Primality gives a root w_j in [0,U] with A_j=w_j modulo p_i. The same selected prime works for all coordinates. The local-residual leaf gives e(i,w;x)-f(i,w;x)=0 modulo p_i. Monotonicity bounds its absolute value by e(n,U,...,U;x)+f(n,U,...,U;x)<H<p_i. Therefore this integer residual is zero. This supplies the required witnesses for each i.

## Completeness

Choose witnesses at each of finitely many i and take U to bound all coordinates. Compute H,T,m_i,B. Pairwise coprimality gives CRT representatives c=i and A_j=w_{ij} modulo each m_i. Since (U+1)! is coprime to every m_i, each binomial range leaf vanishes modulo m_i. The residual leaf vanishes modulo m_i by polynomial congruence. Thus their nested norm vanishes modulo every m_i and hence modulo B. The index divisibility holds by construction.

All arguments are finitary and formalizable in ZFC. The theorem neither assumes Con(ZFC) nor uses a standard-model soundness principle.

## What changes relative to the incoming one-stack constructor

The supplied direct source has five local parameters a,b,c,u,v, but its proposed global constructor first inserts 84 nonlinear wire coordinates and applies bounded closure to 89 local coordinates. Generic CRT closure then introduces one upper bound and one encoded value per local witness, plus a falling-factorial condition per coordinate.

The present route has two separable changes:

1. Apply bounded closure to the original local polynomial, not its quartic flattening. The 84 wires are not independent local existential coordinates at this stage. Flatten only the final ordinary polynomial, if degree four is desired.
2. Share one upper bound U, and combine all range tests and the local residual into one inert-prime norm congruence. There are m binomial graph calls but only one bound, no per-coordinate factorial graph, and one combined congruence instead of m range congruences plus the residual and index congruences.

This removes (m-1) bound coordinates and (m+1) separate congruence tests at the certificate interface relative to separate range, evaluation and index tests. An implementation with one unrestricted integer quotient per congruence saves the same number of quotient slots; natural-domain graph constructors may have different bookkeeping. These are interface counts, not final Diophantine variable counts. The omitted local wires may reappear later when flattening; no claim that all 84 disappear from a final quartic is justified.

A balanced norm of m+2 leaves has degree at most 2^ceil(log2(m+2)) in its leaves. A deliberately unbalanced root can give the high-degree local residual degree two while placing lower-degree range leaves under a deeper tree. Arithmetic DAG sharing must be preserved in graph construction; naive expression-tree substitution can overwhelm the interface savings.

## Explicit remaining obstacle

To turn this into an improved consistency polynomial, one must implement and count the factorial/binomial/power graph constructors with sharing, instantiate the unflattened local source and beta graphs, prove the new closure correctness in the desired formal environment, and then compare the final variable/degree/circuit frontier. The current artifact stops before that work. It advances the certificate mechanism, not the current 9-positive/10-integer or quartic-variable records.
