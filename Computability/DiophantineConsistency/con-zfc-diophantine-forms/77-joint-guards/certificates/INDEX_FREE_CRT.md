# Index-free inert-prime bounded closure with one variable-power graph

## Status

This is a universally proved simplification of the previous inert-prime CRT certificate. It removes the encoded index coordinate and its norm leaf, and reuses the product numerator's scale to eliminate one entire variable-power graph. The supplied checker verifies polynomial identities and arithmetic fixtures, not a Lean theorem. Factorial, binomial and variable-power graph compilation is still explicit remaining work. No new closed consistency-polynomial variable count is claimed.

## Input and exact statement

Fix a natural bound n, external natural parameters x, an integer m>=1, and fixed polynomials e(i,w;x), f(i,w;x) with nonnegative integer coefficients, where w has m coordinates. Put P=e-f, with integer subtraction. Choose a fixed integer d>=0 at least the degree of P in its index variable i. The zero polynomial may use d=0.

We encode

    for every i<n there exists natural w with P(i,w;x)=0.

For an existential natural common bound U define

    H = e(n,U,...,U;x)+f(n,U,...,U;x)+n+U+1,
    T = H!,    D = 4T,
    S = D^n n!,
    M = DS+1,
    B = (S binom(S+n,n)) mod M.

Binomial means the total natural function, with binom(A,k)=0 for A<k. Every later graph replacement must preserve this convention.

Write P(i,w;x)=sum_{k=0}^d P_k(w;x)i^k. Define the ordinary integer polynomial

    R_D(A;x) = sum_{k=0}^d P_k(A;x) D^(d-k)(1-D)^k.

This is the denominator-cleared notation D^d P(D^(-1)-1,A;x). No inverse is present in the actual polynomial, and d is fixed, not a variable exponent.

Define a fixed nested norm on a nonempty list of leaves by N([z])=z and N(L||R)=N(L)^2+N(R)^2 for a chosen fixed binary partition into nonempty lists. A balanced tree may be used. There are m+1>=2 leaves here, so the final N is nonnegative on integer inputs.

The new certificate is

    there exist natural U,A_1,...,A_m such that
    B divides N(binom(A_1,U+1),...,binom(A_m,U+1),R_D(A;x)).

It is equivalent to the bounded family above for all n>=0. There is no encoded index c, no index congruence leaf, and no second variable-power call hidden in the definitions.

## 1. Product extraction with a reused scale

Let m_i=D(i+1)-1 for 0<=i<n. Then

    B = product_{i<n} m_i.

Indeed

    S binom(S+n,n)
      = D^n product_{j=1}^n(S+j)
      = product_{j=1}^n(DS+Dj)
      = product_{j=1}^n(Dj-1) mod (DS+1).

For n>0, each positive factor Dj-1 is strictly smaller than Dj, whence the product is strictly less than D^n n!=S<M. For n=0 the empty product and S are both one, still less than M. Therefore the least remainder is exactly the desired product.

The preceding certificate used the independent majorant Q=(Dn)^n+1 and a second power D^n. The numerator scale S=D^n n! is itself already a sufficient majorant. One may set Q=S, not merely S+1. The final formula therefore uses exactly one variable-power graph, namely D^n; all other newly displayed powers have fixed degrees.

Each m_i is 3 modulo 4. Every prime divisor of m_i exceeds H, since a prime at most H divides T and thus D but cannot divide D(i+1)-1.

The moduli are pairwise coprime. A common divisor of m_i,m_j is coprime to D and divides D(j-i), hence divides j-i. Since 0<|j-i|<=n-1<=H, this difference divides H!=T. The common divisor therefore divides T and is coprime to D=4T, so equals one.

## 2. Eliminate the encoded index polynomially

The coefficient formula satisfies the exact identity

    R_D(A;x)-D^d P(i,A;x)
      = (D(i+1)-1) Q_D(i,A;x),

where the explicitly integral polynomial quotient is

    Q_D = -sum_{k=1}^d P_k(A;x) D^(d-k)
                 sum_{r=0}^{k-1}(1-D)^(k-1-r)(Di)^r.

This is the difference-of-powers identity. In particular modulo m_i,

    R_D(A;x) = D^d P(i,A;x).

D is invertible modulo every m_i and modulo each of their prime factors. Thus the congruence checks exactly the original indexed polynomial after the bounded coordinates are recovered. A separate CRT number c congruent to each i was redundant: the modulus itself already encodes i as D^(-1)-1.

## 3. Soundness

For n=0 the target is vacuous. Otherwise choose any i<n. Since m_i is 3 modulo 4, it has a prime divisor p_i that is 3 modulo 4. Every such p_i exceeds H.

Over the field with p_i elements, u^2+v^2=0 implies u=v=0, because -1 is not a square. Induction on the fixed norm tree therefore implies that every leaf is zero modulo p_i.

For each coordinate, binom(A_j,U+1)=0 modulo p_i. Since p_i>H>=U+1, the identity

    (U+1)! binom(A_j,U+1)=product_{r=0}^U(A_j-r)

and primality imply that A_j is congruent to some w_j in [0,U]. The same selected prime is used for all coordinates. The final leaf and the clearing identity imply D^d P(i,w;x)=0 modulo p_i. Cancel the invertible D^d. Monotonicity of e and f then gives

    |P(i,w;x)| <= e(n,U,...,U;x)+f(n,U,...,U;x) < H < p_i.

The integer P(i,w;x), divisible by p_i and strictly smaller in absolute value, must be zero. This yields the required witness at every i.

The bound applies to the original P after cancelling D^d. Bounding the much larger cleared residual R directly would introduce an unnecessary circular scale requirement and is not part of the proof.

## 4. Completeness

Choose a witness tuple at each of the finitely many i<n and a common natural upper bound U. For n=0 choose U and all A_j arbitrarily; B=1 makes the certificate immediate.

For n>0, pairwise coprimality gives CRT representatives A_j congruent to the chosen w_ij modulo m_i. Every prime factor of m_i exceeds H>=U+1, so (U+1)! is invertible modulo m_i. The falling-factorial identity and A_j=w_ij in the range show that the binomial range leaf vanishes modulo m_i. Polynomial congruence and the clearing identity give R_D(A;x)=0 modulo m_i. Consequently every norm leaf vanishes modulo each m_i; the nested norm vanishes modulo their product B. This is precisely the certificate.

All steps are finitary mathematical arguments. They assume neither Con(ZFC) nor soundness of the standard model. A full formal object-language proof still has to implement the required arithmetic internally.

## 5. Completely exposed graph interface and conditional count

There is no claim that factorials, binomials or variable exponents are ordinary polynomial notation. To make the remaining interface explicit, suppose selected exact natural graph polynomials have f internal witnesses for factorial, p for power, and b for total binomial, excluding their visible inputs and output. Let graph outputs be

    T=H!, F=n!, E=D^n, C=binom(EF+n,n),
    L_j=binom(A_j,U+1).

Use ordinary expressions S=EF, M=D*EF+1 and introduce natural B,K,r,V with the three ordinary equations

    S*C=B+M*K,
    M=B+r+1,
    N(L_1,...,L_m,R_D(A;x))=B*V.

The second equation guarantees 0<=B<M. These three equations together with the selected graph polynomials are an explicit ordinary polynomial system, and their squared sum is an ordinary polynomial once the chosen graphs are substituted.

The exposed natural coordinates are U,A_1,...,A_m; T,F,E,C,L_1,...,L_m; and B,K,r,V. Their count is exactly 2m+9. The full conditional count is

    2m+9 + 2f + p + (m+1)b.

Under the same graph-output and remainder convention, the preceding certificate has 2m+11+2f+2p+(m+1)b coordinates. Thus this interface saves exactly p+2 coordinates: the old encoded index, the removed power output, and that power graph's internal witnesses. No numerical value for f,p,b has been claimed or silently replaced by zero. Additional quartic flattening would require its own count; the cleared residual may raise degree/operation costs even while removing coordinates.

## Verification and remaining work

`check_index_free_crt.py` verifies the integer difference-of-powers quotient for four unrelated source polynomials, including an index-independent source; exact product extraction and coprimality for 90 cases including n=0; 2,030 anisotropic prime-field pairs; 1,930 index-free range/residual cases; a two-coordinate complete CRT fixture; and negative controls for split primes and missing residual bounds. It uses explicit runtime checks and also passes Python optimized mode.

These controls accompany, rather than replace, the universal proofs. To obtain a smaller completed consistency polynomial, the selected factorial/binomial/power graphs, their exact counts and shared subexpressions, the whole direct checker, and the formal consistency bridge must still be supplied and measured. The independently completed local graph improvements in `LOCAL_GADGET_PROOFS.md` do not depend on solving this global closure problem.
