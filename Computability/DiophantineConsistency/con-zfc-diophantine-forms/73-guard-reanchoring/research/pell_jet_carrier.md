# First-order Pell jet and a weaker Y scale

This is a proved arithmetic lemma and a proposed carrier, not a complete new endpoint.

Write psi_b(n)=U_{n-1}(b), with psi_b(0)=0 and psi_b(1)=1. For positive S and n,

    psi_(1+2S)(n) = sum_{j=0}^{n-1} binom(n+j,2j+1) 4^j S^j.

The identity follows by induction from psi_b(n+2)=2b psi_b(n+1)-psi_b(n), or by comparing coefficients in its rational generating function t/(1-2(1+2S)t+t^2).

Set k=2psi_(1+2S)(n), R=2n-1, and P(t)=(t-1)(t+1)(t+3). Then

    6(k-R-1) = S P(R) + 192 S^2 T,

where

    T=sum_{j=2}^{n-1} 4^(j-2) binom(n+j,2j+1) S^(j-2)

is a nonnegative integer. In particular the jet error is divisible by 192S^2. For n=2 the error vanishes; for n=3, T=1, proving that 192 is the sharp common coefficient in this displayed normalization.

## Carrier lemma

Suppose q>=16, gcd(q,3)=1, q^2 divides Y, and X,Y,n,R are positive integers with 1<=n<R<q^4. Let S=XY^2, k=2psi_(1+2S)(n), r0=k-R-1, U=qY^2, and choose any integer L with L=R modq. Assume

    U divides S(P(L)+2)-6r0.                 (C)

Then 2n=R+1 and q divides 2X.

Proof of exact index: S is divisible by q^4 and U by q^5, so q^4 divides 6r0. If q is odd, gcd(q,6)=1, hence q^4 divides r0. If q is even, q^4 divides6r0 forces r0 even; k is even, so R is odd, and L is odd. Thus P(L) is even, S(P(L)+2) is divisible by 2q^4, and U is divisible by 2q^4. Equation(C) then gives 2q^4 dividing6r0, hence q^4 dividing r0 since gcd(q,3)=1. The first Pell congruence gives q^4 dividing k-2n. Therefore q^4 divides2n-R-1. Its absolute value is less than q^4, so it is zero.

Proof of radix restriction: the jet identity now applies with R=2n-1. The difference P(R)-P(L) is divisible by q. Therefore U divides S(P(R)-P(L)), because S=XY^2. Also U divides S^2 because q dividesY. Hence U divides6r0-SP(L). Subtract from(C) to obtain U dividing2S; cancellingY^2 yields q dividing2X.

If separately X=2^R and R>3q, then q dividing2X implies that q is a power of2 and that q dividesX. Indeed q=2^t and q<=2^(R+1); the bound R>3q excludes t=R+1 (and directly gives t<R).

For the native R polynomial, L=MC*J-F-alpha satisfies L=R modq. The authentic mask bound MC<beta and C=q-F-alpha>0 give |L|<q. Thus P(L) has only degree3 in the supplied variables, rather than the degree12 of P(R).

## Degree cost

The proposed main carrier is

    Dstar = U(X+ac) + H(U gamma + S(P(L)+2)-6r0),

where a=(X+1)Y and H=4a+3. It preserves Dstar=U b0 modH. With all X,Y,L as linear supplied coordinates/registers, the correction S P(L) has degree6, Dstar has degree8, and the squared main-norm residual has degree16. Its square therefore reaches degree32. This does not improve the current adaptive degree30 P13. A lower-degree correction remains unresolved.

The positive sign of Dstar can be proved after first-Pell classification supplies n>=2 and k>=8XY^2, using |L|<q; it should not be assumed merely from gamma>0. Completeness must separately check positivity of the reconstructed gamma. Finally, q^2|Y does not imply q^3|Y, so a final equivalence cannot be justified by claiming the old source coordinates have all been restored. One needs direct native decoding or a canonical witness replacement.

## Power recovery needs only X,Y>=1

Suppose X,Y>=1, n>=2, R=2n-1,

    A=(X+1)Y+2, P0=2XY^2+1,
    c=psi_A(R), k=2psi_P0(n), kY<c<k(Y+1),
    D=chi_A(R), a=A-2, H=4a+3,
    D-ac=X modH.

Then X=2^R.

The recurrence bounds give psi_A(R)>=(2A-1)^(R-1) and psi_P0(n)<=(2P0)^(n-1). Since

    (2A-1)^2-8P0
      =4(X-1)^2Y^2+12(X+1)Y+1 >0,

we obtain c/k>4^(n-1)/2=2^(R-2). Thus Y+1>2^(R-2), whence Y>=2^(R-2). It follows that H>=8Y+3>2^R. Also 0<X<H. Reducing the Pell polynomial identity moduloH, where Delta=a^2, gives D-ac=2^R modH. The two positive integers X and2^R lie belowH and are congruent, hence equal. No radix-divisibility or stronger Y-scale premise is needed for this sublemma.
