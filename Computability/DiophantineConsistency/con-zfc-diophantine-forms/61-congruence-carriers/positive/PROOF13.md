# Thirteen positive unknowns, exact degree 34, 93 operations

## Result and honest comparison

This construction removes the transport quotient z as well as the index
quotient h from the integral-root kernel. It has thirteen strictly positive
unknowns, degree 34 and 93 binary arithmetic gates (52 multiplications,
24 additions, 17 subtractions). It improves the degree-126/91-operation
thirteen-positive point in package59 and the degree-132/83-operation point
in package57. Compared with 126/91, degree decreases by 73.016% while the
literal gate count increases by two. The low-variable nine-positive and
ten-unrestricted-integer results remain separate tradeoffs.

The bounded comparison snapshot is ProveIt
beb0192cb8dc36f78c369c080f2adfbc1887a486. This is an ordinary mathematical
existence reduction, not a global minimality claim or a newly kernel-checked
end-to-end theorem. The exact source coefficients and semantic dependencies
are the same as in PROOF14.md: the complete compact source44/source58 tuple,
the native compiler/refutation theorem, and the precise signed Pell-index
recovery interface. No coefficient is selected by assuming consistency.

## Complete polynomial

The thirteen supplied positive integers are

    j,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma.

Every other symbol is a polynomial register; it introduces no witness.
The four fixed coefficient ports are beta,K0,MC,MF, with
beta=2^590069-1 and the whole compact binding, MF already shifted. Put

    J=3j+1, q=beta J+1, C=q-F-alpha,
    E=XY, k=eta+zeta, c=kY+eta,
    a=E+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=EkY, b0=X+ac, I=ic^2,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    r0=k-R-1, U=q^5,
    Dstar=U b0+H(U gamma+q^4 X-r0),
    Kaux=Delta(f^2-1), V=f^2(cT-R)-c,
    W=(q-1)k+1, M=q^3(q-1),
    Bt=(qK0+X)C-qF,
    Z=M(ell+k+r)+(q-1)Y-q^3 W Bt.

Here qF in the formula for Bt means q times the supplied variable F.
The four residuals are

    A0=Z^2-M^2[ell(ell+k)+1],
    A1=Dstar^2-U^2(1+Delta c^2),
    Aa=(V+u)^2-Kaux*u*(2V+u)-1,
    As=f^2-Delta I^2-1.

The fixed polynomial is

    P13=A0^2+A1^2+Aa^2+As^2.

The equation P13=0 is intended over positive integers. The actual division-
free graph p13_degree34.json computes all registers and charges every binary
operation, including multiplication by numerals. build13.py regenerates it.

## Why the first carrier removes transport without a positivity gap

Suppose A0=0. Rational-square-root integrality yields M|Z and an integer
(possibly signed) tau=Z/M with tau^2=ell(ell+k)+1. Since gcd(q,q-1)=1 and
W=1 mod(q-1), reduction of M|Z modulo q^3 and modulo q-1 respectively gives

    q^3|Y,                  q-1|Bt.

Define proof-only integers s=Y/q^3>0 and t=Bt/(q-1). Dividing the literal
carrier then gives

    tau=ell+k+r+s-Wt.

The norm implies |tau|<ell+k: the difference of the relevant squares is
ell*k+k^2-1>0. Therefore

    Wt=ell+k+r+s-tau>0.

As W>0, t>0 and Bt>0. If C<=0, however,
Bt=(qK0+X)C-qF<0, since K0,X,q,F>0. Thus C>0 is recovered BEFORE using
any index argument or the still-unproved q|X. This order avoids the
circular use of compiler bounds that would otherwise invalidate absorption.

Now q>=16, F,alpha>0 and C>0 give 3q<R<q^4-2 exactly as in PROOF14.md.
Also q=2 mod3 and H=3 modq, so gcd(q,H)=1.

## Recover the second scale and the exact Pell index

The proof from PROOF14.md applies, with |tau| used as the positive first
Pell root. Its steps are repeated here to make the logical order explicit.

1. Before q|X is known, Dstar>Uac-Hk>k(UaY-H)>0. A1=0 gives a positive
   integer D=Dstar/U and

       D^2-Delta c^2=1, q^5 | q^4X-r0.            (1)

2. Pell classification supplies A=a+2, P0=2XY^2+1 and p,n>=1 such that
   c=psi_A(p), D=chi_A(p), k=2psi_P0(n), |tau|=chi_P0(n).
   The case n=1 would give k=2 and c<=2Y+1, contradicting p>=2 and
   c>=2A>=4Y+4. Hence n>=2,

       c>kY>=4P0Y>8XY^3>=8q^9>2R.

   P0>A and c>k imply n<p; Pell growth gives c>2p.

3. As=0 gives f=chi_A(m), I=psi_A(m). The divisibility c^2|I implies
   p|m by strong divisibility; writing m=pv and reducing
   I/c=psi_D(v) modc gives c|v. Thus c|m and m>=pc>2p.

4. Let Maux=Delta I and y=|V+u|. Then Kaux=Maux^2 and Aa=0 gives
   Maux^2 V^2-(Maux^2-1)y^2=1. It forces y>0, V!=0; also f>2c>4
   excludes V=+/-1. The congruences V=-c modf and V=-R modc hold,
   since f^2=1 modc. The inherited signed auxiliary-index theorem,
   now with all hypotheses checked, gives p=R.

5. Equation (1) gives q^4|r0. First-Pell congruence gives
   k=2n mod4XY^2; since q^3|Y, its modulus is a multiple of q^4.
   Thus q^4 divides 2n-R-1. With 1<=n<p=R<q^4, this forces 2n=R+1.
   Consequently r0=k-2n is a positive multiple of 4XY^2, hence of U=q^5.
   Equation (1) now forces q|X. Put w=X/q>0 and h=r0/E>0, both integers.

6. The number gamma_old=gamma+w-r0/U is integral, and D=b0+H gamma_old.
   Because D>(a+1)c and c>kY>X, gamma_old>0.

All steps before item5 work with the directly supplied X>=1; they do not
silently assume X=wq or E>=q^4.

## Recover the removed transport coordinate

Once X=qw is known, the already positive integer Bt becomes

    Bt=q[(K0+w)C-F].

Since q-1|Bt and gcd(q,q-1)=1, there is an integer z_new>0 with

    (K0+w)C-F=(q-1)z_new, t=q z_new.

Set z_old=z_new+1>0. Then

    (K0+w)C+(q-F)-z_old(q-1)=1.

The old transport condition is restored exactly, with a positive quotient.
Together with the previously recovered h,s,w,gamma_old, normalized i,f,
and Told=fT, y=|V+u|, this gives a positive solution of the inherited source
kernel. Native compiler soundness therefore gives a finite ZFC refutation.

## Completeness: the new positive gap exists

Start with a canonical compact source witness for a finite refutation.
Its X=2^R, R>3q and q>=16 imply w=X/q>q. As C>=1 and q-F>=2, the transport
identity gives

    z_old(q-1)=(K0+w)C+q-F-1>w+1>q,

so z_old>=2. Define t=q(z_old-1)>=q and W=(q-1)k+1. Set

    r=Wt+tau-ell-k-s.

Canonical tau>ell and k>XY>s give

    r>qW-k-s>0.

Thus the new gap is a positive integer. Substitution gives
Z=M tau, so A0=0. Choose j=(J-1)/3>0 and

    gamma=gamma_old-w+r0/q^5>0

as in PROOF14.md (canonical gamma_old>w and r0/q^5>0).
The same canonical odd-index quotient construction supplies T,u>0 with
V=chi_(Delta I)(R)/(Delta I) and V+u=psi_(Delta I)(R). Therefore Aa=As=A1=0.
All thirteen supplied integers are positive. This proves the reverse
existence implication. Negation and the inherited source calibration yield
in ordinary mathematics formalizable in ZFC

    no positive zero of P13  <=>  Con(ZFC).

## Exact polynomial identities behind the final 93-gate version

A less economical but useful independently specified first carrier sets

    T1=(qK0+X)C+q(q-F-1),
    Zold=M(ell+k+qW+r)+(q-1)Y-q^3WT1.

Since T1-q(q-1)=Bt, Zold=Z identically for every assignment. Factoring this
identity saves three binary gates, reducing the initial 98-operation graph
to 95. Two additional shared-register identities described in
CIRCUIT_OPTIMIZATION.md reduce this to 93. The independent checker deliberately retains Zold as its direct
formula, thereby checking this simplification rather than merely repeating
the builder's version.

## Exact degree and reproducibility

The residual degrees are exactly 15,17,13,14; only A1^2 reaches degree34.
The leading form is

    64(3 beta j)^20 (eta+zeta)^2 X^4 Y^6 gamma^2.

The coefficient of j^20 X^4 Y^6 eta^2 gamma^2 is 64(3beta)^20>0.
The first carrier's degree15 is established by exact cancellation of its
formal degree16 terms, not by a naive DAG bound. check13.py expands each
actual residual and each separate direct formula in all thirteen variables
and four symbolic coefficient ports, and checks equality, exact degree,
leading form, full liveness and gate count. The output degree follows from
the unique highest residual; no cross-square cancellation is possible.
It runs successfully normally and with python -O, using no external packages.

Files: build13.py, its DAG helper dag.py, p13_degree34.json, check13.py,
CHECK13.json. PROOF14.md gives additional source-interface and carrier detail.
The finite checks do not test consistency or replace unbounded semantic
proofs. No newly kernel-checked compiler or object-level ZFC derivation is
claimed.
