# Combining transport absorption with an adaptive second carrier

## Results and limits

This is an incremental composition, not the requested qualitative breakthrough.
It gives thirteen positive witnesses, degree 30 and 94 operations, versus the
inherited degree34/93 form. It also gives twelve positive witnesses, degree114
and105 operations, versus degree118/104. The SOS sibling has degree172/104
and is not a new degree record. No claim of global minimality or new kernel
verification is made.

The exact literal polynomials are p13_degree30.json and
p12_product_split2.json. Their four ports are the **whole** source44/source58
compact tuple: beta=2^590069−1, K0, MC, and already-shifted MF. No ports from a
second encoding may be substituted. The inherited native compiler and K215
calibration are mathematical dependencies, not tests performed here.

## Explicit construction

Use every register, witness and residual in inherited/PROOF13.md, with exactly
one replacement. Instead of U=q^5 and q^4 X in Dstar, set

    K=4qY, U=qK=4q^2Y,
    Dstar=U(X+ac)+H(U gamma+KX−r0), r0=k−R−1.

The thirteen witnesses remain j,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma.
A0,Aa,As are unchanged, A1=Dstar^2−U^2(1+Delta c^2), and
P13=A0^2+A1^2+Aa^2+As^2. All letters are polynomial registers, never additional
witnesses. The builds include the entire formula rather than a patch requiring
runtime access to the inherited graph.

For twelve witnesses use every formula in inherited/AUDIT12.md with this same
replacement to A1. Keep J=6j+1, the divided auxiliary norm N, and finalizer
P12=(1+A0)(1+A1)(1+N)−1. Its witnesses remain
j,F,alpha,i,T,X,Y,r,eta,zeta,n,gamma.

## Ordered soundness of the thirteen-variable construction

1. A0=0 is unchanged. Its rational-square-root argument gives q^3|Y and
(q−1)|Bt, where Bt=(qK0+X)(q−F−alpha)−qF. Write s=Y/q^3 and t=Bt/(q−1).
The identity tau=ell+k+r+s−Wt, W=(q−1)k+1, and |tau|<ell+k show t>0.
Thus C=q−F−alpha>0 BEFORE any use of q|X. The authentic coefficient bounds
give q>=16 and 3q<R<q^4−2. Also q=2 mod3 and H=3 modq, so gcd(q,H)=1.

2. Dstar is strictly positive: r0<k, b0=X+ac>akY, H<5a, and UY>5 give
Dstar>Ub0−Hk>ak(UY−5)>0. Square-root integrality in A1 gives the positive
integer D=Dstar/U and U|H(KX−r0). Reducing modulo K yields K|Hr0.
Since H is odd, gcd(q,H)=1, and gcd(Y,H)=gcd(Y,3), d=gcd(K,H)<=3.
Consequently mu=K/d divides r0, and mu>=4qY/3>=4q^4/3>R+1.
This step does not require q|X.

3. The unchanged normalized strong equation As=0 is used, NOT the ordinary
strong equation in the SharedTaps endpoint. The argument of inherited/PROOF13.md
therefore applies without an X>q syntactic shift. Classifying the first and
main Pell roots gives positive indices n_first,p, with n_first<p. The case
n_first=1 is impossible since it gives k=2, c<=2Y+1, whereas p>=2 gives
c>=2(a+2)>=4Y+4. Thus c>8XY^3>=8q^9>2R and c>2p.
The normalized strong condition gives f=chi_A(m), c|m and m>=pc>2p.
With the auxiliary norm all hypotheses of the signed index lemma hold,
so p=R. This uses only already proved bounds, not the deleted index quotient.

4. First-Pell congruence gives k=2n_first mod4XY^2. Since q|Y,
K=4qY divides 4XY^2. Thus mu divides 2n_first−R−1. Since
1<=n_first<p=R and mu>R+1, this implies 2n_first=R+1 exactly.
Hence r0 is a positive multiple of 4XY^2. The quotient
(4XY^2)/U=XY/q^2 is integral because q^3|Y; therefore U|r0.
Returning to U|H(KX−r0) gives q|HX and then q|X. Put w=X/q>0.
The old index coordinate h=r0/(XY) is a positive integer.

5. Define gamma_old=gamma+w−r0/U. The carrier gives
D=X+ac+H gamma_old. The main positive Pell root satisfies D>(a+1)c,
and c>X by n_first>=2, so gamma_old>(c−X)/H>0.
The unchanged transport recovery gives z_old=t/q+1>0 and restores the exact
source transport equation. The inherited native kernel thus yields a finite
ZFC refutation. Every deleted source witness is recovered as an integer with
the sign needed by that interface.

## Completeness

Take a canonical compact source witness, with X=qw, Y=sq^3,
2n_first=R+1 and r0 a positive multiple of 4XY^2. As above U|r0.
Set gamma=gamma_old−w+r0/U. The inherited canonical gap gamma_old>w
makes this strictly positive. The old first carrier's canonical r is unchanged
and positive; the unchanged canonical odd-index construction provides T,u,f,i.
The modified carrier now satisfies Dstar=UD, so all four residuals vanish.
Thus positive solvability of P13 is equivalent to a finite ZFC refutation.

The twelve-variable norm elimination is unchanged literally except A1. Its
signed root recovery, absence of zero denominator, and canonical congruence
are proved in inherited/AUDIT12.md. It lifts each new P12 solution to a new
P13 solution with j13=2j12, f13=|f| and u13=|y|−V>0. Conversely the canonical
auxiliary ordinate y=-1 modQ yields the positive new n. In the product finalizer
q is even, so U=4q^2Y is even. A0,A1,N are squares modulo4, hence no unit
factor can equal−1. Thus P12=0 iff all three residuals vanish. Negation yields,
in ordinary mathematics formalizable in ZFC, no positive zero iff Con(ZFC).

## Exact algebra and accounting

check13.py independently expands each residual and compares it with a separately
written formula. Degrees are exactly 15,13,13,14, giving degree30. A0 has nonzero
leading term −2 q0^8 k0^2 X Y^2 Bt0, with
q0=3 beta j, k0=eta+zeta, Bt0=(K0q0+X)(q0−F−alpha)−q0F.
Its alpha X term proves nonvanishing after all fixed-port specializations.
check12.py verifies the prefix and the divided norm over independent cut
registers. Degrees15,13,86 give product degree114. A fixed-port-independent
selected leading coefficient is recorded in CHECK12.json. All arithmetic
operations, including multiplication by numerals, are counted; powers are
computed by multiplication gates. These tests do not establish unbounded
semantics or consistency.
