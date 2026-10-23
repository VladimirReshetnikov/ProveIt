# Fourteen positive unknowns, exact degree 34, 93 operations

This is a new composition relative to ProveIt snapshot
`beb0192cb8dc36f78c369c080f2adfbc1887a486`, using the whole compact source-44/source-58
coefficient tuple with beta=2^590069-1. The comparison is the existing
fourteen-positive degree-52/79-operation construction in packages 55 and 59.
The new point has 14 positive variables, degree 34, and 93 binary operations.
It reduces degree by 34.615%, with 14 additional gates. It is not a new
fewest-variable, operation-count, or global-optimality result.

## Literal polynomial

Supply exactly the fourteen strictly positive integers

    j,F,alpha,z,f,i,T,X,Y,r,eta,zeta,u,gamma.

Every subsequent letter is an arithmetic register. Use four fixed ports
beta,K0,MC,MF, with MF already shifted by beta. Set

    J=3j+1, q=beta J+1, C=q-F-alpha,
    E=XY, k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=EkY, b0=X+ac, I=ic^2,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    r0=k-R-1, U=q^5,
    Dstar=U b0+H(U gamma+q^4 X-r0),
    Kaux=Delta(f^2-1), V=f^2(cT-R)-c.

The five residuals are

    A0=(q^3(ell+r)+Y)^2-q^6(ell(ell+k)+1),
    A1=Dstar^2-U^2(1+Delta c^2),
    At=q[K0 C+(q-F)-z(q-1)]+XC-q,
    Aa=(V+u)^2-Kaux*u*(2V+u)-1,
    As=f^2-Delta I^2-1.

Define P14=A0^2+A1^2+At^2+Aa^2+As^2.
The intended equation is P14=0 over positive integers. Its literal DAG is
intermediate14/p14_degree34.json; intermediate14/build14.py reproduces it using only the Python standard
library. Operation counts include multiplication by fixed numerals.

## The idea

A square carrier enforces two congruences in a deliberate order. The main
square forces

    q^5 | H(q^4 X-(k-R-1)).

The first carrier gives q^3|Y; q=2 mod3 gives gcd(q,H)=1. Reducing the main
congruence first modulo q^4 recovers the exact first Pell index, because
R<q^4. Only after that exact recovery does the stronger modulus q^5 force
q|X. The fifth power is useful: a q^4 carrier would leave only a q^3 index
modulus, which is smaller than the available bound on R.

The old index quotient h is thereby removed, while both high-degree scaled
coordinates X=wq and Y=sq^3 can remain free inputs. The strong norm is kept
normalized so its rank argument does not require the large-index hypothesis
of the ordinary-strong lemma. Using that latter lemma too early would make
the proof circular.

## Inherited interfaces, precisely

1. The authentic native compiler, with the whole compact tuple, has positive
   outer coordinates q=beta J+1, X=wq, Y=sq^3, c=kY+eta, k=eta+zeta,
   main root D=X+ac+gamma_old H, first root tau, normalized strong witness
   f^2-Delta(i c^2)^2=1, auxiliary norm
   Delta(f^2-1)(Vold^2-y^2)+y^2=1,
   Vold=c(Told f-1)-Rf^2,
   index k-hE-R=1, and transport (K0+w)C+q-F-z(q-1)=1.
   Such a tuple gives a finite syntactic ZFC refutation. Conversely a
   refutation gives canonical tuples of this type. This is the ordinary
   mathematical source interface, not a new formalization claim.
2. Canonical compact tuples have B=2^590069, q=B^N,
   J=1+B+...+B^(N-1), N=581197^n>1 odd, R=3 mod4,
   c=psi_(a+2)(R), and k=2psi_(2XY^2+1)((R+1)/2).
   They permit the padding used in package58. The two canonical positive
   gaps tau-ell-Y/q^3>0 and gamma_old-X/q>0 are proved in package58,
   report §§6.2-6.3, by explicit growth inequalities.
3. Pell classification, strong divisibility, composition, and the signed
   auxiliary-index recovery theorem are the inherited elementary Pell
   interface. The latter says, with A>=2, Delta=A^2-1,
   c=psi_A(p), f=chi_A(m), c|m, m>2p, M>1, c|M,
   M^2=Delta(f^2-1), and 0<p,R<c/2, that an integer solution

       M^2 V^2-(M^2-1)y^2=1,
       V=-c mod f, V=-R mod c

   implies p=R (signed V and y are allowed). This is exactly the signed
   interface used by package57 low_degree/PROOF.md §5, also explained in
   package53 short/PROOF.md §5. Its proof uses the odd-index Chebyshev
   quotient identities and the plus-congruence index step-down theorem.
   No q, X, h or gamma hypothesis is part of this index-recovery lemma.

## Soundness, without premature division or rank assumptions

All five residuals vanish at a positive zero.

1. Rational square-root integrality in A0=0 gives q^3|Y. Set s=Y/q^3>0,
   tau=ell+r+s>0. Then tau^2-ell(ell+k)=1. Since beta=1 mod3 and J=1 mod3,
   q=2 mod3. Also a=Y(X+1), so H=3 modq and gcd(H,q)=1.

2. Dividing At=0 by q over the rationals gives

       (K0+X/q)C+(q-F)-z(q-1)=1.

   If C<=0, its left side is at most 1-F<=0. Hence C>0. With F,alpha>=1,
   the authentic coefficient bounds give

       3q<R<q^4-2, q>=16.

   The upper bound follows from G<q^2-q and
   (MC+q MF)J<(q-1)(1+2q). This argument needs no q|X hypothesis.

3. Dstar is positive before recovering any deleted quotient. Indeed r0<k,
   c>kY, and U a Y>H, so

       Dstar>Uac-Hk>k(UaY-H)>0.

   From A1=0 and square-root integrality, D=Dstar/U is a positive integer
   and D^2-Delta c^2=1. It also follows that

       q^5 | H(q^4X-r0), hence q^5 | q^4X-r0.       (*)

4. Write A=a+2, P0=2XY^2+1. Pell classification yields

       D=chi_A(p), c=psi_A(p),
       tau=chi_P0(n), k=2psi_P0(n),  p,n>=1.

   Since c>1, p>=2. If n=1 then k=2 and c=2Y+eta<=2Y+1, whereas
   c>=psi_A(2)=2A>=4Y+4, contradiction. Thus n>=2. Consequently

       k>=4P0>8XY^2,
       c>kY>8XY^3>=8q^9>2R.

   Since P0>A and c>k, monotonicity gives n<p. Pell growth gives c>2p.
   These bounds are established before recovering q|X or h.

5. As=0 yields f=chi_A(m), I=psi_A(m), m>=1. Since c^2|I, strong
   divisibility gives p|m. Write m=pv. Composition gives
   I=c psi_D(v), and psi_D(v)=v D^(v-1) modc. Because D^2=1 modc,
   c|v. Thus c|m and m>=pc>2p.

   Put M=Delta I. Then M^2=Kaux and c|M. With y=|V+u|, Aa=0 is
   M^2 V^2-(M^2-1)y^2=1. It forces y>0 and V!=0. The congruences are
   V=-c modf and V=-R modc, since f^2=1 modc. We have now checked all
   signed auxiliary-index hypotheses from interface3; hence p=R.
   (For clarity, the impossible V=+/-1 branch is excluded as f>2c>4.)

6. From (*) we have q^4|r0. The first Pell congruence is

       k=2n mod4XY^2.

   Since Y is a multiple of q^3, q^4 divides 4XY^2. Therefore
   q^4 divides 2n-R-1. But 1<=n<p=R and R<q^4 give
   |2n-R-1|<q^4. Thus 2n=R+1.

   Now r0=k-2n is divisible by 4XY^2, hence by U=q^5. Equation (*) then
   gives q^5|q^4X, so q|X. Set w=X/q>0 and h=r0/E. The first congruence
   makes h integral; k=2psi_P0(n)>2n for n>=2 makes h>0.

7. Set gamma_old=gamma+w-r0/U. It is integral, and
   D=b0+H gamma_old. Moreover D>(a+1)c, and c>kY>X, so

       H gamma_old=D-ac-X>c-X>0.

   Thus gamma_old>0. The previously rational transport is now the original
   integer transport. Take Told=fT>0 and y=|V+u|>0; then
   Vold=c(Told f-1)-Rf^2=V. We have recovered the complete positive
   normalized source interface. Its soundness gives a finite ZFC refutation.

## Completeness and positivity

Start with a canonical positive source tuple for a refutation. Keep the
normalized i and f. Put the directly supplied X=wq, Y=sq^3 and

    j=(J-1)/3,
    r=tau-ell-s,
    gamma=gamma_old-w+(k-R-1)/q^5.

The first is a positive integer because J=1 mod3 and J>1. The second is
positive by interface2. The third is integral because k-R-1 is a multiple
of 4XY^2, itself a multiple of q^7 for the canonical scales. It is positive
because gamma_old>w and k>R+1. Substitution gives Dstar=q^5 D.

It remains to supply the squared-modulus auxiliary pair. Put M=Delta i c^2.
For R=2v+1=3 mod4, the odd-index polynomial identities give

    V*=chi_M(R)/M>1, y*=psi_M(R)>V*,
    V*=-c mod f^2, V*=-R mod c.

Since gcd(c,f)=1 and f^2=1 modc, the number

    T=(V*+c+Rf^2)/(cf^2)

is a positive integer. Set u=y*-V*>0. These are exactly the canonical
squared-modulus reconstruction of packages51/58, with M in place of their
ordinary strong root. All five new residuals vanish. This proves both
existence implications, hence after composition and negation the claimed
ordinary ZFC-provable equivalence with Con(ZFC).

## Degree and finite verification

The residual degrees are exactly (11,17,3,13,14). The only degree34 contribution
to P14 is A1^2. Write Q=3 beta j. Its leading form is

    in_34(P14)=64 Q^20 (eta+zeta)^2 X^4 Y^6 gamma^2.

Thus the coefficient of j^20 X^4 Y^6 eta^2 gamma^2 is 64(3beta)^20>0.
The main cancellation is, with Z=U gamma+q^4X-r0,

    A1=U^2(2acX+X^2-Hc^2-1)+2U(ac+X)HZ+H^2Z^2.

The independent standard-library checker expands the actual DAG and these
separately specified formulas in all fourteen witnesses and four symbolic
ports. It proves finite polynomial identities, exact degrees, leading forms,
liveness and the 93-gate ledger. It also runs a few finite Pell-carrier
examples; those examples are explicitly not semantic validation or consistency
searches. Run `python3 intermediate14/build14.py` and `python3 intermediate14/check14.py`.

No new end-to-end Lean/Rocq or object-language ZFC derivation is supplied.
The compiler and index step-down theorem remain explicit inherited inputs.
