# Three Pell square conditions compressed to one square

## Result and scope

There are four new fixed integer polynomials, each in ten strictly positive
integer unknowns. The scaled profiles are 87 operations at exact degree 436
and 88 operations at exact degree 380. The direct profiles are 92 operations
at degree 384 and 93 operations at degree 334. Operations are live binary
additions, subtractions and multiplications, including fixed-constant
multiplications. These improve the operation count of the 89/288 and 94/262
uncentered predecessors, not their degrees. No global minimum is asserted.

The new mechanism is simultaneous coprimality with both auxiliary-Pell
factors. It replaces the four-factor two-root norm by one square equation.
All coefficients are the complete, coherent compact44 BFS tuple bound in
each JSON file. This is not a mixture with the public indexed tuple.

The new unbounded arithmetic argument composes with the retained ordinary
native/controller/refutation calibration. Its conclusion is that ZFC proves
absence of positive zeros equivalent to Con(ZFC), with the inherited finite
refutation convention. It is not a new Lean theorem or an internal
object-ZFC proof object, and it does not assert consistency.

## Complete polynomial definition

The positive unknowns are J,F,alpha,i,T,w,Y,n,eta,zeta on the scaled chart;
replace w by x on the direct chart. The four fixed integer ports are beta,
K0,MC,MF, with beta odd, beta>=31, K0>0 and 0<MC<beta<MF<2beta.
Their complete literal payloads and finite recipe are in coefficients/.

Define the following integer polynomials. No displayed intermediate is a
separately quantified variable.

    q=beta J+1, C=q-F-alpha, mu=q^2+1,
    scaled: X=wq, h=q-1, B=(K0+w)C-F, P=q^3(q-1), low=(q-1)Y-q^3 B,
    direct: X=q+x, h=q(q-1), B=(qK0+X)C-qF, P=q^4(q-1),
            low=q(q-1)Y-q^3 B-(q-1)X,
    A=mu Y(X+1)+1, Delta=A^2-1, H=4A-5,
    k=eta+zeta, c=kY+eta, Vfirst=X mu^2 Y^2,
    D=1+Vfirst(Vfirst+1)k^2,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J, e=k-R-1,
    Kc=1+Delta c^2, E=i c^2 A Kc,
    Fstrong=1+Delta D E^2, Q=Delta^2 D E^2, delta=Q-1,
    b=c(T+alpha)-R, V=Fstrong b-c,
    Dnum=Q V^2-1, G=D Fstrong, Kpos=X(3c-2X)+2,
    M=P mu^2 H.

For the 87/436 and 92/384 equations set L=V^2. For the 88/380 and
93/334 equations set L=(Delta D E)(Fstrong b). Then put

    Z=P mu^2 [H(n-LB)+Kpos]+H[mu^2 low-Pe],
    N=delta Z^2-M^2 G Dnum.

The equation is N=0. Its complete literal circuit, without divisions,
square roots, exponentiation gates or hidden witnesses, is supplied in each
equations/*.json file. The normalized rational identity used only in proofs is

    Z/M=n+Kpos/H+Y/q^3-(1+hL)B/h-e/mu^2-[X/q^4].             (1)

The bracket is present only on the direct chart. Relative to the predecessor,
the first, main and auxiliary kernels have the same functional form, but
the strong ordinate has been additionally saturated by A Kc. There is no V
or other large polynomial center in (1).

## 1 Root recovery before any transport or source argument

All positive inputs give A>6, c>=3, E>=c^2 A Kc, D>1 and delta>4.
Fstrong>c+2. Because b is integral, V=Fstrong b-c is nonzero and |V|>1:
if b=0 then V=-c; otherwise |V|>=Fstrong-c>1. Hence Dnum>0.

The following are polynomial congruences, valid before any square root is
known to be integral:

    Fstrong = 1 mod D, delta = -1 mod D, Dnum = -1 mod D;
    delta = -A^2 mod Fstrong;
    Dnum = -(1+Delta c^2) = -Kc mod Fstrong.

The last line uses Q=Delta(Fstrong-1) and V=-c mod Fstrong.
Because A and Kc divide E, Fstrong is 1 modulo both A and Kc. Thus

    gcd(D,Fstrong delta Dnum)=1,
    gcd(Fstrong,delta Dnum)=1.                              (2)

At a zero of N, the positive integer D Fstrong delta Dnum is the rational
square (delta Z/M)^2, hence is an integer square. By (2) and unique prime
factorization, D and Fstrong are separately squares. Write D=tau^2 and
Fstrong=f^2 with tau,f positive integers. Also delta Dnum is a square,
so y=sqrt(Dnum/delta) is rational. Set I=tau E. Then

    f^2-Delta I^2=1, Q=(Delta I)^2, c^2 divides I,
    Q V^2-(Q-1)y^2=1.                                    (3)

The retained adjacent-Pell descent makes y a positive integer. Its short
proof does not assume a particular sign of V. Write y=a/m in lowest terms,
so m^2 divides Q-1. For v=|V|>1 the transformation

    v'=(2Q-1)v-2(Q-1)y, y'=(2Q-1)y-2Qv

preserves Qv^2-(Q-1)y^2=1, has integral nonzero v' with |v'|<v, and
preserves the reduced denominator m of y'. The inequalities needed are
v<y<Qv/(Q-1). Taking absolute values and descending reaches v=1,y=1;
therefore m=1. The original square equation consequently gives

    Z/M=epsilon tau f y, epsilon in {-1,+1}.                (4)

The single-square compression has recovered exactly the three required
Pell conditions and an integral carrier. It did not assume parity, B>=0,
the main index identity, or any source semantics.

## 2 The transport majorants are sufficient

The inherited all-index strong/auxiliary folding lemma applies to (3), with
c<=I, c^2|I and V=-c mod f. It gives c=psi_A(p) for positive odd p.
The unchanged first norm gives k=2 psi_(2Vfirst+1)(j), and j=1 is excluded
as in the predecessor: it would give k=2 and c=2Y+1 strictly between the
first two main ordinates. Thus k>=8Vfirst+4 and

    c>8X mu^2 Y^2, Kpos>0, H>3X.

The unconditional retained mask estimate R<c alpha/4 yields

    b=c(T+alpha)-R>c>k,X, V>(Fstrong-1)b>b>1.

This order does not use the sign of B. Put g=tau f and a=g y. The strong
norm gives f<A I, so g<A D E. Furthermore

    V>(Fstrong-1)c=Delta D E^2 c>4 A D E>4g,               (5)

because Delta/A>A-1>5 and E c>=1. The auxiliary equation gives y<2V.
Therefore a<2gV<V^2/2. Also b-e=c(T+alpha)-k+1>0, so

    rho=e/mu^2<b/4,
    [X/q^4]<b/4.                                        (6)

If rho is negative the same one-sided estimate remains valid. For L=V^2,
(5)-(6) show a+rho+[X/q^4]<L, since b<V<V^2.

For the lower-degree variant, SE=Delta D E>4g, so
L=SE(Fstrong b)>4gV>2a and also L-a>2gV>b. This again gives
a+rho+[X/q^4]<L. All inequalities are strict and pre-transport.

Solve (1) and (4) for the positive coordinate n:

    n=epsilon a-Kpos/H-Y/q^3+(1+hL)B/h+rho+[X/q^4].       (7)

If B<=-1, the transport term is at most -L-1/h. Equations (5)-(6),
Kpos/H>0 and Y/q^3>0 make the right side negative. Hence B>=0. Since
F>0, its definition on either chart forces C>0.

## 3 Later source reconstruction

This is the precise inherited dependency boundary. B>=0 gives
3q<R<q^4-2. The normalized strong rank and signed auxiliary-index lemmas,
using c^2|I and the same congruences V=-c mod f and V=-R mod c, give p=R.
Odd R gives even q and odd J. Only then does gcd(mu^2,PH)=1 isolate
mu^2|e from the integral carrier (4). The first-index congruence yields
j=(R+1)/2. The zero-offset ratio estimates give Y>X^r/3 and
X^(r+1)<H, where R=2r+1, r>=48.

The carrier still gives H|P Kpos. The retained whole-product projection,
without cancelling a nonunit through H, then gives X=2^R. The direct
chart's later q|X and q^4|X steps remain in their original order. The
remaining fractions give q^3|Y and the nonnegative integer t=B/h (after
B=q Bt on the direct chart). The only required property of the changed
weight is 1+hL=1 mod h, which holds for every integer L. The fixed-minus
parity, half-binomial rounding and fresh unscaled source reconstruction
are unchanged. Consequently a positive zero yields a finite refutation
under the whole calibrated coefficient tuple.

Replacing a sum of roots by their product does not assert any root-index
identity not already obtained from the three recovered equations. The
later argument uses only integrality of the normalized carrier, not the
particular integer on its right side. Full statements of the inherited
interfaces and their original proofs are retained in provenance/.

## 4 Fresh positive completeness

Starting from a finite refutation, take the canonical outer and first-Pell
data supplied by the inherited source theorem: X=2^R, R=3 mod 4, r>=48,
q^3|Y, t=B/h>=0, c=psi_A(R), D=tau^2, eta,zeta>0, and
rho=(k-R-1)/mu^2>=1. Do not retain the former strong witness.

Choose a positive Pell index m such that

    tau c^2 A Kc divides psi_A(m).

It exists because the determinant-one recurrence matrix is invertible
modulo this fixed positive modulus, and a positive power is the identity
in the finite matrix group. Let I=psi_A(m), f=chi_A(m), and
i=I/(tau c^2 A Kc)>0. This gives exactly E=i c^2 A Kc and (3).

Apply the inherited auxiliary-completeness lemma to this fresh strong
pair, obtaining the same positive T and positive y,V with (3). All source
congruences, including the construction of T=Tstar-alpha>0, are unaffected
by adding a divisor to the strong period. Set the actual L to either
specified polynomial and define the integer

    n=tau f y-Kpos/H-Y/q^3+(1+hL)t+rho+[X/q^4].            (8)

The canonical estimates give tau>Y>=Y/q^3 and f>Xc>Kpos/H. Since
tau,f>=3 and y>=1, tau f y>=tau f>tau+f>Y/q^3+Kpos/H.
All remaining terms in (8) are nonnegative, so n>0, even when t=0.
The carrier equals tau f y, proving N=0. Every quantified coordinate is
strictly positive. This is a fresh existence construction, not a claim
of a positive pointwise inverse from the predecessor's zero set.

## 5 Exact global degree and literal counts

All variables have degree one and all four coefficient ports degree zero.
The following degrees and leading forms follow directly from the literal
definitions. Let q0=beta J, k0=eta+zeta, X0=q0 w on the scaled chart and
X0=q0+x on the direct chart. Put c0=k0 Y, A0=q0^2 Y X0,
D0=q0^8 X0^2 Y^4 k0^2, E0=i A0^3 c0^4. Then the leading forms of
Fstrong,Q,b,V,M are respectively

    F0=A0^2 D0 E0^2, Q0=A0^4 D0 E0^2,
    b0=-q0^3(q0-F), V0=F0 b0,
    M0=4q0^8 A0 (scaled), 4q0^9 A0 (direct).

The B leading forms are B0=w(q0-F-alpha) on the scaled chart and
B0=(q0 K0+X0)(q0-F-alpha)-q0 F on the direct chart. Each is nonzero,
including for the actual fixed tuple; on the direct chart the coefficient
of x alpha is -1.

    register        scaled   direct
    A                  5        4
    Delta             10        8
    c                  2        2
    Kc                14       12
    E                 24       21
    D                 18       16
    Fstrong           76       66
    Q,delta           86       74
    b                  4        4
    V                 80       70
    Dnum             246      214
    G                 94       82
    M                 13       13
    B                  2        2

For the low-operation variant, L0=V0^2 and deg L=160 or140. The uniquely
highest part of Z is -M0 L0 B0, of degree175 or155. Consequently
delta Z^2 has degree436 or384 and leading form Q0 M0^2 L0^2 B0^2.
The other summand M^2 G Dnum has degree366 or322, strictly smaller.
Thus N has exactly degree436 or384.

For the lower-degree variant, L0=A0^2 D0 E0 F0 b0, of degree132 or115.
The same unique-dominance calculation gives deg Z=147 or130 and
deg N=380 or334. These exceed366 or322 respectively. The same product
Q0 M0^2 L0^2 B0^2 is the nonzero leading form. The domain is an integral
polynomial ring, so these are global attained degree proofs for the actual
fixed coefficients, not degrees inferred from a sampled specialization.

The literal source-row comparison is: add five saturation gates, delete
the one n+V gate, and replace the thirteen-gate two-root tail by a
seven-gate square tail, saving two gates overall. V^2 was already live.
The lean majorant adds one multiplication. Independent topological and
backward-live checks ensure every counted row and every input is used.

## 6 Finite checks and their limits

build.py reads the frozen parent JSON, never imports its source programs,
and constructs the four complete graphs. verify.py independently checks
the literal definitions, normalized carrier, all coefficient payload hashes,
coprimality identities, exact polynomial replays and leading terms, and
dependency liveness. Normal and optimized Python runs must agree. These
finite checks supplement the unbounded proof; they do not establish the
absence of zeros or replace the inherited logical calibration.
