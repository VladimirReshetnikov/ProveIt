# A smaller quartic: 32 positive variables and 23 quadratic equations

Source pin: `3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

This combines the inputless coefficient recipe of package 06, the ordinary
strong norm of package 02, and the quadratic lifting idea of package 08.
Its additional savings come from restoring the two original auxiliary
quotients and then eliminating the main index, which becomes linear.

All four coefficients are the cross-compiler numerals in `../compiler/cross_constants.json`: beta=B−1,
K0, MC and MF, with MF the *shifted source port*. The coherent original
package-06 tuple is an alternative. In particular no coefficient
from the independently normalized package 08 is substituted.

## Literal system

The 32 unknowns are

    J,F,alpha,z,f,h,i,s,w,tau,eta,zeta,y,gamma,o,j,
    N,E,P,c,a,X,D,C2,G,L,F2,V,g,I,Baux,Delta.

Initially all are strictly positive integers. The following are abbreviations,
not additional unknowns:

    q=beta*J+1, k=eta+zeta, H=4a+3, C=q−F−alpha,
    R=k−1−hE.

The first four are affine and the last is quadratic. The 23 equations are:

1. L=q²−1.
2. N=q(L+1).
3. X=wq.
4. a=E+sN.
5. E=X(a−E).
6. c=k(a−E)+eta.
7. P=E(c−eta)+k.
8. tau²=P(P−k)+1.
9. D=X+ac+gamma H.
10. Delta=a²+H.
11. C2=c².
12. D²=Delta C2+1.
13. G=(q−1)(q−F)+alpha.
14. R=LG+(MC+q MF)J.
15. (K0+w)C=F+z(q−1).
16. F2=f².
17. V=of−c.
18. V=jc−R.
19. g=y²−V².
20. I=i C2.
21. Baux=I².
22. Baux=Delta(F2−1).
23. y²=Baux g+1.

After the abbreviations are expanded every residual has total degree at most
two. The explicit expanded residuals are in `quartic32.json`. Their sum of
squares is one degree-four integer polynomial. Its coefficient of tau^4 is
1, so the degree is exact. Replacing every unknown by n+1 gives a quartic
in 32 nonnegative unknowns.

## Why it represents the same positive solvability problem

Equations 1–7 give

    Y=a−E=sq³, E=XY, a=Y(X+1), c=kY+eta,
    P=EkY+k.

Thus equation 8 is the ordinary first norm

    tau²−XY²(XY²+1)k²=1.

Equations 9–12 give the main norm, equations 13–15 give packing and transport,
and 20–22 give the ordinary strong equation

    (ic²)²=Delta(f²−1).

The auxiliary coefficient is therefore a square. Equations 19 and 23 give

    I² V²−(I²−1)y²=1.

These are the blank ordinary-strong equations with the original two
auxiliary congruences exposed. The same first/main bootstrap as package 02,
using the package-06 bounds on R, gives c=psi_A(p)>A Delta², c>2p and c>2R,
where A=a+2. The ordinary strong-rank theorem gives

    f=chi_A(m), c|m, p|m, I=Delta psi_A(m), c² | f²−1.

The signed auxiliary step-down theorem gives p=R from V=of−c=jc−R. In the
present positive system its hypotheses follow directly from o,j,V>0.
The unchanged half-binomial/Pell and compiler arguments recover an accepting
blank computation, and hence a finite ZFC refutation.

To compare explicitly with the 15-coordinate ordinary system, put

    T=(o+Rf)/c.

This is an integer: from of+R=(j+1)c,

    o+Rf=f(of+R)−o(f²−1)

is divisible by c. It is positive. Moreover

    c(Tf−1)−Rf²=of−c=V.

Conversely, any positive source solution supplies

    o=cT−Rf,
    j=Tf−1−R(f²−1)/c.

The package-02 rank and positivity proof shows these are positive integers;
the remaining registers have the displayed unique values. The auxiliary
norm implies (Baux−1)g=V²−1, so g>0. All introduced positive coordinates
therefore exist.

The shift of the transport quotient is z=new, with old quotient z+1. In a
positive source solution, X=2^R and w=X/q>q>F. Since C≥1, the equation
(K0+w)C−F=(old_z−1)(q−1) has positive left side, so old_z≥2. Thus the
new quotient is strictly positive. The inverse shift is immediate.

## Where the two-variable saving comes from

The old 34-variable lift used the normalized strong relation. Replacing it
by the ordinary strong relation changes I=i Delta c² to I=ic². Its register
K=Delta c² is then used only to state D²−1=K=Delta C2; eliminating K saves
one variable and one equation.

Next, replacing the merged auxiliary quotient T and its register V0=Tf−1
by o and j preserves the variable count. R then occurs only linearly.
Eliminating it with R=k−1−hE saves another variable and another equation.
The result is 32 variables and 23 quadratics, compared with 34 and 25.

## A 50-variable equation over all integers

Only the following nine quantities need positive-domain guards:

    J,F,alpha,z,i,s,w,eta,zeta.

All 23 remaining unknowns may range over all integers. This larger domain
has the same *existence* of solutions; it need not have a tuplewise map to
the positive system preserving every coordinate.

The scale equations force q,L,N,X,Y,E,a,c,C2,Delta,P positive. Transport
with z,F>0 forces C>0, so G and the packed R are positive. The usual bounds
give E>R+2 and 0<R<q^4. The first norm yields

    k=2 psi_P0(n), P0=2XY²+1,
    2n≡R+1 (mod E), n≥(R+1)/2≥24.

No positivity of h is needed here. The main equation classifies |D|, yielding
c=psi_A(p), p>n and c>A Delta²,c>2p,c>2R. The ordinary strong theorem applies
to |f| and gives |f|=chi_A(m), c|m, c|I, m≥c>2p. In particular I>1.

For the auxiliary norm, V cannot vanish. Classify

    |I V|=chi_I(ell), |y|=psi_I(ell).

Since I divides chi_I(ell), ell=2v+1 is odd. Let sigma be the sign of V.
Writing chi_X(2v+1)=X Q_v(X²) gives V=sigma Q_v(I²). The polynomial identities

    Q_v(1−A²)=(-1)^v psi_A(ell),
    Q_v(0)=(-1)^v ell

show, modulo |f| and c respectively, that

    psi_A(ell)²≡c² (mod |f|),
    sigma (-1)^v ell≡−R (mod c).

The signed chi step-down lemma, after doubling, gives ell≡±p (mod m), hence
mod c. Consequently R≡±p (mod c), and 0<p,R<c/2 forces p=R. Neither o nor j,
nor V,f,y, needed a prescribed sign.

The index no-wrap and ratio arguments now give R=2n−1. Write r=n−1, so
R=2r+1 and r≥24 in the valid compiler range. The elementary Pell bounds

    psi_b(t)>(2b−1)^(t−1) for t≥2,
    psi_b(t)≤(2b)^(t−1)

and (2A−1)²>2P0 X imply

    Y+1>c/k=psi_A(2r+1)/(2psi_P0(r+1))>X^r/2.

Thus Y>X^r/3>2^R and Y>X. This excludes the negative main root. Indeed the
two Pell sequences chi_A(t)−a psi_A(t) and chi_A(t)+a psi_A(t) reduce modulo
H=4a+3 to 2^t and 2^(−t), respectively. These identities follow directly
from the recurrence; no division by 3 is needed. If D<0, equation 9 implies

    X 2^R≡−1 (mod H),

contrary to 0<X 2^R<XY<a<H−1. Therefore D>0 and X=2^R. Finally

    D−ac=2c−psi_A(R−1)>c>Y>X

implies gamma>0. The native compiler soundness argument now proceeds
unchanged. Completeness follows from the original positive construction.

For each of the nine guarded quantities substitute its own copy of

    Pos(u,v,w)=1+u²+v²+w(w+1).

This is positive for all integers, and represents every positive integer
by the three-square theorem applied to 4(n−1)+1. The other 23 coordinates
remain unrestricted. There are 9*3+23=50 integer unknowns. Every residual
has degree at most four, and their sum of squares has exact degree eight:
the first residual has nonzero degree-four leading part

    −beta²(J_1²+J_2²+J_3²)².

The sum of squares of the leading residual forms cannot vanish identically.

## Audit scope

`build_quartic32.py` uses only the Python standard library and the included
small sparse-polynomial module. It emits all residuals, verifies degree and
coordinate counts, and checks the exact first-norm and quotient-restoration
identities. It is not a Lean or Rocq proof and does not independently verify
the inherited compiler or generic Pell theorems. No global optimality is
claimed. The coefficient numerals remain finite recipes of astronomical
size, just as in the source construction.

