# Four separated roots: twelve unrestricted integers, degree 512, 132 operations

## Result and boundary

The complete fixed polynomial `integer12_degree512.json` has twelve unrestricted
integer unknowns, exact total degree 512, and 132 live binary operations:
82 multiplications, 25 additions and 25 subtractions. Every square and scalar
multiplication is charged. Named registers are abbreviations, not unknowns.
The six full coefficient integers are retained, including the already shifted
MF. The new reduction has integer zeros exactly when the inherited signed
fifteen-variable kernel does. Composing the explicitly inherited ordinary
native/compiler/refutation calibration proves in ordinary ZFC that universal
integer nonvanishing is equivalent to syntactic Con(ZFC). This does not prove
consistency, assert nonvanishing, supply a new end-to-end kernel certificate,
or claim a global minimum. The 13/152/119 predecessor remains a different
variable/degree/cost tradeoff. The current twelve-integer comparison points include degree500/139 operations
(source121) and degree1084/123 operations (source113). This new point trades
seven fewer operations for twelve more degrees against the former, and nine
more operations for 572 fewer degrees against the latter. It is not a
twelve-variable or twelve-variable-degree record. Those are distinct earlier
constructions, not the immediate parent. Across variable counts the catalogued
11/398/121 equation dominates this 12/512/132 point; the new
contribution is a simpler four-root elimination and a within-twelve tradeoff,
not a global Pareto-frontier result.

## 1. Entire literal polynomial

Inputs in literal order are

    j,C,z,h,r,v,w,T,c,n,p1,p2 in Z.

The six supplied fixed ports are beta,K0,MC,MF,cone_A,cone_B. Their complete
bytes and finite reconstruction recipe are in
`inherited_round20/inherited/coefficients`. In particular
beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104. Define

    J=6j+1, qm=beta J, q=qm+1, W=12w+4, X=qW, Y=v,
    F=(K0+W)C-z qm,
    R=[q(q-F)-C](q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    ell=EY, k=R+1+h ell, eta=c-Yk, L=ell k,
    I=(2r+1)c^2, Ds=Delta I^2, Fs=1+Ds,
    Q=Delta Ds, V=Fs(cT-R)-c,
    q3=q^3, M=2q3, U=MH, Klo=X(2X-3c)-2,
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    budget=(Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(kq^2)^2],
    G=4(budget-p1^2-p2^2)-3,
    Dt=1+L(L+k), U2=U^2,
    Zc=U(n+2L)+M Klo+H(Y-q3),
    delta=Q-1, Cy=QV^2-1, DU2=delta U2,
    s=delta Zc^2, aa=DU2 Fs, bb=9 DU2 Dt,
    cc=729 DU2 G, dd=81 U2 Cy,
    sdplus=s+dd, acsum=aa+cc, acprod=aa cc,
    pairs=acprod+bb acsum, m=sdplus-acsum-bb,
    m2=m^2, sd=s dd, hh=m2+4(sd-pairs),
    triple=acprod bb,
    n0=hh^2+16[sd m2-4 triple sdplus],
    P=n0^2-64 sd(m hh-16 triple)^2.

Only additions, subtractions and multiplications occur. All powers displayed
here are fixed small natural powers. There is no division or proof search in
this polynomial.

## 2. Universal norm identity and nonzero denominators

For independent formal arguments define H4(s,aa,bb,cc,dd) by the final eleven
registers above. It is homogeneous of degree eight in these five arguments,
and satisfies the exact identity

    H4(z^2,A,B,C,D)
       = product over eps in {+1,-1}^4
         (z-eps1 sqrt(A)-eps2 sqrt(B)-eps3 sqrt(C)-eps4 sqrt(D)).   (1)

This identity is formal: it holds over the complex numbers with any choices
of square roots, including zeros or coincident square classes. One derivation
substitutes z+sqrt(D) and z-sqrt(D) into the three-root norm and multiplies.
The independent standard-library checker multiplies all sixteen linear factors
and compares every coefficient with the printed formula.

Unconditionally q is even and nonzero: beta is odd and greater than one,
and beta(6j+1)=-1 is impossible. Thus |q|>=2, |W|>=4, |X|>=8.
The integer a=(X+1)Y is zero or has absolute value at least seven, whence
Delta=(a+2)^2-1>=3. H is odd and nonzero, so U is nonzero.
Also ell=XY^2 is even and ell(ell+1)>=0. Therefore

    Dt=1+ell(ell+1)k^2>=1, Fs=1+Delta I^2>=1.

Since Q=(Delta I)^2, either Q=0 or Q>=9. Consequently delta never vanishes;
Cy also never vanishes (when Q=0 it is -1, and otherwise QV^2 cannot be one).
G=1 mod4, so G never vanishes. These statements precede every zero assumption.

Writing rho=Zc/U, homogeneity and (1) give

    P=delta^8 U^16 product over eps in {+1,-1}^4
      [rho-eps1 sqrt(Fs)-3 eps2 sqrt(Dt)
           -27 eps3 sqrt(G)-9 eps4 sqrt(Cy/delta)].                (2)

The denominator clearing delta^8 is exact. No division gate is hidden in P;
(2) is proof notation for the literal polynomial in Section 1.

## 3. Four-root separation, including signed and dependent square classes

The fixed beta is 1 modulo 3 because 1064921 is odd. Hence, for every input,

    J=1, q=-1, W=1, X=-1, a=H=Delta=0             (mod 3).

It follows that Fs=1, Q=0 and delta=Cy=-1 modulo 3. Furthermore
ell=-Y^2 modulo 3, so ell(ell+1)=Y^4-Y^2=0 modulo 3 and Dt=1 modulo 3.
Thus the squared 3-adic valuations of the four summands, in order

    sqrt(Fs), 3sqrt(Dt), 9sqrt(Cy/delta), 27sqrt(G),

are 0, 2, 4, and 6+v3(G)>=6. The auxiliary valuation is a rational valuation;
its integrality has NOT yet been assumed.

For completeness, write every nonzero rational radicand as d u^2, where d is
a signed squarefree integer and u is a nonzero rational. Distinct radicals
sqrt(d), including d=1, are linearly independent over Q. This follows by
adjoining square roots of the relevant primes and -1 and applying character
projections for the sign-change automorphisms. The argument includes negative
radicands and dependent multiplicative square classes.

Group a vanishing factor of (2) by its signed squarefree classes. Consider
an irrational class d!=1 (the rational rho belongs to class 1). A class
containing any of the first three roots has v3(d)=0. Its coefficients among
those roots have distinct valuations 0,1,2; its guard coefficient, if present,
has valuation at least 3. Every nonempty such group therefore has a unique
least-valuation coefficient and cannot sum to zero. A class containing only
the guard term cannot vanish either. Classes with v3(d)=1 cannot meet the
first three roots. Thus no irrational class occurs at all. In particular this
also excludes possible cancellation between two imaginary roots; no sole-
imaginary-term premise or prior positivity assumption is used.

At every zero of P there are signed rational numbers f,tau,t,g with

    f^2=Fs, tau^2=Dt, t^2=Cy/delta, g^2=G,
    rho=f+3tau+9t+27g.                                          (3)

The rational roots f,tau,g of integer radicands are integers. G is consequently
positive and g is odd. The fourth root is integral by the next lemma.

## 4. Adjacent-coefficient rational Pell integrality

Lemma. If Q>1 is an integer, u is an integer, and t is rational with
Q u^2-(Q-1)t^2=1, then t is an integer.

Proof. Write |t|=r/m in lowest terms. The equation implies m^2 divides Q-1.
The case u=0 is impossible; |u|=1 gives |t|=1. Otherwise reflect signs and
write u>1,t>0. Then u<t<Qu/(Q-1). The norm-preserving transformation

    u'=(2Q-1)u-2(Q-1)t,
    t'=(2Q-1)t-2Qu

has an integer first coordinate because m divides Q-1. The strict inequalities
give -u<u'<u. Also u' cannot be zero by the preserved equation. The reduced
denominator of t' is still m: 2Q-1=1 modulo m and the subtracted term is
integral. Reflect signs again and descend in the positive integer |u| until
|u|=1, where the denominator is one. Therefore m=1 originally. This is an
unbounded descent, not an inference from a finite search. QED.

For (3), the defining equation is QV^2-(Q-1)t^2=1. If Q>=9 the lemma applies.
If Q=0, Cy/delta=1, so t=+1 or -1 directly. This explicitly handles the zero-
scale case without assuming c or I nonzero before it is established.

## 5. Exact maps on all zeros of the inherited fifteen-variable kernel

The inherited kernel has variables j,C,z,h,r,v,w,T,c,n_old,f_old,y_old,p1,p2,p3.
Its front agrees with Section 1, except its Q and V are initially

    Q_old=Delta(f_old^2-1), V_old=f_old^2(cT-R)-c.

Write Z_old=U n_old+M Klo+H(Y-q3). Its four residual equations are

    (Z_old+Uk)^2+4U(L Z_old-U)=0,
    f_old^2-Delta I^2-1=0,
    V_old^2-(Q_old-1)y_old(2V_old+y_old)-1=0,
    budget-1-p1^2-p2^2-p3(p3+1)=0.                              (4)

The entire inherited calibrated equation is zero exactly when these four
residuals vanish; its proof and literal source are retained byte-for-byte.

Given any new zero, take the signed integers in (3), whose existence and
integrality were proved above, and define

    f_old=f, y_old=t-V, p3=(g-1)/2,
    n_old=n-k-f-tau-9t-27g.                                    (5)

Keep all other coordinates. Then
Z_old/U+2L+k=rho-f-tau-9t-27g=2tau. The polynomial identity

    (Z+Uk)^2+4U(LZ-U)=(Z+U(2L+k))^2-4U^2Dt

therefore gives the first residual in (4). The second follows from f^2=Fs,
which also identifies Q_old=Q and V_old=V. The Pell equality gives the third.
Finally p3(p3+1)=(G-1)/4=budget-p1^2-p2^2-1 gives the fourth.
All restored coordinates are integers; no unproved divisibility is concealed.

Conversely, from any zero of (4), the first residual yields
(Z_old/U+2L+k)^2=4Dt. A rational number with integer square is an integer;
that integer is even because its square is divisible by four. Thus

    tau=(Z_old/U+2L+k)/2 in Z.

Set g=2p3+1 and t=V_old+y_old, and retain f=f_old. The other residuals give
f^2=Fs, g^2=G and t^2=Cy/delta. Put

    n=n_old+k+f_old+tau+9t+27g.                                (6)

Then rho=f+3tau+9t+27g, so a factor of (2) vanishes and P=0. Delete the three
old witnesses f_old,y_old,p3. This is a total construction on every old zero,
not just a canonical family. The selection of square-root signs is explicit
existential proof data, not a polynomial register or an extra unknown.

## 6. Exact degree and attained fixed coefficient

Use the highest homogeneous forms

    q0=6 beta j, X0=12q0 w, Y0=v,
    F0=12wC-q0 z, R0=-q0^3 F0,
    a0=X0Y0, I0=2r c^2, U0=8q0^3 a0,
    Fs0=4a0^2 r^2 c^4, Q0=4a0^4 r^2 c^4,
    V0=-4a0^2 r^2 c^4 R0.

The degrees of (s,aa,bb,cc,dd) are at most (48,42,48,46,64).
The last is attained, with dd's complete leading form

    dd0=81 U0^2 Q0 V0^2
       =2^12 3^4 q0^6 a0^10 r^6 c^12 R0^2.                    (7)

H4 is homogeneous of ordinary degree eight and its dd^8 coefficient is +1.
Every other monomial uses at least one of the four lower-weight inputs.
Therefore P has complete leading form dd0^8 and exact degree 512.
In particular, the authentic fixed-coefficient witness is

    [j^192 w^80 v^80 r^48 c^96 z^16] P
      =2^448 3^304 beta^192 >0.                               (8)

The exponents total 512. To isolate it set C=0 in (7); no other term can
contribute to this C-free monomial. This proof does not replace the fixed
numerals by generic coefficients, nor use a sampled degree line.

## 7. Verification, source closure and inherited calibration

`build.py --check`, `check.py` and `reconstruct_coefficients.py` use only the
Python standard library. The checker binds every literal register to a
separately written polynomial formula, verifies topology/liveness/all twelve
variables/all six ports/counts, multiplies the sixteen formal factors exactly,
checks the full homogeneous weighted leading form, verifies the modulus-three
front, checks the restore identities and corrupts every live binary gate.
Normal and Python -O runs have identical explicit acceptance conditions.
Coefficient reconstruction executes only the inspected finite constructor:
all six complete payloads, all 943 tiles and 69,230 basis convolution checks.
There is no network, blank-machine execution or Diophantine zero search.

`SOURCE_PINS.json` records current comparison commit
892d73e1ab4bc5fd34ecca1967b06dc47ca95494, the exact retained round20 predecessor,
and its authenticated upstream source153 signed packet. All source files,
licenses/notices and complete numeral reconstruction data remain portable.
The inherited ordinary native/compiler/refutation theorem is a named logical
dependency, not something proved by these finite checks. See `CLOSURE_MAP.md`.
