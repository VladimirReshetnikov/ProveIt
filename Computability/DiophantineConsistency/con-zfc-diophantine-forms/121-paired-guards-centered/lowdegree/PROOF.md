# Fully centered first-root carrier: fifteen integers, degree 48, 108 gates

## Result and exact dependency boundary

The complete division-free integer polynomial in `equation.json` has fifteen unrestricted integer variables, exact total degree 48 and 108 live binary arithmetic operations. Its integer-zero existence is equivalent to the previously verified fifteen-integer degree-56 carrier. Thus its inherited ordinary native/compiler/refutation theorem yields the same ZFC-provable equivalence between absence of integer zeros and syntactic Con(ZFC). This is a new ordinary arithmetic reduction, not a consistency proof, a global optimum, an encoded object-language derivation, or a new end-to-end proof-assistant certificate.

The improvement is a second centering of the first Pell root. It needs no new Pell theorem, inequalities, or sign assumption. The complete two-way maps below are elementary integer identities and apply to every zero.

## 1. Complete fixed polynomial

All fifteen inputs are unrestricted integers:

    j,C,z,h,r,v,w,T,c,n,f,y,p1,p2,p3.

The six fixed numerals beta,K0,MC,MF,cone_A,cone_B are the complete pinned integer payloads in `coefficients/`; MF is already shifted as in the predecessor. All remaining names are polynomial abbreviations, never additional witnesses:

    J=6j+1, qm=beta J, q=qm+1, W=12w+4,
    X=qW, Y=qv, F=(K0+W)C-z qm,
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    k=R+1+hE, eta=c-Yk, L=EYk,
    I=(2r+1)c^2, Q=Delta(f^2-1), V=f^2(cT-R)-c,
    M=2q^2, U=MH, Klo=2X^2-3Xc-2,
    Z=Un+M Klo+H(v-q^2),
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    budget=k^2(q^2-Derr)-4q^2 eta^2,
    pos=1+p1^2+p2^2+p3(p3+1).

Define four residuals

    Cnew=(Z+Uk)^2+4U(LZ-U),
    B=f^2-Delta I^2-1,
    Caux=V^2-(Q-1)y(2V+y)-1,
    G=budget-pos.

The single final equation is

    P=Cnew^2+B^2+Caux^2+G^2=0.

The carrier's alternative exact form, used only in its proof, is

    Cnew=Z^2+2(2L+k)UZ+U^2(k^2-4).

The short runtime expression and the rebracketing L=E*(Y*k), reusing Y*k from eta, give the 108-gate count.

## 2. Unconditional modulus facts

The authenticated beta is 2^1064921-1, hence odd and 1 modulo 3. Therefore q is even and 2 modulo 3. It cannot be zero: q=0 would imply beta divides 1, whereas beta>1. H is odd and hence nonzero; since a=Y(X+1) and q divides Y, H=3 modulo q. Consequently gcd(H,2q^2)=1 and U is nonzero on every integer assignment. None of these conclusions assumes that any residual vanishes.

## 3. Early monic integrality, CRT, and parity

At a zero of P every squared residual vanishes. Put t=Z/U in Q. The new carrier gives the monic equation

    t^2+2(2L+k)t+k^2-4=0.

The rational-root theorem gives t in Z. Equivalently (t+2L+k)^2=4[1+L(L+k)], but no radical extraction is needed. Thus U divides Z. Reducing the defining numerator Z modulo M and modulo H, and cancelling only the coprime factors justified above, gives

    v0=(v-q^2)/M in Z,    g=Klo/H in Z,
    t=n+g+v0.

The monic equation modulo 2 gives t^2+k^2=0 modulo 2. Hence t+k is even and

    s=(t+k)/2

is an integer. In square-root language, x=t+2L+k is an integer with x^2 divisible by 4, so x is even. This addresses the parity that cannot be assumed merely from rationality.

## 4. Complete maps to and from the predecessor

Write the predecessor carrier, using its own numerator Zold, as

    Cold=Zold^2+(2Zold-Uk)UL-U^2.

All definitions besides the carrier and coordinate n are identical in the two equations.

### New to old

At any new zero, compute the integers t,g,v0,s above. Keep every other input unchanged and set

    nold=s-g-v0.

Then Zold/U=s. The exact universal identity

    (2s-k)^2+2(2L+k)(2s-k)+k^2-4
      =4[s^2+(2s-k)L-1]

and t=2s-k imply Cold=0. The three remaining predecessor residuals are unchanged and already zero. This gives an actual predecessor zero with no sign choices, positive-domain conventions, or canonical-witness restriction.

### Old to new

At any predecessor zero, its carrier gives the monic equation

    sold^2+(2sold-k)L-1=0,    sold=Zold/U.

Thus sold is an integer, and the same CRT gives integer g and v0, with sold=nold+g+v0. Keep every other input and set

    nnew=2nold+g+v0-k.

Then Znew/U=2sold-k. The displayed identity implies Cnew=4Cold=0 after the corresponding substitution. The other three residuals remain zero. This constructs a new zero from every predecessor zero.

These maps prove equivalence of integer-zero existence and in fact are mutually inverse on the two zero sets. They are not polynomial substitutions with integer coefficients on all ambient assignments: the divisions defining g and v0 are licensed at zeros by monicity and CRT, and the division by 2 by the proved parity. No such division occurs in the final polynomial.

The previously verified predecessor theorem, and only that theorem, now supplies the connection to the normalized native construction, compiler, refutation predicate, and syntactic Con(ZFC). This proof does not silently claim to re-prove that inherited chain.

## 5. Exact degree for the authentic fixed constants

The register degrees are

    q:1, X:2, Y:2, F:2, R:5, k:5, a:4, H:4,
    Delta:8, L:11, I:3, Q:10, V:7, U:6, Klo:4, Z:7.

The four residual degrees are respectively 24,14,18,16. In Cnew, the unique degree-24 contribution is 4ULZ. All other terms have degree at most 22. The top part of Z is U0 n. Therefore

    (Cnew)24=4U0^2 L0 n,
    P48=16U0^4 L0^2 n^2,

where, writing the subscript 0 for the leading homogeneous part,

    q0=6 beta j, X0=12q0 w, Y0=q0 v,
    U0=8q0^2 X0Y0,
    L0=X0Y0^2(R0+hX0Y0).

Since R is independent of h, selecting the h^2 coefficient in P48 gives exactly

    [j^26 w^8 v^10 h^2 n^2] P
       =2^58 3^34 beta^26 > 0.

The exponents sum to 48. The other three squared residuals have degrees at most 28,36,32 and cannot cancel this coefficient. Thus the exact degree is 48 after all six huge constants are fixed; it is not merely a generic coefficient-degree estimate.

## 6. Arithmetic metrics and verification scope

The literal DAG has 108 live gates: 61 multiplications, 25 additions, 22 subtractions. Squares and scalar multiplications each use ordinary counted multiplication gates; there are no division gates or hidden arithmetic registers. All fifteen variables and all six fixed numerals are live. The retained predecessor had degree 56 and 110 gates, so this endpoint improves both degree and evaluation cost at the same variable count.

`review/audit.py` independently evaluates every named register over exact polynomial rings without importing the builder, verifies the carrier identities, authenticates coefficient bytes, computes exact leading forms and the displayed nonzero coefficient, checks liveness and gate counts, and rejects deliberate mutations. It passes under normal and optimized Python. The finite checks certify transcription and algebra, not the unbounded inherited consistency theorem. A separate reviewer checks the ordinary proof and source boundary.
