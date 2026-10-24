# Fourteen positive unknowns in exact degree twenty-four

## Statement and scope

The frozen polynomial `P13` has thirteen strictly positive unknowns, exact
degree 28, and 98 live binary arithmetic operations. Introduce one additional
strictly positive coordinate E, use E in place of the computed register XY,
and add the defining residual E-XY. The resulting integer polynomial P14 has
fourteen positive unknowns, exact degree 24, and 101 live binary operations.
Its positive zero set is in explicit bijection with the positive zero set of
P13. Consequently it has exactly the same ZFC consistency interpretation and
exactly the same inherited mathematical dependencies as P13.

This is an elementary register lift of the new P13 construction. Its
contribution is a further variable/degree tradeoff. It introduces no new
Pell lemma or arithmetic source assumption.

## 1. Literal polynomial

The fourteen strictly positive inputs are

    F, alpha, C, f0, i, T, X, Y, r, eta, zeta, u, gamma, E.

The four fixed ports beta,K0,MC,MF are the whole compact source44 tuple used
by P13; beta=2^590069-1, and MF is already shifted. In particular E is an
additional unknown, while all of the following names are polynomial
abbreviations. Define

    B=beta+1, b=3 beta, b2=b^2, L=beta b2,
    q=F+alpha+C, k=eta+zeta, c=kY+eta,
    ell=EkY, a=E+Y, H=4a+3, Delta=a^2+H,
    I=ic^2, Nf=b f0+q-B, F2=Nf^2,
    G=(q-1)(q-F)+alpha,
    Rhat=beta G(q^2-1)+(MC+q MF)(q-1),
    M0=q^3(q-1), Bt=(qK0+X)C-qF,
    Z=M0(ell+r)+(q-1)Y-q^3 Bt,
    Sb=4 beta qY, Mb=q Sb,
    Dhat=Mb(X+ac)+H[Mb gamma+Sb X-beta(k-1)+Rhat],
    Vhat=F2(beta cT-Rhat)-Lc, Yhat=Vhat+Lu.

The five residuals are

    A0=Z^2-M0^2[ell(ell+k)+1],
    A1=Dhat^2-Mb^2(1+Delta c^2),
    Aa=b2 Yhat^2-Delta(F2-b2)(Yhat^2-Vhat^2)-b2 L^2,
    As=F2-b2(1+Delta I^2),
    AE=E-XY.

The required polynomial is

    P14=A0^2+A1^2+Aa^2+As^2+AE^2.

Every abbreviation is explicitly polynomial in fourteen inputs and fixed
integer coefficients. `p14_degree24.json` gives the exact arithmetic DAG.

## 2. Exact positive-zero-set bijection

Let x denote the ordered tuple of thirteen original unknowns. Let the four
residuals of P13 be A_j(x), and let the four residuals above be
tilde_A_j(x,E). The circuit construction gives the polynomial identities

    tilde_A_j(x,XY)=A_j(x)

for every one of j=0,1,a,s.

If P13(x)=0 with x strictly positive, then all four A_j(x) vanish. Set
E=XY, which is strictly positive. All five residuals of P14 vanish.
Conversely, if P14(x,E)=0 with all fourteen coordinates strictly positive,
each residual is zero because it is a sum of integer squares. The last
residual forces E=XY, so each A_j(x)=tilde_A_j(x,E)=0 and P13(x)=0.
The extension E=XY is unique. Thus projection and the map x -> (x,XY) are
mutually inverse bijections between the positive zero sets.

These are polynomial identities and elementary ordered-integer arguments,
formalizable in ZFC. Combining them with P13's proved reduction gives

    ZFC proves: (there is no positive-integer zero of P14) iff Con(ZFC).

This statement asserts an equivalence provable in ZFC; it assumes neither
the truth of Con(ZFC) nor the absence of zeros. The source compiler and
Pell proofs needed for the P13 endpoint are inherited without alteration.
The finite algebra checker verifies the register lift and its size claims;
it is not a newly generated end-to-end formal proof of that semantic
endpoint.

## 3. Exact degree

Treat the native ports and all derived fixed leaves as constants. With E
independent, a and H have degree 1, Delta has degree 2, c has degree 2,
ell has degree 3, Rhat has degree 4, and Nf has degree 1. Cancellation of
the two leading norm squares gives residual degrees

    deg A0=12, deg A1=11, deg Aa=12, deg As=12, deg AE=2.

For a fully checkable description, put q=F+alpha+C, k=eta+zeta and keep
Bt=(qK0+X)C-qF, which is homogeneous of witness degree 2. The degree-12
leading forms of the three maximal-degree residuals are

    lead(A0)=q^7 E k Y (2qr-2Bt-qk),
    lead(Aa)=9 beta^4 (3 beta f0+q)^4 q^6(q-F)^2,
    lead(As)=-9 beta^2 i^2 k^4 Y^4(E+Y)^2.

The degree-24 leading form of P14 is the sum of the squares of these three
expressions. Only As depends on i. Hence the coefficient of the monomial

    i^4 eta^8 E^4 Y^8

is precisely 81 beta^4, which is nonzero for the specified fixed beta.
This proves exact total degree 24; the sum-of-squares expression cannot
silently drop below the claimed degree.

`check14.py` expands the five residuals with symbolic native ports, compares
them with separately stated identities, checks all three leading forms,
checks the exact final sum-of-squares structure, and checks liveness. It
uses standard-library integer arithmetic and behaves identically with
Python assertions disabled. Its term counts are 1921,6203,26877,81,2.

## 4. Exact operation count and reproducibility

The operation convention charges every live binary addition, subtraction,
and multiplication on witnesses, including squaring and multiplication by
fixed constants. Register reuse and fixed integer leaves are free.

Take the frozen P13 circuit, rename the old E=XY gate to Eprod, add E as
an input, and leave every former use of E as a use of that new input. The
old multiplication remains live in AE=E-Eprod. Computing AE, squaring it,
and adding its square adds precisely three operations to the original 98.
The resulting 101 gates consist of 26 additions, 17 subtractions, and 58
multiplications. The residual system has 92 gates; the five-square
finalizer has 9 gates. Every gate, witness, and native port is live.

The generator `build14.py` checks the frozen source digest before writing
the candidate. Its source is included as `p13_degree28.json`, with digest

    1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49

The resulting candidate `p14_degree24.json` has digest

    91a307011482e1850b97ae4a4222f024bcbbde00a7a7850e6635e8b875729495

To regenerate and check, run from this directory:

    python3 build14.py
    python3 check14.py
    python3 -O check14.py

The ordinary proof is the exact unique lift above. The checker's symbolic
algebra receipts support the literal formula, degree, count, and source
identity claims; finite execution does not replace the inherited P13
correctness proof.
