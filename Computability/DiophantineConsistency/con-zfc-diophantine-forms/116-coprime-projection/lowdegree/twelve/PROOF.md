# Four-root carrier: twelve integers, degree 500

## Result and dependency

This endpoint has twelve unrestricted integer variables, exact total degree500 and148 live binary arithmetic operations. It removes the remaining p1 guard witness by representing its square inside a four-root norm. It improves both degree and arithmetic cost over the inspected twelve-variable degree1000/180-operation equation. Its proof is a direct extension of the reviewed thirteen-variable construction, not a new native calibration. The same ordinary source34/compiler/refutation and formalization boundaries apply.

## 1. Complete scalar equation

The variables are

    j,C,z,h,r,v,w,T,c,n,p2,p3.

Use the shared thirteen-variable definitions for all outer registers, Dtau,Df,Da and the centers Aroot,Broot,Croot. Replace the guard by the integer radicand

    G0=budget-1-p2^2-p3(p3+1).

There is no p1 variable. Set

    Ztotal=Z+U(Aroot+Broot+Croot),
    sroot=Ztotal^2,
    ar=4U^2 Dtau, br=36U^2 Df,
    cr=324U^2 Da, er=729U^2 G0,
    p=ar*br, q4=cr*er, u=ar+br, v4=cr+er,
    s=sroot-u-v4,
    k4=s^2-4u*v4+4(p+q4),
    l4=s+2v4, m4=s+2u,
    Even=k4^2+16[p*l4^2-q4(m4^2+4p)],
    Odd=k4*l4+8q4*m4.

The complete single equation is

    P12=Even^2-64p*Odd^2=0.

The expression uses only additions, subtractions, multiplications and fixed powers. `specification.json` lists every shared abbreviation in full and `equation.json` gives the exact scalar DAG; the formal radicals in the proof below are not quantified coordinates.

## 2. Norm identity and first CRT

The direct four-root identity is

    P12=product over all16 signs of
      [Ztotal +/- sqrt(ar) +/- sqrt(br) +/- sqrt(cr) +/- sqrt(er)].

It follows by taking the successive quadratic norms after grouping the first two and last two roots. In the usual intermediate form, put

    K=k4, L=-4l4, M=-4m4, N=-8.

The first quadratic norm's even and odd parts are

    K^2+pL^2-q4(M^2+pN^2), 2KL-2q4MN.

Their norm is exactly Even^2-64p*Odd^2 after substituting the displayed L,M,N. This proves the direct scalar evaluator is the complete16-sign norm, including singular radicand cases.

Since U is unconditionally nonzero, division by U^16 identifies the same monic degree16 polynomial in the rational total center

    x=Z/U+Aroot+Broot+Croot,

with radicands4Dtau,36Df,324Da,729G0, all integers. Therefore P12=0 makes x an integer by the rational-root theorem, and hence U|Z. The unchanged unconditional coprime CRT proof recovers

    v=q^2(2v0+1), H|Klo.

This step precedes the budget's positivity and every radical classification.

## 3. Recovering the guard without assuming it

The same unconditional residues give Dtau=Df=Da=1 modulo3. The norm factorization supplies a rational signed sum with weights

    2 sqrt(Dtau), 6 sqrt(Df), 18 sqrt(Da), 27 sqrt(G0).

If G0=0, omit that root and use the already-proved three-root separation. Otherwise decompose every nonzero integer radicand as a signed squarefree integer times an integer square. In a nonrational squareclass, the first three terms have distinct three-adic coefficient orders0,1,2, when present. The fourth term has coefficient order at least3. A group containing only the fourth term is plainly nonzero. A group with any earlier term has a unique coefficient of least three-adic order, so its signed sum cannot vanish modulo3 after division by that power. Independence of the distinct squareclass characters over Q therefore forces every radicand to be a rational square and hence an integer square. This argument permits G0 negative initially; a negative squareclass cannot survive. Zero G0 was separately allowed, not divided by.

Choose integral roots

    tau^2=Dtau, f^2=Df, e^2=Da, g^2=G0.

In particular

    budget=1+p2^2+p3(p3+1)+g^2>0.

Thus all of the original centered-budget conclusions hold after root extraction. The CRT scale gives c!=0 and Q=(Delta I)^2>=9. The adjacent-coefficient lemma proved in the thirteen-variable component makes

    y0=e/(Q-1)

an integer. No divisibility by Q-1 was assumed merely because Da was square.

## 4. Complete maps to the fifteen-variable equation

Let gproj=Klo/H and v0=(v-q^2)/M, integral by CRT. From any twelve-variable zero choose the integer roots above and set

    p1_15=g, f15=f, y15=y0-V,
    n15=tau-L-gproj-v0.

All fifteen-variable rows vanish exactly as in the thirteen-variable restoration, and the guard follows from g^2=G0. This gives an actual fifteen-variable zero.

Conversely take any fifteen-variable zero. Its source proof supplies the integral roots

    tau=|Z15/U+L|, f=|f15|,
    e=(Q-1)(V+y15), g=p1_15.

Discard f15,y15,p1_15 from the variable list and choose

    n12=2tau+6f+18e+27g-Aroot-Broot-Croot-gproj-v0.

The four radical squares are exactly Dtau,Df,Da,G0, so one signed norm factor vanishes. This gives a twelve-variable zero from every fifteen-variable zero. No new canonical-tuning, sign, positivity, or odd-period condition is introduced.

## 5. Exact degree and runtime cost

The shared degrees are

    deg(U)=6, deg(Z)=7,
    deg(Aroot)=11, deg(Broot)=7, deg(Croot)=41,
    deg(G0)=16.

Use the same formal Laurent scaling as the thirteen-variable degree proof. The first three radical corrections have scaled degrees at most5,5,3 after multiplication by U. The uncentered fourth root has degree14 after that multiplication. Hence the16 norm factors have leading degrees

    eight factors of degree47,
    four factors of degree17,
    four factors of degree14.

The first group reverses the auxiliary center, the second reverses the first center with the auxiliary center matched, and the final four match both of those centers. In the final group the guard radical has degree14, strictly above the strong center's scaled degree13 and Z's degree7, so no leading cancellation is possible. Therefore the exact degree is500, with leading homogeneous part

    2^12*729^2*U0^16*Aroot0^4*Croot0^8*G00^2.

This product is nonzero; G00=-4q0^2Y0^2k0^2 is itself a nonzero polynomial. Selecting the h^8 and z^8 terms gives the actual coefficient

    [j^228 w^76 v^84 h^8 z^8 r^32 c^64] P12
      =2^488 3^332 beta^228 >0.

The exponents sum to500. The formal Laurent method proves an upper bound for the actual polynomial norm and displays a nonzero exact leading component; it is not a claim about asymptotic behavior on every numerical signed assignment.

The direct evaluator has148 live gates:90 multiplications,35 additions,23 subtractions. All twelve integer inputs and the same six complete fixed coefficients are live. No additional quantified square root or positivity witness is hidden in the norm notation.
