# Polynomial radical centering: ten positive variables, degrees 253 and 252

## Scope and new result

The two literal integer-polynomial circuits `first.json` and `second.json` have ten strictly positive unknowns, respectively 102 and 104 live binary arithmetic gates, and exact total degrees 253 and 252. They use the complete original compact44 coefficient tuple retained without alteration in `coefficients/`. Their positive zero sets are nonempty exactly when the finite-refutation predicate of the retained source61/native/controller calibration is true. At that calibration, absence of a positive zero expresses Con(ZFC).

The new ingredient is polynomial approximation of the reciprocal term in the fused radical's expansion. This is not merely another name for the old sharp center: that center leaves a degree-17 defect, whereas the present centers leave degree-16 and degree-15 defects. We pay five or seven additional gates. This is a modest new degree/circuit tradeoff, not a nine-variable breakthrough or a global optimality claim. It is an ordinary unbounded arithmetic proof relative to the retained calibration, not a new machine-checked Lean endpoint or a proof of consistency.

The entire preceding packet is retained under `prior/`, including its proof, coherent coefficients, upstream source pins and source theorem texts. No remote repository is changed.

## 1. Complete formulas

The independent variables are J,F,alpha,i,T,x,Y,n,eta,zeta in the strictly positive integers. Fixed ports beta,K0,MC,MF are those of `coefficients/BINDING.json`; in particular beta is odd, beta>=31, K0>0, and 0<MC<beta<MF<2beta.

Define

    q=beta J+1, X=q+x, mu=q^2+1, p=mu Y,
    A=p(X+1)+1, Delta=A^2-1, H=4A-5,
    k=eta+zeta, c=kY+eta, v0=p^2 X,
    D=v0(v0+1)k^2+1, E0=i c^2, E=2E0,
    G=(q-1)(q-F)+alpha,
    R=G(q^2-1)+(MC+q MF)J, e=k-R-1,
    C=q-F-alpha, B=(q K0+X)C-q F,
    Fs=1+Delta D E^2, Q=Delta^2 D E^2, delta=Q-1,
    b=c(T+alpha)-R, V=Fs b-c, Dnum=Q V^2-1,
    P=q^4(q-1), M=P mu^2 H, Kpos=X(3c-2X)+2.

Select one of the following polynomial corrections:

    Q1=p v0 k^2,
    Q2=p(v0-p^2)k^2.

For j=1 or 2, put

    S_j=A D E-E0 Qj,
    Z_j=P mu^2[H(n+V+S_j-bB)+Kpos]
        +H[mu^2(q(q-1)Y-q^3B-(q-1)X)-P e],
    s_j=delta Z_j^2, u=delta M^2 D Fs, v=M^2 Dnum,
    N_j=(s_j-u-v)^2-4uv.

The equation is N_j=0. Every displayed abbreviation is an integer polynomial, and the output registers of the JSON circuits implement exactly these formulas. All fixed-numeral multiplications count as gates. In the graph, `I` denotes E and `E0` denotes E0; neither is an additional unknown.

## 2. A whole-polynomial soundness map with no sign circularity

Let N_old be exactly the uncentered degree-262 polynomial in `prior/uncentered.json`. The following is an identity of integer polynomials at every integer input, not only at zeros:

    N_j(J,F,alpha,i,T,x,Y,n,eta,zeta)
      = N_old(J,F,alpha,2i,T,x,Y,n+S_j,eta,zeta).       (1)

Indeed the change i_old=2i gives E_old=2i c^2=E, so all radicands, b, V, M and source registers coincide. Replacing n_old by n+S_j then makes the complete old and new carriers identical.

It remains to check positivity of the substituted coordinates without assuming any Pell equation or source result. On every positive input, p>1, X>q>=32 and v0=p^2X>p. Therefore

    0<Q2<Q1=p v0 k^2<v0^2 k^2<D.

Consequently, with E=2E0,

    0<E0(2A-1)D<S_j=A D E-E0 Qj<A D E.              (2)

In particular 2i>0 and n+S_j>0. All other old coordinates are unchanged and positive. Thus every positive zero of N_j maps to a positive zero of N_old. The retained whole-zero-set soundness theorem applies, including its correct order of root extraction, signed folding, transport, index recovery, coprimality, whole-product projection and fresh unscaled source reconstruction. This proves soundness without assuming a sign of a radical, parity of q, transport nonnegativity, or denominator divisibility in advance.

The map is not claimed to be a bijection. Completeness requires fresh witnesses, proved next; a pointwise positive inverse to (1) is neither available nor used.

## 3. Completeness with even strong ordinate and positive carrier

A finite refutation supplies the canonical source data from `prior/PROOF.md`, Section 5: X=2^R>q, R=3 modulo 4, R>3q, q^3|Y, q^4|X and nonnegative native transport t=B/[q(q-1)]. Write r=(R-1)/2>=2, let

    c=psi_A(R),
    k=2 psi_(2v0+1)((R+1)/2),
    tau=chi_(2v0+1)((R+1)/2),
    eta=c-kY, zeta=k-eta, rho=(k-R-1)/mu^2.

The retained zero-offset ratio theorem gives eta,zeta>0, D=tau^2 and integer rho>=0.

To enforce the new factor 2 in E, choose a positive power m of the determinant-one Pell recurrence matrix that is the identity modulo 2 tau c^2. Such a positive m exists because the matrix is an element of a finite group. Let

    I=psi_A(m), f=chi_A(m), i=I/(2 tau c^2)>0.

Then I=tau E, Fs=f^2 and Q=(Delta I)^2. This period choice is the only change from the old canonical strong witness; it does not presume that an arbitrary old i is even.

Use the retained auxiliary-completeness lemma with its explicit witness

    S0=Delta I,
    V*=chi_S0(R)/S0, y=psi_S0(R),
    T*=(V*+c+R f^2)/(c f^2), T=T*-alpha.

That lemma proves T* is an integer. The same Pell growth estimate gives V*>=(3Q)^r>=9Q^2, hence T*>9S0>alpha and T>0. Thus the literal V is V*. Put h_y=y-V*>0. Since y<2V*,

    h_y=(V*^2-1)/[(Q-1)(y+V*)]>V*/(4Q)>=9Q/4.      (3)

The retained projection and divisibility theorem gives integers

    kappa=Kpos/H with 0<kappa<c<I,
    sY=Y/q^3 with 0<sY<c<I,
    uX=X/q^4>0.

The center S_j is an integer polynomial. From (2), f>(A-1)I, and I=tau E, one has

    S_j-tau f < A D E-tau f < D E < I^2,

where the last strict inequality uses E>1 and D E=I^2/E. Now set

    W=1+q(q-1)b,
    n=W t+rho+tau f-S_j+h_y-kappa-sY+uX.             (4)

Every term is an integer. Wt,rho,uX are nonnegative, and the total possible negative loss is less than I^2+2I<4I^2. Inequality (3) exceeds 4I^2 since Q=Delta^2 I^2 and Delta>=3. Hence n>0, including the case t=0.

The exact center identity is

    Z_j/M=n+V+S_j+Kpos/H+Y/q^3
          -W B/[q(q-1)]-X/q^4-e/mu^2.

Substituting (4) makes it tau f+y. Because D Fs=(tau f)^2 and Dnum/delta=y^2, a conjugate factor of N_j vanishes. All ten coordinates are strictly positive. This proves completeness and the claimed nonemptiness equivalence.

## 4. Exact degree: 253 and 252

All unknowns have degree 1 and fixed coefficients have degree 0. Write q0=beta J, X0=q0+x and k0=eta+zeta. The nonzero highest homogeneous forms are

    [N_1]_253=-2^20 q0^122 X0^27 Y^60 i^10 k0^32(q0-F)^2,
    [N_2]_252= 2^20 q0^122 X0^26 Y^60 i^10 k0^32(q0-F)^2.  (5)

For example the respective coefficients of J^122 x^27 Y^60 i^10 eta^32 F^2 and J^122 x^26 Y^60 i^10 eta^32 F^2 are -2^20 beta^122 and +2^20 beta^122. They do not vanish at the actual coherent coefficient tuple.

Here is an upper-bound proof and coefficient derivation for the entire polynomial, not only a ray computation. Scale every unknown by a formal parameter t and work over the rational-function field in those unknowns. Choose formal Laurent roots

    g=sqrt(D Fs) near A D E,
    y=sqrt(Dnum/delta) near V.

The square leading forms permit these binomial expansions. The degrees are

    p:3, A:4, v0:7, D:16, E0:5, Fs:34, delta:42,
    V:38, M:13, g:25, y-V:-4.

Set h=A D E-g. The exact identity h(A D E+g)=D^2E^2-D gives degree(h)=17, and

    h-DE/(2A)=(DE h-2AD)/[2A(A D E+g)]

has degree at most 9. Because E=2E0,

    S_j-g=E0(D-A Qj)/A + (a Laurent term of degree <=9).  (6)

The crucial exact polynomial remainders, with v0=p^2X, are

    D-A Q1=[v0(1-p^2-p)]k^2+1,
    D-A Q2=[p^4-p^3 X+p^3+p^2 X]k^2+1.              (7)

Their degrees are respectively 15 and 14, so (6) has exact degrees 16 and 15. Their leading forms are respectively

    -e0 p0^3 k0^2,
     e0 p0^3 k0^2/X0,

where e0=i k0^2Y^2 and p0=q0^2Y. The rational leading form in the second line is legitimate inside the Laurent field; all denominators cancel in the final polynomial.

Let

    r0=n-bB+Kpos/H+Y/q^3-B/[q(q-1)]-X/q^4-e/mu^2.

It has degree at most 6, and Z_j/M=V+S_j+r0. The exact four-factor identity is

    N_j=delta^2 M^4 product_(eps,nu=+/-1)
          (Z_j/M+eps y+nu g).

Two factors have degree 38 with leading form 2V, one has degree 25 with leading form 2g, and the fourth has degree 16 or 15 with leading form S_j-g. Consequently the total degrees are

    2(42)+4(13)+2(38)+25+16=253,
    2(42)+4(13)+2(38)+25+15=252.

To verify the constants and monomials in (5), set

    a0=q0^2 X0Y, d0=q0^8 X0^2Y^4k0^2,
    e0=i k0^2Y^2, rmask0=q0^3(q0-F).

The highest forms of delta,M,V,g are respectively

    4a0^4 d0 e0^2, 4q0^9 a0,
    -4a0^2 d0 e0^2 rmask0, 2a0 d0 e0.

Multiplying them with the last-factor leading forms above gives (5). This also certifies that the highest polynomial terms cannot cancel at the authentic fixed coefficients.

## 5. Literal gate counts and reproducible tests

Start from the 97-gate sharp circuit. Replace its one gate E=i c^2 by E0=i c^2 followed by E=2E0, adding one gate. Keep the old A D E gate as Cg0. For Q1 add pk=p k and Qapprox=pk(v0 k), reusing the existing v0 k register. Multiply Qapprox by E0 and subtract it from Cg0. These four further gates give 102.

For Q2 instead add pk=p k, vminus=v0-p^2, vminusk=vminus k and Qapprox=pk vminusk. The p^2 register already exists. Multiplication by E0 and subtraction give six further gates, hence 104. All vertices and all ten variables are live. The operation splits are 61 multiplications, 21 additions and 20 subtractions; and 62 multiplications, 21 additions and 21 subtractions.

Run

    python -B build.py --check
    python -B check.py
    python -B -O build.py --check
    python -B -O check.py

The standard-library checker independently audits every gate, coefficient hash and bit length, the live graph, signed whole-polynomial translations, a sparse free-polynomial proof of (7), exact integer univariate expansions, modular expansions with actual coefficient payloads, independent closed formulas, and finite Pell-period controls with the doubled modulus. Finite controls supplement the unbounded proof; they are not a substitute for it.

## 6. Research boundaries

Further terms DE/(8A^3), etc., have degree at most 9 and do not address the degree-15 reciprocal-X remainder in (6). This is an obstacle to that local centering approach, not a theorem about all polynomials or all encodings.

A tempting rational center A D E-2DE/H would use an existing denominator and formally reduce degree further. It does not preserve the source projection: the congruence becomes H|(Kpos-2DE) rather than H|Kpos. It is not a proved construction and is deliberately excluded. Likewise no removal of the strong-period variable or carrier variable has been proved.
