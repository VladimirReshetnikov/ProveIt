# Triple-centered three-root carrier: thirteen integers, degree 274

## 0. Result and boundary

The polynomial in `equation.json` has thirteen unrestricted integer variables, exact total degree274 and129 live binary arithmetic operations. It combines the first, strong and auxiliary Pell roots in one fixed-prime-separated, triple-centered norm, retaining the existing centered sign budget. It is equivalent in integer-zero existence to the adjacent fifteen-integer equation, with complete maps below. Its ordinary compiler/refutation dependency and formalization boundary are unchanged. It is not a consistency proof or a global minimum claim.

## 1. Full scalar specification

The variables are

    j,C,z,h,r,v,w,T,c,n,p1,p2,p3.

Use the shared definitions of the fourteen-variable sibling, including

    I=(2r+1)c^2, Df=1+Delta I^2,
    Q=Delta(Df-1)=Delta^2 I^2,
    V=Df(cT-R)-c, M=2q^2, U=MH,
    Klo=2X^2-3Xc-2, Z=Un+MKlo+H(v-q^2),
    budget=k^2(q^2-Derr)-4q^2 eta^2,
    pos=1+p1^2+p2^2+p3(p3+1), G=budget-pos.

There is no f or y variable. Set the three centers and errors

    A=2L+k, B=6(a+2)I, Croot=9(2Q-1)V,
    aa=4-k^2, bb=36(1-I^2), cc=81(4-4Q-V^2).

Then, with Dtau=1+L(L+k) and Da=(Q-1)(QV^2-1),

    A^2+aa=4Dtau, B^2+bb=36Df, Croot^2+cc=324Da.

The following monic quartic is the centered two-root polynomial for A,B:

    p(t)=t^4+p3 t^3+p2 t^2+p1 t+p0,
    AB=A+B, ab=aa+bb,
    p3=4AB,
    p2=4AB^2+4AB_product-2ab, where AB_product=A*B,
    p1=4AB(2AB_product-ab),
    p0=(aa-bb)^2-4AB(A*bb+B*aa).

The name AB denotes the sum in these formulas, while AB_product is the product. The retained `horner_specification.json` uses the explicit unambiguous formulas `4*AB**2+4*Aroot*Broot-2*ab` and `4*AB*(2*Aroot*Broot-ab)`.

For a completely scalar, division-free specification of the final norm, let

    a1=Z+p3 U, b1=-U,
    a2=a1 Z-b1 U cc+p2 U^2,
    b2=-a1 U+b1 Z+2Croot b1 U,
    a3=a2 Z-b2 U cc+p1 U^3,
    b3=-a2 U+b2 Z+2Croot b2 U,
    a4=a3 Z-b3 U cc+p0 U^4,
    b4=-a3 U+b3 Z+2Croot b3 U,
    N=a4^2-2Croot a4 b4-cc b4^2.

All of these are ordinary integer polynomials. The single final equation is

    P13=N+G^2+N G^2=0.

The runtime evaluates the identical norm by the much shorter direct F8 formula:

    Wtotal=Z+U(A+B+Croot),
    s=Wtotal^2, u=4U^2 Dtau, v=36U^2 Df, w=324U^2 Da,
    N=[(s+w-u-v)^2-4(sw+uv)]^2-64swuv.

The formal Horner construction is retained in `horner_equation.json` and `horner_specification.json` as a degree/identity comparison, not as the counted runtime circuit. The optimized full ordered formulas and exact DAG are respectively `specification.json` and `equation.json`. Its coefficients are exactly the six fixed payloads in `../coefficients/`; no other adjustable numerical data is used.

## 2. Exact norm identity and early monic integrality

Work first in the formal rank-two algebra with w^2+2Croot*w-cc=0. Multiplication of pairs (x,y), representing x+yw, is

    (x,y)(x',y')=(xx'+cc yy', xy'+yx'-2Croot yy').

The four a,b pairs above are simply Horner evaluation of

    U^4 p(Z/U-w).

Their final quadratic norm is a4^2-2Croot a4 b4-cc b4^2. Consequently the exact scalar identity is

    N=U^8 product over all eight signs of
      [Z/U+A+B+Croot
       +/- sqrt(A^2+aa) +/- sqrt(B^2+bb) +/- sqrt(Croot^2+cc)].

The identity is an identity of polynomials after denominators are cleared; it is valid even if an error, radicand, or center happens to vanish. The algebra is a device for proving the scalar formula, not an extra quantified witness.

For integers N,G, the final equation is equivalent to N=G=0: it says

    (1+N)(1+G^2)=1,

and the positive integer divisor 1+G^2 of1 must be1. No sign assumption on N is needed.

As in the other two endpoints, U is unconditionally nonzero. The rational total center Z/U+A+B+Croot is now a root of a monic integer polynomial of degree8, the three-root norm. Hence it is an integer. Subtracting the integer centers proves U|Z. The same coprime CRT therefore recovers

    v=q^2(2v0+1), H|Klo,

before classifying any root. In particular the cubic scale and v!=0 are already licensed; no singular zero-v branch is skipped.

## 3. Fixed three-adic separation of all three roots

The affine definitions imply q=2,W=1,X=2 modulo3. Thus a=(X+1)Y=0 and Delta=0 modulo3. For ell=XY^2, either ell=0 or ell=-1 modulo3, so

    Dtau=1, Df=1, Q=0, Da=1 modulo3.

All three radicands are therefore nonzero integers prime to3, independently of the guard or a Pell row.

From N=0, the exact factorization supplies a rational signed sum

    epsilon1*2 sqrt(Dtau)+epsilon2*6 sqrt(Df)
      +epsilon3*18 sqrt(Da).

Write each nonzero integer radicand as d*s^2, with d a signed squarefree integer and s a positive integer. Because the radicands are prime to3, both d and s are prime to3. Group terms with the same squareclass d. Distinct squareclasses give linearly independent radical characters over Q in their multiquadratic extension, also when a radicand is negative. Therefore every nonrational group must have coefficient zero.

But within any group the integer coefficients have distinct powers of3: exactly0,1,2 from the respective weights2,6,18. Dividing by the smallest power of3 and reducing modulo3 shows their signed sum cannot vanish. Hence no nonrational squareclass can occur. All three radicands are rational squares, and therefore nonnegative integer squares. This also proves positivity of Da rather than assuming it before root separation.

Choose integer roots tau^2=Dtau, f^2=Df and e^2=Da. Positive tau and f may be used. We next justify the needed auxiliary root e/(Q-1) without silently assuming divisibility.

## 4. Adjacent-coefficient rational descent

The recovered scale and guard give c!=0 and Delta>=3. Thus Q=(Delta I)^2>=9 and delta=Q-1 is nonzero. The rational number y0=e/delta satisfies

    QV^2-(Q-1)y0^2=1.

The following elementary lemma proves it integral.

**Lemma.** If S>=2, V is an integer and y is rational with

    S^2 V^2-(S^2-1)y^2=1,

then y is an integer.

**Proof.** Write |y|=m/n in lowest terms, n>0. Then n^2 divides S^2-1. Put d=(S^2-1)/n^2, a positive nonsquare integer. The two positive norm-one units

    S+n sqrt(d), S|V|+m sqrt(d)

belong to Z[sqrt(d)]. Its least positive norm-one unit eta=a+b sqrt(d) exists, and the usual division-by-powers minimality argument gives every positive integer-coordinate unit as a power of eta. Thus

    S=chi_a(t), n=b psi_a(t),
    S|V|=chi_a(s), m=b psi_a(s)

for positive indices t,s. Modulo chi_a(t), shifting an index by2t or reflecting about t changes only its sign. Folding s reduces its abscissa to +/-chi_a(r),0<=r<=t. Since S divides chi_a(s), strict growth forces r=t, hence s is an odd multiple of t. The composition identity now gives psi_a(t)|psi_a(s), so n|m. Coprimality yields n=1. This proves the lemma.

Applying the lemma with S=|Delta I| proves y0 integral. No sign of V or e was discarded; the original signed y0 can be used after proving its absolute value integral. Even without the guard, the only other possible square Q is0, where the conclusion follows from y0^2=1; Q=1 cannot occur because Delta>=3 unless I=0, which gives Q=0.

## 5. Complete maps to and from the fifteen-variable equation

### Thirteen to fifteen

The CRT offsets g=Klo/H and v0=(v-q^2)/M are integers. With the integral roots from Sections3–4, set

    f15=f, y15=y0-V, n15=tau-L-g-v0.

Keep every other shared coordinate. Then Z15/U=tau-L, so its first row vanishes; its strong row is f15^2-Df=0, its centered auxiliary row is exactly the equation of Section4, and its budget row is unchanged. This yields an actual fifteen-variable zero.

### Fifteen to thirteen

At any fifteen-variable zero, choose the integer roots

    tau=|Z15/U+L|, f=|f15|,
    e=(Q-1)(V+y15).

The centered auxiliary row gives e^2=(Q-1)(QV^2-1)=Da. The CRT offsets g,v0 are integral. Set

    n13=2tau+6f+18e-A-B-Croot-g-v0.

Then Z13/U+A+B+Croot=2tau+6f+18e, so one of the eight exact norm factors vanishes. The same budget witness triple has G=0, and the unit-product output is zero. The root e may be signed, which is harmless because every sign occurs in the norm.

Both maps apply to every zero, not merely to a canonical subset. They introduce no hidden witness into the literal polynomial and require no new strong-index tuning or odd-period assumption.

## 6. Exact degree through triple centering

The ordinary degrees are

    deg(U)=6, deg(Z)=7,
    deg(A)=11, deg(B)=7, deg(Croot)=41,
    deg(aa)=10, deg(bb)=6, deg(cc)=38.

To compute the exact cleared norm degree, scale every unknown by a formal parameter s and work over the rational-function field in their independent leading coefficients. The formal Laurent square roots have expansions

    sqrt(A^2+aa)=A+O(s^-1),
    sqrt(B^2+bb)=B+O(s^-1),
    sqrt(Croot^2+cc)=Croot+O(s^-3).

These expansions follow algebraically from the binomial series, since each error has strictly lower degree than its center squared; they do not assert an inequality on numerical signed assignments. The eight cleared factors have degrees

    47,47,47,47,17,17,13,7.

The four degree47 factors are those with the auxiliary-center sign reversed; among the rest two reverse the first center, one reverses the strong center, and one matches all three centers. The last factor has leading Z, since the three corrections after multiplication by U have degrees at most5,5,3, below deg Z=7. Thus N has degree242 and leading homogeneous part

    N242=128 U0^8 A0^2 B0 C0^4 n.

This is also an upper-bound proof: every factor's formal Laurent degree is bounded as stated, and their product is the literal polynomial N. Since the leading coefficient displayed is nonzero, the bound is attained.

The guard has degree16, so the unit-product finalizer has degree242+32=274, with leading part N242*G16^2. Taking the h^6 term from k^6 and z^4 from R^4 gives

    [j^124 w^41 v^47 h^6 z^4 r^17 c^34 n] P13
      =2^265 3^174 beta^124 >0.

The exponent sum is274. The independent checker also checks the generic norm identity, its weighted leading form, and an attained-degree specialization of the actual fixed coefficient slice. No generic-coefficient assumption substitutes for the authentic positive beta in this exact coefficient.

The optimized live gate count is129:76 multiplications,31 additions,22 subtractions. The endpoint improves both arithmetic gates and degree over the inspected13-variable degree536/135-gate endpoint. No unconditional arithmetic-circuit optimum is claimed.
