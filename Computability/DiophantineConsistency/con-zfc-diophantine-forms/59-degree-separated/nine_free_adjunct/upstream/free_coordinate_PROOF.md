# A free carrier and a smaller two-block source

## Fixed equation, domain, and proof boundary

The primary object is `generated/calibrated_absorbed_positive.json`, a division-free arithmetic circuit for one polynomial in the **nine strictly positive integers**

    b, g, h, s, w, C, i, j, n.

Every other letter below is a polynomial abbreviation. The circuit has exactly 560 live binary operations (173 additions, 55 subtractions, 332 multiplications), including scalar multiplications. Its exact total degree is 4,686,812. The natural-variable circuit substitutes each input plus one and uses 567 operations. Coefficients are fixed by the complete four-port binding `COEFFICIENT_BINDING.json`, the explicit fixed-power recipes, and the supplied materialized leaves. No coefficient is selected by testing consistency.

This component proves a new mathematical reduction to the existing positive quadratic source. Its consistency equivalence imports the source compiler/calibration theorem and the numerical Jones ratio theorems stated below. These are ordinary mathematical arguments formalizable in ZFC, not a new end-to-end Lean/Rocq certificate or an exported derivation in an object-language ZFC calculus. Finite checks establish identities, explicit data, and implementation facts; they do not establish unbounded unsolvability.

## 1. The exact source and the inherited numerical interface

The source is the **original** package-31 system of 22 quadratic equations in 31 positive coordinates, stored in `upstream/upstream_parent_quartic31.json`. Its four fixed ports are beta, K0=K, MC, MF=MF_source. The complete Wang943 mixed 121-by-8801 tuple has port bit lengths 1064921, 1070004, 1064921, and 1064922. MF is already shifted. Individual ports must never be substituted from another tuple.

Write p_r(x) for residual r after replacing every positive source coordinate by x_i+1. Inherited compiler/calibration gives

    exists x in N^31, all p_r(x)=0
    iff the fixed literal machine halts on blank tape
    iff the repository's syntactic ZFC proof calculus has a finite refutation.

The source's fifth residual has p_5(0)=1. Thus the all-zero shifted source vector is not a solution.

The source-dependent proof is `upstream/COEFFICIENT_PROOF.md`, with exact hash and provenance in the coefficient binding. `upstream/SIGNED10_PROOF.md` identifies this original source interface; its later Sun-specific finalizer is not invoked here. The numerical Jones ratio interface is retained verbatim in `upstream/NineRatio.lean` and its adjacent numerical proof files. This component does not claim to rerun that Lean development.

The ratio contract used is as follows. Given R,N>=8, 0<b<=R,N, Gcap>0, positive g,h,s,w,i,j_old and phi>=0, form the standard ratio registers in Section 5 with

    C_old = 2R+1+bw+phi,
    H_old = 2R+1+j_old C_old.

The four conditions are a0 a square, DFI a square,

    JF divides QF+J(H_old-C_old),
    mu > 0.

They imply that b is a power of two, N^2 divides binomial(2R,R), and 8g<Gcap. Conversely, the central-binomial divisibility, b a power of two, and the stronger bound 32g<Gcap supply the ratio witnesses. These are the existing numerical `ratio_sound` and `ratio_complete` theorems; their old positional source is not assumed.

## 2. Explicit selective quadratic code

Let W=183. The 31 positive variable positions, in the source's stored coordinate order, are

    9,25,23,139,35,151,168,21,91,181,94,52,150,180,7,135,
    38,88,183,106,178,136,20,138,8,64,105,154,37,137,120.

Adjoin padding position w_0=0. The residual order and the corresponding targets are

    order:   16,2,9,14,21,7,15,22,13,3,19,20,1,10,17,8,4,6,11,18,12,5
    targets: 70,86,451,685,1050,1296,1530,1874,2212,2358,2696,2780,
             2792,3157,3290,3634,3929,4238,4384,4527,4865,5190.

For a source monomial x^alpha put

    c_(r,alpha)=(2-|alpha|)! product_i alpha_i! [x^alpha]p_r,
    e(alpha)=sum_i alpha_i w_i,
    Dcode(T)=sum_(r,alpha) c_(r,alpha) T^(target_r-e(alpha)).

The 136 nonzero terms have distinct, nonnegative encoding exponents. For every supported source monomial alpha and every one of the 528 padded quadratic monomials beta, the finite certificate verifies

    target_r-e(alpha)+e(beta) is a target
    iff beta=alpha,

and then the target is target_r. There are exactly 71,808 interactions and 136 intended hits. Consequently, for C_x(T)=(1+sum x_i T^w_i)^2,

    [T^target_r] C_x(T) Dcode(T)=2p_r(x).

This is an exact identity in all 31 source variables and all four fixed ports. The maximum exponent of Dcode is 5190 and its coefficient is 2. All other coefficients have absolute value below

    M=2^2134927.

The independent auditor reconstructs the shifted source and the factorial weighting directly from the original residual monomials, independently of the builder's source-expansion helper, and enumerates every interaction.

## 3. The sparse source and the smaller two-block number

Fix

    kappa=2134940, a=2^kappa=8192M,
    cstar=2^16012039=2^(15kappa/2-11).

Define the following ordinary polynomial registers:

    B = a b^2,
    ell = sum_i B^w_i,
    A_targets = sum_r B^target_r,
    N0 = B^184,
    Mask = N0-1-(b-1)ell,
    Jcode = 2(1+g)^2 Dcode(B)+A_targets,
    Scode = g+N0 Jcode,
    Tcode = Mask+N0(B-2)A_targets,
    L = b B^5741,
    R = (Scode+Tcode)L+L-1-Scode,
    N = cstar B^2966,
    Gcap = 32b B^183.

All sum indices and exponents are fixed. The final polynomial contains no binomial coefficient, variable exponent, division, radical, or hidden existential index.

### Bounds before the binary-base conclusion

For every positive b, B-1>M, and the leading coefficient of Dcode gives

    B^5190 < Dcode(B) < M B^5191/(B-1).

The explicit low mask has digits B-b at the allowed positions and B-1 elsewhere, so 0<=Mask<N0. Therefore Scode>0 and Tcode>=0 for every positive assignment, even without an upper bound on g. The alternative expression

    R=(L-1)Scode+L Tcode+L-1

proves R>=L-1>=8 and b<=R. Also N>=8 and b<=N. These facts allow the numerical ratio theorem to be applied before the final equation has been decoded.

Suppose now that g<4bB^183. Since g is integral, 1+g<=4bB^183. Also g<N0, because 4b<B. Put Z=B^5557. Then

    2(1+g)^2Dcode(B)
      < 32Mb^2 B^5557/(B-1)
      = B Z/[256(B-1)] < Z/128.

The target sum is below Z/128; hence 0<Jcode<Z/64. Similarly

    (B-2)A_targets < B^5191 < Z/128.

Since Z>128, these imply

    Scode < N0 Z/32,
    Tcode < N0 Z/64,
    Scode+Tcode < N0 Z=B^5741<=L.

These bounds include b=1. The previous source used 2bB^5741 and an additional L^2 term; neither is needed for this argument.

### Exact popcount threshold

When b=2^k, B=2^v with v=kappa+2k, and L=2^u with u=k+5741v. For S,T>=0 with S+T<L,

    R=(S+T)L+(L-1-S).

Its binary blocks do not overlap. Let pop denote binary digit sum and tau=pop(S)+pop(T)-pop(S+T). Then

    pop(R)=u+pop(T)-tau,

where tau>=0 and tau=0 exactly when S&T=0. Legendre's valuation identity gives v_2(binomial(2R,R))=pop(R). The explicit mask has

    pop(Tcode)=206v-31k-22.

Consequently

    u+pop(Tcode)=5947v-30k-22
                =2[(15kappa/2-11)+2966v]
                =2 log_2(N).

Therefore N^2 divides binomial(2R,R) exactly when Scode and Tcode are bitwise disjoint. The case k=0 is included; it introduces no extra solutions.

### Sparse target padding with signed borrows

The low-word condition g & Mask=0 is equivalent to

    g=sum_i x_i B^w_i, 0<=x_i<b.

For such a decoded word, write h_t=[T^t](C_x Dcode). The source coefficient bound gives |h_t|<1024M b^2=B/8. The high word is

    Jcode=sum_t (2h_t+delta_t)B^t,

where delta_t=1 at target positions and zero otherwise. Normalizing these signed digits produces incoming borrows only in {-1,0}. At a target, h_t=0 produces normalized digit 0 or 1, both disjoint from B-2. If h_t>0 the digit lies between 2 and B/2; if h_t<0 it lies above B/2. Both cases have a masked bit. Thus

    Jcode & ((B-2)A_targets)=0
    iff every h_target=0
    iff every p_r(x)=0.

Positivity and the preceding word bounds make this ordinary finite binary arithmetic, with no negative-integer bit convention. Combining both words gives source soundness. For completeness, given a common shifted source zero, choose an arbitrarily large power of two b>max_i x_i and put g=sum x_iB^w_i. The source's nonzero-vector property gives g>0. Also g<bB^183, so 32g<Gcap. The carry test and central-binomial condition follow.

## 4. Why the carrier can be an independent input

The central new coordinate choice is that C is an independent positive input. The previous formula defined C=2R+1+bw+phi; that definition gave C the enormous degree of R. Its required lower bound will instead follow from the existing positive margin.

The only possible difficulty before recovering the margin is that

    Q=3(bw)C-2((bw)^2-1)

may be negative. Writing W1=bw, the shifted numerator

    J(n+W1^2)+Q

is strictly positive for every input, because J>=3, n>=1, and

    J(n+W1^2)+Q
      =Jn+(J-2)W1^2+3W1C+2>0.

The offset is a polynomial already present in Q. It costs no new variable. Section 6 proves that the final equation forces the margin to be positive; Section 5 then recovers the old carrier range, and Section 6 proves the shifted n remains positive in the reverse direction.

## 5. Ratio registers and exact quotient absorption

Set

    U=N^2w, Y=N^2s, M0=RY,
    P=2M0^2U, K=R+1+h(P-1),
    A=M0(U+1), B1=2R+1, W1=bw,
    J=4A-5, Q=3W1C-2(W1^2-1),
    D=(A^2-1)C^2+1,
    E=iJDC^2,
    F=(A^2-1)E^2+1,
    G=A+F(CD+1-A),
    H=C+F(B1+(j-1)C),
    I=(G^2-1)H^2+1,
    a0=(P^2-1)K^2+1,
    a1=64DFI,
    mu=[K^2-4(C-KY)^2]Gcap-8gK^2.

Every required magnitude is positive for C>=1; in particular A>=2, J>=3, D>=A^2, and CD+1-A>0. Moreover U>=N W1, so A>W1.

If mu>0, then |C-KY|<K/2, so C>K(Y-1/2)>K because Y>=64. Also K>=R+P and P>R+W1+1. Therefore

    C>2R+1+W1=B1+W1.

The old carrier parameter phi=C-B1-W1 is consequently a nonnegative integer, in fact positive. Thus allowing C as a free input is sound once the margin has been recovered.

Since E is divisible by both J and C, F is congruent to 1 modulo J and modulo C. The old ratio divisibility

    JF | QF+J(H_old-C)

is equivalent to J|Q and F|(H_old-C). If the old ratio witnesses are given, let z=(H_old-C)/F. Then z>0 and z=B1 modulo C. Because the old carrier has 0<B1<C, z=B1+j0C for a unique j0>=0. Taking the new positive coordinate j=j0+1 gives exactly our H. Conversely our H has

    j_old=1+((F-1)/C)B1+F(j-1)>0,

an integer, and equals B1+j_old C. Thus the original and absorbed ratio conditions are exactly equivalent:

    a0 square, a1 square, J|Q, mu>0.

The scale 64 does not change whether DFI is a square. This reparameterization uses no unproved cofinality of a restricted witness family.

## 6. The final polynomial and its complete reduction

Define

    t0=iJC,
    T0=t0(8D^2-4D-1),
    V0=PK,
    V1=T0GH,
    Omega=J mu,
    Theta=J(n+W1^2)+Q-Omega(V0+V1),
    X0=Omega^2 a0,
    X1=Omega^2 a1.

The equation is

    F9=(Theta^2-X0-X1)^2-4X0X1=0.

The exact majorant identities are

    V0^2-a0=K^2-1>0,
    DF=t0^2D^3(D-1)+D,
    T0^2-64DF=t0^2(8D+1)-64D>0,
    V1^2-a1=[t0^2(8D+1)-64D](GH)^2+64DF(H^2-1)>0.

The third expression equals 8D(t0^2-8)+t0^2 and t0>=3. Hence V0>sqrt(a0)>0 and V1>sqrt(a1)>0 without assuming a zero.

If mu=0, the shifted numerator makes Theta>0, so F9=Theta^4 cannot vanish. Otherwise the four real norm factors imply

    n+W1^2+Q/J=mu Z,
    Z=V0+V1+r0+r1,
    r0^2=a0, r1^2=a1,

for some real choices of signs. The unconditional strict majorants give Z>0. The left side is positive by Section 4, so mu>0 follows before any assertion that the roots are rational. This recovers the old carrier range.

Now P<A^2, D>C^2, F>=A^2, G>A, I>=A^2, and C>K. Therefore

    DFI>A^4C^2>P^2K^2>a0.

Thus a1>a0, and r0+r1 cannot be zero. Its value Theta/Omega is rational. For x=r0+r1!=0, the identity

    2xr0=x^2+a0-a1

makes r0 rational, and then r1 rational. Rational square roots of integers are integers. Since r1/8 is a rational square root of DFI, DFI is also a square. The displayed factor equation, with Z integral, gives J|Q. All four original ratio conditions are now established.

Conversely, take ratio witnesses. Convert their C and H as in Section 5 and choose the positive integer roots r0,r1. Set

    n=mu(V0+V1+r0+r1)-W1^2-Q/J.

This is an integer. It is strictly positive: A>W1 and D>C^2 imply W1^2<D and W1C<D. Thus W1^2+Q/J<4D, while T0>5D, G,H>=1, and V1>5D. Since mu>=1 and Z>V1, the chosen n is positive. The corresponding norm factor vanishes. This proves both directions, including the witness domain.

Combining this argument with Sections 1-3 proves, in ordinary mathematics formalizable in ZFC,

    F9 has a zero in positive integers iff a finite ZFC refutation exists.

Negating the statement yields absence of positive zeros iff Con(ZFC). No consistency assumption was used.

## 7. Hybrid source evaluation without moving any target

This is a circuit improvement, not a change in the polynomial. Put u0=B^183 and u_i=B^(183-w_i). Homogenize the inherited 60-operation positive quadratic source at the coordinates u_i+u0. For an affine addition, multiply the lower-degree summand by the required power of u0; for multiplication, add homogeneous degrees. The comparisons are homogenized to degree two.

The source60 transport row is the newer shifted transport normalization. Add beta*J*u0 to its fifteenth homogeneous residual to recover the **original** package-31 residual. The independent auditor expands all 22 comparisons in all 35 symbols and verifies exact equality to the original source.

For a shifted quadratic residual, factorial weighting doubles diagonal monomials and leaves mixed monomials unchanged. Therefore add one further copy of each diagonal coefficient times u_i^2, including the padding diagonal u0^2, to the homogenized residual. Multiplication by B^(target-366) then gives exactly that row's reversed coefficient block.

The targets 70 and 86 are below 366, so that last multiplier would not be polynomial for those two rows. Evaluate those two small rows directly instead. Evaluate the other twenty rows through the shared homogeneous circuit, and combine the blocks by sparse Horner evaluation. This avoids a global target translation and preserves every exponent and the exact polynomial. It saves 161 operations compared with this component's direct term evaluator. The degree certificate deliberately uses the separate direct evaluator, so the gate-saving evaluation does not conceal a degree cancellation.

## 8. Exact degree and reproducible evidence

Put r=deg R=22233, q=deg N=5932, and W=183. The exact degree is

    104r+400q+8W+316=4,686,812.

The certificate rewrites the inner norm using

    E0=J(n+W1^2)+Q,
    delta1=V1^2-a1,
    Theta^2-Omega^2(a0+a1)
       =E0^2-2E0Omega(V0+V1)
          +Omega^2[(K^2-1)+delta1+2V0V1].

The positive decomposition of delta1 above resolves the leading cancellation. Under the diagonal substitution of one indeterminate for all nine inputs, the resulting leading coefficient is exactly

    2^94 a^2343092 (a+4)^104 cstar^400 >0.

The generated certificate carries every coefficient in the two independent fixed symbols a,cstar and encounters no unresolved positive-degree leading cancellation. Its upper bound is a full multivariate total-degree bound; the nonzero diagonal coefficient proves equality for the actual positive fixed coefficients.

`verify.py` replays the builder, all exact identities, the 71,808 extraction interactions, 11,049 generic carry cases, 33 threshold calibrations including b=1, 1,200 modular full-circuit diagnostics, liveness and operation counts, source hashes, fixed integer materialization, and byte-identical reconstruction. The core runs both normally and under Python -O. The modular diagnostics supplement the universal algebraic proofs and are not substituted for them.

## 9. The original-H comparison

The two-operation-larger comparison keeps H=B1+jC with j positive. Put u=JF, v=QF+J(H-C), Omega=u*mu, and Theta=u(n+W1^2)+v-Omega(V0+V1), with the same norm polynomial. The source, free carrier, and majorant proof are unchanged. Before recovering the margin, the left side n+W1^2+v/u is positive because the shifted Q contribution is positive and H-C>0. After recovering positive mu, the same radical separation makes both roots integral and forces u|v, exactly the old ratio divisibility. For completeness, W1^2+v/u<4D+H, while V1>5DH>=4D+H; hence the reconstructed n is positive. This supplies the same complete equivalence for its 562-operation positive circuit and 571-operation natural translate, both of degree 4,686,812. They are reference presentations; the 560-operation absorbed circuit is primary.
