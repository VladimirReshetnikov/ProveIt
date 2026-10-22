# A 27-integer-variable norm-resultant construction

## Current complete coefficient instantiation

Every main JSON packet and its builder in this release selects the complete
`T4-4094-binary-copy-zero-padding-5pow11` tuple from
`../coefficients/COEFFICIENTS.json`, with tuple SHA-256
`726ac1d0ae1957f75f71966a65c8730403998a1f719e927f6894babea12cf938`.
The aliases are Bm1/beta -> beta, Kconstant/K0 -> K, MC -> MC, and
MF -> MF_source. MF_source is the shifted port MF_native + B - 1.
The whole-tuple transfer proof is `../coefficients/COEFFICIENT_PROOF.md`;
it preserves the native interface, rank congruence, parity, positive odd i,
and positive square w required by the signed and low-degree reductions.
Here B = 2^(5^11). References below to original06/blank67 and d = 5^67
describe the historical source proof, not the numerical instance selected
by this release. Its same completeness argument applies through the
proved transfer with odd d = 5^11 and odd five-power tableau area.
No individual coefficient is mixed with another compiler's tuple.
The vendored source evidence remains unchanged.

## Result and scope

At repository pin `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`, combine the explicit resultant of `09-combined13` with the odd-normalized-multiplier and square-power-scale canonical witnesses of `14-integer29`. A strengthened denominator bound permits the primitive scalar itself to be an arbitrary integer. This gives a single polynomial in **27 unrestricted integer variables**, with 136 binary arithmetic operations and exact degree 1116. A four-equation variant costs 130 operations and has maximum degree 1064. Its sum of four squares costs 141 operations and has degree 2128.

This reduces the comparable unrestricted-integer dimension from 29 to 27. It does not reduce the 13-positive-variable dimension, establish global minimality, or improve the smallest positive-domain arithmetic count. It is an ordinary mathematical proof using the inherited compiler/Pell theorems, not a new proof-assistant certificate.

The historical derivation used the original `06-blank67` constants supplied at `09-combined13/upstream/06_k215_constants.json`, not the package-09 default T-shape recipe. In that historical instance the cell-bit exponent is `5^67`, and the shifted MF port is `MF_native+B-1`. The odd-cell-bit/five-power completeness used below is explicitly established for this original compiler. The constants remain closed finite integer recipes; they are not four arbitrary parameters.

## 1. Explicit polynomial

Use seven positive integer coordinates

    J, F, alpha, z, s, eta, zeta,

and six unrestricted coordinates

    r, u, h, T, gamma, t.

Put `i=2r+1`, `w=u^2`. With fixed constants beta=B-1, K, MC, MF (shifted), define the following integer polynomial abbreviations. Every abbreviation is substituted, not a quantified unknown.

    q=beta J+1, Cw=q-F-alpha,
    X=wq, Y=sq^3, E=XY, k=eta+zeta, c=kY+eta,
    a=E+Y, H=4a+3, Delta=a^2+H,
    Dmain=X+ac+gamma H,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Lfirst=E kY,
    Nmain=Dmain^2-Delta c^2,
    Nk=k-hE-R,
    Nt=(K+w)Cw+q-F-z(q-1),
    A=1+Lfirst(Lfirst+k),
    D=1+Delta i^2 c^4,
    Q=Delta(D-1)=(Delta i c^2)^2,
    v=cT, b=c+RD, d=Q-1,
    e=Q(Dv^2+b^2)-1,
    B0=2Qvb, M=D+v^2,
    C=d(t^2+M^2 A)-e,
    U=C^2+D B0^2-4d^2 t^2 M^2 A,
    Res=U^2-4C^2 B0^2 D,
    P=Nmain Nk Nt(1+Res)-1.

The mixed-domain equation is P=0. Finally replace each of the seven positive coordinates by its own disjoint copy of

    Pos(x,y,z)=x^2+x+y^2+z^2+1.

There are 7*3+6=27 unrestricted integer unknowns. Pos is always positive, and represents every positive integer by Legendre's three-square theorem applied to 4n-3. Thus this last substitution preserves existence in both directions.

## 2. Outer units and the zero square-scale boundary

Suppose P=0. Every displayed factor is an integer unit. Since Delta is 0 or 3 modulo 4, Nmain cannot equal -1. Since Res is U^2 modulo 4, 1+Res cannot equal -1. Consequently

    Nmain=1, Res=0, Nk=epsilon, Nt=nu,
    epsilon,nu in {-1,1}, epsilon*nu=1.

Initially w>=0 and i is a nonzero integer. If w=0, then X=E=0, a=Y, Dmain=ac+gamma H, and

    Nmain=H(2ac gamma+gamma^2 H-c^2).

This contradicts Nmain=1 because H=4Y+3>1. Thus w>0 and X>=q. This exclusion precedes all growth, rank, or root-reconstruction steps.

The inherited transport-unit argument uses z>0 and K+w>0, not signs of h,T,gamma,t, and gives Cw>=0. The authentic-mask bounds then give

    q>=16, Y>=q^3>=4096,
    0<R<q^4-2, E>=q^4>R+2, a>R+2.

The index equation k=R+epsilon+hE and k>0 imply h>=0: h<=-1 would imply k<=R+1-E<0. Therefore R<=k+1<=3k/2, using k>=2. Also c<k(Y+1).

## 3. A strict root-separation bound, valid before recovery

Set S=c^2+R^2. Since Y>=4,

    S < k^2((Y+1)^2+9/4) < 2k^2Y^2.

Writing Lfirst=kXY^2 gives

    A=1+k^2 XY^2(XY^2+1)>k^2 X^2Y^4>16S.

The last inequality follows already from X>=16 and Y>=4. In particular A>1+8S.

Let K0=Dv^2+b^2. All of D,Q,d,M,b are positive; D>1, Q>1, d>=Q/2. Since b=c+RD and D>1,

    b^2 <= 2D^2(c^2+R^2)=2D^2 S,
    M^2=(D+v^2)^2 >= D^2,
    M^2 >= 4Dv^2.

These hold for signed or zero T. Hence

    K0 <= M^2(1/4+2S),
    A M^2 > 4K0,
    d A M^2 > 2QK0.

Since e=QK0-1 and

    |B0| sqrt(D)=2Q|v|b sqrt(D) <= QK0,

we obtain the strict bound

    C=d t^2+dM^2A-e > QK0+1 > |B0| sqrt(D).

In particular C>0, even for arbitrary signed t and T. This is stronger than the positive-domain denominator bound in package 09.

## 4. Excluding t=0 and T=0

If t=0 then U=C^2+D B0^2, so

    Res=(C^2-D B0^2)^2>0

by the strict bound above, contradicting Res=0. Thus t is nonzero; no positivity or parity condition on t is necessary.

Suppose T=0. Then v=B0=0 and Res=0 implies

    C^2=4d^2 t^2 M^2 A.

As d,t,M are nonzero, put tau=C/(2dtM). This is rational and tau^2=A is an integer, so tau is an integer. Put y=t-M tau, also an integer. The defining identity for C gives

    d y^2=e=Qb^2-1,
    Qb^2-(Q-1)y^2=1.

But Q=Delta(D-1), b=c+RD, and Delta>R give

    Q-b=(Delta-R)D-Delta-c
        >=D-Delta-c
        =1+Delta(i^2 c^4-1)-c>0.

Thus 1<b<Q. The last Pell-type equation is impossible: it implies |y|>=b+1 and therefore

    b^2-1=(Q-1)(y^2-b^2)>=(Q-1)(2b+1)>b^2-1.

The final strict inequality uses Q-1>=b. Contradiction. Hence T is nonzero, so B0 is nonzero.

## 5. Exact reconstruction and signed soundness

All required denominators have now been proved nonzero. Define, in the proof only,

    f=-U/(2CB0),
    tau=(C+B0 f)/(2dtM),
    y=t-M tau.

Res=0 gives f^2=D. A rational number whose square is an integer is an integer, so f is an integer. By the identity U+2CB0 f=0,

    (C+B0 f)^2=4d^2 t^2 M^2 A,

and hence tau^2=A; tau is likewise an integer. Thus y is an integer by its definition. This does not use the false general principle that a rational point on an integral Pell conic has integral coordinates.

Expanding the unsquared identity gives

    d y^2=e-B0 f=Q(vf-b)^2-1.

Since f^2=D,

    f^2-Delta i^2c^4=1,
    V=vf-b=c(Tf-1)-Rf^2,
    QV^2-(Q-1)y^2=1,
    tau^2-Lfirst(Lfirst+k)=1.

Together with Nmain=1 and the two common-sign index/transport units, these are exactly the normalized signed equations analyzed in `14-integer29/proofs/signed_domain_proof.md`. Its normalized-rank, signed auxiliary quotient, no-wrap, signed-main-root, half-binomial, and native-window arguments apply. In particular i is nonzero, w>0, and the seven source coordinates retain positivity. The arguments recover the positive index/transport signs and a genuine blank K215 halting run. No positivity of the reconstructed f,tau,y is needed.

## 6. Completeness

For the original 06 compiler, package 14 proves that any accepting blank computation has a canonical witness with square w and odd positive normalized i. The square restriction follows from odd cell_bits=5^67 and an odd five-power tableau area. The odd-i restriction uses strong index m=cR rather than 2cR.

Take that canonical witness and set t=M tau+y. The source tau,y,M are positive, so t is a valid unrestricted integer. Its three norm equations imply the exact resultant identities above and hence Res=0; the remaining three factors all equal 1. Thus P=0. Choose three-integer Pos preimages for the seven positive coordinates. This gives a 27-integer zero.

Soundness and completeness prove, by the same ordinary arguments internalizable in ZFC as the pinned source compiler, that this explicitly coefficient-bound equation has no integer zero exactly when Con(ZFC). This does not prove consistency or inconsistency, and does not add a formal assistant verification of the machine-to-Diophantine bridge.

## 7. Exact circuit counts and degrees

The pinned 84-gate product, 78-gate comparison system, and 89-gate sum of squares receive exactly 52 new gates: seven Pos expressions at 7 gates each, i=2r+1 at 2 gates, and w=u^2 at 1 gate. All supplied variables and gates remain live. The resulting counts are:

- Product: 27 integer variables, 136 gates = 72 multiplications + 64 additions/subtractions, exact degree 1116.
- Four-equation system: 27 integer variables, 130 gates = 69 multiplications + 61 additions/subtractions; exact residual degrees 35,13,4,1064.
- Sum of squares: 27 integer variables, 141 gates = 73 multiplications + 68 additions/subtractions, exact degree 2128.

For the degree proof assign weight 2 to the seven positive source coordinates and w, and weight 1 to i,h,T,gamma,t. Then

    deg(q,X,Y,E,k,c,a,Delta)=(2,4,8,12,2,10,12,24),
    deg(A,D,Q,v,b,M)=(44,66,90,11,74,66),
    deg(e)=238, deg(dM^2A)=266, deg(d t^2)=92.

Thus C has the unique highest term from dM^2A; U has the unique highest term C^2, degree 532; and Res has the unique highest term U^2, degree 1064. The subtracted term 4C^2B0^2D has degree 948, so no leading cancellation is possible.

Let E0 and c0 denote the leading weighted forms of E and c. The Res leader is E0^40 i^24 c0^56. Expanding the main norm cancels its degree-44 terms, leaving the nonzero leader 8 E0^2 c0 gamma of degree 35. Nk has leader -h E0, degree 13, and Nt has leader

    w(beta J-F-alpha)-z beta J,

of degree 4. Their product with the resultant leader is nonzero, proving exact degree 1116. The residual is uniquely dominant in the sum of squares, proving degree 2128.

After substitution, the leading forms remain nonzero: Pos contributes x^2+y^2+z^2, w contributes u^2, and i contributes 2r. Setting the second and third coordinates of each Pos to zero leaves an injective monomial substitution, so no hidden leading cancellation occurs.

`build_integer27.py` emits all three literal circuits and verifies every operand, gate, and supplied port. The receipt records 288 exact substitution comparisons, 72 isolated signed reconstruction fixtures, 3003 gap-inequality checks, and two modular-univariate attained-degree diagnostics for each packet. These finite checks supplement, not replace, the proof above.
