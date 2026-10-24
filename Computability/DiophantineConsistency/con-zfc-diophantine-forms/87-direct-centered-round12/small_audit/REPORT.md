# Independent audit of the round12 small-variable equations

## Finding

PASS, at the stated ordinary mathematical composition boundary. No defect was found in the five integer zero-set transformations or the eleven-positive-variable two-center construction. This is not an end-to-end formal certificate of the native compiler, Pell classification, or the literal K215/ZFC calibration. Those inherited semantic theorems remain dependencies, exactly as disclosed by the producers.

The independent checker is `check.py`. It imports no producer program and uses only the Python standard library. JSON is inert data. Polynomial strings pass a restricted AST grammar allowing names, integer constants, unary signs, addition, subtraction, multiplication and fixed nonnegative integer powers. The arithmetic circuit is separately checked for SSA order, permitted operations, defined leaves, live witnesses and live gates. No `eval`, `exec`, SymPy, generated-module import, or upstream program execution is used by this checker.

`CHECKS.json` records:

- All six actual integer-family payload hashes and all four actual positive-family payload hashes, bit lengths and byte lengths.
- All five literal integer packets against the retained exact 24-variable parent, including deleted rows and the centered auxiliary row correction, on 1,500 signed assignments across three prime fields. Zero, minus-one and plus-one assignments are explicitly included.
- Every common named positive circuit register against an independently written mathematical definition on 600 signed assignments, across the same three fields.
- Exact univariate polynomial slices over three finite fields using the actual fixed coefficient payloads. These give the advertised degree lower bounds after actual specialization, not merely at symbolic generic coefficients.
- An exact sparse integer-polynomial expansion of the positive norm in seven independent registers, including the universal 99/198 weighted-degree cancellation and its leading forms.
- The exact eight-conjugate norm identity in four independent formal variables.

Finite substitutions are transcription diagnostics and degree lower bounds. They are not offered as proofs of the universal semantic equivalences or of multivariate degree upper bounds. The latter are established by the algebra below.

## 1. Integer domains and zero sets

All listed witnesses are unrestricted integers. Each final equation is the sum of squares of the literal residuals, hence vanishes exactly when every row vanishes. Fixed coefficient ports are bound, not unknowns. There are no divisions or variable exponents.

Replacing alpha by C=q-F-alpha is an integral polynomial coordinate change, with inverse alpha=q-F-C. The transport row is exactly

    (K0+W)C-F-z(q-1).

Solving for F is monic; there is no division by K0+W or by q-1. In particular the z witness must remain, and does remain.

The first-root coordinate change tau_old=tau+E(c-eta) is an invertible integer shear. With k=1-V+jc+hE, expansion of the old first norm cancels E²(c-eta)² and leaves

    tau²+(2tau-k)E(c-eta)-1.

It does not require any other row to vanish.

For the 21-variable chart, put V=fo-c and y_old=fo+y. Then

    y_old²-V²=(c+y)(2fo+y-c).

Writing S=I²-Delta(f²-1) and Aold=I²(V²-y_old²)+y_old²-1, the new auxiliary row satisfies the exact polynomial identity

    Anew=Aold+S(y_old²-V²).

The retained S row makes this reversible in both directions. I occurs only in S after the operation; its monic definition I=(2r+1)c² can therefore be substituted and removed. This is not cancellation of a potentially zero factor. No f, c, o, y, I, Delta or auxiliary sign/nonzero hypothesis is used in these transformations.

The 20-variable chart deletes a=E+Y, V, I and F by monic definitions. The 19-variable chart deletes E=XY and a=(X+1)Y instead. Those assignments follow from the original first two rows without division: a-E=Y and E=X(a-E). The 18-variable chart further substitutes eta=c-Yk. Here k depends on V,j,c,h,E but not eta, so this last substitution is genuinely monic and noncircular.

The free-scale chart restores E=XYfree and a=(X+1)Yfree. Its retained row is Yfree-(2v_scale+1)q³. Thus projection uses Yfree=a-E and restoration recovers both original rows. The free scale is one listed unknown, not a hidden free coefficient.

## 2. Integer degrees on the actual slice

The complete tuple has beta=2^1064921-1, cone_A=2^1113 and cone_B=2^666104; all are nonzero. The exact same actual payloads are used by the independent modular polynomial calculations.

- 21 variables, 9 rows, degree 16. The centered auxiliary row has degree at most 7. The transport-substituted determinant T has degree 4; its pure (w3,C) top term is -144 cone_A² w3² C². The joint guard alone has degree 8. The final coefficient of w3^8 C^8 is 12^8 cone_A^8=429981696 cone_A^8, strictly positive.
- 20 variables, 8 rows, degree 20. The top of a=E+Y is 54 beta³ J3³ v_scale, of degree 4. The strong norm and main norm have degree at most 10; the original auxiliary row has degree 10, and the guard degree at most 8. The coefficient of f^4 v_scale^4 J3^12 is 54^4 beta^12=8503056 beta^12, uniquely supplied by the squared strong norm.
- 19 variables, 7 rows, degree 32. E has degree 6 and top 1944 beta^4 J3^4 w3 v_scale. Thus k has degree 7, Z=eta(k-eta) degree 8, and the guard degree 16. Other rows have degree at most 14. The final coefficient of eta^4 h^4 w3^4 v_scale^4 J3^16 is 1944^4 beta^16=14281868906496 beta^16.
- 18 variables, 6 rows, degree 88. The top of eta=c-Yk is -104976 beta^7 h J3^7 w3 v_scale², degree 11. Then Z has top -eta_top², degree 22, and the guard has degree 44. Other rows remain below degree 44. The selected final coefficient is 104976^8 beta^56=2^32 3^64 beta^56, at h^8 w3^8 v_scale^16 J3^56.
- Alternate 20 variables, 8 rows, degree 20. E has top 36 beta J3 w3 Yfree, degree 3. The guard and old auxiliary row have degree at most 10. Only the guard supplies eta^4 h^4 J3^4 w3^4 Yfree^4, with coefficient 36^4 beta^4=1679616 beta^4.

These leading coefficients are positive actual integers, not genericity assumptions. The restricted evaluator also recovers each advertised degree over every one of the three finite fields.

## 3. Positive soundness: ordering and exceptional cases

The eleven witnesses are strictly positive. Before any equation is imposed, k>=2, c>=3, a>=2, Delta>=15, I>=c² and q>1. Let b=c Told-R, an arbitrary integer at this stage. The inherited separation argument uses only those inequalities, not C>0 or q³|Y:

    1<Dtau<Df<Q, |V|>1,
    sqrt(Dtau)<(a+1)c,
    sqrt(Df)>(a+1)c².

If b=0, V=-c and the strong root dominates the sum of the first and auxiliary roots. If b is nonzero, |V|>=Df-c and the auxiliary root dominates the other two. Thus no signed root sum is zero. The radicands are pairwise distinct: if Dy were Dtau or Df, the equality Q(D-V²)=D-1 would force a positive integer strictly between 0 and Q to be divisible by Q.

The norm identity is an actual product over eight signed sums; its radicands are positive rational numbers. A zero therefore yields a signed triple with rational sum. The explicit rational-recovery formula has denominator xi(xi+xj)(xi+xk), nonzero because the roots are nonzero and their squares distinct. It follows that all three roots are rational. The first and strong roots are integral by rational-square integrality.

For the auxiliary root, adjacent-Pell saturation is valid for every Q>1, even without Q being a square. If y=a/m is reduced and QV²-(Q-1)y²=1, then m² divides Q-1, so (Q-1)y is integral. Replacing positive |V|>1 by

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserves the equation, gives 0<|V'|<V and preserves the reduced denominator m, since 2Q-1=1 modulo m. Absolute values permit iteration. V=0 is impossible; at V=1 the equation forces y=1. Hence m=1. This covers every sign and excludes the only possible zero failure explicitly.

Consequently M divides Zbar before any reconstructed transport positivity is asserted. Reduction modulo q³, together with gcd(q-1,q³)=1, gives q³|Y.

Now the authentic masks satisfy 0<MC<beta and beta<MF<2beta, checked on actual payloads. They imply 0<(MC+qMF)J<2q² and q>=16. The written bound R<q³(q+alpha) is valid without C>0; also R>-Fq³. Since Y>=q³ and c>Y,

    c(q+alpha)>R,
    b=c(T+q+alpha)-R>cT>=c,
    V=Df b-c>1.

Thus positivity has not been assumed prematurely. With delta=Q-1>(Delta-1)Df, c<2kY and Delta-1>4Y², the exact positive gap satisfies

    0<y-V<V/delta<b/(Delta-1)
      <c Told/(Delta-1)+Fq³/(Delta-1)<k Told+F=L.

Also Dcenter²-Df=I²-1>0, and 0<Dcenter-f<I. Therefore

    r=n+L+V+Dcenter-f_signed-y_signed>0

for every recovered pair of signs. The signed values, not their absolute values, are used in this equality. Absolute values are used only to obtain positive f,y and to bound r. With u=y-V>0, all hypotheses of the source70 weighted-carrier theorem hold. That theorem, rather than an unproved positivity heuristic, recovers the native positive witnesses.

The product finalizer is valid without assuming its residuals nonnegative: both are squares modulo 4, so neither is -2. The alternative factors (-1,-1) in (1+N8)(1+A1)=1 are excluded. Thus its zero set is exactly the simultaneous zero set.

## 4. Positive completeness: the cofinality argument

The source61 auxiliary reconstruction applies to a normalized strong pair with c²|I (indeed it needs only c|I). It gives one positive V0,y0 with

    QV0²-(Q-1)y0²=1,
    V0=f²(c T0-R)-c.

The proposed matrix

    B=[[2Q-1,2(Q-1)],[2Q,2Q-1]]

has determinant 1 and preserves QV²-(Q-1)y². All entries are positive. For h=c f²>0, the reduction of B lies in the finite group SL2(Z/hZ), so some positive power is the identity modulo h. Iterating this power gives positive, strictly increasing and unbounded Vj,yj, with Vj=V0 modulo h. Hence

    Tj=(Vj+c+R f²)/(c f²)

is integral and unbounded. This genuinely proves the required cofinality; it does not silently assume an auxiliary completeness lemma supplies arbitrary large T.

Choose Tj>q+alpha and kTj+F>I; then T=Tj-q-alpha is positive and L>I. Only after this choice are W and the transport r computed. The inherited canonical promises t0>=q, tau>ell and s<k give

    r=W t0+tau-ell-k-s>qW-2k>2L>L+I.

The last bounds follow from q>=16 and L>=k. It follows that

    n=r-L-(Dcenter-f)+(y-V)>0.

This establishes positivity of every new coordinate. The adaptive gamma uses only the unchanged outer canonical data, so enlarging the auxiliary pair does not destroy its construction. There is no dependence cycle between the auxiliary orbit, its chosen weight and the transport gap.

## 5. Positive exact degree and cost

The 113 live binary operations are independently recounted: 64 multiplications, 32 additions and 17 subtractions. Every one of the eleven witnesses and four fixed ports is live. The circuit is division free.

For the universal norm cancellation, take independent formal registers (M,V,D,z,e,A,Q) of weights (4,18,7,8,10,16,18), where D=Dcenter, e=I²-1, z=Zbar-M(V+D), A=M²Dtau. Then Bf=M²(D²-e), Cnum=M²(QV²-1). The exact independently expanded Jn identity is

    Jn=(Q-1)[z²+2MDz+M²e-A+2MV(z+MD)]-M²(V²-1).

The 89-term Ncenter expansion has weighted degree 99 and unique leading term 8Q²M³V²Dz. The 1110-term N8 expansion has weighted degree 198 and leading form

    64Q^4 M^6 V^4 D²(z²-A).

These are exact universal polynomial calculations over Z, not degree observations after a specialization. Here z has degree at most 8 and A degree at most 16. Their leading difference is

    z0²-A0=M0² L0 Bt0(L0 Bt0-2ell0).

For the adaptive carrier, write Dstar=Uac+B with B=UX+H(U gamma+SX-r0). Then

    A1=B²+2UacB-U²(Hc²+1).

The largest degree is 13, supplied by 2UacB, whose leading form is exactly

    32q0²k0X²Y^4[4q0²Y gamma+q0³(q0-F)].

Combining these formulas gives the stated degree-211 coefficient. Choosing gamma, then T², then the minimum q0 degree forces the remaining choices alpha² in Bt0² and F^4 in (q0-F)^4. The coefficient at

    j^48 i^18 eta^39 X^30 Y^67 F^4 T² alpha² gamma

is exactly 8192(3beta)^48>0. This is independent of K0,MC,MF and nonzero on the authentic tuple. Therefore degree 211 is exact, not merely a propagated upper bound. Three actual-payload finite-field slices independently recover degrees N8=198, A1=13 and P11=211.

## 6. Source and packaging qualification

The reviewed source70 weighted-carrier theorem, source70 eleven-root separation proof, and source61 signed-index/positive auxiliary reconstruction proof are in the authenticated incoming centered-norm archive under its provenance directory. The new `positive/` component should include these source files, or an explicit internal archive path, in its final provenance bundle rather than leave the ordinary semantic dependency implicit. This is a packaging recommendation, not a newly identified mathematical assumption.

No global minimality, arithmetic-circuit optimality, historical novelty, proof of Con(ZFC), or new end-to-end formal verification follows from this audit. The claimed internal equivalence follows by composing the newly checked reductions with the expressly inherited compiler/calibration theorems.

## 7. Additional audit: the materialized 12-positive / degree-70 manuscript endpoint

This circuit arrived during the audit. It is correctly labeled a materialization of the incoming manuscript, not a new mathematical construction. The independent checker now also verifies its 100 live operations (55 multiplications, 26 additions, 19 subtractions), 12 live positive witnesses, 600 signed modular literal-formula comparisons, the exact universal ordinary-norm merger identity, and actual-tuple polynomial slice degrees (15,13,42) and total degree 70 over three fields.

The soundness dependency order in the incoming manuscript is essential and valid. A0 first gives q³|Y, the positive transport quotient and C>0. A1 gives the positive main Pell root and q^4|(k-R-1), using gcd(q,H)=1 and q^5|U. The first recurrence then gives 2m1=R+1 modulo q^4. Since 0<R+1<q^4 and m1>0, it follows that m1>=(R+1)/2, without auxiliary rank recovery. Consequently p>m1 and c>(a+2)Delta² are already established before the ordinary strong equation is recovered. This removes the otherwise circular use of the ordinary strong-rank lemma.

With f=t+1>=2 and c>2R, V=f²(cT-R)-c>1, so bN=2(1-Q)(n+V) is nonzero. N=0 then permits the rational definitions i*=AN/(d bN), u*=n-i*. They satisfy d i*²=Q and h(u*)=0. Adjacent-Pell saturation gives integral y*=V+u*, then integral i*; absolute values recover positive i and y. The ordinary strong-rank lemma is applicable with the already established large-c hypothesis. It supplies c²|f²-1, needed for V=-R modulo c, as well as c|m and m>2p. The signed-index lemma now gives p=R, after which the exact first-index identification and outer native coordinates follow.

The soundness endpoint is the ordinary source kernel, not a claim that i/Delta must be integral. The manuscript and materialization make this distinction correctly. Conversely canonical normalized witnesses are converted by i_ordinary=Delta i_normalized, and n=i_ordinary+(y-V)>0. The exact identity checked independently is

    N at Q=d i² = d² h(n-i)h(n+i).

Since J=6j+1 is odd and beta is odd, q is even; A0,A1 are squares modulo 4. N is also a square modulo 4 because bN is even. All three factors in the unit-product finalizer must individually be +1: a factor -1 would correspond to residual -2, which is excluded. Thus the finalizer is sound for three, not just two, residuals.

The universal upper degrees are also transparent. In N, deg d=8, deg Q=6, deg V=6, and the unique degree-13 term of h(n) is -2QVn. Therefore AN has degree 21, while d bN²Q has degree 38. This gives degree N=42. The already established carrier cancellations give degrees 15 and 13. The top forms yield the coefficient 64(6beta)^18 at j^18 F² eta^11 X^8 Y^19 t^8 n² gamma alpha, nonzero on the actual tuple. Hence the total degree 70 is exact.

The producer has now retained `positive/interfaces/weighted_carrier.tex`, `three_root_norm.md`, `package61_report.tex`, `ORDINARY_KERNEL.md` and the incoming manuscript. The earlier packaging recommendation has therefore been addressed for the reviewed source interfaces.
