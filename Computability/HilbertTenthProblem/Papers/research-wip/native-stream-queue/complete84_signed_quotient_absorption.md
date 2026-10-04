# Fixed polynomial absorption of the auxiliary quotient has finite input projection

Fix any valid inherited compiler-numeral slice of the actual complete84 polynomial. Let E93 consist of its 70 computed registers independent of `auxiliary_quotient` T and `y_aux`, together with all 23 supplied ports other than T,y. For every fixed integer polynomial G in those 93 named values, the literal substitution T=G(E93), with all other supplied witnesses positive, has finite ordinary-positive-input projection. This includes signed G and its zero-value sector.

The proof first allows T to be any integer and recovers the main index and the exterior bounds directly. It never invokes the positive-T parent theorem on a signed tuple. It does **not** assert unchanged full native/compiler equivalence, the old R=3 mod4 conclusion, or a positive-coordinate map restoring T. No generic G compiler, arithmetic saving, new complete circuit, or global minimum is claimed. The unchanged84 source is authenticated as evidence.

## 1. Actual equations and finite-input theorem

Use the complete84 meanings

    a=Y(X+1), A0=a+2, Delta=A0²−1, H=4a+3,
    X=wq, Y=sq³, E0=XY, k=eta+zeta, c=kY+eta,
    D=X+ac+(rho+sigma)H, gamma=rho+sigma,
    R=r_lhs, T=auxiliary_quotient, y=y_aux,
    S=Delta*i*c², V=c(Tf−1)−Rf².

Here T is not `transport_quotient`. The literal auxiliary and strong factors are

    Na=S²V²−(S²−1)y²,
    Ns_scaled=Delta*f²−S².

The full polynomial is P5*Na*Ns_scaled−Delta, with the same five other factors P5 as in the current source. Its all-ring factorization by Delta converts every zero under consideration into a product of seven integer units. This factorization remains valid for signed T; Delta>1 follows from the other positive supplied ports before any zero equation.

Let E93 be exactly the ordinate-absorption interface: the 70 actual computed registers independent of T,y, and the 23 supplied ports other than T,y. For fixed G in Z[E93], set

    t=deg G, L=max(1,sum of absolute coefficients of G),
    B_G=3t+ceil(log_2 L)+3.

Take t=0,L=1 for G identically zero. Every positive zero after the literal substitution T=G(E93) satisfies

    G(E93)!=0,             2d*x+b<R<=B_G.

Thus this substitution has finite ordinary-positive-input projection even if G takes negative values. Coefficients and degree of G are fixed on the compiler slice. The argument does not price an implementation of G or address substitutions depending on T or y.

## 2. Recovering p=R without positive auxiliary quotients

The normalized85 proof's unit-sign exclusions do not use T>0. Since Delta is0 or3 modulo4, the main, input and normalized strong norms cannot equal−1. Since S² is0 or1 modulo4, Na is congruent to y² or V² and likewise cannot equal−1, regardless of V's sign. For the first norm put U=XY²>1. A hypothetical positive solution tau²−U(U+1)k²=−1 satisfies Uk<tau<(U+1/2)k. The Pell transformation gives the smaller positive coefficient k'=(2U+1)k−2tau and first coordinate tau'=(2U+1)tau−2U(U+1)k; replacing tau' by its nonzero absolute value preserves the negative norm and contradicts minimality of k. Thus all five norms are+1. The index and transport factors remain units with a common sign epsilon in {−1,1}.

The same transport/slack bootstrap gives C>=0: the literal transport factor is (Kconstant+w)C+1−F−(transport_quotient−1)(q−1), whose last terms are nonpositive. Since Kconstant+w>=2, C<=−1 would make this unit at most−2. Thus the original positive slacks give F+Z<q and |W|<q. The actual shifted-mask packing bounds then give

    q>=B>=16, R>3q+1, R+2<q⁴<=E0<a.

Its proof uses the positive *transport* quotient, which has not been changed. The first and main norms classify

    tau=chi_P(n), k=2psi_P(n), P=2XY²+1,
    D=chi_A0(p), c=psi_A0(p),
    2n=R+epsilon modulo E0,
    p>n>=(R−1)/2>=24.

The unchanged ratio c>kY, together with the index unit and h>=1, gives c>2R. Pell growth gives c>A0*Delta² and c>2p. These precede any auxiliary sign argument.

The normalized strong equation is

    f²−Delta*(i*c²)²=1.

Its positive solutions at parameter A0 have an index m>=1 with

    f=chi_A0(m), psi_A0(m)=i*c².

The Pell addition identities and Euclidean algorithm give strong divisibility

    gcd(psi_A0(r),psi_A0(s))=psi_A0(gcd(r,s)).

Since c=psi_A0(p)>1 divides psi_A0(m), strict growth implies p|m. Write m=p*j. Expanding (D+c*sqrt(Delta))^j gives

    psi_A0(p*j)/c = j*D^(j−1) modulo c.

The left side is divisible by c, while gcd(D,c)=1. Hence c|j, and in fact p*c|m. In particular c|m and m>=p*c>2p. This is the direct normalized-rank argument of the pinned normalized85 mathematical review, Section4. It uses neither an auxiliary sign nor an old positive-parent zero. The larger c>A0*Delta² bound is available above but unnecessary for this direct route.

Now Na=1 and y>0 give a positive odd index ell=2v+1 with

    |SV|=chi_S(ell), y=psi_S(ell),
    V=e*C_v(S²), e in {−1,1},
    C_v(0)=(−1)^v*ell,
    C_v(−Delta)=(−1)^v*psi_A0(ell).

The sign e is retained. The two literal congruences, valid for every integer T, are

    V=−c modulo f,             V=−R modulo c.

Since S²=−Delta modulo f, squaring the first congruence and using the Pell doubling identity gives

    chi_A0(2ell)=chi_A0(2p) modulo chi_A0(m).

Here is the needed step-down directly. Reduce ell to ±z+j*m with 0<=2z<=m. The Pell pair at 2m is (−1,0) modulo f, so the displayed congruence compares ±chi_A0(2z) with chi_A0(2p). If 2z=m, the former is zero modulo f while 0<chi_A0(2p)<f. Otherwise both positive representatives are below f/(2A0−1), since their indices are at most m−1 and chi_A0(m)>(2A0−1)chi_A0(m−1). Their sum is below f. A negative congruence is therefore impossible; a positive congruence forces equality and z=p by strict growth. Thus ell=±p modulo m, hence modulo c. Since c divides S, the second congruence gives

    e*(−1)^v*ell=−R modulo c.

Consequently R=±p modulo c. Both R and p are positive and strictly below c/2, so p=R. No positivity of V, or of the old restored o,j, is used.

Finally write 2n=R+epsilon+zE0, z>=0. If z>=1 then E0>R+2 contradicts n<p=R. Hence 2n=R+epsilon. The epsilon=−1 branch gives p=2n+1 and contradicts c<k(Y+1) by the main/first ratio comparison in the normalized85 mathematical review, Section6. Explicitly, 2A0²−1>P and A0>Y+1 give psi_A0(2n)=2A0*psi_(2A0²−1)(n)>=A0*k and c=psi_A0(2n+1)>k(Y+1). Thus the index and transport units are both +1. This uses the individual equations, not a full positive-parent zero.

## 3. The signed parity caveat is real

The historical fixed-minus parity argument assumes a positive auxiliary root. Retaining e=sign(V) in that argument instead produces, on its odd-index hypotheses,

    e*(−1)^((R−1)/2)=−1.

Thus e=−1 can correspond to the opposite R=1 mod4 branch. This theorem does not claim a genuine full zero on that branch, but it cannot import the old R=3 mod4 conclusion merely from the signed step-down above. In particular the positive-T parent theorem cannot be invoked by leaving a negative T, or negative restored o,j, unchanged.

The finite-input argument below does not need either residue class, X=2^R, the exact half-binomial Y, the canonical input index v_input=u, or accepted-computation soundness.

## 4. Direct bounds for all 93 exterior values

From p=R>=3 and the main Pell equation alone,

    c>=psi_A0(3)=4A0²−1,
    a²<c/4, Delta,H<c, D<A0*c<c².

The main root definition gives

    0<gamma*H=D−ac−X<2c,
    0<rho,sigma<gamma<c.

The input quantities still have their literal meanings

    u=2d*x+b, kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H.

Outer positivity gives u<q+b<2q<R. Since kappa>=1 and a>q, mu>a−q>0. Its positive norm therefore classifies mu=chi_A0(j), kappa=psi_A0(j). The sequence

    E_j=chi_A0(j)−a*psi_A0(j)

is strictly increasing: E_0=1, E_1=2, and E_j=2psi_A0(j)−psi_A0(j−1) for j>=1, so E_(j+1)−E_j=(4A0−3)psi_A0(j)−psi_A0(j−1)>0. Since W<q<=X and rho<gamma,

    E_j=W+rho*H<X+gamma*H=E_R,

so j<R. Consequently kappa<c, mu<D and delta<c. This is enough; identifying j with u is unnecessary.

The two input bounds that might otherwise depend on W>0 follow directly:

    W+a*kappa>a−q>0,
    W+rho*H>H−q>0.

Thus `exponent_partial=W+a*kappa`, `modulus_multiple=rho*H`, and `difference_multiple=a*kappa` are all positive and below mu. The other input producers are bounded exactly as in the exterior table: kappa<c, delta*Delta=kappa−u<c, mu²<D²<c⁴, and Delta*kappa²=mu²−1<c⁴.

For completeness, the following table covers every one of the old 64 computed values. Source register names are literal. Put U=XY². Rows sharing an estimate are listed together; the fresh receipt attaches each name to its exact four-entry instruction, mathematical value and bound. No register is omitted from the partition.

| Literal source registers | Value and signed-T-zero bound |
|---|---|
| norm_first,norm_main,norm_pair,norm_input,norm_triple,norm_index,norm_transport | All equal1. |
| tau_square | tau²=k²U(U+1)+1<c⁴. |
| R10b,ksn2,R10a,hpm1 | k<c, kY<c, c, hE0=k−R−1<c. |
| first_root_base,first_next,first_product | kU<c²/4; k(U+1)<c²/2; their product<c⁴/8. |
| cam2,D1,gam,R14 | ac,D−gammaH,gammaH,D are positive and at most D<c². |
| gamma_sum,a4,a4m5 | gamma<c; 4a<H<c; H<c. |
| L15,a_square,A,c2,Ac2 | D²<c⁴; a²<c/4; Delta<c; c²<c⁴; Delta*c²<c³. |
| index_product,index_rhs | delta*Delta=kappa−u<c; kappa<c. |
| difference_multiple,exponent_partial,modulus_multiple,exponent_rhs | a*kappa, W+a*kappa, rhoH,mu are positive and at most mu<D<c². |
| mu2,kappa2,scaled_kappa2 | mu²<c⁴; kappa²<c²; Delta*kappa²=mu²−1<c⁴. |
| repunit,q,Lbig,n2,wn2,sn2,UM,R12 | q−1,q,q²,q³,X,Y,E0,a, all at most a<c. |
| q_minus_F,q_minus_FZ,C_after_alpha,scaled_t,marked_rhs | q−F,q−F−Z,C+2dx,2dx,C, all positive and below q. |
| W,odd_index,index_difference | |W|<q; u<2q<R; k−hE0=R+1<a. |
| gap_product,gap,Lm1,rproduct | (q−1)(q−F)<q²; gap=q(q−F)−Z is positive and <q²; q²−1<q²; rproduct<q⁴<=E0<a. |
| qMF,mask_factor,mask,r_lhs | qMF<2q²; MC+qMF<3q²; mask<3q³<a; R<a. |
| kinner,innerC,transport_partial,local_rhs | Kconstant+w<q²+X<a; innerC<q³+X<a; transport_partial<q³+X+q<a; local_rhs=transport_partial−1<a. |

The estimates use no additional auxiliary premise:

* First/root group: k<c, XY²<a²<c/4, and tau²=XY²(XY²+1)k²+1<c⁴.
* Main group: c²<c³, Delta*c²<c³, D²<c⁴, and all positive summands of D are below D.
* Packing group: the original positive slacks give F,Z,alpha,2dx,C<q and |W|<q. Its gap and shifted-mask bounds give the listed producers below q⁴ or 3q³, hence below a where required.
* Fixed transport recipe: Kconstant=DC+B*DR<B²<=q², with actual shifted MF<2(B−1), and MC<B−1. Since w=X/q, X>=q, Y>=q³, the bounds `Kconstant+w<q²+X<a`, `innerC<q³+X<a` and `transport_partial<q³+X+q<a` follow. The retained +1 transport equation bounds its positive quotient by a. Nt=1 also gives C>0, because `(Kconstant+w)C=F+(transport_quotient−1)(q−1)>0`.
* Supplied exterior witnesses and fixed numerals are covered by the same inequalities, h*E0=k−R−1, and 2d<B<=q. In particular x<q<c.

For the fixed-numeral bound specifically, complete78 Section2 gives DC,DR as positive separated coefficient strings with all exponents below the cell width and every coefficient below the inner radix. Complete76 Section1 enlarges the width parameter L past g+Emax when adding the optional high monomial. Modified75 Sections1 and4 strengthen the coefficient bound and retain that layout. Thus the corrected DC,DR still satisfy 0<DC,DR<B, and Kconstant=DC+B*DR<B² before any history or q-power typing. The modified75 export is the shifted MF_source=MF_native+B−1, with 0<MF_native<B−1; this is the source convention used in the table, not the unshifted historical value. These exact texts are authenticated dependencies of the helper.

The seven units, eight first/root values, twelve main values, nine input values and twenty-eight remaining values total64. The source census and exact row guards check this complete partition.

The 21 old supplied values are all covered separately:

| Supplied values | Bound |
|---|---|
| Jrep,F,alpha,Z | Each <q<c. |
| eta,zeta,h | eta,zeta<k<c; hE0=k−R−1<c and E0>=1 give h<c. |
| s,w,tau_root | s<Y<a<c, w<X<a<c, tau_root²=tau_square<c⁴. |
| delta,rho,sigma | Each <c by the direct input/main bounds. |
| transport_quotient | Its positive product with q−1 is local_rhs<a, so the quotient <a. |
| x | 2dx<q implies x<q<c. |
| Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF | B−1<q; Kconstant<q²<a; 2d<B<=q; b<=d; MC<B−1<q; shifted MF<2q<c. |

The shifted MF bound is below c because c>kY>=2Y>=2q³. These are direct signed-domain bounds, not bounds obtained by invoking a positive-parent theorem.

The unchanged normalized strong equation gives

    f²=1+Delta*i²*c⁴, f>i, f>2c, S>f.

Hence c⁴<f². Exactly the six additional computed values in the ordinate interface are f², Rf², S, S², Delta*f² and Delta. Since R,Delta<c<f, each is below f³. The additional supplied values i,f are also bounded by f³. Therefore the signed-domain bound is

    |E_j|<=f³ for all 93 interface values.

## 5. Growth of |T| and the finite cutoff

With c=psi_A0(R), the odd auxiliary-index congruence modulo f gives

    ±psi_A0(ell)=−c modulo f.

If ell<R, both c−psi_A0(ell) and c+psi_A0(ell) lie strictly between zero and 2c<f, a contradiction. Thus ell>=R. The chi recurrence gives chi_S(ell)>S^ell for ell>=2, so

    |V|=chi_S(ell)/S>f^(R−1).

On the other hand, integrality gives c,R<=f−1, so

    c+Rf² <= (f−1)+(f−1)f² < f³, f>=2.

Together with cf<f², the literal T equation therefore gives, including T=0,

    |V|<=cf|T|+c+Rf²<f²|T|+f³.

If |T|<=f^(R−4), then R>=5 and f>=2 give

    |V|<f^(R−2)+f³<=2f^(R−2)<=f^(R−1),

a contradiction. Therefore

    |T|>f^(R−4)>0.

This excludes T=0 after the signed rank/bound argument; it is not an off-zero divisibility exclusion. Negative T need not be excluded separately.

For T=G(E93), the interface bounds give |T|<=L*f^(3t). If R>=3t+ceil(log_2 L)+4, then f^(R−4)>=L*f^(3t), contradicting the strict lower bound. This proves the cutoff in Section1. For integer L>=1, the logarithmic ceiling is `(L−1).bit_length()`.

## 6. Source evidence and scope

The fresh helper authenticates the actual complete84 trio, the exterior and ordinate trios and their existing proof dependencies as inert bytes. Its full literal source trace checks all84 definitions against the source-specific mathematical interface. It recomputes both dependency partitions, all64+21 and70+23 named values, and the sole T consumer. The receipt saves the unchanged actual source and attaches every bound to its actual producer or supplied port.

The all-ring check processes every row, cutting only computed values already proved independent of all four auxiliary witnesses. It expands norm_pair, norm_triple, c2, Ac2, every auxiliary producer, all final products and the output subtraction. It verifies exactly

    F84=Delta*(P5*Na*(f²−Delta*i²*c⁴)−1).

This is an authenticated full-source factorization, not a test on sampled tuples. T remains a formal signed indeterminate throughout; no positive restoration or evenness in T is asserted. The independently formed expression for V and its two normalized congruences are checked symbolically at the same source boundaries.

Finite arithmetic components corroborate normalized-rank divisibility, the odd-index polynomial identities and parity, signed chi step-down, both signs in the local index recovery, strict growth and the coefficient-norm cutoff. They are not histories or full polynomial zeros and do not substitute for the quantified proof in Sections2–5. The full signed-domain inequalities are the mathematical argument above, tied to a complete literal census; they are not inferred from finite sampling.

No generic G circuit or count is emitted. The complete84 polynomial, fixed recipe and supplied interface are unchanged in the authenticated evidence. The original84 universal bound is unchanged. No negative-T history, rejected-input witness, or full signed-T compiler transfer is claimed.

The exact source calculation has17 terms on each side of the Delta-normalization identity. The complete receipt includes all84 unchanged instructions, all25 supplied ports and their liveness, the exact64+21 and70+23 censuses, all individual literal bound records, and both signed congruence identities. The source remains84=47M+37A; this is an authenticated parent ledger, not a new operation bound.

Finite evidence comprises14 odd-index coefficient arrays and98 evaluations of their exact identities;175 normalized-rank congruence cases;1,792 successful signed step-down cases; six explicitly limited main/strong/auxiliary components with both signs of V and T; seven projected-input sequences and their difference identities;300 strict chi-growth checks;70 two-sign smaller-index exclusions;38 integer constant-term bounds; and234 degree/coefficient-norm cutoff cases at four bases. The six components use small R=3 or5, so they do not satisfy the actual full-source lower bound on R and are expressly not full zeros or histories.

The helper imports only the standard library. All predecessors are read as bytes or strict JSON, never imported or executed. Duplicate keys, floating-point numbers and nonfinite constants are rejected. Explicit checks survive optimized Python; canonical JSON comparison distinguishes types. The generated receipt binds the exact helper bytes. Output generation uses exclusive creation; `--expect` performs an exact fresh replay.

The writer, fresh normal replay and fresh `python3 -O` replay all passed, with replay working directory `/` and absolute helper/root/receipt paths. No repository or predecessor was changed.

Use the installed packet with:

```sh
python3 /absolute/path/complete84_signed_quotient_absorption.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/complete84_signed_quotient_absorption.json
python3 -O /absolute/path/complete84_signed_quotient_absorption.py \
  --root /absolute/path/native-stream-queue \
  --expect /absolute/path/complete84_signed_quotient_absorption.json
```

The22 authenticated files, including transitive context pins inherited from the exterior and ordinate receipts, are:

| File relative to the native-stream-queue directory | SHA-256 |
|---|---|
| ../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md | `47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b` |
| ../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md | `75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87` |
| ../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md | `b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39` |
| complete75_half_binomial_compiler.md | `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117` |
| complete83_auxiliary_product_collapse.md | `a224d930f94a3888b4208147dc54d90127999342313120a5239e40408e948d50` |
| complete83_computed_gamma_obstruction.md | `02b55f39ea585c76563897fcb0040f75d4257c410ffc3c27d5f3686822632d04` |
| complete83_direct_gamma_witness_obstruction.md | `c1f7a146ba85020ea1ed436e64de9a9163f9c5c7ac8d013d46d719ccef92d3f4` |
| complete83_free_coefficient_scout.md | `867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31` |
| complete83_input_quotient_dichotomy.md | `46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505` |
| complete84_auxiliary_ordinate_absorption.json | `8101345c3c6588539fe56f340322ba573e66ce66b978db7da8154781c23547f8` |
| complete84_auxiliary_ordinate_absorption.md | `9cc0fc5f3d9f72dd3fc150c1253cb038fef1eb0666dc72b1096ed86c85481b53` |
| complete84_auxiliary_ordinate_absorption.py | `9d8ea463330b31dea1af8187784981b576c932a3799ca45a5dabfe2ea0bc2c94` |
| complete84_exterior_auxiliary_absorption.json | `ec0b2a298d4382867ca0d638e3b52b18be3ad38a64ea7c4efb96d1ad985d692b` |
| complete84_exterior_auxiliary_absorption.md | `69f8e40bd44dca5bcb2f0f292a2ad842fff5a41b2014007f3f986176cd7bd8de` |
| complete84_exterior_auxiliary_absorption.py | `46e42d8947c1e5cbed62a4473fa83d96115a80b334656ea45ad1f31796bde0a9` |
| complete84_scaled_strong_output.json | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| complete84_scaled_strong_output.md | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| complete84_scaled_strong_output.py | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| complete85_auxiliary_bezout_projection.md | `d8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b` |
| review_complete84_exterior_auxiliary_absorption.md | `df47a59713fca80a9a059bda9b2a5956774d67ebcd60b5ce99b54096414eee3a` |
| review_complete84_exterior_auxiliary_absorption_math.md | `bdf25d1eb78850aa434ead4cf5fb2b62c2c8318413c55c9bcd73d6ca55d0b0d4` |
| review_complete85_auxiliary_bezout_math.md | `77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d` |

Helper SHA-256: `cc5ed27ffcffefbd76b85ea36efa05637e06a0eb7fa221c6d9e31af9ea4f9d5f`.

Receipt SHA-256: `c9522c55adb3e602c2d355cb98d4e313c5e258a66e93bf0bbca52d56fddd9a00`.

This packet develops the prior signed-quotient scout and its bounded Pascal challenge into a complete literal-source/proof artifact. Their parity warning is retained; no full signed-domain compiler theorem is inferred. Independent review of this new final packet is separate from those earlier conceptual checks.

