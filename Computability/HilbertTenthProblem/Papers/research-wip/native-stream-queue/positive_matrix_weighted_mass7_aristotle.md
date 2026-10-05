# Seven positive coordinates, three input operations and an exact dyadic mass

Root identified an inherited six-dimensional projective scalar-zero interface that is stronger for this purpose than the seven-dimensional Gram interface used by the recent positive8 packet. A fixed integral coordinate change and a weighted positive lift give **seven strictly positive integer state coordinates**, the same **3=2M+1A ordinary-input loader**, one terminal coordinate equality, and a fixed dyadic multiplier C for the total mass at every step. The alphabet is fixed independently of the program and ordinary input.

The lift has constant column sums and a fixed positive right eigenvector. It is not generally doubly stochastic after unweighted normalization. A valid eight-dimensional doubly stochastic construction is recorded separately below. Exact mass gives a word-independent height bound, but does not supply its own paid unbounded-duration certificate. We prove a conditional range-elimination interface and an all-size carry obstruction to omitting that condition. No complete fixed-arity history source, complete compiler count or universal gate improvement is claimed.

## 1. The inherited projective input and a fixed integral chart

The full group_projective_zero_mortality6.md was read inertly. Its Sections1--4 prove, over one fixed finite signed integral6-by-6 alphabet A_sigma, the following ordinary-input contract. For every recursively enumerable S_p, fixed positive program numerals alpha,gamma give

    tau=alpha*x+gamma,
    v6(x)=(1,tau,tau^2,1,tau,tau^2)^T,
    u6=(1,0,0,1,0,0),
    x in S_p iff exists a finite word w: u6 A_w v6(x)=0.       (1)

The actual recipe is alpha=12*2^(p+1), gamma=12*2^p+1. The positive ordinary input x varies, while p and the resulting numerals are fixed. In particular tau>=2; the valid recipe has tau>=37. The alphabet comes from a single effectively specified universal fibre-product subgroup. Its finite numerical matrix list and external embedding foundations are inherited, not newly transcribed or independently verified here.

The inherited argument uses both projective blocks. Its fixed subgroup congruences eliminate negative projective signs; the b-exponent and graph-group abelianization then remove the two stabilizer ambiguities. The scalar in(1) is a sum of two squares. This note preserves that exact two-block ordinary-input contract, not the weaker single-block test refuted in the source. Its fixed-word certificates and rank-one mortality generator are different interfaces and are not silently imported as a paid unbounded history.

Let Q have rows

    e1+e4, e2-e4, e3-e4, e4, e5-e4, e6-2e4.                 (2)

It is integral and unimodular. Explicitly, for y=Qz,

    z4=y4, z1=y1-y4, z2=y2+y4,
    z3=y3+y4, z5=y5+y4, z6=y6+2y4.                          (3)

Thus G_sigma=Q A_sigma Q^(-1) is a fixed finite integer alphabet. Set

    h=(1,1,1,1,1,2)^T, k=(h,1)^T,
    D=[I_6 | -h], E=[I_6;0].                                (4)

Here Dk=0, DE=I_6 and the sum of the seven entries of k is8. The supplied positive column is

    z(x)=(3,tau,tau^2,2,tau,tau^2,1)^T,
    Dz=(2,tau-1,tau^2-1,1,tau-1,tau^2-2)^T=Qv6(x).          (5)

All entries of z are positive. No positivity of arbitrary signed G-trajectories is assumed. The entire column is loaded by

    scaled=alpha*x; tau=scaled+gamma; tau2=tau*tau,            (6)

which is exactly3=2M+1A, with zero supplied auxiliary witnesses. Copies and fixed entries3,2,1 cost no arithmetic. Q is used to prepare a fixed alphabet, not applied by an uncharged variable matrix product. The first row of Q is u6 and h_1=1, so the desired terminal zero will be equality of coordinates1 and7.

## 2. The weighted positive integer lift

Write R=max_(sigma,i) sum_j |G_sigma[i,j]|. Choose a power of two kappa>28R, taking kappa=1 if R=0, and set C=8kappa. This is a finite fixed recipe independent of p and x. For each letter let

    c_sigma^T=1_6^T G_sigma,
    b_sigma^T=kappa*1_7^T-c_sigma^T D,
    L_sigma=E(8G_sigma)D+k b_sigma^T.                        (7)

All quantities in(7) are integers. To prove strict positivity, for j<=6 let c_j=sum_i G_ij; then |c_j|<=6R. For i<=6 the corresponding entries are

    L_ij=8G_ij+k_i(kappa-c_j).

The correction relative to k_i*kappa has absolute value at most8R+6k_i R<=14k_i R. The last column has

    L_i7=-8(Gh)_i+k_i(kappa+c^T h).

Since |(Gh)_i|<=2R and |c^T h|<=12R, its correction has absolute value at most16R+12k_i R<=28k_i R. The bottom row has no E-term and obeys the same weaker bounds. Consequently every entry satisfies L_ij>=k_i>=1. The strict inequality in kappa>28R, together with integrality, includes the unit margin. If R=0, the formula gives L=k1^T, again strictly positive.

The exact identities are

    D L_sigma=8G_sigma D,
    1_7^T L_sigma=C1_7^T,
    L_sigma k=Ck.                                           (8)

The first follows from DE=I and Dk=0. For the second, 1_7^T E(8G)D=8c^T D and (1_7^T k)b^T=8kappa1_7^T-8c^T D. For the third, Dk=0 and b^T k=kappa*(1_7^T k)=C.

For a word w=(sigma1,...,sigman), use L_w=L_sigman...L_sigma1, and the same order for G_w and A_w. Induction gives

    D L_w=8^n G_w D,
    (L_w z(x))_1-(L_w z(x))_7=8^n u6 A_w v6(x).              (9)

This includes the empty word. There is no division or supplied duration scalar in the operational equality test. Combining(1),(9) proves

    x in S_p iff some finite word w has
                   (L_w z(x))_1=(L_w z(x))_7.                (10)

Every actual intermediate state is a strictly positive integer vector, every letter is fixed before input/program vary, and the loader remains(6). The empty word is rejected, since its coordinate difference is2. The factor8^n rescales the inherited signed action; it preserves zero exactly but does not preserve its numerical value. This is not a full-operator mortality or group-inverse claim.

## 3. Exact mass and the correct normalization

Let H0=sum_i z_i=2tau^2+2tau+6. By the column identity in(8), every length-n word has

    sum_i (L_w z)_i=C^n H0.                                  (11)

Thus a single duration value U=C^n controls total mass, independently of the chosen letters. C is a fixed power of two. The mass C^n H0 need not itself be a power of two; the dyadic quantity is U. Positive integrality gives each coordinate at most C^n H0-6.

Let K=diag(k). The ratio-normalized matrices

    P_sigma=K^(-1)L_sigma K/C

are row stochastic by Lk=Ck. Moreover (P_sigma)_ij>=k_j/C. Subtracting the identical row (k_j/C)_j leaves a nonnegative matrix with row sum theta=1-8/C=1-1/kappa. For oscillation max-minus-min, every n>=1 satisfies

    osc(K^(-1) C^(-n) L_w z)<=theta^n osc(K^(-1)z).           (12)

The empty word is treated separately. If kappa=1 the ratio state becomes constant after one step. Otherwise0<theta<1. Along any infinite word the ratio minima increase and maxima decrease, and their difference tends to0. The conserved mass fixes their common limit: C^(-n)L_w z converges to k*H0/8. This statement does not replace exact finite equality.

**Review remark 1 (weighted stationarity is not double stochasticity).** A strengthened claim of common unweighted row sum C would be false. For G=I_6, choose kappa=32, so C=256. Formula(7) gives row sum225 at rows with k_i=1 and row sum442 at the row with k_i=2. Every column still sums to256, and Lk=256k. On the input(5), coordinate1 minus coordinate7 is2*8^n and never0, although its normalized value is2/32^n and tends to0. This is a literal algebraic boundary example, not a universal input instance. The exact endpoint and normalization conclusions above use precisely the proved identities.

## 4. The valid positive8 doubly stochastic intermediate

The preceding positive8/nine-loader packet supplies a signed7-dimensional alphabet G with its accepted scaled ordinary-input zero relation. For each letter G_sigma, write r_i=sum_j G_sigma,ij,c_j=sum_i G_sigma,ij,s=sum_ij G_sigma,ij, and suppress sigma in the displayed matrix entries below. Set the common bound R=max_(sigma,i) sum_j |G_sigma,ij|. Choose one fixed power of two kappa>15R for the whole alphabet, or1 if R=0, and C=8kappa. The following8-by-8 integer matrix is strictly positive:

    L_ij=8G_ij+kappa-c_j                 (i,j<=7),
    L_i8=kappa+s-8r_i                    (i<=7),
    L_8j=kappa-c_j                       (j<=7),
    L_88=kappa+s.                                            (13)

Indeed |c_j|,|s|<=7R and every displayed correction has absolute value at most15R. Direct summation gives both row and column sums C. With D8=[I_7|-1], D8L=8G D8. Thus L/C is genuinely doubly stochastic, has fixed dyadic normalization, and preserves the positive8/nine-loader equality predicate. Relative to that packet's signed G-action the scale is8^n; relative to its older Gram action the total signed conjugation scale is16^n. In all cases only zero acceptance is unchanged.

**Review remark 3 (one bound for the whole alphabet).** The preliminary draft wrote the shorthand R=max_i sum_j |G_ij| without explicitly taking the maximum over letters. Interpreting that as an independent choice for each letter would not prove a common C: G=0 could use kappa=1 and G=I_7 could use kappa=16, giving C=8 and128. The corrected statement takes one maximum over the entire finite alphabet before choosing kappa. Each letter formula was valid; the shared-normalization quantifier needed this clarification.

This intermediate uses eight coordinates and remains valid. A uniform-kernel seven-coordinate version obtained by taking M=7G and C=7kappa would have known fixed-base mass but not a dyadic C. The weighted construction(7) attains seven coordinates and dyadic mass by changing uniform row sums to the explicit eigenvector relation Lk=Ck. No prior frozen positive8 or fourteen-/nine-loader artifact is changed.

## 5. What mass can remove from a history certificate, conditionally

The full earlier group_four_register_canonical_history47.md already proves the relevant method: an independently certified height bound for the actual selected word allows a single scalar bound on packed history words to replace individual state-digit range predicates. That note leaves duration/height geometry, selector typing and selected-source products explicitly unpaid. The signed atomic matrix193 source instead includes four range lanes; its Sections3--5 use those bounds before recovering each matrix transition. The uniform-context source has eight range lanes in its preceding layout. Their numerical ledgers belong to those specific four-coordinate sources and do not apply to the present seven-coordinate alphabet.

Here is the exact specialization of the canonical method to(7). Suppose a later component certifies duration n>=1, base B, P=B^n, and

    B>C^n H0.                                                (14)

Supply positive history words H_i and one positive bound slack with sum_i H_i+slack=P. Each H_i then has canonical length-n base-B digits x_i(j) in[0,B). Assume that a separately paid selector interface chooses exactly one L-letter per cell and provides exact digitwise selected-source products of those canonical digits. Let V_i be the packed word whose jth coefficient is the i-th coordinate of L_sigma(j) x(j), before any base-B carrying. Enforce the seven recurrence comparisons

    B V_i=H_i+F_i P-z_i(x).                                  (15)

No separate state-digit range mask is needed under these hypotheses. To prove this, follow the selected word as an ordinary mathematical trajectory y(j), starting at z(x). Equations(11),(14) bound every coordinate of y(j), j<=n, strictly below B. The constant coefficient of(15) is z_i-x_i(0), strictly between-B and B; reduction modulo B forces x_i(0)=z_i. Once all earlier coordinates have been recovered, the next discrepancy is y_i(j)-x_i(j), again strictly between-B and B. Simultaneous induction modulo successive powers of B forces every history digit. The remaining top coefficient forces F_i=y_i(n), without any prior endpoint range assumption.

Conversely, the genuine history has positive initial digits, and sum_i y_i(j)=C^j H0<B for j<n. Hence sum_i H_i<P and the bound slack is positive. Exact selected-source words and recurrence telescoping complete this conditional converse. The one scalar history bound costs seven additions for seven words and their slack, plus its comparison; this is only its local ledger, not the full history cost.

Thus(11) provides a word-independent numerical condition sufficient for the existing range-elimination proof. It does not pay(14), P=B^n, selectors, digitwise multiplication, recurrence coefficients or chronology. The previous constant-row-sum positive8 lift already supplied a maximum-coordinate growth estimate C^n max_i z_i, so double stochasticity alone is not a newly proved unconditional range saving. The new useful equality is the exact aggregate mass and its known dependence on length; its arithmetic certification still matters.

## 6. An all-size obstruction to self-certifying mass profiles

**Review remark 2 (a packed mass equation is not a height certificate).** Root supplied a dyadic numerical carry example; the following symbolic family shows the same failure at every integer C>=2, including every C allowed by(7). Put

    B=2C^2, n=2, P=B^2,
    M0=2C+1, H=M0+B*C, Mend=C^2+1.                            (16)

Then

    (BC-1)H=P*Mend-M0.                                       (17)

To check(17), note CM0=B+C, so the intermediate coefficient CM0-C is exactly B; its carry becomes one extra unit in the top coefficient. Every proposed mass value M0,C,Mend lies strictly between0 and B. Also0<H<P/C, since H=2C^3+2C+1<4C^3=P/C. When C is dyadic, so are B and P. Nevertheless the actual first update is CM0=B+C, not the proposed next digit C, and actual final mass C^2 M0 differs from Mend. Thus even positive canonical digits, a stronger-than-usual global packed bound, dyadic base and the exact aggregate recurrence do not establish the intended mass trajectory.

For C=8 this is B=128,P=16384,M0=17,H=1041,Mend=65; both sides of(17) equal1064943. These are scalar mass-interface counterexamples. They are not asserted to extend to a full selected-matrix/native certificate or to the special initial mass polynomial in(11). Their scope refutes deriving(14), or coefficientwise mass correctness, solely from(17) and the displayed size conditions. A different coupling to the actual input or a paid duration relation could exclude them; none is supplied for free here.

If exact selected-source products partition each canonical history digit, column sums make the sum of seven vector recurrence residuals equal the corresponding aggregate mass residual. Replacing one vector comparison by a proved mass comparison is then an algebraic reformulation. It does not delete a comparison unless the needed mass equation and endpoint identity have already been independently paid. Counterexample(16) also explains why assuming that equation carries no semantic burden would be circular.

**Open question 1 (credited paid-history task).** Root requested a concrete advantage for unbounded arithmetic compilation. The present result improves the fixed positive endpoint substrate to dimension7 with three input operations and gives exact dyadic mass. The next required task is an explicit paid coupling of duration and height, or another no-carry mechanism, together with selectors and recurrence checks. No such complete source is emitted here, and no global lower bound or impossibility of that future construction is asserted.

## 7. Provenance and execution scope

Root proposed the projective6 reuse, both lift constructions and the scalar carry example. The author independently read the full projective6 proof, derived the inverse and entry bounds, checked the ordinary-input and fixed-alphabet quantifiers, generalized the carry example to all C>=2, and compared the actual prior canonical/range interfaces. Exact immutable source bytes and declared read spans are bound in the accompanying metadata. The earlier external effective embedding and unmaterialized universal alphabet remain explicitly inherited.

No supplied, archived, committed, predecessor or frozen helper was executed or imported. No saved source array was evaluated, no degree propagation or scientific sampling was performed, and no build was run. Only inert proof reading and fresh byte/metadata work are used. All new files are in/tmp; repository files, Git and prior frozen artifacts are untouched.
