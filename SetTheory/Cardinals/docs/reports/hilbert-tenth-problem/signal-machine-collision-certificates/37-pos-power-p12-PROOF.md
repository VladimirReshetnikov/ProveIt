# Twelve positive leaves for POWER by two rational recoveries

4 October 2026. A separate arithmetic continuation. The frozen directory
`/workspace/shared/positive-power22-reduction-20261004` is unchanged. This is a new formula, not a retroactive recount of an earlier formula or numbered report.

## 1. Statement and domains

Let b be an integer with b>=2, and let C,o be positive integers. The semantic exponent is C-1. The five residuals below give an explicit integer polynomial P_12 such that

    o=b^(C-1) iff there exist eleven positive auxiliary integers with P_12=0.

The module has twelve positive leaves when its output o is included. Its index C and a separately supplied base are excluded from that twelve. For an unrestricted positive base input B, put b=B+1; B is an additional external input. All counts use ordinary positive integers, never rational witnesses. Rational expressions appear only in the proof of reconstruction.

The sum of five squares has exact joint total degree 20 for every fixed integer base b>=2, including b=2, and exact degree 24 for an independent base b or the positive affine parameterization b=B+1. C is an independent positive input or the independently counted shifted counter in the composition. No degree statement for arbitrary nonlinear base/index substitutions is asserted.

The all-exponent equivalence imports the precise constructive Pell theorem pair pinned in Section 7. The elimination and all sign/domain recoveries are proved here. Finite evidence is supporting evidence, not a replacement for the all-input proof or that theorem dependency.

## 2. Every positive leaf and every residual

Use the six directly positive leaves

    o, g, q_b, q_v, J, q_alpha,

and six natural aliases

    d_wb, d_wC, d_yC, q_sigma, q_tau, q_r.

Each natural alias z is the expression z_plus-1 in its own distinct positive adapter leaf z_plus. Thus the count is 6+6=12, including o. In particular q_alpha is directly positive, not an adapter for a natural quotient. No leaf u or alpha_plus remains.

Define integer polynomial expressions, not new variables,

    w=b+d_wb,                 y=C+d_yC,
    beta=1+4y q_b,            v=y^2 q_v,
    t=C+4y q_tau,             M=b o+J,
    d=2b,                    A=M+b^2+1,
    X=y(A-db)+db o+dM q_r,
    U=d beta-A,
    S=q_alpha X+U q_sigma.                                    (1)

The complete residual list is

    H_1=X^2-d^2-(A^2-d^2)y^2,
    H_2=U^2-d^2 q_alpha^2-(A^2-d^2)q_alpha^2 v^2,
    H_3=S^2-d^2 q_alpha^2-d^2 q_alpha^2(beta^2-1)t^2,
    H_4=w-C-d_wC,
    H_5=A^2-d^2-d^2((w+1)^2-1)(wg)^2.                        (2)

The promised polynomial is literally

    P_12=sum_(i=1)^5 H_i^2,                                   (3)

with every alias in (1) and every positive-adapter shift expanded. There are no other constraints, divisions, congruence residuals, concealed variables, or power predicates in (3). H_1 uses the denominator d alone; no unnecessary q_alpha^2 factor is included. H_2 and H_3 clear denominators by d^2 q_alpha^2.

### Fixed base two

For b=2 use

    w=2+d_wb, y=C+d_yC, beta=1+4y q_b,
    M=2o+J, A=2o+J+5,
    X=y(A-8)+8o+4M q_r,
    U=4beta-A, S=q_alpha X+U q_sigma,
    v=y^2q_v, t=C+4y q_tau.

The five residuals are exactly

    X^2-16-(A^2-16)y^2,
    U^2-16q_alpha^2-(A^2-16)q_alpha^2(y^2q_v)^2,
    S^2-16q_alpha^2-16q_alpha^2(beta^2-1)(C+4y q_tau)^2,
    w-C-d_wC,
    A^2-16-16((w+1)^2-1)(wg)^2.                              (4)

## 3. Reconstruction: no rational or negative solutions are admitted

Suppose all twelve leaves are positive integers and all five H_i vanish. Then

    w>=b>=2, y>=C>=1, beta>=5, v=y^2q_v>=y>=1,
    t>=C>=1, M=bo+J>bo>0, d=2b>0, A>0, q_alpha>=1.           (5)

For the proof only, set alpha=A/d in Q. Dividing H_5=0 by d^2 gives

    alpha^2=1+((w+1)^2-1)(wg)^2.                              (6)

The right side is an integer, and it exceeds w^2 since w>=2 and g>=1. A rational number whose square is an integer is an integer: writing it p/q in lowest terms with q>0, q^2 divides p^2, and coprimality forces q=1. Thus alpha is a positive integer and alpha>w>=b. Its restored positive leaf alpha_plus=alpha-1 is therefore positive. Also A=d alpha gives

    M=2b alpha-b^2-1.                                        (7)

Next set u=U/(d q_alpha) in Q, which is well defined by (5). Dividing H_2=0 by d^2 q_alpha^2 gives

    u^2=1+(alpha^2-1)v^2.                                    (8)

This right side is an integer, so the same rational-square lemma proves u is an integer. Since v>=1 and alpha>=2, (8) implies u^2>=alpha^2, hence |u|>=alpha>0. The definition of U gives

    beta=alpha+u q_alpha.                                    (9)

If u were negative, it would be <=-alpha, so beta<=alpha-alpha q_alpha<=0, contradicting beta>=5. The value u=0 is already excluded by |u|>=alpha. Consequently u>0. Reconstruction needs the integrality of u; the sign proof specifically uses the strict positive-integer domain q_alpha>=1. Merely assuming a nonzero rational q_alpha would not justify the same bound.

In the 13-leaf predecessor, its retained positive integer u and its congruence residual also gave alpha=beta-u q_alpha as an integer directly. Its rational-square argument for alpha was valid but not necessary there. Eliminating u removes that shortcut; the auxiliary Pell norm (6) now supplies the needed independent integer recovery.

Define integers

    x=y(alpha-b)+bo+M q_r,
    s=x+u q_sigma.                                           (10)

All natural aliases are nonnegative, alpha>b, and bo>0, so x>0 and s>0. The identities X=dx and S=d q_alpha s follow from (1), (9), and (10). Dividing H_1 by d^2 and H_3 by d^2 q_alpha^2 recovers

    x^2=1+(alpha^2-1)y^2,
    s^2=1+(beta^2-1)t^2.                                     (11)

For completeness, the restored 22-leaf module satisfies every one of its fifteen equations:

    x^2=1+(alpha^2-1)y^2,
    u^2=1+(alpha^2-1)v^2,
    s^2=1+(beta^2-1)t^2,
    beta=1+4y q_b,
    beta=alpha+u q_alpha,
    v=y^2 q_v,
    s=x+u q_sigma,
    t=C+4y q_tau,
    y=C+d_yC,
    w=b+d_wb,
    w=C+d_wC,
    M=bo+J,
    alpha^2=1+((w+1)^2-1)(wg)^2,
    2alpha b=M+(b^2+1),
    x=y(alpha-b)+bo+M q_r.                                  (12)

Equations (8), (11), H_4, and (6) supply the nondefinitional equalities, and all others are identities. The restored w,M,x,y,u,v,s,t are positive. beta_plus=beta-1 is positive; alpha_plus was checked above. In this old 22-leaf domain the natural q_alpha uses positive adapter q_alpha+1. All six retained natural aliases also use their positive adapters, including when their value is zero. Thus no eliminated positive-domain requirement is lost.

The pinned old-module theorem, detailed in Section 7, now gives o=b^(C-1). This proves soundness.

## 4. Completeness, exact image, and the non-bijection qualification

Start with any 13-leaf solution from `dependencies/elimination_PROOF.md`, Section 3. Equivalently reconstruct its 22-leaf solution (12). Write its natural quotient as q_alpha,0>=0, and its parameter as beta_0. Its remaining data alpha,w,M,g,x,y,u,v,q_v,J and the three natural slacks may be held fixed.

The old-module theorem yields the Pell coordinate identity

    (x,y)=(X_C(alpha),Y_C(alpha)),

where these are integer polynomials characterized by

    X_0(z)=1, Y_0(z)=0,
    X_(n+1)(z)=zX_n(z)+(z^2-1)Y_n(z),
    Y_(n+1)(z)=X_n(z)+zY_n(z).                               (13)

Induction proves the Pell norm identity, positivity at z>=2,n>=1, and X_n(1)=1,Y_n(1)=n. Integer polynomials preserve argument congruences. For every integer k>=1, define

    beta_k=beta_0+4yu k,
    s_k=X_C(beta_k), t_k=Y_C(beta_k),
    q_b,k=q_b,0+u k,
    q_alpha,k=q_alpha,0+4y k.                                (14)

Then q_b,k>0 and, crucially, q_alpha,k>0 even if q_alpha,0=0. Also beta_k is congruent to alpha modulo u and to 1 modulo 4y. Hence s_k is congruent to x modulo u, and t_k to C modulo 4y. Define integer quotients

    q_sigma,k=(s_k-x)/u, q_tau,k=(t_k-C)/(4y).                (15)

These quotients are nonnegative. Indeed v=y^2q_v>=y and the two old Pell norms imply 0<x<=u, while 1<=C<=y<4y. If z>0, L>0, 0<r<=L and z=r+Lq with integer q, then q<=-1 would imply z<=0. Apply this elementary residue lemma to the positive s_k,t_k. All other old equations remain unchanged and the third Pell identity follows from (13). This constructs a strict-q_alpha old solution for every k>=1.

Any such solution yields a twelve-leaf solution by deleting u and replacing the old q_alpha adapter by the quotient itself. Identities U=d u q_alpha and S=d q_alpha s give H_1=d^2R_1, H_2=d^2q_alpha^2R_2, H_3=d^2q_alpha^2R_3, H_4=R_11 and H_5=d^2R_13 in the numbering of (12), so all five residuals vanish.

If o=b^(C-1), the pinned theorem supplies an old solution; (14) supplies a strict one; and this elimination supplies a new solution. This proves completeness, including C=1.

### Exact witness map and image

For fixed b,C,o, let W_13 be the old 13-leaf solution set and let W_13^+ be its subset whose natural q_alpha is >=1. Let W_12 be the solution set of (2). There is a bijection

    W_13^+ <-> W_12.                                        (16)

The forward map preserves the other eleven leaf values, removes the positive u leaf, and changes the old adapter q_alpha_plus into the new direct leaf q_alpha=q_alpha_plus-1. The inverse retains the other leaves, restores q_alpha_plus=q_alpha+1, and restores the unique u=U/(d q_alpha). Section 3 proves that this u is a positive integer. The maps are inverse by the old congruence residual and the displayed identities.

The image of the inverse map in W_13 is exactly the subset beta>alpha, equivalently q_alpha>=1 because u>0. This is not a bijection with all of W_13, and it is not literal coordinate projection because one adapter is translated. For example, the old b=2,C=1,o=1 fixture has alpha=beta=17 and q_alpha=0, so it is excluded. The progression (14) proves existential equivalence, rather than pretending excluded tuples survive unchanged. The map from an arbitrary old solution via k=1 need not be injective or inverse to reconstruction.

### Polynomial identities against the 13-leaf presentation

Let F_1,...,F_6 be the old residuals and put F_4=U-duq_alpha. Treat u as an extra indeterminate only for checking these identities. Its old S expression is S_old=X+duq_sigma. Then

    H_1=F_1, H_4=F_5, H_5=F_6,
    H_2-q_alpha^2F_2=F_4(U+duq_alpha),
    H_3-q_alpha^2F_3=
      F_4 q_sigma(2q_alpha X+(U+duq_alpha)q_sigma).             (17)

These exact polynomial identities also make clear why no extra congruence residual is retained: in the new reconstruction it becomes the definition of u, and integrality/sign follow independently.

## 5. Exact degrees and genuinely infinite fibers

For a fixed base the aliases have degrees

    deg w=deg y=deg M=deg A=1,
    deg beta=deg X=deg U=2,
    deg v=3, deg t=2, deg S=3, deg d=0.

The five exact residual degrees, after all positive shifts, are

    4, 10, 10, 1, 6.                                       (18)

Only H_2 involves q_v. In H_2 the degree-ten monomial

    -J^2 q_alpha^2 d_yC_plus^4 q_v^2

has coefficient -1. Its squared contribution

    J^4 q_alpha^4 d_yC_plus^8 q_v^4                         (19)

has coefficient 1 in P_12 and degree 20. To obtain this monomial in H_2^2, neither factor can contain another variable, so the indicated term is its only source. No other H_i uses q_v. All residuals have degree at most ten, proving exact degree 20 for every fixed b>=2, not just b=2.

For an independent base or b=B+1,

    deg w=deg y=deg d=1,
    deg beta=deg M=deg A=2,
    deg v=deg U=3, deg t=2, deg X=4, deg S=5.

The exact residual degrees are

    8, 12, 12, 1, 8.                                       (20)

For b=B+1 the B^2 term of A gives the coefficient-minus-one term

    -B^4 q_alpha^2 d_yC_plus^4 q_v^2

in H_2. Therefore

    B^8 q_alpha^4 d_yC_plus^8 q_v^4                         (21)

has coefficient 1 in P_12 and degree 24, with the same unique-source argument. Replace B by an independent b for that convention. All residuals have degree at most twelve, proving the exact degree claim.

For every accepted fixed b,C,o, (14) gives infinitely many new witnesses because the retained direct leaf q_b,k=q_b,0+uk is strictly increasing. Restriction to k>=1 only removes the possible initial endpoint; it does not remove the infinite freedom. No finite-fold conclusion is available.

For an explicit exponent-zero family, set b=2,C=1,o=1 and keep

    g=3, J=61, q_v=34,
    d_wb=0, d_wC=1, d_yC=0, q_r=0, q_tau=0.

For every integer k>=1 take

    q_b=4+577k, q_alpha=4k, q_sigma=4k.                     (22)

These are twelve-leaf solutions, with each natural alias converted to its positive adapter. Reconstruction gives alpha=17,u=577,beta=s=17+2308k,t=1. At k=0 the polynomial identities still hold, but q_alpha=0 is outside the new positive domain; this cleanly exhibits the strict-image distinction.

## 6. Explicit native-gap composition with the three-witness compiler

Let the three external inputs g_1,g_2,g_3 be positive, and D=g_1+g_2+g_3 an expression. Use positive shifted counters L,R and two independent copies of the base-two module, with (C,o)=(L,p) and (R,q). Add

    G_1=(20g_1-D)p-2D,
    G_3=(20g_3-D)q-2D.                                     (23)

The names L,R avoid conflict with a module's internal expression A. The base-two theorem and (23) enforce exactly the encoding

    g_1/D=1/20+(1/10)2^(-(L-1)),
    g_3/D=1/20+(1/10)2^(-(R-1)).                            (24)

For a fixed deterministic two-counter program and fixed T>=0, use the retained bounded compiler with three positive witnesses j,r,s. To specify all of its residuals here, put K=T+1, N=K^2, delta=(N-1)!, and for i=1,...,N put

    a_i=1+floor((i-1)/K), b_i=1+((i-1) mod K),
    L_i^0(z)=(-1)^(N-i) binom(N-1,i-1) product_(h!=i)(z-h),
    V_1(z)=sum_i a_i L_i^0(z), V_2(z)=sum_i b_i L_i^0(z),
    R_0(z)=product_(i=1)^N(z-i), H_S(z)=product_(i in S)(z-i).

The product in L_i^0 is over h=1,...,N excluding i. Empty products are 1. S is the finite set of accepted clipped classes for halting by T, or for first halting exactly at T, as defined in the retained proof. It is part of the coefficients for the fixed program/horizon, not an extra witness or free input. The six residuals are

    R_0(j),
    (delta L-V_1(j))(V_1(j)-delta K),
    delta L-V_1(j)-delta(r-1),
    (delta R-V_2(j))(V_2(j)-delta K),
    delta R-V_2(j)-delta(s-1),
    H_S(j).                                                (25)

The complete composed polynomial is G_1^2+G_3^2 plus the ten squares from the two copies of (2) plus the six squares in (25). Every module has its own twelve leaves, including its output. The three gap inputs, L,R,j,r,s and the two modules' internal leaves are otherwise distinct.

The paid decoding ledger is 2+2*12=26 positive witnesses and 2+2*5=12 residual slots. Adding (25) gives exactly

    external positive inputs: 3,
    positive witnesses: 2+24+3=29,
    all variables including inputs: 32,
    residual slots: 2+10+6=18,
    final polynomial equations: 1.                         (26)

These literal counts retain even zero or duplicate residual slots at T=0. They apply to both by-horizon and exact-horizon versions.

Correctness follows without any unencoded-input promise: a zero first determines p=2^(L-1),q=2^(R-1), then (23) gives exactly (24), and (25) enforces the chosen bounded-halting condition on those counters. Conversely encoded accepted counters supply L,R,p,q, both new POWER witnesses, and the unique bounded triple. The retained clipping proof justifies the finite class table for all input sizes. No native interpreter or physical simulator is needed for this proof.

If P_(program,T) denotes the sum of (25)'s squares, the exact degree is

    deg F=max(20,deg P_(program,T)),
    deg F<=max(20,4(T+1)^2-4) for T>=1,
    deg F=20 for T=0.                                      (27)

The degree-twenty monomial (19) in each independent module is absent from the other module, gap terms, and compiler. If deg P>20 its highest-degree part is unchanged; otherwise one of those module monomials survives. The bound in the second line is not asserted to be an equality.

The input uniquely fixes p,q via (23), then uniquely fixes L,R, and the compiler uniquely fixes j,r,s. Nevertheless the full 29-witness fibers are infinite whenever nonempty, by varying (14) in either POWER copy. T still indexes different polynomials, so this is not a single fixed-polynomial unbounded-halting theorem or universal-polynomial record. No renewed claim about arbitrary physical execution is made.

For the separately retained finite-trace alternative, the same replacement has T(E+2)+26 positive witnesses and T(E+Z+4)+13 residual slots, and exact degree 20. Its exact-first-halt trace for T>=1 adds one residual and no witness. This follows by adding the unchanged trace ledger to the paid decoding ledger, without recounting old reports.

## 7. Precise dependencies and scope of verification

The imported number-theoretic dependency is Mario Carneiro's pair `Pell.matiyasevic` and `Pell.eq_pow_of_pell` in mathlib4 commit

    ac77769fabe23cb237559e7f56578dbead91499f,

file `Mathlib/NumberTheory/PellMatiyasevic.lean`, SHA-256

    993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a.

Source: https://github.com/leanprover-community/mathlib4/blob/ac77769fabe23cb237559e7f56578dbead91499f/Mathlib/NumberTheory/PellMatiyasevic.lean.

The source is copied unchanged and retained inertly with the Apache 2.0 license and attribution. The theorem statements at lines 760-766 and 860-864, recurrence at lines 104-114 and 133-142, and constructive witness branches at lines 767-806 and 865-897 were inspected as text. No new Lean verification is claimed.

In (12), the first nine equations specialize the positive-index branch of matiyasevic to Pell index C, forcing (x,y)=(X_C(alpha),Y_C(alpha)). The final six equations specialize the power theorem to n=b,k=C,m=bo,modulus M,auxiliary w,g and parameter alpha. They give b^C=bo, and cancellation of b>0 gives o=b^(C-1). The strict bound M>bo is supplied by J>0. The natural subtraction alpha-b in the source agrees with ordinary subtraction because Section 3 proves alpha>b. Other inner source differences are nonnegative, and a natural equality a-b=1 translates exactly to a=b+1.

Conversely the source's constructive power branch supplies w,alpha,M,g, with g nonzero because alpha>1. Its constructive nonzero-index Pell branch supplies the old positive norms/congruences. Pell x,u,s are positive; y>=C>=1 and v>0 make q_v positive. beta>1 and beta congruent to 1 modulo 4y make q_b positive. The congruence t=C modulo 4y with 1<=C<=y<4y excludes t=0. The four one-sided quotient signs and all other adapters are justified in the copied full `positive22_PROOF.md`; the auxiliary α-recovery and 13-leaf equivalence are proved in `elimination_PROOF.md`. Those full proofs and the POWER58, POWER60, native-gap, and compressed proofs were read as static text. The new strict quotient step and u recovery are Sections 3-4 above.

`SOURCE_PINS.json` records all unchanged mathematical dependencies and their hashes. `static_algebra.py` is freshly authored standard-library exact sparse-polynomial and finite-fixture arithmetic. It imports or executes no upstream/author/science script, Lean, counter interpreter, physical simulator, or saved schedule. It is read in full before execution. It expands the positive-shifted polynomials, checks counts/liveness/exact degrees/coefficient-one monomials, verifies (17), checks complete fixed finite Pell fixtures and the symbolic family (22), and checks literal compositions against hand-declared finite acceptance tables.

`evidence/results.json` records the actual checks, and the manifest hashes every deliverable and evidence artifact. The before/after full hash inventory verifies that the frozen original packet remains byte-for-byte unchanged. There is no claim of minimum arity, minimum degree, novelty, priority, arithmetic-gate improvement, efficient or small Pell witnesses, finite-fold representation, exhaustive literature coverage, or an unrelated universal-polynomial bound.
