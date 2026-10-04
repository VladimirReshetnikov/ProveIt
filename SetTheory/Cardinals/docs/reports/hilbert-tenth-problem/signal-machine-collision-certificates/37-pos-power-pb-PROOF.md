# Four one-sided quotients in the positive POWER module

4 October 2026. A separate arithmetic continuation. The retained 26-leaf construction and frozen Reports 65/66 are unchanged. The reduction below is an equivalence proof for a new displayed formula; it is not a claim that the old formula had fewer declared variables.

## 1. Domains and the precise result

Let b be an integer base with b>=2, C a positive integer index, and o a positive integer output. The semantic exponent is C-1, including exponent zero when C=1.

There is an explicitly displayed sum-of-squares integer polynomial with exactly 22 positive module leaves including o, or 21 existential positive auxiliary leaves when o is treated as an external argument, such that

    o=b^(C-1)  iff  some positive auxiliary tuple makes all 15 residuals zero.

C and b are not among the 22 module leaves. In a composition they must already be counted as external inputs, outer witnesses, fixed coefficients, or expressions in those quantities. To make a variable base an unrestricted positive input, use a separate positive leaf B and substitute b=B+1; this B is an additional external input, not a free module leaf. For a fixed base, including b=2, no base variable is needed.

The joint total degree of the sum of these 15 squares is exactly 12 for fixed b, for an independent base b, or for the positive-base substitution b=B+1. The same degree upper bound holds after an affine base substitution; arbitrary higher-degree base substitutions are not covered by that degree statement. In all these statements C is an independent positive input or an affine index expression. Degrees are measured in the independent inputs and leaves before imposing the residual constraints.

## 2. Every leaf and every residual

Use the 13 directly positive leaves

    o,w,M,g,x,y,u,v,s,t,q_b,q_v,J,

and two positive leaves alpha_plus,beta_plus defining

    alpha=alpha_plus+1, beta=beta_plus+1.

Use seven natural aliases

    d_wb,d_wC,d_yC,q_alpha,q_sigma,q_tau,q_r,

each equal to its own distinct positive adapter leaf minus 1. Adapters may equal 1, which represents the natural value 0. There are precisely 13+2+7=22 positive leaves; aliases do not introduce additional leaves or equations.

The complete residual list is

    R_1  = x^2-1-(alpha^2-1)y^2
    R_2  = u^2-1-(alpha^2-1)v^2
    R_3  = s^2-1-(beta^2-1)t^2
    R_4  = beta-1-4y q_b
    R_5  = beta-alpha-u q_alpha
    R_6  = v-y^2 q_v
    R_7  = s-x-u q_sigma
    R_8  = t-C-4y q_tau
    R_9  = y-C-d_yC
    R_10 = w-b-d_wb
    R_11 = w-C-d_wC
    R_12 = M-b o-J
    R_13 = alpha^2-1-((w+1)^2-1)(wg)^2
    R_14 = 2alpha b-M-(b^2+1)
    R_15 = x-y(alpha-b)-b o-M q_r.                  (1)

Every product in this display is ordinary integer multiplication. The polynomial is literally sum_(i=1)^15 R_i^2 after all positive shifts; no residual, division, power predicate, or sign condition is hidden. For b=2, R_14=4alpha-M-5 and R_12=M-2o-J.

## 3. Why the four quotients were already nonnegative

The retained module has the same equations except for four paired-natural presentations:

    beta+u alpha_1-alpha-u alpha_2=0,
    s+u sigma_1-x-u sigma_2=0,
    t+4y tau_1-C-4y tau_2=0,
    x+M r_1-y(alpha-b)-b o-M r_2=0.               (2)

All eight aliases in (2) are natural, with positive adapters. Initially they express arbitrary signed integer quotients. The following argument uses only the other equations, positivity, and the divisibilities in (2); it does not assume any quotient's desired sign.

First, R_9 gives y>=C>=1, while R_6 gives v=y^2 q_v>=y because q_v>=1. The two Pell equations imply

    u^2-alpha^2=(alpha^2-1)(v^2-1)>=0,
    u^2-x^2=(alpha^2-1)(v^2-y^2)>=0.

The quantities being compared are positive, so

    1<=alpha<=u, 1<=x<=u.                         (3)

We repeatedly use the elementary residue lemma: if L>0, 0<r<=L, z>0, and z=r+Lq for an integer q, then q>=0. Otherwise q<=-1 gives z<=r-L<=0, a contradiction. Equality r=L is allowed, so no strict-bound case is lost.

Apply the lemma to beta congruent to alpha modulo u and s congruent to x modulo u. Equation (3) gives beta>=alpha and s>=x. Apply it to t congruent to C modulo 4y; here 1<=C<=y<4y. It gives t>=C. Thus

    (beta-alpha)/u, (s-x)/u, (t-C)/(4y) are nonnegative integers.   (4)

For the fourth quotient, equations R_10 and R_13 give w>=b>=2 and

    alpha^2=1+((w+1)^2-1)(wg)^2>w^2,

since g>=1. Hence alpha>w>=b. Define the ordinary integer

    h=x-y(alpha-b).

Its positivity follows without using the final congruence: both x and y(alpha-b) are nonnegative, and

    x^2-[y(alpha-b)]^2=(2alpha b-b^2-1)y^2+1>0.    (5)

Indeed alpha>b>=2 makes the coefficient 2alpha b-b^2-1 positive. Therefore h>0. Equation R_12 gives 0<b o<M. The last equation in (2) says h=b o+M(r_2-r_1). Applying the residue lemma with r=b o and L=M gives

    h>=b o,  (h-b o)/M>=0.                        (6)

These conclusions apply to every positive solution of the old module, not merely to a specially chosen constructive witness. They hold for every integer b>=2, including variable bases whose domain has been established in the outer construction.

## 4. The exact witness maps and positive adapters

Given any old solution, preserve its directly positive leaves, alpha_plus,beta_plus, and three slack aliases. Define

    q_alpha=alpha_2-alpha_1=(beta-alpha)/u,
    q_sigma=sigma_2-sigma_1=(s-x)/u,
    q_tau=tau_2-tau_1=(t-C)/(4y),
    q_r=r_2-r_1=(x-y(alpha-b)-b o)/M.             (7)

Section 3 proves all four values are natural integers. Their new positive adapters are q_alpha+1,q_sigma+1,q_tau+1,q_r+1. Thus they are genuinely positive even when the quotients vanish. Substitution proves all residuals in (1) vanish.

Conversely, from a new solution set the natural aliases

    alpha_1=sigma_1=tau_1=r_1=0,
    alpha_2=q_alpha, sigma_2=q_sigma, tau_2=q_tau, r_2=q_r.       (8)

The four first positive adapter leaves in the old pairs are therefore 1, not 0. The four second adapters are q+1. All are positive and (2) follows directly. Every other old leaf is unchanged. This is a section of the projection in (7), proving existential equivalence without discarding the positive-domain requirement. It is not a bijection of full old and new witness tuples: the old redundant common shifts have been removed.

## 5. Exact imported theorem and all-exponent equivalence

The number-theoretic dependency is Mario Carneiro's constructive pair `Pell.matiyasevic` and `Pell.eq_pow_of_pell` in mathlib4 commit

    ac77769fabe23cb237559e7f56578dbead91499f,

file `Mathlib/NumberTheory/PellMatiyasevic.lean`, SHA-256

    993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a.

The exact source is retained inertly in `dependencies/pell-source.lean`, with its Apache 2.0 license and attribution. Its source URL is
https://github.com/leanprover-community/mathlib4/blob/ac77769fabe23cb237559e7f56578dbead91499f/Mathlib/NumberTheory/PellMatiyasevic.lean.
The theorem statements at lines 760-766 and 860-864, the recurrence at lines 104-114 and 133-142, and the constructive specialization at lines 767-806 and 865-897 were inspected as text. No Lean build, upstream execution, or claim of new theorem-prover verification is made.

In mathematical notation, the first theorem says that (x,y) is the index-k Pell pair for a>1 exactly when a>1, k<=y, and either (x,y)=(1,0), or there are natural u,v,s,t,beta with

    x^2-(a^2-1)y^2=1,
    u^2-(a^2-1)v^2=1,
    s^2-(beta^2-1)t^2=1,
    beta>1, beta congruent to 1 modulo 4y,
    beta congruent to a modulo u,
    v>0, y^2 divides v,
    s congruent to x modulo u,
    t congruent to k modulo 4y.

Its zero branch is excluded here by y>=C>=1. The second theorem's positive-base and positive-index branch characterizes n^k=m by natural w,a,t,z and a>1 satisfying

    X_k(a) congruent to Y_k(a)(a-n)+m modulo t,
    2an=t+(n^2+1), m<t, n<=w, k<=w,
    a^2-((w+1)^2-1)(wz)^2=1.

In the source the displayed subtractions are natural subtractions. A natural equality A-B=1 is equivalent to A=B+1. Our inner differences alpha^2-1,beta^2-1,(w+1)^2-1 are nonnegative, and Section 3 proves alpha>b. Thus ordinary subtraction alpha-b agrees with the source's natural subtraction; no hidden domain change occurs.

The retained generic derivations are `dependencies/POWER58_PROOF.md`, Section 7, and `dependencies/POWER60_PROOF.md`, Section 6. The base-two specialization is `dependencies/native_gap_PROOF.md`, Section 3. Substitute n=b,k=C,m=b o,t=M,z=g,a=alpha in the positive branch. Residuals 1-9 give (x,y)=(X_C(alpha),Y_C(alpha)); residuals 10-15 give b^C=b o. Cancelling b>0 yields o=b^(C-1).

Conversely, if o=b^(C-1), the source's constructive power theorem and the positive-index Matiyasevic theorem supply the old congruence witnesses. The power witness g is nonzero, since g=0 would force alpha=1; x,u,s are positive Pell x-coordinates; y>=C>=1; v>0 and y^2|v give positive q_v; beta>1 with beta congruent to 1 modulo 4y gives positive q_b. The congruence for t and 1<=C<=y<4y excludes t=0. The strict bound M>b o gives J>0. Natural slacks and the old signed quotient pairs therefore admit all stated positive adapters, including at C=1. Section 4 converts this old solution to the new one. This proves the all-exponent equivalence, conditional on the explicitly identified theorem dependency, not on finite testing.

## 6. Exact degree and module count

For fixed b or b=B+1 the residual degree list is

    4,4,4,2,2,3,2,2,1,1,1,d_12,6,d_14,2,

where d_12=d_14=1 for fixed b and 2 for the independent affine base B+1. These are exact degrees for the literal residual polynomials with independent inputs and module leaves. In both cases R_13 has top homogeneous part -w^4 g^2; all other residuals have degree at most 4. Consequently the sum of squares has exact top homogeneous part w^8 g^4 and exact total degree 12. Affine substitutions cannot raise the upper bound, and when w,g remain independent module leaves this degree-12 term remains.

The old leaf ledger was 13+2+11=26. Four pairs of natural adapters have become four single natural adapters, while the three natural slacks remain. The new ledger is 13+2+3+4=22. The output is included once. With output and index supplied externally, there are 21 auxiliary witnesses, not 22; quantifying an outer index adds its own witness. All 15 residual slots are retained. No gate count or minimality claim follows from this variable reduction.

## 7. Infinite fibers remain at every accepted argument

Removing common-shift aliases does not make this formula finite-fold. Fix b,C,o and any one solution. Keep alpha,w,M,g,x,y,u,v,q_v,J and the three slack aliases fixed. Section 5 establishes

    x=X_C(alpha), y=Y_C(alpha).

Define integer polynomials X_n(z),Y_n(z) recursively by

    X_0(z)=1, Y_0(z)=0,
    X_(n+1)(z)=z X_n(z)+(z^2-1)Y_n(z),
    Y_(n+1)(z)=X_n(z)+z Y_n(z).                  (9)

These are the same Pell coordinates as the inspected source for z>=2. Induction gives their Pell identity, positivity X_n(z),Y_n(z)>0 for z>=2,n>=1, and X_n(1)=1,Y_n(1)=n. Since they are integer polynomials, congruent arguments give congruent values modulo every positive modulus.

Let beta_0 be the old value of beta in the chosen solution. For every natural k set

    beta_k=beta_0+4yu k,
    s_k=X_C(beta_k), t_k=Y_C(beta_k).             (10)

Then beta_k>=beta_0>=2, beta_k congruent to alpha modulo u, and beta_k congruent to 1 modulo 4y. Hence

    s_k congruent to X_C(alpha)=x modulo u,
    t_k congruent to Y_C(1)=C modulo 4y.          (11)

Use q_b,k=(beta_k-1)/(4y)=q_b,0+u k>0 and the natural quotients

    q_alpha,k=(beta_k-alpha)/u,
    q_sigma,k=(s_k-x)/u,
    q_tau,k=(t_k-C)/(4y).

All three are nonnegative by the same positive-residue lemma using (3); alternatively q_alpha,k=q_alpha,0+4y k. Keep q_r unchanged. The Pell identity for (s_k,t_k), (11), and these definitions verify every residual. All positive adapters stay positive. Even at k=0 the replacement Pell pair need not equal the original (s,t); this is harmless, since the argument constructs a new family from every solution and preserves the required fixed data.

The beta_plus leaf equals beta_k-1 and is strictly increasing because 4yu>0. Thus (10) gives infinitely many distinct new positive witness tuples for every accepted (b,C,o). This is genuine variation of the Pell parameter and associated witnesses, independent of the removed paired-alias shifts. Compositions retain infinite complete fibers by varying one module while preserving its index and output and every outer witness.

### 7.1 A fully explicit exponent-zero family

For b=2,C=1,o=1 keep

    w=2, M=63, g=3, alpha=17,
    x=17, y=1, u=577, v=34,
    q_v=34, J=61, d_wb=0,d_wC=1,d_yC=0,q_r=0.

For every natural k take

    beta=17+2308k, s=beta, t=1,
    q_b=4+577k, q_alpha=4k, q_sigma=4k, q_tau=0.   (12)

Every residual is identically zero in k. alpha_plus=16, beta_plus=16+2308k, the slack adapter for d_wC is 2, and every natural alias is represented by its value plus 1. In particular the zero aliases use positive leaf 1. This family alone disproves a finite-fold claim, while Section 7 proves the stronger statement for every accepted argument and every base b>=2.

## 8. New native-gap composition counts

The native inputs are the same three arbitrary positive gaps g_1,g_2,g_3, with D=g_1+g_2+g_3 an expression. Introduce positive shifted counters A,B and two independent new modules with (C,o)=(A,p),(B,q), base 2. Add the two residuals

    (20g_1-D)p-2D,
    (20g_3-D)q-2D.                               (13)

The predicate includes being encoded by g_1/D=1/20+2^(-a)/10 and g_3/D=1/20+2^(-b)/10 for natural counters a=A-1,b=B-1. It does not assert anything about arbitrary unencoded physical executions. The output powers and decoded counters are unique whenever they exist, exactly as in the retained proof; the module's internal witnesses remain infinite.

The paid decoding overhead is now

    A,B: 2; two full modules, including p,q: 2*22;
    total positive witnesses: 46;
    residual slots: 2+2*15=32.

Adding the retained finite trace for a fixed program with E edges including the absorbing halt edge, Z zero edges, and fixed horizon T gives

    positive witnesses: T(E+2)+46,
    all variables including three inputs: T(E+2)+49,
    residual slots: T(E+Z+4)+33,
    exact degree: 12.

The first-halt-exactly-T trace version for T>=1 adds one residual and no witness; at T=0 it agrees with the by-horizon version. These are literal presentation counts, including degenerate constant or zero residual slots. This replaces only the module in the fully displayed native-gap proof; its trace correctness is unchanged.

Alternatively compose with the three-positive-witness, six-residual polynomial P_(program,T)(A,B;j,r,s) defined in `dependencies/compressed_PROOF.md`, Sections 1-6. Define the new final polynomial by adding its six squares to the 32 decoding/module squares. The ledger is

    external positive inputs: 3,
    A,B: 2,
    two modules including p,q: 44,
    compressed j,r,s: 3,
    total positive witnesses: 49,
    total variables including inputs: 52,
    residual slots: 38,
    final polynomial equations: 1.

For both by-horizon and first-halt-exactly-horizon compressed versions,

    deg F=max(12,deg P_(program,T)),
    deg F<=max(12,4(T+1)^2-4) for T>=1,
    deg F=12 for T=0.

The degree equality follows from the independent monomials w_A^8 g_A^4 and w_B^8 g_B^4, which P does not use. The second line remains an upper bound, not an exact degree formula. The original three-witness compressed theorem, acceptance table, coefficient costs, and uniqueness of its projected triple do not change. Full fibers of this new 49-witness composition are infinite by Section 7. T still indexes different polynomials; this is not one fixed polynomial for unbounded halting, nor a universal-polynomial record.

## 9. Verification and limits

The fresh `check_reduction.py` uses only standard-library exact integer and sparse-polynomial arithmetic. It is inspected before execution. It expands all positive adapters; checks exact degrees, top monomials, leaf liveness and counts; evaluates base-two and generic-base Pell fixtures; verifies the maps in both directions, including nonzero old common shifts; and checks the parameter family (12) as a polynomial identity, not just at sampled k values. It also checks finite instances of (10), and literal composed polynomial counts with hand-declared finite acceptance sets. No counter-machine interpreter, physical simulator, saved schedule, author checker, upstream code, or Lean is executed.

Finite fixtures do not prove the all-exponent equivalence or all-input composition. Those assertions follow from the displayed mathematics and the pinned theorem dependency. The exact source pins and finite evidence are separate from those proofs. No claim is made about efficient construction, witness height, arithmetic-gate cost, smallest variable count, novelty, priority, finite-fold representability, or general unbounded-horizon compression.
