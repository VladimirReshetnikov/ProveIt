# Two positive witnesses for bounded two-counter halting

4 October 2026. A separate continuation. This task does not modify the predecessor three-witness compiler, accepted twelve-leaf POWER module, their audits, or Reports 66–68. The separate concurrent sealing of Report68 and its post-seal verification are recorded in PRESERVATION.md. This two-witness construction makes no novelty, priority, global minimality, or universal-polynomial claim. The separate ONE_WITNESS.md proves only a scoped zero-versus-one auxiliary-variable classification for fixed finite clipping predicates, without a degree restriction.

## 1. Statement and finite-horizon scope

Fix a finite deterministic two-counter program M with initial state q0 and designated halt state H. Counters are natural integers. Each nonhalt instruction either increments one counter and takes its specified successor, or tests one counter for zero, taking its specified zero successor when zero and otherwise decrementing it and taking its specified positive successor. The other counter is unchanged. Arbitrary control loops are allowed.

For each fixed integer T>=0 we construct an integer polynomial

    P_(M,T)(A,B;r,s)

in two positive integer inputs A,B and exactly two positive integer witnesses r,s. The inputs represent native counters (A-1,B-1). Its zero set satisfies

    exists r,s>0: P_(M,T)=0
      iff M reaches H within T transitions from (q0,A-1,B-1).

For every accepted positive input the ordered witness pair is unique. The same assertion for first reaching H exactly at transition T uses the same formula with a different finite acceptance table. There are five residual slots, summed as squares into one equation, at every horizon including T=0.

For T>=1 the joint degree, including the inputs, is at most 4T. The displayed polynomial has exact degree

    max(2(T+1),4,2 deg F_S),                                  (1)

where F_S is the explicitly defined two-variable rejection interpolant below and deg 0=-infinity. At T=0 a separately specified five-slot presentation has exact degree two.

For each T>=2 the upper bound 4T is attained by the by-horizon polynomial of one fixed program consisting of two successive zero tests, with every positive branch entering a nonhalting sink. This is an exact worst-case statement for this displayed construction; it is not a lower bound on alternative constructions.

T indexes different polynomials. The table, products, degrees, and coefficients change with T. This is an effectively generated fixed-witness-arity family, not one fixed polynomial having T as an extra input. Finite table construction is paid work. No unbounded-halting representation, single-fold MRDP result, or efficient bounded-halting algorithm follows.

## 2. Clipping and the table

Make H virtually absorbing, leaving both counters unchanged after arrival. This is finite-prefix bookkeeping. Put

    K=T+1, a*=min(a,T), b*=min(b,T).

Starting from (a,b) and (a*,b*), the two runs have the same states q0,...,qT and take the same branches for transitions 1,...,T. To prove it, suppose the first t transitions agree, where t<T. An initially smaller counter was identical and has received the same changes. An initially large counter's representative started at T, so at the next instruction entry it is at least T-t>0. The original is this value plus its fixed nonnegative initial offset. Hence any tested counter gives the same zero/nonzero answer and the next transition agrees. Induction proves the claim. The representative can become zero after transition T; there is no further test in the specified prefix. Loops cause no difficulty. At T=0 there is no transition to compare.

Thus the positive input representatives are

    u*=min(A,K), v*=min(B,K).                                 (2)

Let S be the subset of [1,K]^2 whose native representatives (i-1,j-1) meet the desired by-T or first-exactly-T predicate. In principle its K^2 bits are computed by examining the initial state and at most T transitions for each representative. This costs at most K^2 T native transitions; those representative counters never exceed 2T. No interpreter is run in this packet. The table fixtures used below are declared from elementary closed-form cases.

If q0=H, the by-T table is full for every T; its exact-T table is empty for T>0. At T=0 either version is full, namely {(1,1)}, precisely when q0=H, and empty otherwise. The clipping lemma proves that the actual input is accepted exactly when (u*,v*) belongs to this fixed table, even for unboundedly large A,B.

## 3. Cleared tensor interpolation

Assume first T>=1, hence K>=2, and let c=(K-1)!. For i=1,...,K define

    ell_i(z)=(-1)^(K-i) binom(K-1,i-1)
                product_(1<=h<=K,h!=i)(z-h).

The product of differences at i is (-1)^(K-i)(i-1)!(K-i)!, so

    ell_i(i)=c, and ell_i(h)=0 for h!=i in [1,K].             (3)

All coefficients are integers. Moreover sum_i ell_i(z)=c as a polynomial: both sides have degree at most K-1, and agree at K distinct nodes.

Define the integer rejection interpolant

    F_S(x,y)=sum_((i,j) in [1,K]^2 outside S) ell_i(x)ell_j(y).
                                                                    (4)

Its degree in each coordinate is at most K-1 and its joint degree is at most 2K-2. At a grid node it is exactly 0 for membership in S and c^2 otherwise. The full table gives F_S=0; the empty table gives the constant c^2 because both basis sums equal c. Thus neither extreme requires an exception to interpolation or introduces a spurious root on the grid.

The variables x,y in this definition describe a polynomial, not additional witnesses. No denominator depends on an input or witness, and no rational coefficient remains.

## 4. Five residuals and full domain recovery

Define integer expressions, not new variables,

    u=A-r+1, v=B-s+1, R_K(z)=product_(i=1)^K(z-i).

The five residuals are

    D1=R_K(u),             D2=R_K(v),
    D3=(r-1)(u-K),         D4=(s-1)(v-K),
    D5=F_S(u,v),

and the promised polynomial is

    P_(M,T)=D1^2+D2^2+D3^2+D4^2+D5^2.                       (5)

All four actual variables A,B,r,s range over ordinary positive integers. Expressions u,v are not assumed positive before the equations are imposed.

**Soundness and recovered domains.** A sum of real squares, hence a sum of integer squares, can vanish only if each residual vanishes. D1 and D2 force u,v to be integer roots in [1,K]. The definition of u gives A-u=r-1>=0. If u<K, D3=0 forces r=1 and hence A=u. If u=K, positivity of r forces A>=K. These cases give exactly u=min(A,K), and similarly v=min(B,K). They also uniquely give

    r=A-min(A,K)+1, s=B-min(B,K)+1.                           (6)

In particular 1<=r<=A and 1<=s<=B. There are no negative representatives, rational slacks, or hidden range variables. D5=0 then says precisely that the clipped pair is in S, which is the required halting assertion by Section 2.

**Completeness.** If the desired predicate holds, take the positive pair (6). Then u,v are the clipped representatives. The range residuals vanish. In each classification product either the slack is one or the representative is K, so it vanishes. The table residual vanishes by acceptance. Therefore (5)=0.

**Uniqueness.** Every zero has the exact pair (6). Thus the native compiler's full witness fiber is a singleton for accepted inputs and empty otherwise. Unlike the later POWER composition, the native compiler itself has no auxiliary freedom.

The strict positive domain matters. Allowing r=0 can select u=A+1=K even when A=K-1, since D3 then vanishes through u-K. That can incorrectly choose the tail class. Positivity is a hypothesis, not an implicit inequality supplied by the polynomial.

### Horizon zero

Use the five residual slots

    A-r, B-s, 0, 0, epsilon,

where epsilon=0 if q0=H and epsilon=1 otherwise. Thus

    P_(M,0)=(A-r)^2+(B-s)^2+epsilon.                         (7)

The first-exactly-zero version is identical. Accepted inputs have the unique positive witnesses (A,B); rejected inputs have none. Both polynomials have exact degree two, with six nonzero monomials when epsilon=0 and seven when epsilon=1.

This is an explicitly separate definition at T=0. Substituting K=1 into all five residuals of (5) would retain unnecessary quadratic classification residuals, and their squares would have degree four. We do not silently discard those terms while claiming to use that unchanged formula. The five-slot count in (7) intentionally retains its zero slots.

## 5. Exact degree and the fixed worst-case program

For K>=2, D1 and D2 have exact degree K, and D3 and D4 exact degree two. The substitution x=A-r+1,y=B-s+1 preserves the total degree of every nonzero polynomial f(x,y). Indeed its top homogeneous part becomes f_top(A-r,B-s), which is nonzero because setting r=s=0 gives f_top(A,B).

A nonempty collection of real homogeneous polynomials of equal degree cannot have identically zero sum of squares unless each is zero: evaluate at every real point, then use nonnegativity. Apply this to the highest-degree parts of the five residuals. Their top squares cannot cancel. Therefore

    deg P=max(2K,4,2 deg F_S).                               (8)

Since deg F_S<=2K-2 and 2K<=4K-4 for K>=2, the degree is at most 4K-4=4T. For empty and full tables, (8) gives exact degree 2K. At T=1 (K=2), every acceptance table gives exact degree four.

For the fixed worst-case program, use states Q_A,Q_B,L,H, initial state Q_A, and instructions:

- Q_A: test a; if zero go to Q_B, otherwise decrement a and go to L
- Q_B: test b; if zero go to H, otherwise decrement b and go to L
- L: increment a and return to L

No sink transition reaches H. Starting at a=b=0 first reaches H on transition two, not transition one. If a>0 it enters L on transition one; if a=0,b>0 it enters L on transition two. Thus for every T>=2 its by-T table is exactly S={(1,1)}.

For this table,

    F_S(x,y)=c^2-ell_1(x)ell_1(y).

Each ell_1 has degree K-1 and leading coefficient (-1)^(K-1); their product has leading coefficient one on x^(K-1)y^(K-1). Hence F_S has exact degree 2K-2 and P exact degree 4K-4=4T. This degree witness is one fixed program across all T>=2.

For this particular fixed program the exact-T table is singleton only at T=2 and is empty for T>2. We do not claim otherwise. For each individual T>=2, the exact-T upper bound can also be attained by inserting a chain of T-2 increment instructions on the successful path after the second zero test before H; that program depends on T. No delay is needed at T=2. These are mathematical program descriptions, not executed traces.

## 6. Coefficients, support, storage, and construction cost

Let ||f||_1 be the sum of absolute coefficient values after all substitutions into A,B,r,s. Put

    B_K=(K+1)!, L_K=2^(K-1) B_K.

For i>=1, the affine factor u-i=A-r-(i-1) has coefficient norm i+1. Thus products obey precisely the same simple bound as their univariate versions. Using subadditivity, submultiplicativity, and the sum of binomial coefficients gives

    ||R_K(u)||_1,||R_K(v)||_1 <= B_K,
    sum_i ||ell_i(u)||_1 <= L_K,
    sum_i ||ell_i(v)||_1 <= L_K,
    ||F_S(u,v)||_1 <= L_K^2.

Also ||r-1||_1=2 and ||u-K||_1=K+1, so each classification residual has norm at most 2(K+1). Consequently

    ||P||_1 <= Q_K:=L_K^4+2B_K^2+8(K+1)^2.                  (9)

Every integer coefficient has magnitude at most Q_K. Its magnitude requires at most ceil(log2(Q_K+1)) bits, with a separate sign bit if desired. This is O(K log(K+1)), uniformly in the program/table. Formula (7) handles T=0 directly.

### Expanded support and an honest tradeoff

The substituted tensor square F_S(u,v)^2 has total degree at most 2K-2 in the variable pair (A,r) and independently at most 2K-2 in (B,s). Its support therefore contains at most

    binom(2K,2)^2=K^2(2K-1)^2

monomials. The other four squares are pure in one of those pairs and have degree at most 2K, since K>=2. The pairwise monomials of degrees at most 2K-2 are already counted. At most

    2[binom(2K+2,2)-binom(2K,2)]=8K+2

additional monomials can occur. Thus a uniform explicit support ceiling is

    K^2(2K-1)^2+8K+2=O(K^4).                                (10)

Cancellations can reduce it. We make no lower-bound or tightness claim for this ceiling.

Storing each signed coefficient and its four binary exponents yields an expanded description of O(K^5 log(K+1)) bits, by (9)-(10). The old three-witness construction had O(K^2) monomials and an O(K^4 log(K+1)) expanded-bit upper bound, although its coefficient bits and degree were O(K^2 log K) and O(K^2), respectively. Removing the class-code witness lowers arity and degree, but the tensor substitution loses the old narrow support shape. The new expanded support and bit upper bounds are worse. These are representation upper bounds, not a proof that every new instance is larger than every old instance.

### Factored arithmetic circuit and finite preprocessing

Let m=K^2-|S| be the number of rejected cells. Reuse the 2K factors u-i,v-i. For each coordinate independently, form every ell_i by multiplying its K-1 factors and then its signed binomial coefficient. This elementary shared-factor circuit needs at most 2K(K-1) multiplications for all bases. Forming the two ranges adds 2(K-1), the two classification products adds two, all rejected-cell products add m, and the final five squares add five. In total there are at most

    2K^2+m+5 <=3K^2+5 multiplications.

Computing u,v, the 2K factors and the two shifted slacks, summing the rejected-cell products, and summing the five squares uses at most

    2K+10+max(m-1,0) <=K^2+2K+9 additions/subtractions.

Thus at most 4K^2+2K+14 ordinary integer arithmetic operations suffice for evaluating this particular factored presentation. This count is an upper bound; multiplication by +/-1 and zero slots could be removed. No division is used. A prefix/suffix optimization of the one-dimensional products is possible but not needed for the O(K^2) claim.

The table itself is K^2 bits. The signed binomial constants have O(K) bits each, all node constants have O(log K) bits, and a straightforward circuit encoding with gate indices has O(K^2 log(K+1)) bits. These factored-description costs do not erase the K^2 T native-transition cost of determining the table in principle. Arithmetic counts are not bit complexity: evaluating at large inputs/witnesses must pay for their integer sizes.

For an explicit coefficient-generation upper bound, form the K univariate bases by repeated linear multiplication in O(K^3) integer operations. Summing their coefficient outer products over the declared table uses O(K^4), as does a naive two-variable convolution for F_S^2. Precompute all powers of A-r+1 and B-s+1 through degree 2K-2. A separable coefficient transform first substitutes the first coordinate in O(K^4) operations, producing O(K^3) coefficient entries, and then substitutes the second in O(K^5). The four remaining squared residuals are smaller. Hence O(K^5) integer operations is a simple expanded-construction upper bound after obtaining S. Coefficient intermediates have O(K log(K+1)) magnitude bits: product/triangle bounds as above, even allowing the factor 3^(4K) from a coarse affine-power substitution bound, suffice. Again this is not a unit-cost bit-complexity or polynomial-in-log(T) claim.

## 7. Composition with the accepted twelve-leaf POWER module

This section imports the accepted module and its audited, pinned constructive Pell dependency. The new native compiler in Sections 1–6 requires neither. We repeat every base-two residual to make the composed polynomial explicit.

For positive index C, one module has six direct positive leaves

    o,g,q_b,q_v,J,q_alpha,

and six distinct positive adapter leaves for natural aliases

    d_wb,d_wC,d_yC,q_sigma,q_tau,q_r,

each alias equal to its own adapter minus one. Thus there are twelve positive leaves including output o, and eleven auxiliary leaves beyond it. Define expressions

    w=2+d_wb, y=C+d_yC, beta=1+4y q_b,
    v_p=y^2 q_v, t=C+4y q_tau, M_p=2o+J,
    Z=2o+J+5, X=y(Z-8)+8o+4M_p q_r,
    U=4beta-Z, V=q_alpha X+U q_sigma.

The five residuals are

    H1=X^2-16-(Z^2-16)y^2,
    H2=U^2-16q_alpha^2-(Z^2-16)q_alpha^2 v_p^2,
    H3=V^2-16q_alpha^2-16q_alpha^2(beta^2-1)t^2,
    H4=w-C-d_wC,
    H5=Z^2-16-16((w+1)^2-1)(wg)^2.                         (11)

The imported result is: for positive C,o, these five equations admit eleven positive auxiliary leaves exactly when o=2^(C-1). Their sum of squares has exact joint degree 20. For every accepted C,o there are infinitely many full module tuples.

### Recovered module domains and the imported theorem boundary

For completeness the essential domain recovery is restated, rather than silently allowing rational leaves. The positive adapters give w>=2,y>=C>=1,beta>=5,v_p>=1,t>=1,M_p>2o and q_alpha>=1. H5 gives

    alpha^2=1+((w+1)^2-1)(wg)^2, alpha=Z/4>0.

A rational number with integer square is an integer by coprime numerator/denominator divisibility. Hence alpha is integral and alpha>w>=2. H2 similarly gives an integral

    u_p=U/(4q_alpha), u_p^2=1+(alpha^2-1)v_p^2,

so |u_p|>=alpha>0. Since beta=alpha+q_alpha u_p and beta>0, q_alpha>=1 excludes u_p<=-alpha. Thus u_p>0. The recovered

    x=y(alpha-2)+2o+M_p q_r,
    s_p=x+u_p q_sigma

are positive integers. Dividing H1 and H3 by their nonzero square denominators recovers their Pell norms, while the expression definitions and H4 recover the original positive slacks and congruences. Every eliminated-domain obligation is restored.

The accepted module proof applies the pinned positive-index Pell characterization at index C and the constructive power theorem at base two and target 2o; the strict modulus M_p>2o and alpha>2 justify its inequalities and natural-subtraction adapters. It concludes 2^C=2o and hence o=2^(C-1). Completeness comes from those constructive theorems, followed by the accepted progression beta_k=beta_0+4y u_p k for k>=1. It makes q_alpha,k=q_alpha,0+4yk strictly positive and q_b,k=q_b,0+u_p k strictly increasing, while preserving the module relations with the appropriate Pell coordinates. Thus all exponents including C=1 are covered and the retained leaves, not only eliminated coordinates, vary infinitely.

This is a restatement and use of the accepted theorem, not a new proof or execution of the all-exponent number-theoretic dependency. The exact source is mathlib4 commit ac77769fabe23cb237559e7f56578dbead91499f, Mathlib/NumberTheory/PellMatiyasevic.lean, declarations Pell.matiyasevic and Pell.eq_pow_of_pell. The inert file SHA-256 is 993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a. Full accepted proof, independent audit, supporting proofs, source, attribution and license are retained under dependencies. SOURCE_PINS.json identifies every copied file. No Lean or upstream source is executed.

### Complete gap polynomial, ledger, and uniqueness

Let g1,g2,g3 be arbitrary positive integer external inputs and D=g1+g2+g3 an expression. Use positive shifted-counter witnesses A,B; two copies of (11) with (C,o)=(A,p) and (B,q), all twelve leaves disjoint; and the two compiler witnesses r,s. Add

    G1=(20g1-D)p-2D, G3=(20g3-D)q-2D.

The complete polynomial is

    Q_(M,T)=G1^2+G3^2+sum_i (H_i^A)^2+sum_i (H_i^B)^2
              +P_(M,T)(A,B;r,s).                            (12)

It has exactly three external positive inputs, 2+2*12+2=28 positive witnesses, 31 total variables, 2+2*5+5=17 residual slots, and one final equation. These are literal slots, including the zero slots at T=0. Outputs p,q are already included in the two module counts; there is no class-code witness.

A zero gives p=2^(A-1),q=2^(B-1) and, because all three gaps and p,q are positive,

    g1/D=1/20+1/(10p), g3/D=1/20+1/(10q).

Thus a zero exists exactly when the triple is encoded by natural counters a=A-1,b=B-1 through

    g1/D=1/20+(1/10)2^(-a),
    g3/D=1/20+(1/10)2^(-b),

and those counters meet the selected bounded-halting predicate. The statement applies to arbitrary positive triples; unencoded triples simply have no witness. Conversely any encoded accepted triple supplies A,B,p,q, constructive module witnesses and the unique pair (6).

The fixed gaps determine p=2D/(20g1-D) and q=2D/(20g3-D); the equations force those denominators positive. Injectivity of powers of two then determines A,B, and the compiler determines r,s. Hence the projection (A,B,p,q,r,s) is unique whenever nonempty. The full 28-witness fiber is infinite: vary the accepted module progression in either copy while keeping its C,o, the other copy, gaps and compiler pair fixed. The composition is neither single-fold nor finite-fold.

The exact degree is

    deg Q_(M,T)=max(20,deg P_(M,T)),
    deg Q_(M,T)<=max(20,4T) for T>=1,
    deg Q_(M,0)=20.                                         (13)

The accepted module's H2 contains -J^2 q_alpha^2 d_yC_plus^4 q_v^2. Its square contributes the coefficient-one degree-twenty monomial J^4 q_alpha^4 d_yC_plus^8 q_v^4, absent from every other residual square and every other block. This proves the degree lower bound independently of the compiler. If the compiler degree exceeds twenty its highest-degree part cannot be changed by the fixed degree-twenty base. The same top-square principle also gives the equality in (13).

This packet makes no new claim about physical trajectories, unencoded physical inputs, collision horizons, or physical resource counts. Reports 66–68 remain their original constructions and ledgers.

## 8. Fresh static verification and its limits

The new static_algebra.py is freshly authored standard-library exact polynomial arithmetic and declared-table fixture evaluation. It is inspected in full before execution. It imports or executes no source-packet checker, upstream code, machine interpreter, physical simulator, saved schedule, or Lean. Source proofs and audits are read as inert text only; source files are hashed for preservation.

The checker constructs the basis and expanded residuals, checks interpolation at all declared nodes, verifies the coefficient/support ceilings and exact-degree formula on selected tables, enumerates finite positive input/witness boxes for all small tables, and checks the singleton-table highest-degree claim. Its complete POWER and gap expansions use the explicitly repeated residuals (11), with fresh code and the declared exponent-zero family rather than a source implementation.

The all-input compiler theorem is proved above, not inferred from finite enumeration. Arbitrary-program table correctness is not checked by algebra or by a table fixture. The all-exponent POWER assertion is imported at its explicitly pinned theorem boundary, not inferred from finite module assignments. Evidence/results.json records actual completed checks, and the final manifest pins every deliverable.
