# Three positive witnesses for bounded two counter halting

4 October 2026. This is a new, separate arithmetic continuation. It does not modify or renumber the retained physical, finite-trace, or native-gap packets. The main theorem is independent of the physical compiler and of the Pell dependency. The optional native-gap corollary imports the two explicitly identified POWER modules.

## 1 The result and its scope

Fix a finite deterministic two-counter program M, an initial control state q_0, and a designated halt state H. The counters are natural integers. An instruction either increments one counter by one and moves to its specified successor, or tests one counter for zero and takes a specified zero successor, otherwise decrementing that counter by one and taking a specified positive successor. The other counter is unchanged. Control states may repeat and programs may loop forever.

For every fixed integer T>=0 there is a completely specified integer polynomial

    P_(M,T)(A,B;j,r,s)

with two positive inputs A,B, representing initial counters a=A-1,b=B-1, and exactly three positive witness variables j,r,s, such that

    M reaches H within T transitions from (q_0,A-1,B-1)
    iff there exist j,r,s>0 with P_(M,T)(A,B;j,r,s)=0.             (1)

For each fixed positive input pair, the witness tuple is unique if it exists. The polynomial is the sum of six explicitly specified squares. Some of these six listed residuals can coincide or vanish identically, so six is a presentation count, not a count of independent or nonzero constraints.

Put K=T+1 and N=K^2. Its joint total degree, including A and B, satisfies

    deg P_(M,T) <= 4N-4, for T>=1;
    deg P_(M,0) = 2.                                           (2)

A first-halt-exactly-T version has precisely the same witness and residual counts and the same bounds. It changes only a finite acceptance set used in the coefficients. The degree bound in (2) is not asserted to be an equality, and no degree-raising terms are added merely to make it one.

These are fixed-arity polynomial **families**. T is an index used to construct a finite table, degrees, and coefficients; it is not a free input of one fixed polynomial. The construction trades the prior trace encoding's growing number of witnesses for growing polynomial degree and coefficient size. It is not a fixed-polynomial representation of unbounded halting, and it gives no new single-fold MRDP result, universal-polynomial bound, variable-minimality result, or priority claim.

## 2 The exact clipping lemma

Extend the native semantics by leaving the control state and both counters unchanged after H. This is virtual bookkeeping, not an assertion about post-halt physical motion. For a native input (a,b), let the representative input be

    (a*,b*)=(min(a,T),min(b,T)).                                (3)

**Clipping lemma.** The original and representative computations have exactly the same control states q_0,...,q_T, and select the same transition branches at times 0,...,T-1. Consequently they have the same first arrival at H whenever that arrival is at most T.

**Proof.** At time zero their states agree. Suppose inductively that their states and selected branches agree through the first t transitions, where 0<=t<T. Each counter then has received exactly the same sequence of changes in the two computations.

For a counter whose original value is below T, its representative was identical, so its current values are identical. For a counter whose original value is at least T, its representative started at T. Since each transition decreases it by at most one, the representative's value at time t is at least T-t>0. The original value equals that representative value plus the nonnegative constant difference between their initial values. Thus both are positive. Whichever counter is tested, its zero/nonzero outcome is the same in both computations. The instruction therefore takes the same branch and performs the same changes; increment and halt instructions also agree. This proves the induction through transition T and establishes the entire control prefix. First-halt times in that prefix depend only on these control states. QED.

The strict inequality is needed only at instruction entry times t<T. A representative tail counter may reach zero **after** transition T, while its original counterpart stays positive. That does not invalidate (1): there is no further zero test in the prescribed prefix. We do not claim equality of final counters, final zero status, or control beyond time T.

At T=0 there are no transitions to compare. Both computations start in q_0, so clipping both counters to zero is harmless. If q_0=H, every input halts by every horizon, and first halting occurs at time zero. Otherwise no input halts at time zero. Loops do not affect the induction: it is over the fixed finite prefix, without any acyclicity assumption.

In shifted positive coordinates, (3) is exactly

    u=min(A,K), v=min(B,K), K=T+1.                              (4)

Thus T+1 is sufficient; the more conservative shifted threshold T+2 is unnecessary. The native threshold T cannot be decreased uniformly for this instruction model when T>=1. Consider the single nonhalt instruction “if a=0 then H, else decrement a and return here.” Starting with a=T-1 first halts on transition T, while starting with a=T first halts on transition T+1. Clipping at T-1 would merge these two answers. This is a sharpness statement for this uniform clipping threshold, not a lower bound on polynomial degree or witness number.

## 3 A finite table for each horizon

For u,v in {1,...,K}, encode the pair by

    i=(u-1)K+v in {1,...,N}.

Conversely define fixed integers

    u_i=1+floor((i-1)/K),
    v_i=1+((i-1) mod K).                                      (5)

Let S_(M,T) be the subset of {1,...,N} for which M, started with native counters (u_i-1,v_i-1), first reaches H at some time 0<=t<=T. Let S_exact_(M,T) instead contain precisely those indices whose first halt is at time T.

Both sets are finite and effectively determined: in principle evaluate each of the N specified native initial configurations for at most T transitions, checking the initial state before the first transition. This is a mathematical definition of the finite coefficient table. No native interpreter is executed in preparing this packet. At most NT native transitions suffice for the table-construction algorithm; counters in those evaluations are at most 2T. No unbounded halting decision is invoked.

If q_0=H, S_(M,T) is the full set for every T, while S_exact_(M,T) is empty for T>0. At T=0 both versions are {1} if q_0=H and empty otherwise.

For the rest of the construction let S mean either chosen table. By the clipping lemma, membership of the unique clipped class (4) in S is equivalent to the corresponding requested halting predicate on all positive inputs A,B, including arbitrarily large inputs.

## 4 Integer interpolation with explicit coefficients

Let d=(N-1)!, taking 0!=1, and let z be an indeterminate. Define

    L_i^0(z)=(-1)^(N-i) binom(N-1,i-1)
               product_(1<=h<=N, h!=i) (z-h),

    U_0(z)=sum_(i=1)^N u_i L_i^0(z),
    V_0(z)=sum_(i=1)^N v_i L_i^0(z).                           (6)

These formulas have integer coefficients and degree at most N-1. Indeed

    product_(h!=i)(i-h)=(-1)^(N-i)(i-1)!(N-i)!,

so L_i^0(i)=d and L_i^0(h)=0 at every other node h. Consequently

    U_0(i)=d u_i, V_0(i)=d v_i, 1<=i<=N.                       (7)

Equivalently U_0=dU and V_0=dV for the usual rational Lagrange interpolants. There is no rational coefficient in the final formula and no denominator depends on an input or a witness. The interpolation identities in (7) have just been proved directly. Their standard general form is recorded in NIST's [Digital Library of Mathematical Functions, Section 3.3(i)](https://dlmf.nist.gov/3.3#i).

Define two more integer polynomials

    R(z)=product_(i=1)^N(z-i),
    H_S(z)=product_(i in S)(z-i),                              (8)

where the empty product is 1. The second polynomial's roots are exactly the accepted classes, including the case that there are no roots.

## 5 Six residuals and the uniqueness proof

Use only the three positive integer witnesses j,r,s. Define the six residuals

    R_0 = R(j),
    R_A = (dA-U_0(j))(U_0(j)-dK),
    L_A = dA-U_0(j)-d(r-1),
    R_B = (dB-V_0(j))(V_0(j)-dK),
    L_B = dB-V_0(j)-d(s-1),
    R_H = H_S(j).                                             (9)

The promised single integer polynomial is

    P_(M,T)=R_0^2+R_A^2+L_A^2+R_B^2+L_B^2+R_H^2.             (10)

Here M and T determine S,K,N,d and the coefficients in (6)-(8). They do not add polynomial variables. The polynomial is fully defined by these finite formulas; expanding every monomial is not needed to specify it.

**Soundness.** A sum of integer squares is zero exactly when all six residuals vanish. R_0=0 first forces j to be one of 1,...,N. Let u=u_j,v=v_j. Since d>0, the A residuals and (7) give

    (A-u)(u-K)=0, A-u=r-1>=0.                                 (11)

If u<K, the first equation forces A=u. If u=K, the second forces A>=K. These are exactly the two cases u=min(A,K). Conversely no smaller u can represent a larger A, and no tail representative u=K can represent A<K. The same argument gives v=min(B,K). Thus j is the unique encoding of the actual clipped input, and R_H=0 places it in S. Section 3 now gives the requested halting assertion.

**Completeness.** If the requested halting assertion is true, take u=min(A,K),v=min(B,K) and put

    j=(u-1)K+v, r=A-u+1, s=B-v+1.                            (12)

These are positive integers. The range and acceptance residuals vanish by the table definition, the classification products vanish because each coordinate is either its exact input or K, and the linear residuals vanish by (12). Hence (10) is zero.

**Uniqueness.** The soundness argument fixes u and v, hence j. Each linear residual then uniquely fixes its slack, exactly as in (12). There is no choice of sign, interpolation denominator, table entry, inactive selector, or additional witness left free. In particular

    1<=j<=N, 1<=r<=A, 1<=s<=B.                               (13)

The unbounded sizes of the input counters are paid for only by the two deterministic positive slacks. No counter values along the trace are witness variables in this construction.

**Horizon zero.** At T=0, K=N=d=1 and U_0=V_0=1. The classification products are identically zero, the two linear residuals are A-r and B-s, and R_0=j-1. If q_0=H, then H_S=j-1, giving

    P_(M,0)=2(j-1)^2+(A-r)^2+(B-s)^2.

Otherwise H_S=1, giving

    P_(M,0)=(j-1)^2+(A-r)^2+(B-s)^2+1.

The accepted inputs have the unique tuple (1,A,B); the rejected version has none. Both polynomials have degree two. Retaining three witnesses at T=0 keeps the family arity uniform; it is not a claim that three are necessary for this trivial horizon.

## 6 Degree and coefficient costs

For T>=1, N>=4. R_0 has degree N, R_H has degree |S|<=N, each linear slack residual has degree at most N-1, and each classification product has degree at most 2N-2. After squaring,

    deg P <= max(2N,4N-4,2N-2)=4N-4.

All degrees are joint in A,B,j,r,s. This establishes (2) without treating an input as a coefficient. The proof permits cancellations in U_0 or V_0 and does not force equality in the bound.

Here is an explicit coefficient-height bound valid even at T=0. For an integer polynomial f let ||f||_1 be the sum of the absolute values of its coefficients. Set

    L=K 2^(N-1)(N+1)!.

The coefficient norm of a product of factors z-h is at most the product of 1+h. From (6), the binomial sum 2^(N-1), and u_i,v_i<=K,

    ||U_0||_1,||V_0||_1 <= L,
    ||R||_1,||H_S||_1 <= (N+1)! <= L,
    dK<=L, d<=L.                                             (14)

Coefficient norms are subadditive and submultiplicative. Therefore each classification product has norm at most 4L^2, and each linear slack residual has norm at most 4L. Consequently

    ||P_(M,T)||_1 <= 2L^2+2(4L^2)^2+2(4L)^2
                  =32L^4+34L^2 <=66L^4.                      (15)

Every coefficient c has |c|<=66L^4. Its unsigned magnitude needs at most

    7+4 ceil(log_2 L)

bits when c is nonzero; add a sign bit if the storage format requires one. Thus coefficient magnitude bit length is O(N log(N+1))=O(T^2 log(T+2)). This bound is uniform in M because M affects only S, a subset of the same N-node set. No polynomial witness-height estimate is needed for the main theorem beyond (13).

The family has constant witness arity but not constant description size or constant degree. In particular, when T is supplied in binary to a polynomial-generation procedure, the displayed degree need not be polynomial in that binary input length. The finite preprocessing and changing coefficients are essential, explicit costs.

### 6.1 Sparse support and the size of an expanded description

The fully expanded polynomial also has only O(N) nonzero monomials. Here is an explicit bound, not a dense five-variable estimate. Write m=N-1 and view U_0,V_0 as univariate polynomials in j of degree at most m. The first classification residual has the form

    R_A=A f_A(j)+g_A(j),
    f_A=d(U_0-dK), g_A=-U_0(U_0-dK),

with degrees at most m and 2m respectively. Its square therefore has only a pure-j part of degree at most 4m, an A part of j-degree at most 3m, and an A^2 part of j-degree at most 2m. The B residual has the identical form with B,V_0.

Likewise L_A=dA-dr+(d-U_0(j)). Its square has only a pure-j part, an A part, an r part, and the three monomials A^2,r^2,Ar. The coefficient of r has j-degree at most m. The B slack gives the analogous B,s terms. Finally R_0^2 and R_H^2 are pure-j polynomials of degree at most 2N.

For T>=1, 2N<=4m. Grouping all contributions into disjoint monomial types gives the complete support ceiling:

    pure j powers:                         4m+1
    A^2 or B^2 times j powers:          2(2m+1)
    A or B times j powers:             2(3m+1)
    r or s times j powers:               2(m+1)
    r^2, s^2, Ar, Bs:                         4
    total:                         16m+11=16N-5.              (16)

Cancellations can only reduce this count. For T=0 the explicit formulas in Section 5 each have nine nonzero monomials. No monomial contains both A and B, both r and s, or any other undeclared combination of the four nonselector variables.

Store each nonzero coefficient as a signed binary integer and each of its five exponents in binary. By (2), (15), and (16), a straightforward fully expanded description has O(N^2 log(N+1)) bits, equivalently O((T+1)^4 log(T+2)). This is an upper bound for this storage convention, not an optimal description-size claim. The finite acceptance table itself is exactly N Boolean values for either selected predicate; converting that table to coefficients incurs the displayed costs.

For completeness, a direct algebraic construction forms each of the N basis products in (6) by repeated multiplication by a linear factor, using O(N^2) integer arithmetic operations per product and O(N^3) overall. Adding and scaling those coefficient vectors, and expanding the six squares with ordinary univariate convolution and the fixed support types above, requires no more than O(N^3) further integer arithmetic operations. Coefficient intermediates in this straightforward construction have O(N log(N+1)) magnitude bits by the same product and triangle bounds as (14)-(15). These are bounds on integer arithmetic operations, not unit-cost bit complexity. Together with the at-most-NT native transitions needed in principle for the table, they make the dependence on T explicit; no polynomial-time-in-log(T) claim is made. The prohibited native table interpreter is not executed here.

## 7 What cannot be concluded from the family

For fixed M the ordinary statement “M halts on (a,b) iff some horizon T accepts” remains true. However, the expression P_(M,T) denotes a different polynomial for each T. Existentially writing “there is a T” outside this family does not turn its varying coefficients, factorials, products, or acceptance tables into terms of a fixed polynomial.

No module here encodes the map T to the coefficient table inside one fixed Diophantine equation. No uniqueness assertion for an unbounded-horizon fixed-polynomial formula follows. Such a formula would also need to account for varying horizons and their certificates; first-halt tables do not supply that missing uniform arithmetic encoding.

The result is elementary finite-horizon compression by finite classification and interpolation. No exhaustive literature survey, novelty claim, claim of optimal three-witness arity, or lower bound against fewer witnesses is made. For the machine instruction semantics and the importance of choosing an exact instruction set, see A. Dudenhefner, [Certified Decision Procedures for Two-Counter Machines, FSCD 2022](https://doi.org/10.4230/LIPIcs.FSCD.2022.16). Its fixed fall-through instruction model is included by the freely specified successors used here. The present clipping and polynomial proof stand on their own; that paper is not cited as establishing the new displayed ledger.

## 8 Composition on three positive native gaps

This section uses the two paid POWER modules retained in `dependencies/native_gap_PROOF.md`, Section 3. It replaces only that packet's finite-trace polynomial by (10). The earlier native-gap packet is unchanged.

The external inputs are arbitrary positive integers g_1,g_2,g_3. Write D=g_1+g_2+g_3 as an expression, with no new variable. An input is called encoded if there are natural a,b with

    g_1/D=1/20+(1/10)2^(-a),
    g_3/D=1/20+(1/10)2^(-b).                                  (17)

The predicate is: the gaps are encoded and M halts by T, or first halts exactly at T, on those encoded counters. It is not a claim about arbitrary physical executions from unencoded gap triples.

Introduce positive witnesses A,B and two independent module outputs p,q. Each module takes a positive index C, respectively A or B, and forces its positive output o to equal 2^(C-1). To make the composition explicit, the full module is repeated below.

### 8.1 The counted POWER leaves and all fifteen residuals

One module has thirteen directly positive leaves

    o,w,M_0,g,x_p,y_p,u_p,v_p,s_p,t_p,q_b,q_v,J_p,

two positive leaves alpha_+,beta_+, with expressions

    alpha=alpha_++1, beta=beta_++1,

and eleven natural aliases

    d_wb,d_wk,d_yk,alpha_1,alpha_2,sigma_1,sigma_2,
    tau_1,tau_2,rho_1,rho_2,

each defined as its own distinct positive leaf minus one. There are 26 positive leaves including o, or 25 auxiliary leaves beyond o. C is not a module leaf; it is the already-counted A or B. The module parameter M_0 is a leaf, unrelated to the fixed counter program M.

Its residuals are

    E_1 = x_p^2-1-(alpha^2-1)y_p^2,
    E_2 = u_p^2-1-(alpha^2-1)v_p^2,
    E_3 = s_p^2-1-(beta^2-1)t_p^2,
    E_4 = beta-1-4y_p q_b,
    E_5 = beta+u_p alpha_1-alpha-u_p alpha_2,
    E_6 = v_p-y_p^2 q_v,
    E_7 = s_p+u_p sigma_1-x_p-u_p sigma_2,
    E_8 = t_p+4y_p tau_1-C-4y_p tau_2,
    E_9 = y_p-C-d_yk,
    E_10 = w-2-d_wb,
    E_11 = w-C-d_wk,
    E_12 = M_0-2o-J_p,
    E_13 = alpha^2-1-((w+1)^2-1)(wg)^2,
    E_14 = 4alpha-M_0-5,
    E_15 = x_p+M_0 rho_1-y_p(alpha-2)-2o-M_0 rho_2.             (18)

All aliases in (18) are substitutions, not additional variables or equations. All leaves in its two copies are distinct from each other, the native gap inputs, A,B, and j,r,s.

The imported equivalence is

    for C,o>0, there exist the 25 positive auxiliary leaves
    with every E_i=0 iff o=2^(C-1).                            (19)

Its precise primary dependency is `Pell.matiyasevic` and `Pell.eq_pow_of_pell` in mathlib4 commit ac77769fabe23cb237559e7f56578dbead91499f, `Mathlib/NumberTheory/PellMatiyasevic.lean`. The retained inert source has SHA-256 993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a. The theorem statements at lines 760-766 and 860-864 were inspected as text. No Lean build or upstream source execution is used.

For clarity, (19) uses the positive-index branch with Pell index C, not C-1. Equations E_1 through E_9 are its Pell characterization, and E_10 through E_15 specialize the power theorem to base 2 and target 2o. They conclude 2^C=2o and hence o=2^(C-1). E_13, w>=2 and g>=1 imply alpha>w>=2, so alpha-2 agrees with natural subtraction. Positive paired quotient leaves represent signed congruence quotients. Completeness and all positive-domain adapters, including C=1, are detailed in the retained native-gap proof. Thus this section depends on that stated number-theoretic theorem, rather than pretending a finite fixture proves exponentiation for all C.

### 8.2 The complete composed polynomial

Add the two gap residuals

    G_1=(20g_1-D)p-2D,
    G_3=(20g_3-D)q-2D.                                        (20)

Use (18) with (C,o)=(A,p) and (B,q). Write E_i^A,E_i^B for their fully shifted residuals. Define

    F_(M,T)=G_1^2+G_3^2
             +sum_(i=1)^15 (E_i^A)^2
             +sum_(i=1)^15 (E_i^B)^2
             +P_(M,T)(A,B;j,r,s).                            (21)

The source equations (18)-(20) and the six squares in (10) specify every term. There is no uninterpreted power predicate in (21).

**Correctness.** A zero of (21) gives p=2^(A-1),q=2^(B-1) by (19). Since D,p,q are positive, (20) gives positive denominators and precisely (17) with a=A-1,b=B-1. Section 5 then gives the chosen bounded-halting predicate. Conversely an encoded input and accepted computation give these A,B,p,q, the constructive POWER witnesses, and the unique triple (12), making every square zero.

**Exact ledger for the displayed construction, for every T>=0:**

    positive external inputs:                           3
    shifted-counter witnesses A,B:                      2
    two POWER copies, including p and q:           2 x 26
    compressed bounded witness triple j,r,s:            3
    total positive witnesses:                          57
    total variables including the external inputs:     60
    residual entries:                        2+30+6 = 38
    final equations:                                    1

The first-halt-exactly-T version has the same counts. As in the main theorem, these are literal presentation counts; identically zero residual slots are not deleted at T=0.

The gap residuals have degree two. The two E_13 residuals have degree six, with leading monomials -w_A^4 g_A^2 and -w_B^4 g_B^2; every other POWER residual has degree at most four. Their squared degree-twelve monomials w_A^8 g_A^4 and w_B^8 g_B^4 have coefficient one and cannot cancel with P, which uses none of those module leaves. It follows that

    deg F_(M,T)=max(12,deg P_(M,T)),
    deg F_(M,T)<=max(12,4(T+1)^2-4) for T>=1,
    deg F_(M,0)=12.                                         (22)

For the equality, if deg P>12 its top degree part cannot be affected by the degree-twelve base. If deg P<=12 the indicated independent degree-twelve monomials remain. This does not turn the upper bound in the second line into an equality. The fixed POWER/gap base has coefficients independent of M,T, so adding it preserves the O(T^2 log(T+2)) coefficient-bit bound, up to a fixed additive contribution to the coefficient norm.

**Uniqueness stops at the projection.** For a given encoded gap triple, (20) fixes

    p=2D/(20g_1-D), q=2D/(20g_3-D).

Their powers-of-two exponents uniquely determine A,B; Section 5 then fixes j,r,s. Thus A,B,p,q,j,r,s are unique whenever witnesses exist. The **full 57-tuple is not unique or finite-fold**: increasing the natural aliases alpha_1 and alpha_2 in the first module by the same nonnegative integer preserves every residual and positivity. They occur together only in E_5. Hence any accepted input has infinitely many full tuples in this displayed native-gap construction.

### 8.3 Conditional physical transport

On the encoded inputs (17), the retained five-signal physical theorem identifies one native transition with one ordered instruction section of the fixed compiler. Subject to that imported physical theorem, (21) is therefore an encoded-input bounded instruction-section reachability certificate. If first halt occurs at k>0, the retained physical bounds are elapsed time strictly between kD and 10kD and at most 32k binary collisions. At k=0 the initial section is already halted.

This continuation does not re-audit the physical proof, does not execute a physical simulator, does not assert arbitrary unencoded physical halting, and does not treat a fixed collision count as a native instruction horizon. The native three-witness theorem in Sections 1-7 needs no physical theorem at all.

## 9 Finite evidence and reproducibility limits

The new `static_algebra.py` was read in full before execution. It uses exact sparse integer polynomial arithmetic authored for this packet. It does not import or execute any prior packet's code, source-author program, machine interpreter, physical simulator, schedule search, or Lean.

It constructs interpolation and polynomial coefficients, checks all interpolation nodes for T=0,...,6, enumerates declared finite acceptance tables, verifies the six-entry/three-witness ledger and coefficient norm bounds, and exhausts candidate class codes with their forced slacks over finite input grids. For N=1 and N=4 it separately brute-forces positive witness boxes for every acceptance subset. Such enumeration is enumeration of polynomial assignments, not execution of counter transitions.

The hand-declared program fixtures are:

1. An initially halted state, with full by-horizon acceptance, and empty exact-T acceptance for T>0
2. A nonhalting initial state at horizon zero, with empty acceptance
3. The one-state decrement/zero-test loop of Section 2, which first halts at a+1; at T=3 its accepted codes are 1,...,12 for by-horizon acceptance and 9,...,12 for exact acceptance
4. An increment instruction returning to itself, with H unreachable and an empty acceptance table

These fixture tables follow from their displayed elementary descriptions. The checker receives them as literal sets; it does not discover them by stepping a program.

The checker also expands the full native-gap composition for several horizons and table choices, checks 57 leaves and 38 residual entries, checks the retained degree-twelve module monomials, and evaluates the complete exponent-zero fixture at (g_1,g_2,g_3)=(3,14,3). A common quotient-pair shift explicitly verifies full-witness nonuniqueness in that fixture. The all-input main theorem is the proof above; the all-exponent statement in the composition is the pinned theorem dependency, not an inference from these finite checks.

Exact evidence counts, actual small-instance degrees, maximum coefficient bit lengths, and checker hashes are recorded in `evidence/static_results.json`. Source copies are retained inertly, with hashes, provenance, and the mathlib license in `SOURCE_PINS.json`. The original source packets are left unchanged.
