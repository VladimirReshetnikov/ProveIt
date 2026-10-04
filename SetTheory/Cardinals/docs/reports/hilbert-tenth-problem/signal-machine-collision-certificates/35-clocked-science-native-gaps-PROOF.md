# Native-gap bounded-halting certificates and exact primitive initialization

4 October 2026. This is a separate arithmetic continuation, not a numbered report. The two physical/finite-trace sources being assembled as Report 64 are preserved unchanged. Source-directory suffixes are historical working labels, not a claim that another report has been delivered.

## 1. The native-input predicate and the precise result

Fix a finite deterministic two-counter program M, its initial control state q_0, and a designated halt state H. An instruction increments either counter and has a specified successor, or tests one counter for zero and otherwise decrements it, with specified successors for both outcomes. Let E be its number of edges after splitting conditional instructions and adding one virtual absorbing halt edge h. Let Z be the number of zero edges. Thus E=I+2C+1 and Z=C when there are I increment and C conditional instructions.

The three external inputs are arbitrary positive integers g_1,g_2,g_3. Define expressions

    D=g_1+g_2+g_3,  x=g_1,  y=g_1+g_2.

In particular D is not a fourth input or a witness. Call a triple **encoded** if there exist natural integers a,b such that

    g_1/D=1/20+(1/10)2^(-a),
    g_3/D=1/20+(1/10)2^(-b).                       (1)

For a fixed integer horizon T>=0, define EncHalt_(M,T)(g) to mean that g is encoded and that M, started in q_0 with its encoded counters a,b, reaches H after at most T instructions. This is also bounded instruction-section reachability for the frozen five-signal compiler on its encoded inputs.

**Native-gap theorem.** The completely specified integer polynomial F_(M,T) below satisfies

    EncHalt_(M,T)(g_1,g_2,g_3)
    iff there are positive integer witnesses W with F_(M,T)(g;W)=0.

Its exact ledger, for the displayed construction, is

    external positive inputs: 3,
    positive witnesses: T(E+2)+54,
    residual equations: T(E+Z+4)+33,
    one final polynomial equation,
    joint total degree: exactly 12.

The same formulas for these counts include T=0, with the separate constant trace residual specified in Section 4. For T>=1 the first-halt-exactly-T version has one more residual, with unchanged witnesses and degree. For T=0 the by-horizon and exact-horizon versions agree.

The inputs g are unrestricted within the positive integers, but the predicate explicitly includes being encoded: an unencoded triple has no witness, whether or not some unrelated physical behavior from that triple reaches a halt label. This is not a theorem about arbitrary unencoded physical executions. It removes the external shifted-counter inputs and the previously external exponential initialization by paying for their enforcement within the polynomial.

T indexes a growing-arity family. It is not a free integer parameter of a single fixed-arity unbounded-halting polynomial. There is no gate-count, circuit-minimality, minimal-witness, efficient-Pell-witness, or new-universality claim.

## 2. Two paid decoding powers

Introduce positive shifted-counter witnesses A,B. Two independent instances of Section 3 have outputs P,Q and indices C=A,C=B respectively. Their conclusion is

    P=2^(A-1),  Q=2^(B-1).                         (2)

Add two residual equations

    G_1=(20g_1-D)P-2D=0,
    G_3=(20g_3-D)Q-2D=0.                          (3)

Since D,P,Q>0, these equations force 20g_1-D>0 and 20g_3-D>0; no sign witnesses are missing. Dividing (3) by 20DP and 20DQ gives precisely (1), with a=A-1 and b=B-1. Conversely any encoded triple supplies these four values and satisfies (3), and Section 3 supplies the remaining module witnesses.

There is no denominator-clearing ambiguity: the equations are ordinary integer equations, and their divisions in this proof are by positive nonzero integers. Every accepted shape has g_1/D,g_3/D in (1/20,3/20], and hence g_2/D in [7/10,9/10); the section is correctly ordered.

The outputs are forced by the input alone:

    P=2D/(20g_1-D),  Q=2D/(20g_3-D).

If they are positive integral powers of two, their natural exponents are unique. Thus A,B,P,Q are unique whenever they exist. An elementary exact decoder can reject nonpositive denominators, nonintegral quotients, and positive quotients not powers of two. This observation is not a substitute for the paid polynomial equations.

## 3. The full specialized POWER equations

Here is one module, written for a positive index leaf C and positive output leaf o; use independent copies with (C,o)=(A,P) and (B,Q). The semantic exponent is C-1, so it can be zero. No exponent leaf other than the already counted C is introduced.

The directly positive leaves are the following thirteen:

    o,w,M,g,x_p,y_p,u_p,v_p,s_p,t_p,q_b,q_v,J_p.

There are two further positive leaves α_+,β_+, defining expressions

    α=α_++1,  β=β_++1.

Finally there are eleven natural aliases

    d_wb,d_wk,d_yk,α_1,α_2,σ_1,σ_2,τ_1,τ_2,r_1,r_2,

each represented by its own positive leaf minus one. These shifts are substitutions, not additional variables or equations. All module leaves are distinct from the other module, trace witnesses, C, and native inputs. There are exactly 13+2+11=26 positive leaves **including o**, or 25 auxiliary leaves beyond o.

The fifteen residual equations of this module are:

    1.  x_p^2 - 1 - (α^2-1)y_p^2 = 0
    2.  u_p^2 - 1 - (α^2-1)v_p^2 = 0
    3.  s_p^2 - 1 - (β^2-1)t_p^2 = 0
    4.  β - 1 - 4y_p q_b = 0
    5.  β + u_p α_1 - α - u_p α_2 = 0
    6.  v_p - y_p^2 q_v = 0
    7.  s_p + u_p σ_1 - x_p - u_p σ_2 = 0
    8.  t_p + 4y_p τ_1 - C - 4y_p τ_2 = 0
    9.  y_p - C - d_yk = 0
    10. w - 2 - d_wb = 0
    11. w - C - d_wk = 0
    12. M - 2o - J_p = 0
    13. α^2 - 1 - ((w+1)^2-1)(wg)^2 = 0
    14. 4α - M - 5 = 0
    15. x_p + Mr_1 - y_p(α-2) - 2o - Mr_2 = 0.       (4)

Let R_j(C,o) denote the left side of equation j, after every stated shift. This is notation for the displayed polynomial, not an uninterpreted exponentiation predicate.

### 3.1 Exact dependency and specialization

The dependency is the pinned source theorem pair Pell.matiyasevic and Pell.eq_pow_of_pell in mathlib4 commit ac77769fabe23cb237559e7f56578dbead91499f, Mathlib/NumberTheory/PellMatiyasevic.lean. Its exact SHA-256 is

    993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a.

The source is retained inertly, with its license and attribution. The theorem statements at source lines 760–766 and 860–864 were read, as were the module derivations in the retained Report 58 and Report 60 sources. No Lean build or upstream code is run.

The generic earlier module uses base B_0>=2, exponent e>=0, k_0=e+1, and m_0=B_0·out. Here substitute B_0=2, e=C-1, k_0=C, m_0=2o. This yields exactly (4), including the constant 5 in equation 14. The positive-domain equivalence is

    there exist the 25 positive auxiliary leaves satisfying (4)
    iff o=2^(C-1),  for C,o>0.                       (5)

For soundness, equations 1–9 are the nonzero-index branch of Pell.matiyasevic: α>1, C>=1, y_p>=C, and the three Pell equations and four congruences are precisely its hypotheses. The paired natural aliases express both signs of each congruence quotient. Thus x_p,y_p are its Pell pair of index C.

Equations 10–15 give w>=2, w>=C, M>2o, the auxiliary Pell condition, the modulus identity 4α=M+5, and the required final congruence. Since w>=2 and g>=1, equation 13 implies α>w>=2. Indeed its right side is at least 1+((w+1)^2-1)w^2>w^2. Hence α-2 is an ordinary nonnegative difference, agreeing with the natural subtraction in the source theorem. Pell.eq_pow_of_pell gives 2^C=2o; cancelling 2 gives (5).

For completeness, apply the constructive power theorem to 2^C=2o. Its auxiliary g cannot be zero, as that would force α=1. Apply the constructive nonzero-index Matiyasevic theorem to the resulting Pell pair. The Pell x_p,u_p,s_p are positive. y_p>=C>=1 and v_p>0 imply q_v>0. Since β>1 and β≡1 modulo 4y_p, q_b>0. The congruence t_p≡C modulo 4y_p and 1<=C<=y_p<4y_p excludes t_p=0. The strict M>2o gives J_p>0. Every signed congruence quotient can be written as the difference of two naturals. This gives all the required positive adapters, including at C=1 (exponent zero).

The source uses natural subtraction in its Pell identities. For naturals u,v, the source equality u-v=1 is equivalent to the ordinary equality u=v+1. The interior quantities α^2-1, β^2-1 and (w+1)^2-1 are nonnegative. Thus no truncated-subtraction condition has been silently weakened or strengthened.

### 3.2 An explicit exponent-zero fixture

For C=1,o=1 one valid assignment, using natural-alias values rather than their positive adapters, is

    w=2, M=63, g=3, α=β=17,
    x_p=17, y_p=1, u_p=577, v_p=34,
    s_p=17, t_p=1, q_b=4, q_v=34, J_p=61,
    d_wk=1,

with every other natural alias zero. Thus α_+=β_+=16, d_wk's positive leaf is 2, and every other natural positive leaf is 1. All fifteen equations can be checked directly. This fixture tests the zero-exponent domain; the all-exponent equivalence is the theorem dependency above, not finite numerical evidence.

## 4. Complete bounded trace equations

Assign distinct fixed integer codes to the states. Each edge e has fixed source u_e, target v_e, and changes d_e,f_e in {-1,0,1}. An increment has one edge. A conditional has its zero edge with changes zero and its positive edge decrementing the tested counter. Add exactly one virtual halt edge h, with source and target H and both changes zero. Do not insert duplicate edges.

For T>=1 introduce positive w_(t,e) for 0<=t<T,1<=e<=E, and positive A_t,B_t for 1<=t<=T. Set

    s_(t,e)=w_(t,e)-1,  A_0=A,  B_0=B.

The trace residuals are:

    S_(t,e)=(w_(t,e)-1)(w_(t,e)-2),               TE residuals
    O_t=sum_e s_(t,e)-1,                          T residuals
    U_t=A_(t+1)-A_t-sum_e d_e s_(t,e),             T residuals
    V_t=B_(t+1)-B_t-sum_e f_e s_(t,e),             T residuals
    Z_(t,e)=s_(t,e)(A_t-1) for an A-zero edge,
             or s_(t,e)(B_t-1) for a B-zero edge, TZ residuals
    C_initial=sum_e u_e s_(0,e)-q_0,              1 residual
    C_t=sum_e v_e s_(t,e)-sum_e u_e s_(t+1,e),    T-1 residuals
    C_final=sum_e v_e s_(T-1,e)-H.                1 residual     (6)

Write R_trace for this literal list. It has T(E+Z+4)+1 entries and T(E+2) positive witnesses. At T=0 it instead has the single constant entry q_0-H and no trace witnesses; those same count formulas apply.

The selector and one-hot equations force exactly one selected edge per time. The update equations force the actual counter updates. A selected zero edge forces its tested shifted counter to be 1. A selected decrement from 1 would give a nonpositive next shifted counter, so it is forbidden without extra guard witnesses. The control equations link the selected edges from q_0 to H. Hence these equations encode precisely the deterministic computation padded at H through T steps. Conversely that padded trace supplies their witnesses. Induction shows that for fixed A,B the trace witness tuple is unique. At T=0 this is the usual empty-tuple convention.

For T>=1, first arrival at H exactly at T is enforced by the additional residual

    H_early=sum_(t=0)^(T-1) s_(t,h).              (7)

All selectors are nonnegative, so it excludes every early halt-loop use with one equation. The final control equation still forces the arrival at H. At T=0 use the same constant trace residual as before.

The halt loop is solely arithmetic padding. The physical compiler's messenger need not continue executing instructions after reaching H; this formula only asserts the physical prefix through first arrival.

## 5. The actual polynomial, correctness, and exact accounting

With all aliases expanded by their definitions, define

    F_(M,T)= G_1^2+G_3^2
             +sum_(j=1)^15 R_j(A,P)^2
             +sum_(j=1)^15 R_j(B,Q)^2
             +sum_(r in R_trace) r^2.                         (8)

The two module copies in (8) have independent internal leaves. This finite sum of explicitly listed squares is an integer polynomial; it does not require monomial expansion to define its coefficients. Fixed program data are coefficients and T fixes the finite list size. There are no quantifiers other than the declared positive leaves, no hidden division, no free exponential input, and no variable-length conjunction for fixed M,T.

Over integer witnesses, (8) vanishes iff all its residuals vanish. Section 3 then forces (2); Section 2 forces the unique encoding (1); Section 4 gives the unique padded trace to H. This proves soundness. Conversely encoded counters that halt by T give A,B,P,Q, the two constructive POWER assignments, and the trace witnesses, so every residual vanishes. This proves completeness.

The witness ledger is

    shifted initial counters A,B:              2
    P and its POWER auxiliaries:              26
    Q and its POWER auxiliaries:              26
    finite trace witnesses:              T(E+2)
    total:                           T(E+2)+54.                (9)

Equivalently count A,B,P,Q as four and the two modules' **remaining 25** leaves as fifty. Counting four plus two times twenty-six would count P,Q twice.

There are 2+30+T(E+Z+4)+1=T(E+Z+4)+33 residuals. The complete number of variables, including native inputs, is T(E+2)+57. In instruction counts the witness and residual ledgers are T(I+2C+3)+54 and T(I+3C+5)+33.

The gap residuals have degree two and the trace residuals degree at most two. After all positive shifts and the base-two specialization, POWER residuals 1–3 have degree at most four, equation 6 degree three, equations 4–5,7–8,15 at most two, equations 9–12,14 at most one, and equation 13 degree six. Specifically equation 13 has highest homogeneous part

    -w^4 g^2.

Thus the output has degree at most twelve. Its degree-twelve part is exactly

    w_A^8 g_A^4 + w_B^8 g_B^4,                              (10)

because only the two independent equation-13 residuals have degree six. In particular both displayed monomials have coefficient one and cannot cancel. The degree is jointly in all inputs and independent positive leaves; it is exactly twelve even for T=0. Constraints that later restrict those leaves are not substituted out when measuring this polynomial's degree.

The construction does **not** retain unique full witnesses. A,B,P,Q and the trace projection are unique, but whenever any full witness exists, increasing both α_1 and α_2 in the first module by the same natural integer changes no residual. Their positive adapters remain positive, and those two aliases appear only together in equation 5. Therefore this displayed formula has infinitely many full witness tuples at every accepted input. No finite-fold or single-fold representation is claimed.

## 6. Exact primitive integer realization of every counter pair

Let a,b>=0 and m=max(a,b). Define integers

    U=2^m+2^(m-a+1),
    W=2^m+2^(m-b+1),
    V=20·2^m-U-W.                                          (11)

They are positive, and (U,V,W) realizes (1) at scale 20·2^m. Indeed U/(20·2^m)=1/20+1/(10·2^a), and similarly for W. The middle gap is positive because U,W<=3·2^m, so V>=14·2^m.

Put c=gcd(U,V,W). Its exact value is

    c=1,  if (a,b)=(0,0);
    c=4,  if (a,b)=(1,1);
    c=2,  if {a,b}={0,1};
    c=10, if m>=2 and a≡b≡3 (mod 4);
    c=2,  otherwise (m>=2).                                (12)

For m=0 the triple is (3,14,3). For m=1 the equal case is (4,32,4), and the mixed cases are (6,30,4) or (4,30,6). These give the first three lines directly.

Suppose m>=2. At least one of a,b equals m; its corresponding U or W is 2^m+2 and has exact 2-adic valuation one. Both U and W are even, as is V, so c has exact 2-adic valuation one. Also c divides U+V+W=20·2^m. Its only possible odd prime factor is 5, with exponent at most one. Finally

    5 divides U iff 5 divides 2^a+2 iff a≡3 (mod 4),

using U=2^(m-a)(2^a+2) and the exact order four of 2 modulo 5. The same holds for W. If both are divisible by 5 then V is as well because their total is divisible by 5. This proves the last two lines of (12).

The primitive triple and its total scale are therefore

    g*=(U/c,V/c,W/c),  D_min=20·2^m/c.                       (13)

Every positive integer triple encoding a,b is a unique positive integer multiple of g*. To prove this without assuming a rational multiplier is integral, its normalized coordinates show it is λg* for a positive rational λ. Since gcd(g*)=1, integer Bézout coefficients form an integer linear combination of the entries of g* equal to 1. Applying the same coefficients to the integer entries λg* gives λ itself as an integer. Hence D_min is the exact smallest positive integer total scale for this specific encoding. This is not a minimum over other encodings or physical constructions.

### 6.1 Exact bit-height cost and its interpretation

Let bit(n)=floor(log_2 n)+1 for positive integers. The scale's exact bit length is

    bit(D_min)=5                         at (a,b)=(0,0),
    bit(D_min)=4                         at (a,b)=(1,1),
    bit(D_min)=5                         in the mixed m=1 cases,
    bit(D_min)=m+2                       if m>=2 and a≡b≡3 (mod 4),
    bit(D_min)=m+4                       in all other m>=2 cases.   (14)

For m>=2, equations (12)–(13) also give the simple scale bound

    2^(m+1)<=D_min<=10·2^m.

The largest gap is always g*_2: from (1), g*_2>=7D_min/10 while each endpoint gap is at most 3D_min/20. Consequently

    bit(D_min)-1 <= max_j bit(g*_j) <= bit(D_min).            (15)

Thus the primitive integer gap description has bit height m+O(1) and numeric height Θ(2^m). If m>=1 has binary length ℓ=floor(log_2 m)+1, then 2^(ℓ-1)<=m<2^ℓ: this bit height is Θ(2^ℓ) as a function of the largest counter's own binary length. It is Θ(m), not Θ(log m). This is an exact cost of the chosen exponential coordinate encoding, not a general lower bound for simulations, encodings, counter algorithms, or Diophantine witnesses. The potentially much larger Pell witnesses have no height bound here.

The decoding bound P,Q<=2D is immediate from (3), since their denominators are positive integers. Hence encoded counters satisfy a,b<=floor(log_2(2D)). The elementary decoder can recover them with polynomial-time arithmetic in the input gaps' binary length. This does not say that producing the much longer gap representation from binary counter values is polynomial-time in their bit length, nor that deciding unbounded halting is possible.

## 7. Physical transport, literature scope, and evidence limits

The retained physical theorem constructs, for each fixed M, a finite rational-speed rule table with exactly five live signals and fixed ordered instruction sections. On every state encoded by (1), it simulates the specified counter transition with at most 32 binary collisions and elapsed time strictly between D and 10D. It preserves D. Its designated halt is a full section. Therefore the theorem in Section 1 transfers exactly to this encoded physical predicate. If first halt occurs at k>0, its elapsed physical time lies strictly between kD and 10kD, and its physical prefix has at most 32k collisions. At k=0 the initial section already has the halt label. Neither virtual arithmetic padding nor a fixed physical collision horizon is asserted.

The literature positioning stays bounded. Finite counter traces and sum-of-squares conjunctions are elementary; the exact instruction semantics are standard, e.g. A. Dudenhefner, Certified Decision Procedures for Two-Counter Machines, FSCD 2022, Definition 2 and Theorem 6, https://doi.org/10.4230/LIPIcs.FSCD.2022.16. Five-live-signal counter simulation has the earlier Durand-Lose precedent documented in the retained physical source; this continuation does not claim it as new. The only substantive arithmetic theorem imported is the explicit pinned constructive Pell pair above, whose source is https://github.com/leanprover-community/mathlib4/blob/ac77769fabe23cb237559e7f56578dbead91499f/Mathlib/NumberTheory/PellMatiyasevic.lean. There is no novelty, priority, exhaustive-search, minimality, or macro-free operation-count claim.

The fresh checker is independent of all author/upstream code. It uses explicit integer sparse-polynomial arithmetic for the complete positive-adapted formula and checks leaf counts, residual counts, degree, and the exact degree-twelve monomials for declared finite graphs and horizons. It evaluates the complete exponent-zero POWER fixture and manually supplied finite trace fixtures, including virtual padding and exact-halt exclusion. It checks (11)–(15) over a finite integer grid and verifies exact input decoding and scaling there. These finite checks support the displayed all-input proofs; they do not replace them.

No physical simulator, next-collision search, saved accepting schedule, native machine interpreter, source packet script, or Lean build is executed. Every copied dependency is read only as inert text. The manifest records their origin and byte hashes and the fresh evidence's hash. This packet is a completed candidate proof and static-evidence continuation awaiting independent review, not a newly numbered or delivered report.
