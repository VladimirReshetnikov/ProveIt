# A unique-witness quadratic certificate for every nonelliptic planar kernel

4 October 2026. This is a new companion corollary. It does not modify the frozen planar-kernel classification or any physical compiler. All inputs and witnesses below are ordinary positive integers.

## 1. Statement and exact input convention

Fix a rational 2-by-2 matrix A which is not infinite-order elliptic, and a bounded open convex rational polygon

    P={u in R² : h_i u<b_i, 1<=i<=m}

containing0. Discard constant guard rows, which are automatically true. Then m>=1 and every b_i>0. Let K={u:A^n u is in P for every n>=0}.

For a positive integer input triple g=(g_1,g_2,g_3), define the linear aliases

    X=2g_1-g_2-g_3,
    Y=g_1+g_2-2g_3,
    N=3(g_1+g_2+g_3).

In this note X and Y are integer aliases, not additional inputs or witnesses. The normalized input is u=(X/N,Y/N). The assumed input domain guarantees N>0. This is precisely u=(g_1/D-1/3,(g_1+g_2)/D-2/3), where D=g_1+g_2+g_3.

**Corollary.** There are an effectively computable integer q>=0 and an explicit integer-coefficient polynomial F(g_1,g_2,g_3,w_1,...,w_q), expressed as a sum of squares of affine linear forms, such that for every positive integer g:

    u is in K  if and only if
    there exists exactly one w in Z_{>0}^q with F(g,w)=0.

For invalid inputs there is no positive witness tuple. The total degree is at most two. The unsimplified construction specified below has exact degree two and is nonconstant, including its zero-witness branches. No POWER module or extra denominator, radius, sign, or selector witness is used.

Uniqueness is for each fixed integer input triple and this fixed compiled list of residuals. Different integer triples can encode the same rational normalized point. The theorem makes no minimal-degree, optimal-arity, uniform polynomial-compilation, or lower-bound claim about elliptic certificates.

## 2. The finite rational description actually needed

The companion classification supplies, on rational points, a finite conjunction

    e_j u=0                       (1<=j<=r),
    alpha_i+v_i u>0               (1<=i<=s),
    beta_k+z_k u>=0               (1<=k<=t),

with all coefficients rational. Only this rational-point equivalence is needed.

Here is why every nonelliptic branch has the required form, including the cases where the exact real kernel is not rational-polyhedral. Write B={u:the forward A-orbit is bounded}.

- B={0}: rational validity is u=0; use two equations and no inequalities
- B is an irrational line: B contains no nonzero rational vector, so rational validity again is u=0; use two equations and no inequalities
- B is a rational line: use one nonzero rational equation for B. If the scalar action on B is nonnegative, K=B intersect P; otherwise K=B intersect P intersect A^(-1)P
- B=R² and A is strictly stable: the effective finite horizon H gives K=intersection_{0<=n<=H} A^(-n)P
- B=R² and A has only real unit eigenvalues: A²=I, so K=P intersect A^(-1)P
- Nonreal unit eigenvalues of finite order d: d is 3,4,or6, and K=intersection_{0<=n<d} A^(-n)P
- Eigenvalues epsilon in {+1,-1} and 0<|mu|<1: the rational projector E=(A-mu I)/(epsilon-mu) gives K=P intersect A^(-1)P, together with Eu and epsilon Eu in closure(P). These last two lists are weak guards
- Eigenvalues epsilon in {+1,-1} and mu=0: K=P intersect A^(-1)P intersect A^(-2)P, with strict guards throughout

This covers zero and negative eigenvalues and nontrivial Jordan blocks through the bounded-orbit classification. In particular, a unit-modulus Jordan block restricts to its ordinary eigenspace, and a stable Jordan block belongs to the stable finite-horizon case. No irrational subspace is encoded by fictitious rational linear equations: the irrational-line branch is replaced by its actual rational-point kernel {0}.

The inequalities above may be redundant or repeated. They are retained as separate rows if present; this has no effect on uniqueness. Outside the two zero-kernel branches, retain all original time-zero guards, so at least one inequality remains.

## 3. Clearing denominators and the full ledger

Multiply each rational equality by its own fixed positive integer denominator to obtain an integer linear form

    E_j(g)=d_j e_j (X,Y).

For each strict row choose a fixed positive integer c_i clearing its three rational coefficients, and put

    L_i(g)=c_i(alpha_i N+v_i (X,Y)).

For each weak row similarly put

    M_k(g)=a_k(beta_k N+z_k (X,Y)).

All E_j,L_i,M_k are explicit integer homogeneous linear forms in the original three input variables. Because N>0 and all clearing factors are positive, rational membership is exactly

    E_j(g)=0 for all j,   L_i(g)>0 for all i,   M_k(g)>=0 for all k.

Introduce one positive witness p_i per strict inequality and one positive witness q_k per weak inequality, and define

    F(g,p,q)=sum_j E_j(g)^2
             +sum_i (L_i(g)-p_i)^2
             +sum_k (M_k(g)-q_k+1)^2.

The aliases are literal linear substitutions, not existentially quantified quantities.

The complete ledger is:

- Input leaves: exactly3 positive integers
- Equality residuals: r; no witnesses
- Strict inequality residuals: s; exactly s positive witnesses
- Weak inequality residuals: t; exactly t positive witnesses
- Total positive witnesses: q=s+t
- Total residual equations: r+s+t
- Final equations: one equation F=0
- Total degree: at most2; exact2 for the specified unsimplified construction
- POWER modules and all other auxiliary witnesses: zero

One convenient unreduced branch ledger, where m is the number of supplied nonconstant polygon rows, is:

- Zero or irrational B: (r,s,t)=(2,0,0)
- Rational B line, nonnegative scalar: (1,m,0)
- Rational B line, negative scalar: (1,2m,0)
- Strictly stable B=R², horizon H: (0,(H+1)m,0)
- Real semisimple unit spectrum: (0,2m,0)
- Nonreal finite order d: (0,dm,0)
- Mixed unit/nonzero stable spectrum: (0,2m,2m)
- Mixed unit/zero stable spectrum: (0,3m,0)

These are constructive counts, not minimized ones. For epsilon=+1, some parity or limiting rows coincide. Keeping them merely supplies additional uniquely forced slack coordinates.

## 4. Correctness, uniqueness, degree, and zero witnesses

For any fixed input g, every squared residual is a nonnegative integer. Consequently F=0 if and only if every residual vanishes. The witness equations force

    p_i=L_i(g),       q_k=M_k(g)+1.

These values are positive integers exactly when the associated strict and weak integer inequalities hold. Thus there is one positive witness tuple for a valid input and none for an invalid input. Equality residuals impose their equations directly and introduce no choices.

Every residual is affine linear jointly in input and witness variables, proving degree at most two. If s+t>0, a witness appears with coefficient -1 in its own residual and in no other residual. Its square therefore has coefficient1 in F, proving exact degree two. If s+t=0 in the stated recipe, the branch uses E_1=X,E_2=Y, so

    F=X²+Y²,

again nonconstant of exact degree two. More generally, a nonzero equality row stays nonzero after the substitution: the map g to (N,X,Y) is invertible over Q, with

    g_1=(N+3X)/9,
    g_2=(N-3X+3Y)/9,
    g_3=(N-3Y)/9.

For q=0, the witness space Z_{>0}^0 contains exactly the empty tuple. Thus the formula has one witness tuple precisely when X=Y=0, which on positive inputs is exactly g_1=g_2=g_3. There is no hidden existential witness in this branch.

A deliberately simplified representation can be constant on the restricted positive-input domain. For example, some kernels contain the entire normalized positive-gap triangle. Such a simplification may give a constant-zero certificate, so exact degree two is a property of the displayed construction and is not asserted to be minimal or necessary.

Finally, rescaling g by a positive integer leaves (X/N,Y/N) unchanged. It changes the integer input and generally its slack tuple. This nonuniqueness of rational encodings is unrelated to witness uniqueness for a fixed g. The theorem concerns the three native input gaps, not a separate arithmetic encoding of those gaps into one integer.

## 5. A half-open example accessible by positive gaps

This is an abstract kernel example with a test point in the normalized positive-gap triangle. The displayed P is not itself contained in that triangle and is not claimed to be a physical compiler fixture.

Take

    A=diag(1,1/2),
    P={ (u,v): -1<u<1, -1<v<1, u+v<1/6 }.

The rectangle is preserved. For the final guard, the orbit values u+2^(-n)v interpolate between u+v and the limit u. Hence

    K=P intersect {u<=1/6}.

The weak limiting face is essential. The integer cleared rows are the five strict forms

    L_1=N+X,
    L_2=N-X,
    L_3=N+Y,
    L_4=N-Y,
    L_5=N-6X-6Y,

and the one weak form M=N-6X. Thus a complete six-witness certificate is

    F=sum_{i=1}^5 (L_i-w_i)^2+(N-6X-w_6+1)^2.

Expanded linear input forms are

    L_1=5g_1+2g_2+2g_3,
    L_2=g_1+4g_2+4g_3,
    L_3=4g_1+4g_2+g_3,
    L_4=2g_1+2g_2+5g_3,
    L_5=-15g_1+3g_2+21g_3,
    M=-9g_1+9g_2+9g_3.

For g=(6,1,5), we have (N,X,Y)=(36,6,-3) and (u,v)=(1/6,-1/12). Its orbit satisfies the strict final guard at every finite time, while its limiting point (1/6,0) is outside P. The unique positive witness tuple is

    (42,30,33,39,18,1).

The last value1 encodes M=0 correctly. Replacing the weak inequality by a strict inequality would wrongly reject this input. Conversely, g=(7,1,5) satisfies every time-zero guard but has M=-9; the forced last slack is -8, so no positive witness exists.

## 6. Dependency and claim boundary

The geometric dependency is the frozen classification at

    /workspace/shared/planar-strict-kernel-classification-20261004/PROOF.md
    SHA256 70eb8f8398d474c3343493fc88c006ce91951a2eb747c9b4133c5c481b666231.

The present corollary adds only exact clearing of rational linear constraints and uniquely determined integer slack variables. Its certificate size depends on the fixed pair (A,P); a stable finite-horizon list can be large. The classification's exponential-facet family precludes inferring uniform polynomial-size explicit linear compilation.

No conclusion is drawn that degree12 is necessary in an elliptic certificate, or that degree2 is minimal here. The irrational elliptic case is excluded because its rational membership has no finite polynomial-sign description of the sort used to obtain this finite linear ledger. That sign obstruction alone is not a lower bound on existential-positive-integer polynomial degree or witness count.
