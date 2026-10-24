# Independent review of the refined batched Pell equation

> **Historical checkpoint, superseded.** This review records the earlier common-certificate construction with natural comparison progression coordinates. It predates the final signed-index theorem and the completed recurrence/source refinements, and is retained as an audit trail. Its natural S,R discussion is not the final domain specification. Use `BATCHED_PELL_THEOREM.md`, `SIGNED_INDEX_THEOREM.md`, `SIGNED_INDEX_INDEPENDENT_REVIEW.md`, and the release receipts for the final equation: 1,873 unrestricted integer variables, 1,468 quadratic residuals, and 77,523 collected monomials. The historical argument below is unchanged.

## Scope and inspected implementation

This review checks the universal mathematical transformation used by `build.py` under `output/con_zfc_batched_pell`, as inspected on 2026-10-24 UTC. It independently compares the construction with the pinned `PellRepresentation.finiteCriterion` and the positive-power criterion from `PowerRepresentation.lean`. It does not independently reprove the source C222/refutation calibration or certify every coefficient in the exported quartic. No Lean or object-language ZFC proof was run.

## Refined certificate

For a nonempty finite list of positive power calls m_i=n_i^{k_i}, group syntactically identical exponent expressions. All n_i,k_i,m_i are natural, n_i,k_i>=1. Define

    W = sum_i(n_i+k_i),
    A = 2 + sum_i m_i + g,       g natural.

The bootstrap coordinate Z is signed. Impose

    Norm(W+1,A,WZ).

For every distinct exponent k_j, use natural x_j,e_j,s_j,r_j and set

    X_j=x_j+1,  Y_j=k_j+e_j.

With natural u,b and signed v, set

    P=product_jY_j, U=u+2, V=4P^2 v,
    B=1+4P(b+1),
    S_j=X_j+U s_j, R_j=k_j+4Y_j r_j.

Impose

    Norm(A,U,V),  B=A modU,
    Norm(A,X_j,Y_j), Norm(B,S_j,R_j).

For each call, T_i is now a polynomial abbreviation rather than an extra input:

    T_i=2An_i-n_i^2-1,
    X_j+Y_j n_i = Y_j A+m_i modT_i.

Here Norm(a,x,y) means x^2-(a^2-1)y^2=1. Congruences use signed quotient witnesses. No absolute value or division occurs in these polynomial definitions.

## Soundness: positivity and the deleted gap variables

W>=n_i+k_i>=2 and A>=2. The bounding norm excludes Z=0, because otherwise A^2=1. Thus |Z|>=1, and

    A^2=1+W(W+2)W^2 Z^2>W^2.

Consequently A>W>=n_i and A>1. The common A expression also gives A>=m_i+2. For any natural n_i>=1,

    T_i-A=(n_i-1)(2A-n_i-1)+(A-2)>=0.

Therefore T_i>=A>m_i>=0. This proves, before any power identity is used, both positivity of the polynomial modulus and the strict output bound previously carried by a private gap. In particular, ordinary A-n_i coincides with truncated natural subtraction. The argument uses the bootstrap norm and natural-domain guards; it would be invalid to omit either.

Every Y_j>=k_j>=1, hence P>0. U>=2 makes V=0 impossible in Norm(A,U,V), since V=0 would give U^2=1. Thus |V|>0. Furthermore Y_j^2 divides |V| for every j, and B=1 mod4Y_j with B>1. Use |V| in the standard finite Pell-index certificate; the norm is unchanged by this sign choice. The displayed definitions already give S_j=X_j modU and R_j=k_j mod4Y_j. All X_j,Y_j,S_j,R_j,U,B are natural. Thus the finite Matiyasevic criterion gives

    X_j=X_A(k_j), Y_j=Y_A(k_j).

For the power criterion use |Z| in the common bounding norm. Its other hypotheses now follow: n_i,k_i<=W, 2An_i=T_i+n_i^2+1, m_i<T_i, A>n_i, and the power congruence. Hence every m_i=n_i^{k_i}.

No completeness assumption or expected value of m_i was used in this argument. In particular A's dependence on all m_i does not create a soundness circularity.

## Completeness: a valid dependency order

First evaluate the original finite arithmetic/macro DAG at its intended inputs, obtaining every true m_i,n_i,k_i. This requires the syntactic dependency check that no new batch auxiliary occurs in any original macro argument. Then choose W and an integer r>=1 so large that

    A=X_{W+1}(Wr)>=2+sum_i m_i.

Such r exists by Pell growth. Since the Pell recurrence modulo W at base W+1 gives Y_{W+1}(t)=t modW, the integer

    Z=Y_{W+1}(Wr)/W

exists. Put g=A-2-sum_i m_i>=0. The common bootstrap norm holds. Set X_j=X_A(k_j),Y_j=Y_A(k_j),x_j=X_j-1,e_j=Y_j-k_j. All are in the required domains. The standard binomial/Pell congruence behind the positive-power criterion gives the displayed power congruences; the preceding elementary argument supplies T_i>m_i for this choice of A.

Now P is fixed. The determinant-one Pell recurrence matrix is invertible modulo 4P^2. Some positive exponent L therefore makes it the identity modulo 4P^2. Set U=X_A(L), V=Y_A(L), u=U-2, v=V/(4P^2). U>=A>=2 and V>0, so these values have the required domains and satisfy the common norm. The norm yields U^2=1 mod4P, hence gcd(U,4P)=1.

CRT gives B=A modU and B=1 mod4P. Add sufficiently large multiples of 4PU until B>A and B>=1+4P, and put b=(B-1)/(4P)-1>=0. Define S_j=X_B(k_j), R_j=Y_B(k_j). Polynomial recurrence in the Pell base gives S_j=X_j modU and R_j=k_j mod4Y_j. Monotonicity for B>A>=2 and k_j>=1 gives S_j>=X_j; the ordinary growth bound gives R_j>=k_j. Thus

    s_j=(S_j-X_j)/U>=0,
    r_j=(R_j-k_j)/(4Y_j)>=0

are natural integers. This proves that encoding the residue conditions by natural progression coordinates loses no completeness witnesses. It also explains why choosing merely an arbitrary small CRT representative B would be insufficient; the large representative B>A is part of the proof.

## Implementation observations

The inspected `build.py` matches the refined certificate:

- deferred powers retain original argument node identities, and equal exponent nodes share one Pell pair;
- all batch constraints are appended after original semantic macro generation;
- power outputs are represented as fresh natural predecessors plus one;
- factorial outputs are similarly shifted, making the required input positivity check independent of the power theorem;
- A is the sum of all deferred outputs plus a natural gap plus two;
- Z and v are explicitly unrestricted, while their absolute values occur only in the mathematical proof;
- U is a natural predecessor plus two, and X_j are natural predecessors plus one;
- S_j,R_j use natural progression coordinates, with one norm each;
- T_i is a signed polynomial expression, whose positivity follows from the global equations rather than a separately added guard;
- signed quotient variables are used for the remaining B and power congruences.

The final unrestricted-integer export must retain guards for all nominally natural semantic inputs except those whose nonnegativity is independently inferred by a proved gate rule. It must not apply these guards to signed Z,v, or congruence quotients. Gate quadratization preserves the semantics only with every retained wire equation included.

## Risks checked and conclusion

No zero Pell branch is inadvertently admitted: A>=2 excludes bootstrap Z=0; U>=2 excludes V=0; k_j>=1 excludes Y_j=0; B>1 and T_i>0 follow before either standard criterion is invoked. Neither CRT nor the sharing argument assumes the Y_j are pairwise coprime. Acyclic evaluation is required only for constructing a complete intended assignment, while soundness applies directly to every simultaneous solution.

No mathematical obstruction was found. The refined system is equivalent to the entire finite family of positive power equalities, under the stated natural/signed domains and the standard Pell criteria. This supplies an ordinary proof formalizable in ZFC of the batching step. The overall no-zero/Con(ZFC) conclusion additionally composes with the separately documented source and compiler theorems.
