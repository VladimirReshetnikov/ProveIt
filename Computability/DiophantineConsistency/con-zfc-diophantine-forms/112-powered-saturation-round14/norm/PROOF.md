# Twelve integers, exact degree 768, and 141 operations

## Scope and selected equation

The selected literal polynomial has twelve unrestricted integer variables, the unchanged six actual fixed coefficients, exact total degree768 and141 live binary arithmetic operations. The preceding reviewed scalar equations had degree1456 at141 operations and degree1200 at145 operations. Thus this candidate reduces degree by47.2527% at unchanged141-operation cost, or reduces both degree and cost relative to the145-operation rational variant. It is an ordinary mathematical zero-existence reduction, not a new kernel-checked or object-language consistency proof and not a global minimality claim.

The complete zero-existence theorem, including the new powered-divisibility saturation and unrestricted supported-modulus interpolation, is proved in `../radicals/PROOF.md`. That theorem restores the same signed native source and the same finite-refutation calibration as the pinned scalar parent. This note supplies its exact scalar arithmetic graph, the center translation, universal norm identities and exact degree certificate.

The canonical artifact is `equation.json`. The polynomial-identical `equation_reduced.json` makes all important cancellations explicit. The first uses141 operations but has naive syntactic bound976; the second uses149 operations and has syntactic bound768. Both have exact degree768. We do not misreport the naive bound as the attained degree.

## Complete mathematical definition

Use twelve unrestricted integer coordinates j,C,z,h,r,v,w,T,c,n,t,s. The six fixed ports beta,K0,MC,MF,cone_A,cone_B are the actual unchanged payloads in `coefficients/BINDING.json`, including the shifted MF convention. In particular beta=2^1064921-1. Define

    J=6j+1, q=beta J+1, W0=12w+4,
    X=qW0, Y=(2v+1)q³, E0=XY,
    a=E0+Y, H=4a+3, Delta=a²+H,
    F=(K0+W0)C-z(q-1),
    R=[q(q-F)-C](q²-1)+(MC+q MF)J,
    k=R+1+hE0, eta=c-Yk, zeta=k-eta,
    U0=cone_A F, W1=cone_B C,
    G=U0 W1-(q-U0-W1)²,
    Pair=G eta zeta-(t²-G-eta zeta+1)²,
    Dg=(3Pair-4)s²+1,
    I=rc², Df=1+Delta I², Q=Delta² I², delta=Q-1,
    V=Df(c-R+4IT)-c, Cy=QV²-1,
    ell=XY², Dt=1+ell(ell+1)k²,
    Kred=X(2X-3c)-2,
    zc=HT+Kred,
    Ac=(zc²+3H²)(zc³-19H³),
    S=srH,
    Z=S(n+QV)-Ac.

The complete equation is

    P=F16(Z; 9S²Df, 81S²Dt, 729S²Dg, S²delta Cy)=0,

where F16 is the product over all sixteen independent signs of Z minus the signed sum of square roots of its four arguments. This sign product is an ordinary polynomial with integer coefficients. Every abbreviation is inlined by the literal graph, which uses only fixed integer leaves and binary addition, subtraction and multiplication. There are no divisions, radicals, variable exponents or additional quantified registers in the graph.

The integral translation n->n+QV is a bijection of Z for every fixed choice of the other eleven variables: Q and V do not involve n. Consequently it preserves zero existence in both directions. In particular, if n_old was supplied by the uncentered completeness proof, take n_new=n_old-QV.

## Why the new carrier is legitimate

Here is the logical interface to the full proof, included to make clear that lower-degree syntax has not silently weakened the theorem.

1. S=0 makes all norm radicands zero; the remaining Ac^16 is nonzero because H!=0 and pi(x)=(x²+3)(x³-19) has no rational root. Thus s,r are nonzero.
2. The inherited prime-3 separation makes every extracted root rational. Recovering the integer guard root first gives Pair>0, hence G>0 and eta*zeta>0. If c=0 then eta*zeta=-Y(Y+1)k²<=0, contradiction. Therefore c,I are nonzero before adjacent-coefficient descent is used.
3. The unchanged Pell rank argument needs c²|I, not s|I. It restores the exact first index and yields R=2r0+1, r0>=24 and |H|>x(x-3)^r0, where x=|X|.
4. The scalar equation gives S|Ac, hence H|Kred^5. With K=X(X+2ac)-1, the identity2K=Kred+HcX and the signed Pell congruence2^R K=Pi modH, where Pi=(sigma X-2^R)(2^R sigma X+1), give H|Pi^5. The authentic beta forces x>=2^64. The rank bound then gives |Pi|^5<|H|, so Pi=0 and the original exact projection is recovered. The full proof explicitly establishes this inequality; H|Kred is not incorrectly inferred just from H|Kred^5.
5. For completeness, choose the same native strong Pell pair with I divisible by4s c², and put r=I/c². Every prime of M=sr divides I. The proved supported-modulus interpolation theorem supplies any T residue modulo M while preserving the fixed strong pair and auxiliary Pell equation. Intersectivity of pi therefore makes Ac/S integral and supplies an integral n. The theorem is stronger than merely all T modulo I; this stronger step is proved, not assumed.

These steps give exactly the same finite ZFC-refutation endpoint as the source. Their complete unbounded proofs, including all signs and the p=2 interpolation case, are in `../radicals/PROOF.md` and its explicitly retained source references.

## Universal cancellation-aware identity

Write

    B=Sn-Ac,
    L=SQV,
    D=S²[Q(V²+1)-1],
    alpha=9S²Df, beta1=81S²Dt, gamma=729S²Dg.

The fourth radicand satisfies the exact identity

    S²delta Cy=L²-D.

Pairing its two signs first gives the universal polynomial identity

    P = product_U [(B-U)²+2L(B-U)+D],

where U ranges over all eight independent signed sums of square roots of alpha,beta1,gamma. The ordinary polynomial interpretation does not require the radicands positive or nonzero.

The reduced graph uses this identity through an exact simplification of the conventional norm's first quadratic register:

    q0 = Z²+gamma-alpha-beta1-(L²-D)
       = B²+2LB+D+gamma-alpha-beta1.

All subsequent arithmetic uses the identical four-root norm. `check.py` independently constructs the generic sign product in a multiquadratic algebra and proves equality with the minimal norm graph. It then proves the full reduced graph equals the same generic norm after Z=B+L and the fourth argument=L²-D. The checks are exact polynomial identities, not numerical inference.

## Exact degree and authentic nonzero coefficients

The new source weights are

    deg I=3, deg S=8, deg Q=30, deg V=23,
    deg Ac=35, deg B=35, deg L=61, deg D=92,
    deg alpha=34, deg beta1=50, deg gamma=62.

In each paired factor, 2LB has degree96. The nearest competitors are D and2L times the guard root, both degree92; B² has degree70. Thus 2LB is the unique highest contribution and

    P_top=(2L_top B_top)^8,
    deg P=8*96=768.

This is also visible wholly inside the polynomial ring in the reduced graph. Its relevant naive bounds are deg q0=96, deg v0=192, deg n0=384 and deg n1=349. Hence the final n0²-gamma n1² has degree at most768. The following attained coefficient proves equality.

Use subscript0 for top homogeneous parts. Directly from the complete prefix,

    q0=6 beta j, W00=12w,
    Y0=2v q0³,
    a0=q0 W00 Y0=2^7 3^5 beta^4 j^4 w v,
    F0=W00 C-q0 z,
    R0=-q0³F0,
    I0=rc²,
    B_top=-4^5 a0^5 T^5,
    L_top=-4s r^5 c^8 a0^7 R0.

Therefore

    P_top=2^104 s^8 r^40 c^64 a0^96 R0^8 T^40.

Two explicitly attained nonzero coefficients are

    [j^408 w^104 v^96 C^8 s^8 r^40 c^64 T^40]P
      =2^816 3^512 beta^408,

    [j^416 w^96 v^96 z^8 s^8 r^40 c^64 T^40]P
      =2^808 3^512 beta^416.

Both exponent sums are768. The actual unchanged beta=2^1064921-1 is positive, so neither coefficient vanishes. This proves the degree after specialization to the authentic full coefficient tuple, not merely for symbolic generic constants.

## Exact circuit cost and checks

`equation.json` has88 multiplications,26 additions and27 subtractions:141 operations. Fixed integer leaves and register reuse cost zero. Every multiplication, including a square or multiplication by a fixed scalar, costs one. No sign product is a unit-cost opaque operation in this count.

`build.py` reconstructs the two literal graphs from the pinned parent prefix and the explicitly documented I,S,Kred changes, dead-code-prunes them and recounts all live gates. `check.py` does not import the generator. It verifies topology, backward liveness, all common prefix registers by exact expression hashing after the specified replacements, unchanged variable and coefficient leaves, actual coefficient payload hashes and beta recipe, generic sign-product identity, polynomial equality of both exported graphs, exact leading coefficients and the syntactic upper bound. It also runs360 signed modular replays with the actual fixed coefficients and rejects an intentionally wrong final sign. These finite tests are supplemental transcription checks, not proofs of the native calibration or consistency.

Run `python build.py`, `python check.py`, and `python -O check.py`. The release includes only the selected768-degree graphs and their proof/certification dependencies. Superseded exploratory graphs are not release artifacts. A conservative800-degree141-operation construction retaining I=src² is available in the accompanying mathematical proof, but is not substituted for the stronger proved primary result.
