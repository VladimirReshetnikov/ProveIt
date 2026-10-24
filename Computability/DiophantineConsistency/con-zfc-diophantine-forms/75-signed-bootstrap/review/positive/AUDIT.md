# Independent audit: adaptive carrier and positive monic projections

## Verdict and scope

No local mathematical defect was found in the new thirteen-positive degree-30/94-operation construction or twelve-positive degree-114/105-operation construction. These are degree improvements with a one-operation cost increase over the incoming 34/93 and 118/104 points, not across-the-board or globally minimal improvements. Their equivalence to a finite ZFC refutation is conditional on the explicitly inherited coherent compiler tuple, normalized native-source theorem, canonical completeness witnesses, and Pell interface. Those dependencies have not been independently kernel-checked here.

The source21, source24, and source26 monic projections are correct over strictly positive integers. Their sums of squares have respectively 21/24/26 unknowns and degree 8/8/6. In particular, the reconstruction of P and V in source21 is genuinely positive on the remaining common zero set; it is not a globally positive ambient polynomial. The 26-positive sextic is dominated in unknown count by an existing historical 25-positive sextic and must not be advertised as a new record. The historical 20-positive octic likewise dominates the 21-positive octic in unknown count at the same degree. Neither projected endpoint is a new record.

## Ordered adaptive-carrier argument

The transport residual is unchanged. Rational-square-root integrality first yields q^3 | Y and q−1 | Bt. Its signed-root inequality then proves t=Bt/(q−1)>0 and hence C=q−F−alpha>0. Only after that can the imported coefficient bounds be invoked to give 3q<R<q^4−2. This ordering is essential; assuming X/q integral at this stage would be circular.

Put K=4qY, U=qK and H=4Y(X+1)+3. Since q=2 modulo 3 and q|Y, gcd(q,H)=1; H is odd; and gcd(Y,H)=gcd(Y,3). Therefore

    d=gcd(K,H)=gcd(Y,3)≤3,
    μ=K/d≥4qY/3≥4q^4/3>R+1.

The equality gcd(K,H)=gcd(Y,3) is valid without any assumption q|X. From the positive-root carrier, U|H(KX−r0); reduction modulo K gives μ|r0. The first Pell congruence k≡2n modulo 4XY² implies k≡2n modulo μ because q|Y makes K divide 4XY². Once the unchanged signed index argument supplies p=R and 1≤n<p, one has

    −(R+1)<2n−R−1<R+1.

Divisibility by μ therefore implies 2n=R+1 exactly. Consequently r0=k−2n is a positive multiple of 4XY², and

    (4XY²)/U=XY/q²

is integral because q³|Y. Thus U|r0. Cancelling K from U|HKX gives q|HX, and gcd(q,H)=1 gives q|X. The missing w, h and gamma_old are now integers, in the correct dependency order.

Dstar>0 follows from r0<k, X+ac>akY, H<5a and UY>5. Thus the rational root Dstar/U is the positive root. The recovered gap satisfies H gamma_old=D−ac−X>c−X>0. The inequality c>X follows from the n≥2 first-Pell growth bound, not merely from c>kY alone.

Completeness selects the inherited canonical witness, for which gamma_old>w is a separately stated dependency. Since r0/U is a positive integer, gamma=gamma_old−w+r0/U>0. It is legitimate to use this canonical property for existence; it is not asserted for every old source solution.

## Normalized strong versus ordinary strong

The retained equation is f²−Delta (ic²)²=1. It must not be replaced by (ic²)²−Delta(f²−1)=0. Under the normalized equation, I=ic² is the main Pell ordinate. If c=psi_A(p), strong divisibility gives p|m for I=psi_A(m); composition and c²|I give c|(m/p), hence c|m and m≥pc>2p. These are precisely the hypotheses of the inherited signed auxiliary-index lemma. The low-degree construction retains this normalized equation literally, so the SharedTaps ordinary-strong source does not introduce an unnoticed X>q premise.

## Twelve-positive norm elimination

The adaptive A1 is the only changed carrier. The inherited norm elimination has B=2(Q−1)(Mn−1)>0, so it has no zero-denominator branch. Its integer-root recovery f=A/B, f²=D produces a nonzero integer f. The auxiliary recovered y is nonzero, and |y|>|V| gives u=|y|−V>0. Thus replacing f by |f| and taking j13=2j12 gives a positive solution of the new thirteen-variable system, not merely an integer solution.

For completeness the canonical odd-index congruence y=−1 modulo Q supplies a positive integer n=f_old+(y+1)/M. With J=6j+1, q is even and the new U=4q²Y is even. Each residual in the product finalizer is a square modulo 4; a unit factor −1 would demand a residual −2, which is impossible. Therefore the product finalizer vanishes exactly when all three residuals vanish. No positivity of those residuals is needed.

## Positive source projections

Every deleted coordinate is defined monically and uniquely. The seven basic reconstructions L=q²−1, N=q³, X=qw, Delta=a²+4a+3, C2=c², F2=f², D=(4a+3)gamma+ac+X are positive for arbitrary positive retained coordinates and positive beta. Baux=I² is also unconditionally positive.

For source21, retained rows give a−E=sN and c=(eta+zeta)sN+eta. Let k=eta+zeta. Then

    P=Ek sN+k>0,
    V=(j−1)c+hE+k(sN−1)+eta+1>0.

This is an explicit positive decomposition: j≥1, sN≥1, and all other displayed positive factors are retained positive coordinates or already-positive reconstructions. It proves positivity of V without assuming a sign for the polynomial jc+hE−k+1 on arbitrary ambient points. Together with exact substitution of all original rows, this gives the required bijection of positive common zero sets.

The source26 sextic uses only unconditional positive reconstructions. Sum of squares is an exact common-zero finalizer over integers. The exact degree is twice the largest residual degree because a sum of real squares of nonzero leading forms cannot cancel.

## Replays and boundaries

`check.py` is an independently written checker using explicit exceptions, so its checks remain active under Python -O. It checks all original-row substitution identities, sparse records, partitions of coordinates, degree/support counts, and the positive decompositions above. Three deliberately perturbed substitution identities are rejected. Normal and optimized runs produce byte-identical receipts. There are also 672 supplemental gcd/divisibility cases; these are explicitly not substitutes for the unbounded argument.

The author-supplied low-degree check13.py and check12.py were replayed in an isolated copy, both normally and with -O; all four executions passed. This is replay of their finite symbolic checks, not a second independent implementation of the full low-degree expansion. Reviewed file hashes are in CHECK.json. No claim is made that these checks decide consistency or establish a new end-to-end proof-assistant theorem.
