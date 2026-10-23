# Independent review of the principal degree-separated nine-variable equation

Outcome: PASS for the new source/CRT/finalizer composition, conditional on the explicitly imported original package-31 compiler theorem and the numerical Jones ratio theorems. This review does not claim to re-prove those inherited semantic theorems or to run their complete Lean dependency tree.

Reviewed principal files: `PROOF.md`, `build_nine.py` as source text, `generated/split_116_positive.json`, `generated/split_116_positive_certificate.json`, the frozen split layout and kernels, the original source and complete old-31 port tuple, and the actual declarations and definitions of `ratio_sound`, `ratio_complete`, and `ProductPellConds` in the supplied Lean sources. The new review script imports neither the builder nor the author's verifier.

## 1. Source and pre-binary contract

The split-116 source is the same exact source independently reconstructed in the Sun10 review: unshifted original 31-coordinate residuals, the invertible changes rho_14=r_14+r_2 and rho_15=r_15+r_3, 89 records, and 22,544 same-degree isolation interactions. Its degree-two kernel has leading coefficient +1 at 1929. The degrees 2027 and 1719 of the other kernels are low enough that U>=B^116 implies Gsource>0 before either an upper bound on g or binary-base recovery. Thus the nine-variable adapter's unconditional positivity is genuine.

For its tighter base constant a = 4096M, rather than the Sun10 constant, the numerical bounds still hold. With g<4bB^116 and b>=1, U<6bB^116; the estimate 2Gsource/Z <86Mb^2/(B-1) is strictly less than 1/32 because B=4096Mb^2 and B>=4. The target terms and the possible low-block carry are absorbed into Z=B^2162. Hence Scode+Tcode<B^2279<L=2bB^2279. No binary assumption is used in establishing this range.

The coefficient bound sums all three degree layers, including unsupported collisions: 993Mb^2<B/4. Sparse padding by one at each selected cell correctly permits either incoming borrow. The low mask recovers nonnegative digits, and the shared shift ell+g converts them to strictly positive parent coordinates. The all-one tuple is not a zero, so the forward packed g is positive. The bound g<bB^116 gives exactly the ratio theorem's stronger completeness requirement 32g<Gcap.

## 2. Even-parameter threshold calibration

This step has no missing parity assumption. With b=2^k, B=2^v and v=2134939+2k,

- log_2 L=1+k+2279v;
- popcount(Tcode)=139v-31k-22;
- the calibrated binomial exponent is 2418v-30k-20;
- 2log_2 N=2(17079502+k+1201v), the same expression.

The identity follows from 16*2134939-20=2*17079502. It allows every nonnegative k, including k=0; at b=1 the low mask simply admits no positive packed g, which introduces no spurious source zero. Completeness can use every sufficiently large power of two, not a sparsely restricted subsequence.

The binary-block formula uses the strict Scode+Tcode<L already proved. Thus there is no unaccounted carry into the leading block.

## 3. CRT transport matches the actual ratio interface

The supplied ratio definitions use E=iJDC^2, old H=B1+j_old*C with j_old>0, and divisibility JF | QF+J(H-C). These agree with the proof's starting interface. The new k0=iJC and E=k0DC are identical, not an extra divisibility restriction.

Since F=1 modulo both J and C, the old divisibility is equivalent to J|Q and F|(H-C). The quotient z=(H-C)/F is strictly positive and congruent to B1 modulo C. Because0<B1<C, precisely z=B1+jC for j>=0. The inverse j_old=1+((F-1)/C)B1+Fj is a positive integer and reproduces H exactly. Therefore no witness is lost by the new H, and no new one is introduced.

The normalized margin m equals exactly one eighth of the original integer margin after substituting Gcap=32t. It is an integer polynomial, and dividing by the known positive constant 8 preserves its strict sign.

## 4. Positivity-first norm has no circular separation argument

The majorants are valid before m>0 is known. From D=(A^2-1)C^2+1 and E=k0DC,

    DF=k0^2 D^3(D-1)+D.

Hence the exact defect of Tpair=k0(8D^2-4D-1) is

    Tpair^2-64DF=(8D+1)k0^2-64D.

Since k0>=3, this exceeds zero. The full defect of V1=Tpair*G*H against 64a1 has the additional nonnegative term 64DF(H^2-1), and the first term is strictly positive. Likewise V0^2-a0=K^2-1>0. Both majorants themselves are positive.

At a norm zero with m!=0, choose the real signed square roots supplied by a vanishing linear factor. These need not yet be rational. Their sum with V0+V1 is strictly positive by the unconditional majorants. The rearranged identity n+Q/J=mZ has positive left side, forcing m>0 first. This argument uses no radical integrality or independent-square-class assumption.

Only then does the margin imply |C-KY|<K/2 and therefore C>K. All additional comparisons are valid: A^2>P, D>C^2, F>=A^2, G>=A, I>=G^2. Thus a1>C^2A^4>K^2P^2>a0. The rational signed root sum is nonzero. The elementary isolation formula 2x*r0=x^2+a0-64a1 forces both roots rational and hence integral. It then gives J|Q. This order correctly resolves the equal-nonsquare cancellation pitfall of an unweighted two-root norm.

If m=0 the norm is (Jn+Q)^4>0. Conversely, given the ratio conditions, positive integer roots and the actual positive integer m produce n=m(V0+V1+r0+r1)-Q/J>0, because V1>Q. This is stronger than the required n>=0 and does not replace the computed margin by a freely selected witness.

## 5. Actual circuit and exact degree

`independent_review.py` checks 97 exact local register identities across the principal and degree-certificate DAGs, including the source kernels as polynomials in B and the four ports. It separately proves five universal polynomial identities: the DF support substitution, Pell pair defect, full root defect, resolved inner-expression identity, and four-factor norm. Together these establish that the two DAGs evaluate the same polynomial, not merely that they agree at sampled inputs.

Using the actual authenticated old-31 coefficient payloads, an independent leading-coefficient propagation on the certificate DAG yields exact degree 2,676,548. The diagonal leading coefficient is nonzero modulo each of 101,1009,1000003, with residues 30,841,734575. These agree with the advertised symbolic leader 2^542 a^1337768 c^400. Since the certificate DAG supplies a genuine polynomial upper bound and its diagonal attains that bound, the degree is exact for the equal principal polynomial.

The principal live operation ledger is 476: 289 multiplications, 164 additions, 23 subtractions. Positive inputs phi,j,n are translated downward by one; the remaining six inputs are unchanged. This is the stated bijection with the mixed domain, not a claim about nine unrestricted integers. Affine translations preserve the exact degree.

Both ordinary Python and `python3 -O independent_review.py` pass. The generated result is `generated/INDEPENDENT_REVIEW.json`. The review found no new mathematical blocker in the principal construction. The inherited compiler and Jones semantics remain the appropriate explicit trust boundary.
