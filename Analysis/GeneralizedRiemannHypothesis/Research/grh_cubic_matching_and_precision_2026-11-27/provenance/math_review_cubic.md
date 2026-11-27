# Independent adversarial review: exact cubic-character packet agreement

Reviewed the proof underlying the final chapter `papers/cubic.tex`, independently derived its valuation and support bounds, inspected the cited primary coding-theory paper, and ran a separate exact enumeration based on local multiplicity triples. The final chapter was also read for consistency, including its exact-order-three and asymptotic error/erasure corollaries.

**Verdict:** I found no substantive mathematical defect in the exact density theorem, its constructions, or its classification of all minimizers. The quantitative smoothed GRH consequence is also sound with a sufficiently large constant depending only on the fixed smoothing function. The main result resolves the cubic-order case of the article's odd-prime-order extremal matching question; it is not a determination of every nonextremal attainable density.

## 1. Fourier reduction and density

For distinct size-k multisets, cancellation gives integer coefficients c_u with sum zero and positive mass at most k. On a given dual class v, let d_j be the sum of c_u over characters taking value zeta^j. Then d_0+d_1+d_2=0. The condition d_0+d_1*zeta+d_2*zeta^2=0 implies d_0=d_1=d_2 because 1+zeta+zeta^2 is the only rational relation; sum zero then makes all three zero. Thus equality of the trace sum is genuinely equivalent to equality of the entire local Euler-factor polynomial in this setting. This step would fail without equal packet sizes or without using the prime order of the root of unity appropriately.

The evaluation homomorphism from reduced residue classes modulo Q onto the dual of X is surjective: a proper subgroup would have a nontrivial annihilating character in X, which would be a nontrivial Dirichlet character identically one on all units, a contradiction. All fibers have equal size. PNT in progressions therefore gives the claimed natural density unconditionally; no GRH enters the exact density result.

## 2. Valuation lemma: a simpler exact proof

Put lambda=1-zeta, so lambda^2=-3*zeta. Let a nonzero zero-sum integer triple d be given. Factor out its largest common power 3^m; write d=3^m e. At least one e_j is nonzero modulo 3. The sum-zero relation forces exactly two types:

* The residues are a permutation of (0,1,2). In the expression H=-3e_2-(e_1-e_2)lambda, the second coefficient is a unit, so the lambda valuation is exactly one. Therefore v_lambda(H)=2m+1 and the positive mass is at least 3^m.
* All three residues are equal to 1 or all equal to 2. The first term has valuation two and the second has valuation at least three, so the valuation is exactly two. Three integers with the same nonzero residue and sum zero have maximum absolute value at least two. Therefore v_lambda(H)=2m+2 and the positive mass is at least 2*3^m.

For a zero-sum triple the positive mass equals its maximum absolute entry. Coalescing the original signed coefficients into three bins cannot increase positive mass. This proves precisely the two packet-size thresholds, including t=1 and t=2 and all equality boundaries.

## 3. Polynomial degree and parity

For x in {0,1,2}, the Newton expansion

`zeta^(e*x) = 1 + (zeta^e-1)x + (zeta^e-1)^2*x(x-1)/2`

is exact. Its degree-j ordinary monomial coefficient is divisible by lambda^j. Tensor products therefore give the analogous statement in several variables. All coefficients of the unique coordinatewise-degree-at-most-two interpolant of H are also divisible by lambda^t when all values are: the interpolation nodes have differences 1,1,2, which are units at lambda. After dividing by lambda^t, all terms of total degree greater than t vanish in the residue field. Thus the reduced ternary polynomial f has degree at most t and is nonzero.

Conjugation fixes the residue field and sends lambda to -zeta^2*lambda, proving f(-v)=(-1)^t f(v). Also f(0)=0. The support containment supp(f) subset supp(H) is in the correct direction for lower bounds.

## 4. Coding-theory input and every boundary case

I opened the primary PDF `https://arxiv.org/pdf/1203.5244` (Leducq, v3) directly rather than relying on a secondary description. The relevant statements are:

* Theorem 1.1, page 2: minimum weight and support description for all degree t(q-1)+s<m(q-1).
* The paragraph before Theorem 1.2, page 2: degree 2<q=3 has second weight 4*3^(r-2), including ambient dimension r=2.
* Theorem 1.2(1), page 2: the even degrees 4 through 2(r-1) have second weight 4*3^(r-j-1) at degree 2j.
* Theorem 2.4, page 3: at degree 2j, every second-weight support lies in an affine subspace of codimension j-1. Its stated range includes j=1 and j=r-1 and q=3.

For even t=2j<2r, the minimum possible support is an affine subspace. Negation invariance would make that affine subspace contain zero (since 2 is invertible over F_3), contradicting f(0)=0. Moving to the second coding weight is therefore justified; no unproved claim about a gap in the possible weights is being inserted.

At r=1 the theorem is already in its saturated range for every k>=1, so no even-degree coding boundary is needed. At a=r-2, the upper range uses degree 2r-2, exactly within the second-weight theorem, and its minimum support is four. The first saturated packet size 3^(r-1) is treated by the elementary support-pair bound. When k<3^(r-1), the valuation thresholds exclude t>=2r-1; hence the coding arguments are never used beyond their range. The t>=2r discussion is harmless but unnecessary in the nonsaturated proof.

## 5. Equality classification

The passage from codeword support to packet structure is valid and stronger than the bare inequality.

In the lower range the minimum support occupies 2/3 of a containing affine space of codimension a. In the upper range the second weight support occupies 4/9 of a containing affine space of codimension a. Each proportion exceeds 1/3, the largest proportion of a proper affine subspace. Hence the support's affine span is exactly that containing space. Since the support is stable under negation, its affine span is a linear subspace.

Fourier inversion then makes c constant on cosets of the annihilator U, which has dimension a. The reduced positive mass is consequently divisible by 3^a. The packet-size interval forces quotient mass exactly one in the lower range and exactly two in the upper range. This rules out additional integer multiplicities in nonsaturated extremizers.

For quotient mass two, a repeated entry would force agreement inside a proper character kernel, of density at most 1/3. Four distinct entries must also have equal sums as characters, since otherwise agreement lies in the kernel of their nonzero sum difference. Recentring gives the two opposite pairs ±alpha and ±beta. Over F_3, four distinct entries force alpha and beta to be linearly independent. This yields exactly the stated two-coset versus four-coset classifications.

In the saturated case support size two means precisely one dual pair {v,-v}. Fourier inversion makes c constant on the three cosets of ker(v), and integrality gives the zero-sum integer triple in the statement. Conversely every such nonzero triple has exactly that support. Repetitions in this saturated regime are correctly retained.

## 6. Quantitative GRH statement

For a fixed nonnegative smooth w supported in (1/2,1), the standard smoothed explicit formula under Dirichlet GRH gives a character-by-character error O_w(sqrt(x) log(2Q)). The Mellin transform decays rapidly, so the zero sum is bounded by the standard zero-counting function integrated against that decay, with one logarithm of Q. Subtracting prime powers costs O_w(sqrt(x)): use Chebyshev for squares and sum the higher powers. Removing Euler factors at primes dividing Q costs O_w(log Q), absorbed in the displayed error for x>=2.

Applying the estimate to |H|^2 gives mean sum(c_u^2)>=sum|c_u|=B and Fourier algebra norm at most B^2. Since B<=2k, a sufficiently large x>=C_w*k^2*log^2(2Q) makes the weighted prime sum strictly positive. The prime lies in (x/2,x). The statement should use a sufficiently large constant, not promise the exact endpoint with an unspecified small constant. This is a generic Fourier argument, not the novel part of the paper.

The disagreement indicator norms are exactly 4/3 in the lower and saturated cases and 16/9 in the upper case. I independently checked the Fourier coefficients on the three and nine cosets respectively. To avoid a notation ambiguity, write the upper intersection subspace as `U + span(alpha,beta)` or `U+<alpha,beta>`; `U+alpha+beta` might otherwise be read as one coset or the span of only alpha+beta. The same distinction applies to `U+<theta>` in the lower case.

## 7. Independent finite enumeration

`code/cubic_independent_enumeration.py` enumerates all packets and compares their exact three-value multiplicities on every dual class. It does not compute complex Fourier sums, lambda valuations, polynomial degrees, or Reed--Muller weights. This makes it an independent check of the result's finite consequences.

It checked 13 parameter cases: r=1 with k=1..6; r=2 with k=1..5; and r=3 with k=1..2. These include 1,036,722 unordered pairs of distinct packets. Every minimum agrees with the theorem. For example, r=2 has minimum support 6 at k=1, 4 at k=2, and 2 at k>=3; at r=3 the minima are 18 and 12 for k=1,2. Results are recorded in `results/cubic_independent_enumeration.json`.

These computations are verification artifacts, not a replacement for the proof or evidence for a global novelty claim.

