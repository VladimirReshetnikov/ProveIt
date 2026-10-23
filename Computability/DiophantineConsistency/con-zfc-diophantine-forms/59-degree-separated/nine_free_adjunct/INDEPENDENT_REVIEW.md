# Independent review of the free-carrier split-source adjunct

Status: **PASS** for the ordinary mathematical composition and the checked literal circuit. This is an independent AI-assisted local review, not external peer review, a new end-to-end proof-assistant certificate, or an exported object-language ZFC proof. The original31 compiler, coefficient calibration, and Jones ratio theorems remain inherited dependencies.

Reviewed principal artifact: `generated/split_116_positive.json`, nine strictly positive integer unknowns, exact degree **1,910,404**, **473** live binary operations (289 multiplications, 162 additions, 22 subtractions). The separate natural-coordinate translation is not an unrestricted-integer theorem.

## 1. Source binding and noncircular numerical hypotheses

The source kernels, all 89 weighted records, the 31-variable positive parent, and its complete old31 coefficient tuple are unchanged from the frozen nine-family source. The row operations are invertible and the same-degree source identities are reused, not generalized merely from finite examples. The unchanged source proof yields S,T>=0 for arbitrary positive source coordinates, and S+T<B^2279 on the actual soundness range g<4bB^116. No bound on g is used to obtain positivity.

For L=bB^2279 and R=L(S+T+1)-S-1,

    R=(L-1)S+LT+L-1 >= L-1 >= 8.

Also b<=R,N and N>=8, so the numerical hypotheses of Jones soundness are available before concluding that b is a power of two. The smaller L still obeys S+T<L, including the b=1 case.

## 2. Two lost bits and the new exact square threshold

For L=2^u and S+T<L, the two disjoint words of R give

    pop(R)=u+pop(T)-[pop(S)+pop(T)-pop(S+T)].

The bracket is nonnegative and vanishes exactly when S&T=0. This removes one bit relative to the old leading-L^2 layout; halving L removes the second bit. The exact new threshold is

    u+pop(T)=2418v-30k-22
            =2(17079501+k+1201v),

with v=2134939+2k. Therefore reducing the old N by exactly two is correct. All k>=0 remain admissible; no odd-parity restriction or unproved cofinality assertion is added.

## 3. Free C and quotient positivity

The old unconditional Q>0 need not hold for free C. The replacement is exact and sufficient:

    E0=J(n+W1^2)+Q=Jn+(J-2)W1^2+3W1C+2>0.

This holds for every positive assignment because J>=3. The strict Pell majorants also hold before a margin sign is known: C>=1 implies D>=A^2, D>C^2, k0>=3, and the published defect identities are strictly positive. The real four-factor identity therefore forces m>0 before any claim of rational or integral roots.

The normalized margin gives |C-KY|<K/2. Since Y>=64, K>=R+P, and P>W1,

    C>K(Y-1/2)>2K>=2(R+P)>2R+1+W1.

Thus phi=C-(2R+1)-W1 is positive, and the old Jones interface is recovered on every zero. The exact CRT substitution retains j0=j-1>=0; it does not discard j0=0 or impose an unjustified restriction on an existing witness.

After recovering m>0, the usual a1>a0 argument is valid, so the rational signed root sum cannot vanish. Rational-square integrality then recovers both square conditions and J|Q. This establishes soundness without assuming square-class independence.

For completeness, the old ratio witnesses are preserved. A>W1, D>=A^2 and D>C^2 imply W1^2<D and W1*C<D. Since Q/J<=W1*C and V1>2D,

    W1^2+Q/J<2D<V1.

Consequently n=m(V0+V1+r0+r1)-W1^2-Q/J is a strictly positive integer for the positive square roots and the normalized integer margin m>=1. The shifted final witness exists constructively; this is not a tuplewise assertion about an old unshifted norm witness.

## 4. Exact degree and leading coefficient

The new source head is R0=2a^4557 with degree r=9115, while the threshold head is N0=c*a^1201 with degree q=2403. Free C has degree 1. Direct recurrence gives

    deg A=18729, deg Delta1=767442, deg Omega=93880.

In the exact cancelled inner identity, Omega^2*Delta1 uniquely dominates, with degree 955202. Squaring gives 1,910,404, strictly above the other final term's degree 1,385,948. Equivalently,

    deg F9=104r+400q+8W+316=1,910,404.

Writing only diagonal leading coefficients, the decisive terms are

    head(Delta1)=2^25 R0^2 (R0*N0^4)^40,
    head(Omega)=-2^8 a^116 R0^5 N0^20.

Their contribution to the final square is

    2^82 a^464 R0^104 N0^400
      =2^186 a^954792 c^400>0.

Thus the multivariate upper bound is attained on the diagonal for the actual fixed coefficients; the reported degree is not a naive bound that overlooks the norm cancellation.

## 5. Independent machine checks

`independent_review.py` imports no construction builder or authored verifier. Its polynomial engine checks 97 exact local register identities in the main and cancellation-certificate circuits, together with five universal norm/Pell identities. It authenticates the actual coefficient payloads and verifies the nonzero diagonal leading coefficient modulo 101, 1009, and 1,000,003. It independently checks topology, full liveness, domain metadata, and the 473-operation ledger.

Additional exact fixtures cover:

- 43,945 two-block popcount/carry cases;
- 65 exact calibration cases, including b=1;
- 3,840 free-C sign, majorant, and carrier-transfer cases;
- 1,701 strictly positive shifted-finalizer constructions.

Normal Python and optimized Python outputs agree. `generated/INDEPENDENT_REVIEW.json` records the results. These finite checks corroborate the universal proof above; they do not establish the unbounded compiler or an internal ZFC semantic bridge by testing examples.

No mathematical defect or required circuit change was found. The proof's source-hash transcription typo was reported and corrected before this review was finalized; the actual data and circuit binding were already correct. The added explicit b=1 exclusion is also valid: its mask is N0-1 and the bounded nonzero g lies below N0.
