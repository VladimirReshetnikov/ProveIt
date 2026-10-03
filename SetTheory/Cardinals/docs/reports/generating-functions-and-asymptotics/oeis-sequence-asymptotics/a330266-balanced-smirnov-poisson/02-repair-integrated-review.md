# Integrated mathematical review

Reviewed 2 October 2026

## Verdict

The standalone report is mathematically consistent with the independently audited repair. No mathematical correction is required. The new distinction between labeled and multiset counts is correct, and the additional multiset inverse-carrier formula is correct. The scope, logarithm convention, error estimates, and attribution caveats are preserved.

This is an independent AI-assisted mathematical review, not peer review or a formal proof-assistant certification. It checks the report's mathematics and transcription; final PDF visual inspection and archive completeness are separate production checks.

## Document reviewed

- `balanced-smirnov-repair.tex`
- SHA-256 of the reviewed version: `f2f720d22cc6685a3b133b8dd4c610cbd7e6b49e13729c470f42edc776934a5e`
- Compared with the earlier detailed mathematical audit, independent exact and symbolic checks, the revised repair, and the pinned manuscript's local source

## Findings by topic

### Exact model, counts, and source mapping

The report correctly distinguishes the common probability p from the labeled count B=N!p and the multiset count S=B/(k!)^n. The two models have the same rank-word distribution because each multiset word has exactly (k!)^n labeled realizations. The support bound X≤n(k−1)<kn, and the zero convention beyond support, are correctly retained.

The exact factorial-PGF identity is indeed contained in the pinned manuscript's Theorem 4.1. The report identifies the original all-orders theorem and its adjacent gap remark consistently with the manuscript. The contraction proof is complete and avoids reliance on an unproved integral interchange.

The newly explicit OEIS mapping agrees with the source manuscript and was independently checked against the three multiset entry definitions: [A114938](https://oeis.org/A114938) for multiplicity two, [A193638](https://oeis.org/A193638) for multiplicity three, and [A321633](https://oeis.org/A321633) for multiplicity four. The first two entries also explicitly link to the corresponding labeled sequences with factors 2^n and 6^n.

### Quantitative uniform theorem

The positivity inequality, factorial-moment domination, complete-homogeneous submultiplicativity, and support-restricted reciprocal-product expansion are transcribed correctly. Empty lists and M=0,1 are explicitly covered. The Touchard bound is a correct additional reformulation of the already audited constant: H_(L+1)(M)≤M^(2L+2), so summation gives e^a T_(2L+2)(a). It also gives zero when a=0 because 2L+2 is positive.

No large-degree or near-pole estimate is silently required. The retained full reciprocal product converts exactly into the factorial moment coefficient, and the final constant is independent of n.

### Integer powers and logarithm

The analytic family F(w,v), removable singularity at w=0, integer specialization w=1/N, coefficient formula for f_s, and finite differentiated Taylor remainder are correct. Using an enlarged v-disk supplies the neighborhood required for Cauchy estimates and the eventual nonvanishing statement.

The logarithm is correctly normalized at v=0, with the second logarithm chosen near 1. The warning about the principal branch on large complex disks is important and accurate. The scope remains fixed k and compact v; growing k and growing adjacency-count relative estimates are not implied.

### All-orders factorial cumulants

The formal identity T_w=exp A_w is correctly presented coefficientwise, without asserting analytic convergence of the infinite differential operator. The Bell-polynomial induction and polynomial-degree count are valid. The order-j factor contributes only previously established S_s coefficients, so the induction is noncircular. At t=1 the formal coefficients agree with the proven analytic asymptotic expansion.

Taking truncation L=r−2 and applying Cauchy yields the stated O(N^(1−r)) bound for every fixed r≥2, including r=2. The exact mean and distinction from ordinary cumulants are correct.

### Third-order and downstream formulas

All b_1,...,b_4, q_1,...,q_3, no-adjacency, fixed-local, count, and ratio formulas agree with the independent symbolic checks. The table for k=2,3,4,5 matches the correct conversion from N=kn to n powers. The expressions for A_1,A_2,A_3 include the correct Stirling contributions.

The ratio argument correctly subtracts discrete expansions without differentiating an uncontrolled discrete remainder. The local coefficient argument handles j=0 and j=1 and claims only fixed-j errors.

### Labeled and multiset inversion

The labeled inverse proof correctly establishes the stronger remainder O(1/(N0 log N0)) on the actual count sequence. Its treatment of arbitrary off-sequence Y and finite-index certification is appropriately limited. Retaining A_2,A_3 does not unjustifiably claim finer Newton accuracy.

For the added multiset note, write a_k=log(k!)/k and c_k=1+a_k. The leading carrier is f_S(x)=x(log x−c_k). If x=L/W_0(L exp(−c_k)), then log x−c_k=W_0(L exp(−c_k)), so f_S(x)=L exactly. Its derivative is log x−a_k, which verifies the printed Newton denominator. The remaining correction h(x) is unchanged, and the same Taylor argument applies with Y=S_(n,k), L=log Y+lambda, on that count sequence. These substitutions are therefore valid.

### Optional gamma tail

The gamma-mixture coefficients and shapes are correct. The cutoff, shifted-mean estimate, Chernoff optimizers, and factorial tail bound retain the audited proof without transcription errors. The proportional-degree estimate also remains correct when the requested degrees lie beyond support, where the contribution is zero.

### Source credit and limitations

The report clearly attributes the exact machinery and displayed coefficients, identifies the pinned original manuscript, and distinguishes the new repair from historical novelty. It accurately describes itself as AI-assisted and unrefereed. The older-literature descriptions agree with the already reviewed provenance; this integrated review does not constitute a new exhaustive literature search or an independent priority determination.

## Production note

The build log available during review contained a large overfull-box warning for a literal repository path in an earlier source revision. That path is absent from the current reviewed TeX. The warning therefore does not establish a defect in the current version. A clean rebuild and final visual check should establish that the current PDF has no corresponding overflow. No TeX changes were made by this review.
