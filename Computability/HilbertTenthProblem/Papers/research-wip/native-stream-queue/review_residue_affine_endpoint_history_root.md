# Root review of the coprime endpoint-history report

**Verdict: PASS for the stated fixed-horizon interface and its two limitations.** The endpoint lemma eliminates intermediate states only under its triangular coprimality condition. The resulting source still has 2T positive selector witnesses and T-dependent constants. It does not lower the complete universal bound of 84 operations.

## 1. Mathematical review

I read the full author note and helper as inert text. In the varying-denominator identity, reduction modulo the first denominator leaves exactly the first affine numerator times the suffix product of later numerators. The stated condition makes that suffix and the first numerator coefficient units. The first state is therefore integral and has the intended residue. Cancelling the first denominator leaves the same problem on the suffix. This proves both reconstruction and uniqueness, including denominator one and the empty word. Individual reduction of each affine fraction would not justify the argument; the cross-time coprimality condition matters.

In the fixed-radix construction, positive complementary selectors force exactly the b interpolation nodes. Induction gives N_j=L^j times the usual denominator-cleared numerator. The final equation cancels the common L^T, so the preceding lemma applies. Starting from positive x, reconstructed states are positive because the specified map is total positive. No hidden supplied intermediate state or division quotient is required. Conversely the actual orbit supplies exactly one selector tuple.

The generic degree estimate follows from increasing the numerator degree by at most b−1 per update, starting at degree one. For a common numerator, all nonlinear terms are individual C(s_j); the degree bound is independent of T. This is a fixed-horizon degree reduction, not a bound on a single variable-duration polynomial.

Remark 1 is an exact projected counterexample, stronger than merely an invalid witness: the formal even/odd itinerary from 1 reaches 2, while the actual map stays on 2^(j+1)−1 and never reaches 2. The earlier prime-payload compiler explicitly has K dividing its branch numerators and modulus, so this endpoint reduction does not transfer to it under the present hypotheses.

Remark 2 supplies terminating algorithms in all three common-slope cases. For a<b, the displayed H satisfies aH+C<=bH. For a>b, n>C+1 implies (a−b)n+c_r>0, so escape beyond both H and the target is permanent. For a=b, the finite residue trajectory is ultimately periodic and each cycle position is an arithmetic progression. Target membership is then decided by finitely many linear equations. The restriction to specified integer targets is explicit; no claim about arbitrary external acceptance predicates is needed.

## 2. Independent operation accounting

For the generic source, the two padded Horner evaluations per step use 2(b−1)T multiplications and the same number of additions. The updates use T products with the previous numerator, T−1 nontrivial fixed weights, and T additions; the final numeral multiple of y uses one product. The selector equations add T additions. Thus the equation graph costs 2bT M+2bT A. Adding T+1 residual subtractions, T+1 squares and T joins gives (2b+1)T+1 M and (2b+2)T+1 A.

For common numerator and T>=2, the C evaluations use (b−1)T of each operation. The weighted sum uses T products, T additions and two endpoint scalar products; selectors use T additions. Hence the graph costs bT+2 M and (b+1)T A. The same SOS overhead gives the author's stated totals. At T=1 the sole unit weight is omitted, recovering 2b+2 for the graph and 2b+7 for the SOS. These are literal padded schedules, not minima.

The predecessor graph has three equations and three witnesses per step. Joining T steps requires T−1 additional state witnesses. Its common SOS therefore adds 3T residuals, 3T squares and 3T−1 joins to T copies of its 4b+3 graph, giving (4b+12)T−1 with 4T−1 witnesses. The new comparison is consistent. The separate packed-history report's 134-operation, 21-witness result concerns an arbitrary nonempty duration and is not directly beaten by this T-dependent family.

## 3. Evidence provenance and boundaries

The accompanying root JSON binds the full note, helper, frozen author receipt, and the two predecessor texts used in this review. It checks all ten saved arrays only as inert definitions: operation counts, unique names, operand availability, equation references, output liveness and declared witness counts. No saved array is numerically or symbolically evaluated. The helper was not executed or imported; its recorded 936 word cases, 120 zeros, 160 selector corruptions and 468 varying-denominator cases remain author-run evidence. My mathematical review and static inspection are independent of rerunning those checks.

The predecessor read scopes here were lines 1–115 of the factored-step note and lines 1–80 of the packed-history note. The author reports its own broader and additional reads separately. A whole-file hash is not evidence of a full mathematical reread.

No predecessor theorem is refuted or removed. The report's numbered Remarks 1–2 retain the failed nonunit endpoint generalization and the limitation of a common-slope point-target proposal. The open obligation is a fixed-arity representation of the selected weighted itinerary with all selector and weight constraints paid. None of the present evidence discharges that obligation.
