# Independent review of the final article's mathematical exposition

Reviewed on 25 October 2026 by a separate AI research agent. This is an ordinary mathematical review within the AI-assisted workflow, not outside human peer review or a proof-assistant certificate.

## Files and scope

The reviewed authoring sources are:

- `output/ConZFC_Trace_Radical_2026-10-25/report/main.tex`;
- `output/ConZFC_Trace_Radical_2026-10-25/report/direct_theory.tex`;
- `output/ConZFC_Trace_Radical_2026-10-25/report/verification_and_outlook.tex`.

The review covers the literal displayed compact formula, compressed soundness inequalities, signed index arguments, polynomial completeness map, diagonal-power label argument, selector and parity compatibility, and integral common-radical projection theorem. Generated residual/metric tables, PDF layout, coefficient payload reconstruction and final archive hashes are separate verification scopes.

**Conclusion: PASS**, at the article's stated inherited arithmetic and syntactic calibration boundary. The corrections identified during this review have been incorporated or explicitly accepted for the final text, as listed below. No unresolved mathematical blocker was found.

## Compact equation

The displayed formula agrees with the component's definitions: Q=4Delta^2U^2G=Delta(f^2-1), f=1+2a, and V=f(cT-R)-c. Only the coefficient in V is linearized; Q retains the square of the strong trace. The shared implementation f=a+(1+a) gives the same polynomial with the same operation count as the matched parent. The final principal label is 87 operations at degree 232.

The explicit doubled trace satisfies f=1 modulo c. This is essential: a generic strong Pell trace need only satisfy f^2=1 modulo c. The article correctly uses the stronger explicit identity to obtain V=-R modulo c while retaining V=-c modulo f.

The root-extraction and adjacent-Pell integrality handoff is consistent with the retained source hypotheses. The early ordinate bound gives c>8q^4. The proof separately excludes the main index 3, then both signs of auxiliary index 3, and obtains |b|>4g. The two index-three equations are exactly

    f(b-4Delta f)=c-(4Delta+3),
    f(b+4Delta f)=c+(4Delta+3).

The resulting bounds L=bV>0, gy<L/2 and |b|/q^6<L/2 are sound. In particular the proof does not assume R or B positive before establishing the transport estimates.

All exceptional negative ranks of the Lucas correction are covered. For R<=-4, the extra negative contribution from B dominates the adverse cubic because |C|>r/q^3, L>(f-1)r^2 and f-1>s^2. The exceptional rank R=0 is separately treated. After these exclusions the article is entitled to use C>0 and the inherited positive mask bounds, then the normalized rank and signed-index lemmas.

The compressed later decoding argument explicitly retains its source proof. It states the correct order: recover the bounded first index using the q^4 congruence, then recover the stronger q^6 divisibility. It does not cancel 6 as a unit modulo q, and the retained valuation argument includes primes 2 and 3.

## Polynomial completeness map

The article's map is an exact polynomial map, not a formal division by c:

    d=2Delta i^2 c^3E, f=1+cd,
    T_new=fT_old-dR.

Then b_new=f b_old and V_new=V_old identically. For the bV transport weight, setting

    n_new=n_old+(f-1)L_old B

preserves n-LB and hence the full carrier and polynomial. For the V^2 weight n is unchanged. The retained parent inequalities 0<R<c/2, B>=0 and positive b_old,V_old establish positivity of all changed coordinates. Soundness for arbitrary new zeros is independently proved; no unjustified inverse or zero-set bijection is claimed.

## Diagonal-power label carrier

The proof at F=t^t is correct. Equal factor counts are obtained before bounding coefficients. Each positive coefficient lies in [1,F], so each difference coefficient has absolute value at most F-1. This is the strict inequality needed for the lowest-nonzero-coefficient argument; a weak bound on individual product coefficients would not have sufficed. The case t=1 is correctly acknowledged.

The subsequent finite Horn flow argument is sound for single-conclusion rules. A conclusion outside the finite derivability closure needs at least one outside premise, so the prescribed positive imbalance at label 1 contradicts failure of derivability. Cyclic rule multisets therefore do not invalidate soundness.

The binomial selector argument uses only F>=Lambda_t, where Lambda_t=lcm(1,...,t); it does not need Lambda_t|F. The article explicitly distinguishes these facts. The two prime-power lemmas have the correct separate roles: one supplies a large selector for every row; the other supplies a compatible row for every prime in the completeness CRT construction.

For completeness, even h0 in t=16+h0^2 makes t even and v2(t^t)>=t. The odd square multiplier is chosen to be a sufficiently large odd multiple of the odd part of t!. Thus y is an even multiple of t!, the beta moduli are pairwise coprime and odd, and their CRT progression permits even beta representatives. The binomial modulus is odd by the exact valuation cancellation. These choices are cofinal and preserve the existence direction for every finite refutation.

## Integral common-radical projection

The stated theorem is correct. If an integral direction d lies in every Hessian kernel and has d_v=1, the displayed shear is unimodular. Every transformed quadratic part is independent of the new coordinate y_v. A residual with linear slope epsilon=+1 or -1 uniquely restores y_v as an integer quadratic polynomial. Substitution into the other residuals preserves degree at most two and gives an explicit polynomial bijection of integer zero sets.

The example verifies the mechanism directly. Constant invertible residual-row operations preserve the intersection of Hessian kernels, so the further-research statement that they cannot alone expose additional common-radical directions is correct. Full column rank modulo a prime implies a nonzero integer minor and therefore zero rational kernel; it certifies exhaustion of this particular projection method in the final chart, not global optimality.

## Corrections resolved during review

1. The auxiliary-index-three sentence was corrected from “neither sign” to “either sign”. The latter is the implication used by the two contradictions.
2. The direct completeness paragraph now explicitly chooses the odd square factor to include the odd part of t!. Merely knowing y is even would not have justified pairwise-coprime beta moduli after replacing the old carrier by t^t.
3. The early size assertion Q>c^2 and the rank-lemma premise c>2p are made explicit; both follow from the already established data.
4. Operation descriptions were updated for sharing f=a+(1+a), so the degree reductions do not claim an added gate.
5. The generic projection discussion uses degree at most four for its sum of squares. The three actual endpoints have exact degree four by their separate coefficient certificates.

## Calibration and limits

The article correctly distinguishes an ordinary proof formalizable in ZFC from a newly checked end-to-end proof-assistant object or encoded object-ZFC derivation. The compact branch retains its complete fixed native tuple; elementary interval bounds alone are not presented as a replacement for that tuple. The direct branch retains the named numerical-calculus and ZF/ZFC refutation equivalences. This review does not independently reconstruct every transitive calibration theorem or certify a global minimum.
