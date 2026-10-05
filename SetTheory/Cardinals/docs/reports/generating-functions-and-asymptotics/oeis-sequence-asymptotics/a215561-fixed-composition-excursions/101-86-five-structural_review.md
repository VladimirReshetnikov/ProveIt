# Independent conceptual review of the balanced-excursion asymptotic

Reviewed1October2026: `asymptotic_proof.md`, Sections1–6. No mathematical correction found.

- The zero-step deletion and exact content extraction are bijective: length4n, absolute-size-two count2n, signed-size-two count0 and total height0 force n copies of each of the four nonzero steps.
- The root-product excursion formula has the stated sign and denominator. Its t=0 singularity is removable. The product of the two inside roots remains analytic through collisions between those roots; contour power sums justify this without choosing their individual branches.
- The base critical polynomial has the stated factorization. The other finite critical value is-4/9, with z=-1 corresponding to an infinite critical time. A fixed outer radius between1/4 and4/9 and analytic root separation give the required uniform local square-root transfer after shrinking the complex mark neighborhood.
- The torus equality conditions give exactly four mark points. Compactness away from them gives a common larger t disk with no kernel root on the height circle. Rouche continuation and the analytic root product give the claimed exponential outer-arc bound. The parity identities hold for every excursion; at the desired indices all four contributions have positive phase, giving factor4.
- The phase Hessian is the mark covariance after eliminating height. Its entries1/4 and1/10, determinant1/40, and the N=4n normalization give precisely the claimed constant K after zero insertion.
- The critical-root amplitude formula follows by factoring out the double root tau. If zeta is the remaining small root, criticality gives tau*zeta*v=-exp[-arcosh(c0)], recovering the displayed logarithmic amplitude without an omitted mark factor.
- I checked the transfer correction from the x and x^3 coefficients. The angular Gaussian contractions yield the signs and factors of the amplitude, mixed cubic, quartic and squared-cubic terms. Exact symbolic recombination confirms c1=13(sqrt(5)-5)/50; see structural_review_constants.json. This was a check of the written formulas, not a repetition of the author's numerical sequence tests.
- The nondegenerate saddle, uniform transfer, parity cancellation and exponential outer control justify every fixed order of the Poincare expansion. The field Q(sqrt(5)) follows from the algebraic root jets and normalized Gaussian moments.
- The Lambert-W branch, first inverse correction and the shrinking integer-rounding qualification are correct. Concatenation gives eventual/indeed immediate strict monotonicity for the threshold discussion. The claim does not identify every subdominant exponential sector and does not prove the unused recurrence.

This is an independent mathematical read and exact normalization check. It makes no visual-layout or manuscript-transcription claim.

## Second correction and final finite-recipe review

The second correction also passes. `check_second_assembly_fast.py` independently reconstructs the implicit root through degree6, all phase jets through6, and the critical amplitude through4 using finite series convolutions and the algebraic small-root expression, rather than logarithmic/acosh Taylor composition. It reconstructs all three marked A1/A0 jets from the coalescing-root expansion and verifies the equal-mark e5 and A2/A0 by direct algebraic roots. Its separate Gaussian convolution yields b2=681/32−77sqrt(5)/10 and c2=36/25−63sqrt(5)/125 exactly. The complete result is in `check_second_assembly_fast.json`.

The finite all-orders coefficient recipe in the final article has the correct Gamma-ratio transfer coefficients, angular phases, mark amplitudes and N=4n rescaling. The additional inverse term is also correct: ell2=c2−c1²/2=(213−83sqrt(5))/500, and subtracting ell2/[nu0(c nu0−3)] leaves an O(nu0^(-3)) error. The omitted interactions with the first shift start at that order. All first- and second-order statements in the final manuscript are mathematically cleared.
