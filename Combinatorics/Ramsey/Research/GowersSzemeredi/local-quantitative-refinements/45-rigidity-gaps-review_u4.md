# Internal AI cross-check of the fourth-uniformity derivation

This document records an internal cross-check performed by a second AI agent during preparation of this article. It is not an external or human peer review, and it does not establish publication priority. The review covered the working fourth-uniformity proof notes and their exact verifier before final LaTeX integration. The corresponding packaged material is in `sections/u4.tex` and `code/verify_u4.py`; this record should not be read as a separate line-by-line audit of every later editorial change.

No mathematical error was found in the reviewed derivations. The constant is a rigorously certified improvement, not asserted optimal.

## Analytic checks

1. **Fourier cube identity.** The four Fourier constraints for the 3-cube have an affine parameterization over every abelian frequency group without any division. Explicitly, if the four initial frequencies are r000=a, r100=b, r010=c, r001=d, the equations force r110=b+c-a, r101=b+d-a, r011=c+d-a, and r111=b+c+d-2a. Thus the displayed affine parameterization is valid even with torsion. Squaring the parallel-face sum gives identity (B) with normalized Fourier coefficients and no omitted group-order factor.
2. **The axes and their intersection.** The s=0 and t=0 axes each sum to E(lambda). Their common term is (sum lambda^2)^2=H^2. Keeping their union proves (C), because every term of the full Fourier expression is nonnegative.
3. **The three pairing families.** Each has weight H^2. Each pairwise intersection has weight M. The triple intersection is the single zero frequency in odd order, with weight lambda0^4=v^2. The bound M<=v^2+w^2/2 follows by grouping distinct nonzero opposite pairs. Substitution gives precisely v^2+10vw+2w^2. Both the zero-frequency bookkeeping and the odd-order hypothesis are essential and correctly retained.
4. **All even moments.** The expansion of the real autocorrelation is a nonnegative-coefficient character polynomial; averaging each word gives zero or its positive coefficient. Retaining balanced words is valid despite extra torsion relations, which can only increase the moment. The coefficient comparison uses product k_j!<=m!, followed by the multinomial theorem, and gives binom(2m,m)/2^m exactly.
5. **Recursion.** For real f, g_h=f*T_hf is the correct multiplicative derivative. V+W=U3(f)^8, and V=E R^4=E(lambda). Thus W>=V-1 follows from the same axes inequality under S=1. No moment of a different random variable has been substituted.
6. **Rational certificate.** I expanded P^2 and checked every coefficient in (J). The replacement of W by V-1 is legitimate because the argument of the squared term is positive. The coefficients of A and B are positive, so their lower moment bounds may be inserted. The remaining polynomial is exactly 4795/832+(3/8)(V-3/2)+(9/8)(V-3/2)^2. The companion verifier reproduces these identities with rational arithmetic.
7. **Cosine dual function.** For odd q>=5 the four congruences have even left sides between -8 and 8. A nonzero multiple of odd q would either be odd or have magnitude at least 10; hence the congruences really are integer equalities. The six surviving total-sign counts yield the stated dual function. The phi1 and phi3 frequency pairs remain disjoint for q=5; phi5 is then constant and has zero inner product with either. More generally phi3 cannot alias phi5 for any odd q>=5. Hence the inner products 222 and 54, and the derivative -864, are correct. Vertex transitivity gives the factor 16 in the first variation. For q=3 the phase-dependent enumeration is needed and was supplied; its minimum 262 exceeds 222.
8. **Ratios and homogeneity.** With S=U2^4 the certificate U4^16>=C S^4 gives c4<=C^{-1/4}. The five-point lower bound uses S^4/Q4, not an incompatible power. Dividing f by 2 gives a 1-bounded mean-zero example and leaves the ratio unchanged. Monotonicity extends the same upper bound to every d>=4.

## Supplementary exact finite verification

- Reran the companion verifier successfully: rational certificate, sign enumeration, independent generating-function DP, fifth-order character aliases, and exact five-point histograms all passed.
- Recomputed with a separate algorithm the five-point cube averages by the derivative recursion Q_d(f)=E_h Q_{d-1}(f*T_hf), with base Q_1(f)=(E f)^2. This is a separate algorithm from the direct cube histogram. It gives Q2=94/25, Q3=19208/625, Q4=6468874/3125 exactly.
- Verified with the same separate algorithm the mean-sensitive U3 inequality on every function with values in {-1,0,1} on Z/3 and Z/5 using the same exact derivative recursion.

The general inequalities rest on the analytic derivations above; the finite checks supplement them.

## Optional exposition improvements

- The affine Fourier parameterization can be justified by the four explicit eliminated variables above, avoiding the appearance of an unproved equivalence.
- When stating the cosine first variation, mention vertex transitivity of the cube average as the reason every differentiated vertex contributes equally.
- Distinguish the strictly improved certified constant from the still-open optimal constant. The current notes already do this clearly.

