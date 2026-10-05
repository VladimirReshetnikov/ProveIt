# Independent review of the A113226 contour expansion and inverse

Reviewed1October2026: `all_orders_proof.md`, together with the independently checked exact EGF derivation. No mathematical correction found.

1. The real arctangent identity gives T=z/2+(pi−3atan w)/w with w=sqrt(4exp(−z)−1). Its small-delta expansion has constant rho/2−3, square-root term−pi sqrt(delta)/4 and linear term+delta/2, all with the stated signs.
2. The integral denominator is uniformly nonzero in the open radius-rho disk. Equality on the boundary requires v=1/2 and equality between the first two exponential-series term phases, forcing z=rho. Compactness away from this point, together with the local slit formula, supplies the claimed slightly larger slit disk; no global assertion about remote branches is used.
3. The left circular arc plus the vertical chord is a valid positively oriented Cauchy contour enclosing zero and avoiding the cut. Its endpoints remain a fixed distance from rho. The arc is exponentially smaller. On the chord, the real-part deficit of(1−it)^(-1/2) is comparable to min(t²,1); the remaining local terms are bounded. Combined with |r+iy|>=r this gives exactly the n^(2eta) loss outside the n^(-5/6+eta) window. Fixed farther chord segments are handled by compact analyticity.
4. With h=n^(-1/6), u=a h^4+i gamma h^5 v and gamma²=2a/3, the h^(-1) terms cancel and the constant quadratic term is−v²/2. The remaining formal series begins at h and has the claimed parity. Its polynomial-Gaussian expansion, weak Gaussian majorant and minor-arc bound justify every fixed order. The factor1/z is correctly included by−(n+1)log(1−u), and the Jacobian produces C=exp(T0)sqrt(a/(3pi)).
5. Independently expanding the first two remaining powers gives R1=i5gamma³v³/(8a²) and R2=35gamma⁴v⁴/(64a³)+a²(1−rho)/2. Gaussian expectation of R2+R1²/2 is exactly a²(1−rho)/2−5/(36a), verifying the first correction and its normalization.
6. The inverse comparison uses the logarithmic derivative log(x/rho)+O(x^(-2/3)), so its displayed integer-ceiling error is correct. The reversion operator is Lagrange–Bürmann after changing variable to the Gamma-core logarithm. The first two reversion contributions give equation12; the omitted c2 term and log-cross terms fit its O(X^(-2/3)/log X) remainder. No unconditional nearest-integer rounding or canonical arbitrary interpolation is asserted.

This approves the exact EGF, the dominant-sector all-orders coefficient theorem and the displayed inverse scope. It is a conceptual mathematical review, not a PDF visual review or an exhaustive priority claim.

## Structural corollaries

The proposed non-D-finiteness corollary is valid. Let Z={log4+2pi i k:k integer}. Along any finite path avoiding Z, the lifted square root w is nonzero and never equals±i, because exp(−z) never vanishes. Thus arctan w continues along the lifted path. Near a chosen z_k its local branch is j pi+w+O(w³), for an integer j, and T=z/2+pi(1−3j)/w−3+O(w²). The principal coefficient never vanishes. Every z_k is accessible and is an essential singularity on the local square-root cover. A D-finite germ has only finitely many possible finite singularities on all continuations, so A is not D-finite. Multiplication of its coefficients by n! preserves P-recursiveness, giving the stated conclusion for a_n as well. Bounded live source searches found a non-D-finite statement for the different unlabeled Fishburn series; that must not be presented as this corollary's prior proof.

The autonomous differential-algebraic equation also checks. Put u=T'=A'/A. Differentiating(4−E)T'−2T=2+E−z gives E=(4u'−2u+1)/(u'+u+1). Its denominator is3 at zero. Applying E'=E and clearing denominators gives exactly
3(2u+1)u''−10(u')²−(2u+8)u'+2u²+u−1=0,
with u(0)=u'(0)=1. Replacing u by A'/A and clearing powers of A supplies a nonzero differential-algebraic equation for A. This does not contradict non-D-finiteness.
