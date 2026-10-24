# Integrated article review

**Date:** 2026-10-24.  
**Reviewer:** the independent positive-frontier / arithmetic-review assistant.  
**Reviewed article:** `report/report.tex`, `report/soundness.tex`, `report/direct.tex`, `report/closing.tex`, and `report/coefficient_recipe.tex` in the assembled `ConZFC_Valuation_and_Signed_Certificates` package.  
**Conclusion:** no blocking mathematical defect found in the new reductions, their current article proofs, or the exact degree arguments. Two direct-section wording corrections found during review have been applied. The scope remains ordinary mathematics and exact finite certificates, with the explicitly identified inherited unbounded calibration theorems; this is not a new proof-assistant derivation of the whole internal ZFC biconditional.

This review supplements `PRIME_TWELVE_INDEPENDENT_REVIEW.md` and `DIRECT_QUARTIC_INDEPENDENT_REVIEW.md`. It concerns the integrated exposition and the highest-risk proof interfaces, rather than repeating the arithmetic artifact checks recorded in those reviews.

## 1. Zero scale, denominator, and initially negative guard

The proof establishes `delta != 0` on every integer assignment, since `Delta>1` and `Q=(Delta I)^2` is either zero or strictly greater than one. The norm's cleared rational interpretation is therefore valid at every integer zero.

At `S=0`, nonzero `H` forces `I=0`, `Q=0`, and `delta=-1`. Both supplied polynomials reduce to `(A^2-B^2 Dm)^16`. Its two factors are values of `H^5*pi((u +/- sqrt(Dm))/H)` in real fields of degree at most two. The new quintic has no root in those fields. Thus a zero has nonzero `I,s,r,c,S` before any valuation or positivity argument uses them.

After division by S, the first four nonzero squared radical orders at 3 are `-2*v3(S), 0, 2, 4`, with `v3(S)>=5`. When nonzero, the guard radical's squared order is `6+v3(Dg)>=6`, and may be odd. Every subset of at least two surviving roots consequently has a unique even least squared order. If `Dg=0`, omitting its zero root is valid. If `Dg<0`, the same algebraic noncancellation lemma applies in the complex multiquadratic splitting field and forces a contradiction by rational root extraction. No premature realness or positivity assumption is made.

The lemma's finite conjugate-product proof is correct: after dividing by a rational prime power, its product is a polynomial in the squared roots over the local ring, reducing modulo the prime to a nonzero power of the distinguished unit square. The automorphism argument then forces each root of a rational signed sum to be rational. This remains valid for negative radicands and dependent square classes.

## 2. Strict guard completeness

The joint positivity lemma is correct in both directions. For positive integers `A1,A2`, put `M=A1+A2-1`. Then `1<=M<=A1*A2`. Between consecutive integer squares `a^2` and `(a+1)^2`, the nearest-square error for an integer M is at most a. Unless M is itself a square, `a<sqrt(M)`; at a square the error is zero. Thus the error is strictly smaller than `sqrt(M)` and hence than or equal to the required threshold in the strict guard inequality. This proves the existential converse, including the boundary `A1=A2=1`.

For soundness, the recovered integer square `Dg` and nonzero s imply `P>0`; the joint lemma yields both strict guards. The determinant-cone argument correctly gives common signs of `q,F,C,alpha` and does not use the later power-of-two conclusion. Its separate proof of `R>0` works for either sign of q using the authentic inequalities `0<MC<beta<MF`.

## 3. Auxiliary integrality and the main congruence

The adjacent-coefficient descent has the needed hypotheses `Q>1`, integral V, and rational y. The equation gives `b^2 | Q-1` for the reduced denominator b. The displayed norm-preserving transform keeps V integral, keeps b unchanged, and strictly decreases `|V|` until `|V|=1`, where b must equal one. Both the strict inequalities and exclusion of `V'=0` are correct.

For the integral-radicand companion, the article correctly sets `y=tilde_y/delta` for the Pell descent while retaining the integral `tilde_y` in that companion's root sum. The primary uses y in its root sum. Both therefore give `H^5 | A+B*d`.

The monicity valuation argument restoring `gamma=(d-b0)/H` works for every prime dividing H, including 3 and 19. If a candidate argument has p-adic order below `v_p(H)`, its fifth power has strictly smaller order than all three other terms of the homogeneous quintic. Extra factors of 3, 19, or 57 in the other coefficients only increase those other orders. Hence `H` divides the argument and gamma is integral.

## 4. Normalized strong-kernel interface

The normalization avoids the invalid parity shortcut `r_old=(Delta*s*r-1)/2`. From `c_*^2 | |I|`, integral Pell classification and strong divisibility give `p | m`. Writing `m=p*ell`, the unit expansion modulo `c_*` gives

```
psi(p*ell)/c_* = ell*chi(p)^(ell-1) (mod c_*).
```

The left side is divisible by `c_*`, while `chi(p)` is coprime to it. Thus `c_* | ell`, yielding the full `p*c_* | m` input. This proof requires no oddness of `I/c^2`.

The displayed integer restorations of `o` and `j_aux` expand exactly to `V=f*o-c=c*j_aux-R`. The relations for `rho=Delta*I` also match the inherited interface. The auxiliary index is odd because an even-index first Pell coordinate is congruent to `+1` or `-1` modulo `|rho|`, whereas the relevant coordinate is divisible by `rho` and `|rho|>1`. Again no odd-multiplier assumption is used.

The subsequent `p=R`, first-index, orientation, and native-decoding conclusions are explicitly invoked as inherited unbounded arithmetic theorems, with the applicable proof sources identified. The article does not assert that its new finite tests establish those theorems. The final sign selection from `X=sgn(c)*2^R`, odd R, and `X=2 mod3` is correct.

## 5. Full interpolation and noncircular witness selection

The article preserves the crucial quantifier order: choose fixed I and f from the canonical data and the positivity witness s, then represent any requested residue class modulo that same I.

For an odd prime dividing I, the first zero index of the Lucas sequence either equals p when p divides Delta, or is prime to p when p does not divide Delta. The elementary unit-binomial lifting calculation therefore gives `v_p(I)>=v_p(m)`. The even-prime formula for even base and even index is correct. These results justify `gcd(m,I^2)|I`.

The period modulo `f^2` is correctly `lambda=4*m*f`. Raising `alpha^(4m)=1-4f*alpha^m (mod f^2)` to the positive integer f proves that period. It yields `gcd(lambda,4I^2)|4I`, so the two congruences prescribing L are compatible for every requested class. The argument does not incorrectly use `4m` as the period.

The odd Chebyshev identities correctly give both `V0=-c (mod f^2)` and `V0=-R+4I*a0 (mod 4I^2)`. The factor 4 is retained in the second modulus. Since f is odd and coprime to I, the numerator is divisible by `4I*f^2`; after division, `f^2=1 mod I` gives exactly `T=a0 mod I`.

After I and f have been fixed, intersectivity supplies a root class for the translated quintic modulo I. Interpolation then supplies T and y, and the final coordinate n is integral. The `P=1` guard case is correctly handled by `s=1,g=0`; the case `P>=2` uses a positive nonsquare coefficient congruent to 2 modulo 3. No circular witness choice or uniformity gap appears.

## 6. Denominator-free norm and exact degrees

The rank-four algebra recipe matches the stated three-root identity. In particular, the intermediate vector represents `delta^4 F8(x-u-v; a1,a2,N/delta)`; the two quadratic norms then give `delta^16 F32`. The clearing identity is polynomial even at formal `delta=0`, although the integer specialization separately excludes that boundary.

Evenness and weighted homogeneity put the cleared norm in the six inputs

```
delta*Z^2, delta*B^2*Dm, 9*delta*S^2*Df,
81*delta*S^2*Dt, 729*delta*S^2*Dg, S^2*Cy.
```

Their degrees are `102,102,120,134,146,150`. The last input has the unique largest degree and its sixteenth-power coefficient is one. Hence the primary's degree-2400 part is exactly `(S^2*Cy)_top^16`, with the stated leading form

```
2^320 * a0^288 * I0^128 * (4*I0*T-R0)^32.
```

Selecting the maximal T power proves the positive coefficient `2^2400*3^1440*beta^1152` at the displayed degree-2400 monomial. No other fixed coefficient port can cancel it. The companion's unique degree-182 radicand similarly yields exact degree 2912 and its stated positive degree-2912 coefficient. Thus these are attained specialized degrees, not merely upper bounds from the circuit graph.

## 7. Direct quartic and corrections applied

The independently checked direct endpoint remains 1,190 unrestricted integer coordinates, 600 quadratic residuals, 26,411 collected monomials, exact degree four, and coefficient height 83,900,628. The ordinary guard and signed projection proofs in the article agree with the independent audit.

During integrated review I identified two exposition issues, now corrected by the author:

1. Nine of the 34 deleted pivot rows are themselves guards. Their constraints are preserved through exact restoration formulas rather than literally remaining as residual rows. The article now says so.
2. The sufficient degree condition for a quadratic restoration is that its target appear only as a scalar linear term in each other row, with no target-containing product. The article now states that condition explicitly.

Neither issue invalidated the literal artifact or its mathematical projection theorem; the independently replayed inverse formulas already preserved all guard conditions.

## 8. Final assessment

The article clearly separates three claims: the new ordinary arithmetic reductions, reproducible exact finite artifact identities, and imported unbounded consistency calibration. The complete internal proof-assistant endpoint remains outside the new deliverable. The reported improvements are tied to identified repository parents, with different natural, positive, and unrestricted integer domains kept separate and no global minimality or worldwide-priority claim.

The integrated article is ready for release subject to the root author's final document and package checks.
