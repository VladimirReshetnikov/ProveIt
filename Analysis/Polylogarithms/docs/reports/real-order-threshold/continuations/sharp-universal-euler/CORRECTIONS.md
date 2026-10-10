# Proposed corrections and scope guards

Pinned source: `3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f`.

## 1. Promote a research status, not an invalid earlier proof

In `chapters/10-discovery.tex`, the universal real-order Euler bound above the critical triangle is explicitly left open. Replace that status with the new all-parameter theorem. The source's warning that the Gaussian maximum alone does not prove the Euler bound was correct. The missing implication is now supplied by the separate `N >= 2` kernel inequality.

## 2. Retain sharper bounds on smaller domains

Keep the constant-one bound on `a >= 1` and the sharp critical/subcritical constant `pi/4 + log(2)/2`. The larger global constant solves a different uniformity problem. The new rational budget `57/50` works on the full positive quadrant, but is not sharp there.

## 3. Strengthen the certified maximum bracket

The source's bracket `1 < b_* < 2` is valid. Add the exact enclosures `1.3021 < b_* < 1.3023` and `1.1365611033 < C_* < 1.1365611046`, citing the new certificate. Keep all additional displayed digits explicitly diagnostic.

## 4. Do not extrapolate scaled-error monotonicity

The statement that all scaled errors decrease would be false. At integer orders `(a,b)=(4,1)`, `R_2 > R_1`, with an exact finite rational certificate in the package. The inspected source only claims the relevant scaled monotonicity on a restricted domain; this is a guard against an invalid future extension, not a claim that the canonical source contains that error.

## 5. Preserve analytic-value and measure hypotheses

The original boundary series can diverge even though the Euler transform converges to the principal analytic value. Retain that convention. The new representation is a positive expectation of a divided difference; it does not assert finite signed-moment representability below the source's threshold.

## 6. Keep independent conjectures open

No change is warranted to the status of the mixed `S_6` identity, the global integer normalized-radius conjecture, or numerical period independence. Certified numerical evaluation does not by itself prove a transcendental identity.

No complete source-manuscript audit, external refereeing, proof-assistant verification or literature-priority claim is represented by these proposed edits.
