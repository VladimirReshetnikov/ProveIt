# Independent mathematical review of the compact supplement

Reviewed 25 October 2026 in a separately assigned AI-assisted task.
This is not external peer review, and it does not replace a full independent
native-calibration proof or the exact finite DAG checks.

## Sources inspected

- `agent_small/PROOF_COMPACT.md`, complete current proof.
- `agent_small/163-trace-radical/compact/PROOF.md`, especially the
  signed-index bootstrap and auxiliary third-index exclusion.
- `agent_small/164-unsquared-factors-linear-selectors/positive/PROOF.md`,
  especially the inverse correction, projection-before-denominator order,
  and completeness interface.

## Findings

The changed argument is sound as an ordinary proof conditional on the
explicitly named inherited root/index/native interfaces.

1. The inherited auxiliary bound is independent of the changed correction
   and of the new carrier shift. It gives |V|>8Q^2,
   Q>f^2, c<f/2, and therefore |b|>8f^3-1/2>4f^2.
2. The inequalities g<f/6 and C<2g, together with
   y<(3/2)|V| and |V|<(3/2)f|b|, give exactly

       |epsilon*g*y+C*V| < (7/8) f^2 |b|
                         < (7/32) b^2 < b^2/4.

   Both signs of b,V and both root signs epsilon are covered.
3. The inverse correction satisfies e*<=k-R-1<b before any sign of R
   is established, because cT-k+1>0. Hence rho<b^2/4 suffices for the
   B<=-1 contradiction. No lower bound on rho is required there.
4. The carrier shift S=CV is an integer polynomial. Once the root gives
   integral z, the old carrier z+S is integral too, so the congruence
   projection and the delayed cancellation at prime 3 are unaffected.
5. Positive completeness cannot be justified by an arbitrary coordinate
   shear because n must be positive. The supplement correctly chooses the
   negative root and proves a cofinal construction instead.
6. Its exact identity

       D0=(Q-1)C^2-QG=E[Q(U^2 E-1)-A^2 U^2 E]>0

   implies C>g sqrt(Q/(Q-1)). The Pell relation then yields the stronger
   quantitative estimate CV-g y>D0 V/[2C(Q-1)], so the required positive
   n follows for sufficiently large V.
7. The matrix [[2Q-1,2(Q-1)],[2Q,2Q-1]] has determinant one and preserves
   QV^2-(Q-1)y^2. It strictly increases a positive pair. Its finite order
   modulo cf^2 supplies unbounded positive pairs in the required residue
   class. The other terms used in the lower bound for n are fixed before
   this cofinal choice; no circular parameter choice was found.
8. The free polynomial identity for C^2-G and the degree bookkeeping in
   Section 6 are consistent: the degree-232 top part cancels, leaving
   Q M^2 V^2 U^2 E^2 of degree 224. Authenticating the literal DAG and
   complete homogeneous coefficient is a separate finite obligation,
   addressed by the supplement's checker rather than asserted by this
   review alone.

No gap was found in the new unbounded transport and centering proof.
The reported ten variables are strictly positive, not unrestricted integer
coordinates. The result is a degree/operation tradeoff and should retain
that domain and metric qualification.
