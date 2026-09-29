# Status and claim boundaries

## Written theorems in this article

1. **Constant-slope rigidity:** in characteristic zero, a polynomial lift
   with each invariant numerator affine in v and nonzero constant Jacobian
   has constant r_v. There is no ordinary-degree cap.
2. **Complete class description:** an explicit tame branch and one
   noninjective core up to diagonal scalings/source shear. The normal forms
   themselves existed in the prior constant-slope report; the enlarged
   scope follows from the new rigidity theorem.
3. **Reduced-base extension:** positive-degree slope coefficients vanish
   over every reduced Q-algebra. No ring-wide two-branch classification is
   claimed when constants can be zero divisors.
4. **Nilpotent failure:** explicit normalized dual-number solutions have
   nonconstant slopes in arbitrary degree.
5. **Universal second-order obstruction:** any nonzero first-order third
   slope at (p,q,r)=(v,t,1) cannot lift to epsilon³=0 while all numerators
   remain affine in v, even with unrestricted t-degree corrections.
6. **Sharp repair and formal extension:** quadratic v-degree is necessary
   and sufficient for the canonical second-order repairs; a standard
   divergence-free formal-flow construction gives unrestricted formal
   integration. No polynomial parameter family or uniform degree bound
   follows from that exponential construction.
7. **Finite coefficient schemes:** specified slope coordinates are nonzero
   nilpotents, including in the local ring at the tame point, and supply
   independent obstructed tangent directions of arbitrarily large dimension.

## Verification actually performed

- All twelve groups in `code/verify_results.py` passed with exact arithmetic.
- Generic determinant/coefficient identities and obstruction formulas were
  checked symbolically; the normal form was checked with arbitrary symbolic
  e(t), beta, and gamma.
- Finite examples, collisions, degree profiles, and input validation were
  checked as recorded in the JSON output.
- PDF was compiled and rendered for layout inspection.

The all-degree pole argument, unique-factorization argument, reduced-base
argument, and classification logic are written proofs, not consequences
of a finite search. No proof assistant was run. No referee review or
independent research review has taken place.

## Attribution and scope

The prior repository report explicitly posed the nonconstant-slope
extension question. Its constant-slope forms, shear extension, tame inverse,
core support profile, and degree spectrum are credited as prior material.
The original noninjective map is not new here. The cubic field model and
S3 normal closure are included with a self-contained proof, but no priority
is claimed for those facts about the original core.

The targeted literature review did not establish worldwide priority for
the new classification or deformation statements. The results concern
source weights (-1,1,2), target weights (2,1,-1), and affine dependence on z.
They are not statements about unrestricted Keller maps, global sparsity,
minimum ordinary degree outside the class, or the entire coefficient scheme.
