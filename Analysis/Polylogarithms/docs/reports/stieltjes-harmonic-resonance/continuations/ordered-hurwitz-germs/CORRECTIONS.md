# Audit and integration safeguards

No substantive error was found in the specific current repository proof
sections examined for this continuation. The existing ordered double
Hurwitz germ, its sign convention, and its ray correction agree with the
new all-depth construction. This is not an audit of the whole manuscript
or of every incoming ZIP.

The following are concrete safeguards for integration, not claims that
the corresponding mistakes already appear in the canonical manuscript.

1. Keep the ordered suffix H2(v,w) in the depth-three polar decomposition.
   Its symmetric average loses the orientation constant. A merged
   argument H2(u+v,w) requires the compensating holomorphic divided difference.
2. Do not call the directional Laurent constant the harmonic regular value.
   Their exact difference is the counterterm in article equation
   `eq:counterterm`; at depth two it is -(d/c) gamma_1(a).
3. A nonlinear path is not specified by its tangent alone. Transverse
   depth d generally requires the (d+1)-jet. Paths contained in a prefix
   polar divisor still need a separate restriction prescription.
4. In the orientation sum, retain the additional -gamma_2(a)/2 term.
   Its omission changes ordered depth-three finite parts.
5. Translate reversed index order and Stieltjes signs/factorials when
   comparing the Matsumoto–Onozuka–Wakabayashi Laurent coefficients.
   Do not identify their analytic remainders with the harmonic-compatible
   remainders here without the divided-difference conversion.
6. Preserve the subtractions inside every Mellin integrand and the
   cancellation at z=0. The separated divergent pieces are not ordinary
   integrals on the full stated domain.
7. The Hurwitz generating identity is proved on Re(z)>-1, not merely
   in its initial Taylor disk. At a+z=0, use reciprocal Gamma rather
   than evaluating a spurious infinite Gamma denominator numerically.
8. Retain the unresolved S6, current S8, arithmetic-minimality, and
   period-independence statuses. No theorem here promotes them.

One numerical implementation refinement is documented separately: the
ray Cauchy grid was increased from 24 to 32 nodes to reduce positive-mode
aliasing. This is not an analytic erratum or a certified truncation bound.
