# Mathematical review and verification scope

3 October 2026

## Independent mathematical review

A reviewer separate from the derivation examined the generic quartic gating construction and the complete fixed-input normal-form application. The reviewed obligations included synchronized terminal clocks, half-open cycle and transition ownership, all intermediate flight and local-prefix times, original-frame quadratic shifts, strict affine sorting, pooled denominator clearance, private-parameter and private-slack zeroing on inactive charts, both exact ledgers, and the complete binary orbit formulas. No gap was identified in this argument conditional on the effective mass-four orbit classification from companion report 12.

The imported classification is a separate mathematical dependency. This addendum does not re-prove it or claim that an executable test constructed every possible profile. A further review checked the eight-witness binary formulas and the restricted uniform-gap strengthening. The latter is explicit and separately tested; it does not widen the generic compiler's fixed-input theorem.

## Exact final test evidence

The frozen quartic suite returned PASS using only exact integer and Fraction arithmetic:

- 5,208 direct binary cellular-automaton state comparisons
- 13,122 full eight-witness cube evaluations across both formats
- 1,920 wrong-output rejections
- 250 rational-coefficient single-chart evaluations
- 40 malformed-input rejections
- 5 immutability and snapshot checks
- 10 strict affine sorting checks
- 160 original-frame quadratic-shift checks
- 200 large-integer nonnegativity checks
- 50 canonical signed-coordinate pair checks
- 1,456 uniform-gap orbit comparisons
- 2,560 uniform-versus-fixed expanded-polynomial comparisons
- One demonstrated false witness accepted after removing inactive-chart gates and rejected by the actual compiler

Uniform checks include x = 0, 1, 2, 5, 19. The minimal permitted initial gap is therefore explicitly covered. Every expected fixed and uniform coefficient fixture is stored with integer coefficients.

The separate binary suite supplies a full radius-six conservation table/potential certificate and broader direct CA regressions. The radius/locality and global conservation arguments are also stated in the report. Independent reruns of the existing suites verify reproducibility; they are not described as independently implemented algebraic audits.

## Independently reviewed SOS refinements

Two optional refinements were added in separate files after the baseline freeze. The original compiler, baseline tests, and baseline fixtures remain unchanged. Both refinement arguments received separate mathematical review.

The generic SOS adapter removes the last selector, makes it the affine expression 1 minus the sum of the retained selectors, and uses the squared residual [E(E-1)]^2. It retains all squared inactive-branch gates. At a zero the natural sum E is zero or one, restoring one-hot selectors and the original unique-private-slack proof. Its witness count is B - 1 + K + M, with unchanged square-slot count. This is restricted to the SOS form; it does not transfer the sign argument to nonsquared product gates. Its binary instance has seven witnesses and ten squares. Tests cover 2,187 seven-witness cube points, 872 uniform-gap orbit comparisons, 10,935 uniform/fixed cube comparisons, 18 one-chart cases with no selector, two parameter-free cases, and 14 malformed-input rejections.

The stronger binary-specific specialization shares the same n, j, and inequality slack between the two charts and uses one Boolean selector. Because the two output maps differ only affinely, its seven residuals remain quadratic. It has four natural witnesses and seven squares, even uniformly in x = d - 7. Tests cover 5,208 direct CA states, 26,040 wrong-output rejections, 3,125 full four-witness cube evaluations, 122 valid-cube phase comparisons, and 32 malformed-input rejections. The proof invokes the already established complete timed chart partition, so the shared parameters and slack are uniquely determined. No generic shared-parameter optimization or minimality claim is made.

## Binary nonnegative real witness refinement

The four-witness binary certificate has a further independently confirmed property at integer external coordinates in the stated domain. Every real zero first has e in {0,1}; then n = x3 - d - e is integral, j = x1 - 3 on the right branch or j = d + n - 4 - x1 on the left branch is integral, and u = d + n - 6 - j is integral. Nonnegative real witnesses are therefore natural and give the same empty or singleton fibers. This reasoning uses the spatial equations and makes no analogous claim for arbitrary chart certificates or the one-witness return-time relation.

The restriction to nonnegative witnesses matters: x = t = 0, output (0,5,7,8), and witness (1,0,-2,3) make all seven residuals zero although the true initial configuration is {0,3,4,7}. This is a documentation and proof refinement; no code or fixture was changed.

## Correction recorded before freeze

A preliminary test assertion expected twelve roots in its small witness cube. Exact enumeration has fourteen roots. The expected test count was corrected; the compiler and theorem were not changed to satisfy that assertion. This is the only reported mathematical-test correction relevant to this release. A typesetting-stage cross-reference was also corrected before release.

## Limits

The natural-witness zero-fiber proof depends on the chart map being globally bijective to the timed orbit. The compiler does not decide injectivity of arbitrary input chart descriptions. Finite witness cubes, trajectory checks, and coefficient comparisons supplement the proof; they do not establish unbounded correctness by themselves. The generic compiler makes no rational or real witness exactness claim; the explicit four-witness binary nonnegative-real strengthening is proved separately above. Unrestricted real witness exactness, general uniform initial-input bounds, untimed witness uniqueness, and general Diophantine single-fold or finite-fold conclusions remain outside the result.
